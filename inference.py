"""Stateless local inference, durable receipts, provenance, and the main-run approval gate."""
from contextlib import contextmanager
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.request import Request, ProxyHandler, build_opener
import json
import os
import re
import tempfile
import time
import uuid
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
PROTO = json.loads((ROOT / "protocol.json").read_text("utf-8"))
HTTP = build_opener(ProxyHandler({}))  # Keep loopback traffic local even with a system proxy.
API = "http://127.0.0.1:1234"
if PROTO["endpoint"] != API + "/v1/chat/completions":
    raise ValueError("This study targets the local LM Studio server only.")


def now():
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def digest(value):
    if not isinstance(value, bytes):
        value = json.dumps(value, ensure_ascii=False, sort_keys=True,
                           separators=(",", ":")).encode("utf-8")
    return sha256(value).hexdigest()


def read(path):
    return json.loads(path.read_text("utf-8"))


def save_text(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as tmp:
        tmp.write(text.encode("utf-8"))
        tmp.flush()
        os.fsync(tmp.fileno())
    os.replace(tmp.name, path)


def save(path, value):
    save_text(path, json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def freeze(path, value, label):
    if path.exists():
        if read(path) != value:
            raise ValueError(f"{label} changed after it was frozen. Keep this run intact and use a new study folder for a revised run.")
    else:
        save(path, value)


@contextmanager
def run_lock(split):
    path = ROOT / "runs" / split / ".lock"
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a+b") as handle:
        if not handle.tell():
            handle.write(b"0")
            handle.flush()
        handle.seek(0)
        try:
            if os.name == "nt":
                import msvcrt
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as exc:
            raise RuntimeError(f"Another process is working on {split}.") from exc
        yield  # Closing the handle releases the lock, including after interruption.


def bank(split):
    if split not in ("pilot", "main"):
        raise ValueError("Choose pilot or main.")
    path = ROOT / "dataset" / f"{split}.jsonl"
    rows = [json.loads(line) for line in path.read_text("utf-8").splitlines() if line.strip()]
    count, prefix, width = (10, "P", 2) if split == "pilot" else (100, "M", 3)
    if [r["id"] for r in rows] != [f"{prefix}{n:0{width}d}" for n in range(1, count + 1)]:
        raise ValueError(f"Expected {count} ordered, distinct {split} IDs.")
    for r in rows:
        if not all(r[k] for k in ("problem", "reference_proof", "provenance", "verification_note", "topic", "title")) or len(r["rubric"]) < 3:
            raise ValueError(f"Incomplete record {r['id']}")
        if r["difficulty"] not in ("Easy", "Medium", "Hard") or not isinstance(r["needs_human_verification"], bool):
            raise ValueError(f"Invalid metadata for {r['id']}")
    if len({r["problem"] for r in rows}) != count:
        raise ValueError("Duplicate problem.")
    return rows


def questions(split):
    # The transport receives just this allowlisted projection.
    return [{"id": r["id"], "problem": r["problem"]} for r in bank(split)]


def select_protocol(split):
    archived = ROOT / "runs" / split / "protocol.json"
    selected = read(archived if archived.exists() else ROOT / "protocol.json")
    if selected["endpoint"] != API + "/v1/chat/completions":
        raise ValueError("This study targets the local LM Studio server only.")
    PROTO.clear()
    PROTO.update(selected)


def design(split):
    return {"protocol_sha256": digest(PROTO), "questions_sha256": digest(questions(split)),
            "dataset_and_rubric_sha256": digest(bank(split))}


def authorize_main():
    path = ROOT / "runs/main/approval.json"
    if not path.exists():
        raise ValueError("Main is locked. Explicit approval of the pilot, rubric and prompts is required.")
    approval = read(path)
    if (approval.get("approved") != ["pilot", "rubric", "prompts"] or approval.get("design") != design("main")
            or approval.get("grading_policy_sha256") != digest((ROOT / "grading-policy.md").read_bytes())):
        raise ValueError("The main design differs from the approved version. Review the current design first.")


def request_payload(item, stage, previous=None):
    if stage not in ("first", "A", "B", "C"):
        raise ValueError("Unknown stage.")
    if stage in ("A", "B"):
        if previous is None:
            raise ValueError("Missing first proof.")
        prompt = PROTO["review_format"].format(instruction=PROTO[stage], problem=item["problem"], proof=previous)
    else:
        prompt = PROTO["first"].format(problem=item["problem"])
    round_number = 1 if stage == "first" else 2
    seed_key = f"proof-study-v1/{item['id']}/{round_number}".encode()
    seed = int(sha256(seed_key).hexdigest()[:7], 16)
    return {"model": PROTO["instance"], **PROTO["generation"], "seed": seed,
            "messages": [{"role": "system", "content": PROTO["system"]},
                         {"role": "user", "content": prompt}]}


def environment():
    def inventory():
        with HTTP.open(API + "/api/v1/models", timeout=10) as connection:
            return json.load(connection)["models"]

    cli = shutil.which("lms") or str(Path.home() / ".lmstudio/bin/lms.exe")
    try:
        models = inventory()
    except URLError:
        subprocess.run([cli, "server", "start", "--bind", "127.0.0.1", "--port", "1234"], check=True)
        models = inventory()
    model = next((m for m in models if m["key"] == PROTO["model_key"]), None)
    if not model or model["quantization"]["name"] != PROTO["quantization"]:
        raise ValueError("The specified local model and quantization were not found.")
    instance = next((x for x in model["loaded_instances"] if x["id"] == PROTO["instance"]), None)
    if instance is None:
        subprocess.run([cli, "load", PROTO["model_key"], "--context-length", str(PROTO["context_length"]),
                        "--parallel", "1", "--identifier", PROTO["instance"], "--ttl", "1800", "-y"], check=True)
        model = next(m for m in inventory() if m["key"] == PROTO["model_key"])
        instance = next((x for x in model["loaded_instances"] if x["id"] == PROTO["instance"]), None)
    if not instance or instance["config"]["context_length"] != PROTO["context_length"]:
        raise ValueError("Load the study model at the specified context length. See README.md.")
    return {"checked_at": now(), "key": model["key"], "quantization": model["quantization"],
            "selected_variant": model.get("selected_variant"), "size_bytes": model["size_bytes"],
            "instance": instance["id"], "load_config": instance["config"],
            "advertised_reasoning": model["capabilities"].get("reasoning")}


def proof_text(content):
    # Preserve the submitted mathematics byte-for-byte inside the output envelope.
    if not content:
        return "", "empty"
    visible = re.sub(r"\A\s*<think>.*?</think>\s*", "", content, count=1, flags=re.S)
    start = visible.find("<proof>")
    if start >= 0:
        end = visible.find("</proof>", start + 7)
        if end >= 0:
            return visible[start + 7:end].strip(), "tagged"
        return visible[start + 7:].strip(), "open_tag"
    return visible.strip(), "untagged"


def record_path(split, stage, pid):
    return ROOT / "runs" / split / "responses" / stage / (pid + ".json")


def infer(split, item, stage, env, previous=None):
    dest = record_path(split, stage, item["id"])
    payload = request_payload(item, stage, previous)
    if dest.exists():
        old = read(dest)
        if old["request"] != payload:
            raise ValueError(f"Saved request differs for {item['id']} {stage}.")
        return old
    began, tick = now(), time.monotonic()
    receipt = ROOT / "runs" / split / "attempts" / f"{stage}-{item['id']}-{uuid.uuid4().hex[:12]}.json"
    log = {"id": item["id"], "stage": stage, "started_utc": began,
           "endpoint": PROTO["endpoint"], "request": payload, "environment": env}
    save(receipt, {**log, "status": "issued"})
    body = None
    try:
        post = Request(PROTO["endpoint"], data=json.dumps(payload).encode(),
                       headers={"Content-Type": "application/json"}, method="POST")
        with HTTP.open(post, timeout=1800) as conn:
            body = conn.read().decode("utf-8")
        raw = json.loads(body)
        choice = raw["choices"][0]
        message = choice["message"]
        input_count = raw["usage"]["prompt_tokens"]
        output_count = raw["usage"]["completion_tokens"]
        if not all(type(n) is int and n >= 0 for n in (input_count, output_count)):
            raise ValueError("Endpoint did not return actual token counts.")
        reason = choice["finish_reason"]
        if reason not in ("stop", "length", "max_tokens"):
            raise ValueError(f"Unexpected finish reason {reason!r}")
        content = message.get("content") or ""
        proof, envelope = proof_text(content)
        result = {**log, "finished_utc": now(), "elapsed_seconds": round(time.monotonic()-tick, 2),
                  "raw_response": raw, "proof": proof, "proof_envelope": envelope,
                  "input_tokens": input_count, "output_tokens": output_count,
                  "finish_reason": reason, "truncated": reason in ("length", "max_tokens"),
                  "budget_reached": output_count >= PROTO["generation"]["max_tokens"],
                  "attempt_receipt": receipt.name}
        save(dest, result)  # Durable canonical success before logging or advancing.
    except Exception as exc:
        if isinstance(exc, HTTPError):
            body = exc.read().decode("utf-8", errors="replace")
        save(receipt, {**log, "status": "error", "finished_utc": now(),
                       "type": type(exc).__name__, "error": str(exc), "raw_body": body})
        raise RuntimeError(f"{item['id']} {stage} failed. See {receipt}. {exc} {str(body or '')[:350]}") from exc
    save(receipt, {"id": item["id"], "stage": stage, "started_utc": began, "status": "saved",
                   "response": dest.relative_to(ROOT).as_posix()})
    if stage == "first":
        print(f"Saved {item['id']} first ({input_count} in, {output_count} out, {reason})", flush=True)
    else:
        print("Saved one review-round response.", flush=True)
    return result


def generate(split, jobs):
    select_protocol(split)
    if split == "main":
        authorize_main()
    if jobs:
        snap = ROOT / "runs" / split / "design.json"
        current = design(split)
        if snap.exists():
            saved = read(snap)
            if any(saved[k] != current[k] for k in ("protocol_sha256", "questions_sha256")):
                raise ValueError("The prompts, settings, or problem statements changed since this run began.")
        else:
            save(snap, current)
        freeze(snap.with_name("protocol.json"), PROTO, "Run protocol")
    env = None
    for item, stage, previous in jobs:
        if not record_path(split, stage, item["id"]).exists() and env is None:
            env = environment()
        infer(split, item, stage, env, previous)


def first(split):
    with run_lock(split):
        generate(split, [(item, "first", None) for item in questions(split)])


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Record the local pilot first-pass responses.")
    parser.add_argument("split", choices=["pilot"])
    first(parser.parse_args().split)
