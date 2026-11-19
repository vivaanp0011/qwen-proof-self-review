"""Verify the measured pilot and generate the data tables used by the paper (Python 3.9+)."""
import argparse
import csv
import hashlib
import json
from pathlib import Path

from inference import bank, design, digest, questions, request_payload

ROOT = Path(__file__).resolve().parent
STAGES = {"first": "First attempt", "A": "Neutral review", "B": "Flagged review", "C": "Fresh retry"}


def read(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8"))


def lines(name):
    return [json.loads(s) for s in (ROOT / name).read_text(encoding="utf-8").splitlines() if s.strip()]


def table(name):
    with (ROOT / name).open(encoding="utf-8-sig", newline="") as handle:
        return list(csv.DictReader(handle))


def check(ok, message):
    if not ok:
        raise ValueError(message)


def unique(rows, key):
    mapped = {key(row): row for row in rows}
    check(len(mapped) == len(rows), "Duplicate record identifiers")
    return mapped


def text_hash(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def verify_run():
    items = unique(bank("pilot"), lambda p: p["id"])
    check(questions("pilot") == read("questions/pilot.json"), "Question-only export differs")
    frozen = read("data/design.json")
    check(design("pilot") == frozen, "Protocol, questions or grading bank differs from the frozen design")
    marks = read("grading/first-grades-at-allocation.json")
    check(marks["rubric_sha256"] == frozen["dataset_and_rubric_sha256"], "Allocation rubric differs")
    check(marks["policy_sha256"] == digest((ROOT / "grading/policy.md").read_bytes()), "Policy differs")
    plan = read("grading/review-plan.json")
    aliases = unique(plan["jobs"], lambda row: (row["problem_id"], row["stage"]))
    first = unique(read("grading/first-decisions.json")["decisions"], lambda row: row["id"])
    decisions = read("grading/review-decisions.json")
    reviews = unique(decisions["decisions"], lambda row: row["id"])
    packet = unique(read("grading/blind-packet.json"), lambda row: row["id"])
    lock = read("grading/review-lock.json")
    display_hashes = {i: digest(p["proof"]) for i, p in packet.items()}
    review_marks = {i: {"grade": d["grade"], "reason": d["evidence"] if d["grade"] == "incorrect" else ""}
                    for i, d in reviews.items()}
    check(list(packet) == plan["grade_order"], "Blind packet order differs")
    check(set(reviews) == set(packet) == {v["blind_id"] for v in aliases.values()}, "Blind IDs differ")
    check((len(reviews), digest(decisions), digest(display_hashes), digest(review_marks)) ==
          (lock["count"], lock["ledger_sha256"], lock["packet_sha256"], lock["grades_sha256"]),
          "Review decisions or packet differ from the before-unblinding record")
    check(set(first) == set(items) == set(marks["grades"]), "First-pass population differs")
    incorrect = {i for i, d in first.items() if d["grade"] == "incorrect"}
    expected = {(i, s) for i in items for s in ("first", "A")}
    expected.update((i, s) for i in incorrect for s in ("B", "C"))
    records = unique(lines("data/generations.jsonl"), lambda r: (r["problem_id"], r["stage"]))
    receipts = unique(read("data/attempts.json"), lambda r: (r["id"], r["stage"]))
    outcomes = unique(table("results/proof-results.csv"), lambda r: (r["problem_id"], r["stage"]))
    audits = unique(table("grading/lean-audit.csv"), lambda r: (r["problem_id"], r["condition"]))
    declarations = {line.split()[-1] for line in (ROOT / "lean/Audit.lean").read_text(encoding="utf-8").splitlines()
                    if line.startswith("#print axioms ")}
    check(records.keys() == outcomes.keys() == receipts.keys() == audits.keys() == expected, "Condition allocation differs")
    expected_order = [(i, "first") for i in items] + list(aliases)
    check(sorted(records, key=lambda k: records[k]["started_utc"]) == expected_order, "Generation order differs")
    for (pid, stage), record in records.items():
        label = f"{pid}/{stage}"
        row, audit = outcomes[pid, stage], audits[pid, stage]
        receipt = receipts[pid, stage]
        check(receipt["status"] == "saved" and receipt["started_utc"] == record["started_utc"], label + " receipt differs")
        first_text = records[pid, "first"]["response"]
        previous = first_text if stage in ("A", "B") else None
        item = {"id": pid, "problem": items[pid]["problem"]}
        check(record["request"] == request_payload(item, stage, previous), label + " request or seed differs")
        if stage == "first":
            verdict = first[pid]
            shown = first_text
            check(marks["grades"][pid]["grade"] == verdict["grade"], label + " first-grade allocation differs")
        else:
            blind = aliases[pid, stage]["blind_id"]
            check(row["blind_id"] == audit["blind_id"] == blind, label + " blind ID differs")
            verdict = reviews[blind]
            shown = packet[blind]["proof"]
            check(packet[blind]["problem"] == item["problem"] and verdict["display_sha256"] == display_hashes[blind],
                  label + " blinded proof differs")
        check(row["grade"] == verdict["grade"] == audit["published_grade"] == audit["audit_grade"],
              label + " archived or audit grade differs")
        check(row["grade"] in ("correct", "incorrect") and verdict["evidence"].strip(), label + " missing judgment")
        if row["grade"] == "incorrect":
            check(row["reason"] == verdict["evidence"], label + " missing or different grading reason")
        check(text_hash(record["response"]) == audit["raw_text_sha256"] and text_hash(shown) == audit["grading_text_sha256"],
              label + " visible text differs from the audit")
        check(audit["answer_excerpt"] in record["response"] and set(audit["lean_theorems"].split(" | ")) <= declarations,
              label + " audit quotation or named theorem differs")
        usage = record["usage"]
        check(usage["total_tokens"] == usage["prompt_tokens"] + usage["completion_tokens"], label + " usage differs")
        check(int(row["input_tokens"]) == int(audit["input_tokens"]) == usage["prompt_tokens"] and
              int(row["output_tokens"]) == int(audit["output_tokens"]) == usage["completion_tokens"], label + " tokens differ")
        check(row["finish_reason"] == record["finish_reason"] and
              (row["truncated"] == "True") == (audit["truncated"] == "True") == record["truncated"] ==
              (record["finish_reason"] in ("length", "max_tokens")), label + " cutoff differs")
        check(int(row["seed"]) == record["request"]["seed"] and float(row["elapsed_seconds"]) == record["elapsed_seconds"],
              label + " seed or timing differs")
    return items, records, outcomes, incorrect


def aggregate(items, records, outcomes, missed):
    correct = lambda i, s: outcomes[i, s]["grade"] == "correct"
    groups = {}
    repairs = {}
    for stage in STAGES:
        selected = [r for (_, s), r in records.items() if s == stage]
        groups[stage] = (len(selected), sum(r["usage"]["prompt_tokens"] for r in selected),
                         sum(r["usage"]["completion_tokens"] for r in selected), sum(r["truncated"] for r in selected))
        if stage != "first":
            repairs[stage] = {i for i in missed if correct(i, stage)}
    initially_correct = set(items) - missed
    broken = sum(not correct(i, "A") for i in initially_correct)
    rates = [(len(initially_correct), len(items))]
    rates.extend((len(repairs[s]), len(missed)) for s in ("A", "B", "C"))
    rates.extend([(broken, len(initially_correct)), (sum(correct(i, "A") for i in items), len(items))])
    b, c = repairs["B"], repairs["C"]
    paired = [len(b & c), len(b - c), len(c - b), len(missed - (b | c))]
    metrics = table("results/metrics.csv")
    expected = rates + [(count, len(missed)) for count in paired]
    check(len(metrics) == len(expected), "Published metric count differs")
    for r, (n, d) in zip(metrics, expected):
        check(int(r["numerator"]) == n and int(r["denominator"]) == d and float(r["percent"]) == round(100*n/d, 2),
              "Mismatch in " + r["metric"])
    token_rows = unique(table("results/token-usage.csv"), lambda r: r["condition"])
    check(set(token_rows) == set(STAGES.values()), "Published token groups differ")
    for s, label in STAGES.items():
        row = token_rows[label]
        check(tuple(int(row[k]) for k in ("completed", "input_tokens", "output_tokens", "truncated")) == groups[s],
              label + " token table differs")
        check(int(row["api_errors"]) == int(row["unconfirmed_requests"]) == 0, label + " unsaved request")
    return groups, repairs, paired


def paper_tables(items, records, outcomes, missed, groups, repairs):
    """LaTeX row macros come from the same individual grades and usage as the CSVs."""
    def macro(name, rows):
        return "\\newcommand{\\" + name + "}{%\n" + "\n".join(" & ".join(row) + r" \\" for row in rows) + "\n}\n"
    def frac(n, d):
        return f"{n}/{d}"
    summary, per_item, costs = [], [], []
    for s, label in STAGES.items():
        total, inp, out, cut = groups[s]
        right = sum(r["grade"] == "correct" for (p, st), r in outcomes.items() if st == s)
        repaired = f"{frac(len(repairs[s]),len(missed))} ({100*len(repairs[s])//len(missed)}\\%)" if s in repairs else "---"
        summary.append([label, frac(right, total), repaired, frac(cut, total)])
        costs.append([label, str(total), f"{inp:,}", f"{out:,}", str(cut)])
    costs.append(["Total", *(f"{x:,}" for x in map(sum,zip(*groups.values())))])
    for i, p in items.items():
        cells = []
        for s in STAGES:
            if (i,s) not in outcomes:
                cells.append("---")
            else:
                cell = "Valid" if outcomes[i,s]["grade"] == "correct" else "Gap"
                cells.append(cell + (r"\cut" if records[i,s]["truncated"] else ""))
        per_item.append([i, p["title"].replace("&",r"\&"), *cells])
    return "% Generated by verify.py from saved individual results.\n" + \
        macro("resultrows",summary) + macro("costrows",costs) + macro("itemrows",per_item)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-tables", action="store_true", help="Regenerate paper/tables.tex from the archived calls")
    args = parser.parse_args()
    items, records, outcomes, missed = verify_run()
    groups, repairs, paired = aggregate(items, records, outcomes, missed)
    content = paper_tables(items, records, outcomes, missed, groups, repairs)
    dest = ROOT / "paper/tables.tex"
    if args.write_tables:
        dest.parent.mkdir(exist_ok=True)
        dest.write_text(content, encoding="utf-8")
    else:
        check(dest.read_text(encoding="utf-8") == content, "Paper tables differ. Use --write-tables to regenerate.")
    print(f"{len(items)} problems, {len(records)} measured answers and their requests, grades and hashes agree.")
    for s, label in STAGES.items():
        n, inp, out, cutoff = groups[s]
        print(f"{label}: {n} answers, {inp:,} input / {out:,} output tokens, {cutoff} cutoffs.")
        if s in repairs:
            inputs = sum(records[p,s]["usage"]["prompt_tokens"] for p in missed)
            outputs = sum(records[p,s]["usage"]["completion_tokens"] for p in missed)
            print(f"  Initial errors: {len(repairs[s])}/{len(missed)} repaired; {inputs:,} input / {outputs:,} output tokens.")
    print("B/C paired (both, B only, C only, neither):", *paired)


if __name__ == "__main__":
    main()
