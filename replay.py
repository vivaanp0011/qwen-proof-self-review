"""Replay a pilot condition in local LM Studio using the exact archived inputs."""
import argparse

from inference import environment, infer, record_path, run_lock
from verify import verify_run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("condition", choices=("first", "A", "B", "C"))
    parser.add_argument("--dry-run", action="store_true", help="Validate and list requests without contacting LM Studio")
    args = parser.parse_args()
    items, records, _, _ = verify_run()
    selected = [r for r in records.values() if r["stage"] == args.condition]
    if args.dry_run:
        for r in selected:
            print(r["problem_id"], r["stage"], "seed", r["request"]["seed"])
        return
    env = None
    with run_lock("replay"):
        for r in selected:
            pid, stage = r["problem_id"], r["stage"]
            previous = records[pid, "first"]["response"] if stage in ("A", "B") else None
            if env is None and not record_path("replay", stage, pid).exists():
                env = environment()
            infer("replay", {"id": pid, "problem": items[pid]["problem"]}, stage, env, previous)
    print("Replay completed. Results are in runs/replay/responses/.")


if __name__ == "__main__":
    main()
