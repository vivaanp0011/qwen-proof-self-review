# Self-review of real-analysis proofs

**Vivaan Pinglikar · Independent researcher**

Does asking Qwen to check a proof help more than asking it to start again? In this local ten-problem pilot, neutral review raised the score from **6/10 to 8/10**. It repaired two of four initial errors and kept all six initially correct proofs. Starting over repaired one error. Telling the model its proof was incorrect repaired none. [Read the paper (PDF)](paper/qwen-proof-study.pdf) · [Editable LaTeX](paper/qwen-proof-study.tex)

| Condition | Correct / attempted | Initial errors repaired | Replies at the output cap |
|---|---:|---:|---:|
| First attempt | 6/10 | — | 8/10 |
| Neutral review (A) | 8/10 | 2/4 | 6/10 |
| Flagged review (B) | 0/4 | 0/4 | 4/4 |
| Fresh retry (C) | 1/4 | 1/4 | 4/4 |

The comparison is paired by problem. For B versus C, both fixed zero, B alone fixed zero, C alone fixed one (P02), and neither fixed three. P10 accounts for neutral review’s one additional repair over starting again. All twelve follow-ups on the four initial errors used the full 2,048-token output allowance. Their total input was 8,970 tokens for A, 8,918 for B and 666 for C. [Individual outcomes](results/proof-results.csv) · [Metrics](results/metrics.csv) · [Token usage](results/token-usage.csv) · [Outcome chart](results/proof-outcomes.png)

## What the grades mean

Qwen ran locally with LM Studio using `qwen/qwen3.8-27b`, quantization `Q4_K_M`, an 8,192-token context, temperature 0.7, top-p 0.9 and the requested reasoning effort `none`. The ten problems were handpicked. There was one draw per condition per eligible problem. The review prompts received the full first answer. The fresh retry used the original prompt with a second-round seed shared across that problem’s follow-ups. [Frozen protocol](protocol.json) · [Observed model settings](data/model.json) · [Model-file hashes](data/model-files.json)

One AI grader used problem-specific rubrics and accepted valid alternatives to the reference arguments. All visible mathematics counted, including material outside the proof tags. Blinded second-round decisions were recorded before the condition mapping was opened. The retrospective audit knew the earlier grades and conditions. Lean 4.19.0 checked formal solutions covering all ten problems and 37 named theorems. The audit retained all 28 grades. Identifying material omissions in English remained an AI judgment. Independent human grading remains outstanding. [Rubric and reference proofs](dataset/rubric.md) · [Per-answer audit and exact excerpts](grading/lean-audit.csv) · [Lean checks](lean/kernel-check.txt)

The fresh P02 retry stopped just before a multiplication. Its stated square-index formula gives one at every spike, which the original rubric accepts as routine algebra. Requiring that final multiplication in print would move fresh retry from 1/4 to 0/4 repairs. The neutral P10 answer explicitly proved that every lower estimate of the area is zero. The fresh P10 answer stopped after using only a nonnegative lower estimate. [Series proofs](lean/Audit/Sequences.lean) · [Integral proofs](lean/Audit/Darboux.lean)

## Reproduce the paper

From the repository root, run the following with Python 3.9 or later. The verification uses the standard library and works offline.

```sh
python verify.py
```

The script reconstructs every request from the frozen prompt and the permitted inputs, verifies the allocation and seeds, checks the hashes of the raw and blinded answers, and compares recomputed grades, paired counts, token totals and cutoff flags with the CSVs. It also checks that the LaTeX tables match the individual results. The mathematical grades are recorded judgments. [Full requests and responses](data/generations.jsonl) · [Blinded packet](grading/blind-packet.json) · [Pre-unblinding hashes](grading/review-lock.json)

To rebuild the paper with pdfLaTeX:

```sh
python verify.py --write-tables
cd paper
pdflatex -halt-on-error qwen-proof-study.tex
pdflatex -halt-on-error qwen-proof-study.tex
```

To recheck the proofs, start from the repository root with the Lean toolchain manager and Git installed:

```sh
cd lean
lake exe cache get
lake --wfail build Audit
lake env lean Audit.lean
```

The lockfile pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Lean checks a formal reconstruction for each problem and selected disputed assertions. A correct theorem by itself cannot establish that a model’s prose included the proof.

## Replay a condition locally

The dry run lists the exact requests for a condition. To generate new responses, use the same model and LM Studio with the local `lms` command available. The runner uses the loopback endpoint on port 1234.

```sh
python replay.py A --dry-run
python replay.py A
```

Use `first`, `A`, `B` or `C`. A replay uses the archived first answers and allocations so the inputs match this pilot, even if a new model generation differs. Completed replay responses are saved and reused in `runs/replay/`. Hardware, runtime and sampler implementation can affect outputs at a fixed seed.

The release contains the completed pilot. The archived data include UTC timestamps and elapsed times for each call. [Question-only inputs](questions/pilot.json) · [Full problem bank for the pilot](dataset/pilot.jsonl) · [Grading policy](grading/policy.md) · [Citation](CITATION.cff)
