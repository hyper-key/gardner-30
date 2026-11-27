# Thirty-one queens on a 30 × 30 board

This research preprint gives a computer-assisted proof of the value of Gardner’s minimum no-three-in-a-line problem for a 30 × 30 chessboard. The independent review recorded here was performed by a separate AI agent. The preprint is awaiting scholarly peer review.

Read the [paper](Gardner/paper/gardner-30.pdf) or open its [standalone Typst source](Gardner/paper/gardner-30.typ) in Typst. The source includes the coordinates used to draw the witness and checks them during compilation.

## Reproducing the checks

From this directory, run the following with Python 3.10 or later. The two commands use the standard library.

```sh
python3 Gardner/validation/check.py Gardner/construction/witness31.json --expect 31
python3 Gardner/paper/audit/independent_audit.py .
```

The second program checks the 31-queen witness by literal insertion, recomputes the coefficient table and verifies all 20,707 supplied local certificates. The archive edition of the separate agent's audit checks the SHA-256 hashes of its five inputs from the audited revision so that it can run outside Git. The certificate algorithms are the same as in that audit. A successful result ends with `PASS independent witness, coefficient arithmetic, and all 20707 local certificates.`

For the complete original computation, including regeneration of the axis lists and the Lean comparators, run `bash Gardner/replay.sh` in the provisioned environment. The dependency pins are in `lean-toolchain` and `lake-manifest.json`. The environment also provides Python, Z3, a C++20 compiler and the configured comparator kernels with bubblewrap isolation. See [environment and comparator information](Benchmark/README.txt) and the [clean replay log](Gardner/records/clean-replay.txt).

The subsequent kernel proofs have a separate command, `bash Gardner/kernel/replay.sh`. The [formalization status](Gardner/kernel/STATUS.txt) and [validation record](Gardner/kernel/VALIDATION.txt) identify the obligations discharged in Lean. The [mathematical proof](Gardner/structure/arguments.md) supplies the link to the exhaustive finite computation.

## Rebuilding the PDF

The note was compiled with Typst 0.14.2 using bundled fonts. It has no external packages, figures, or bibliography files.

```sh
typst compile --ignore-system-fonts --pdf-standard 2.0 Gardner/paper/gardner-30.typ Gardner/paper/gardner-30.pdf
```
