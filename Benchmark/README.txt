SIX-VERTEX KNOWN-ANSWER TOOLING VALIDATION
Date: 2026-11-27. No open-candidate proof attempt or search was performed.

Environment
The existing VM's Nix-provisioned tools were used; nothing was installed and no
system or Nix configuration was changed. This project has no devenv.nix,
devenv.lock, or project Nix shell to enter. Lean is selected by lean-toolchain:
leanprover/lean4:v4.35.0 (compiler commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc).
Lake reports 5.0.0-src+eb6cafb. mathlib is pinned in lakefile.toml and
lake-manifest.json at 56a005855ea17e0b0958f73ec801ae140b0a1679.
Python is 3.13.13; Z3 is 4.16.0; Nix is 2.34.7; Lean MCP is 0.26.2.
Exact Nix store paths are in logs/environment.txt. No missing dependency was
encountered, so no Nix change is proposed. The project pins Lean/mathlib, but
does not itself recreate the VM's Nix system closure or the bundled external
kernel executables. Replay assumes the already provisioned environment.

Definitions and guarantees
SixPointDefs.lean defines Path = Fin 6 -> Fin 6 and valid = injective. Thus a
valid path visits all six bounded vertices exactly once. distance is
min(Nat.dist x y, 6 - Nat.dist x y); lengths enumerates exactly five adjacent
pairs. SixPointChallenge.lean fixes eight theorem statements independently of
the solution. fixed.sha256 freezes the shared definitions, challenge, and
positive comparator configuration; replay verifies those hashes before/after.
The challenge deliberately contains sorry placeholders; these are targets,
not submitted proofs. The accepted solution contains no sorry/native_decide.

Lean proves witness validity and lengths [3,2,1,2,1], equal lengths but invalidity
for the repeated-vertex control, wraparound d(0,5)=1, and wrong edge count when
the closing edge is included. Its parity theorem quantifies over EVERY valid
Path, not only a generated permutation list: distance 2 preserves parity,
adjacent equality propagates along all six positions, and injectivity on the
finite six-element type gives surjectivity, contradicting visits to both 0
and 1. The 36-pair parity lemma uses kernel-reduced decide. The full proof
depends only on propext, Classical.choice, Quot.sound; see logs/axioms.txt.

Independent checks
The ZIP's unchanged six_point_reference.py exhaustively checked 720
permutations: 17 of 21 profiles occur, excluding (0,5,0). It checks witness,
duplicates, wraparound, closing edge, and parity. z3_reference.py emits saved
SMT-LIB and tests six solved-fixture cases; SAT/UNSAT results agree. Z3 is a
cross-check, not part of the Lean proof's trust chain.

Live feedback loop
Feedback.lean originally used `exact Nat.zero_add 5` at line 4 for the goal
SixPoint.distance 0 5 = 1. Lean MCP returned that live open goal and the
type mismatch (0+5=5 versus distance 0 5=1). Replacing the step with `decide`
returned an empty goals_after list and no diagnostics. Both MCP JSON replies,
the failing source snapshot, and command-line diagnostics are retained.
The repaired Feedback.lean is also executed by the replay script.

Verifier controls
Correct: lake comparator --config Benchmark/comparator.json --paranoid -> 0.
It reports acceptance by Lean default and paranoid kernels, lean4lean,
nanoda, con-leche, and con-ron.
Incomplete: SixPointIncomplete.lean replaces witness_valid proof with sorry.
It compiles, but comparator-incomplete.json is rejected for sorryAx -> 1.
Weakened: SixPointWeakened.lean changes witness_valid's type to True and proves
it by trivial. It compiles, but comparator-weakened.json is rejected for a
theorem statement mismatch -> 1. This is a deliberately simple weakening.
No sandbox bypass flag was used. Source compilation alone is insufficient.

Replay in a prepared checkout (exact command actually executed)
  bash Benchmark/replay.sh
Individual commands and expected exit statuses are logged in replay-*.txt.
The script runs Python, Z3, Lake build, repaired proof, axiom report, and all
three comparator cases. The intentional failures are expected and asserted.

Clean-checkout protocol
A local commit and separate detached Git worktree are used. The new .lake
directory receives only cached .lake/packages dependencies, NOT the original
project's .lake/build files. Rebuilding this benchmark therefore regenerates
all its proof artifacts from tracked source. Dependency caches and installed
compiler binaries are reused; this is not a compiler/mathlib bootstrap.
Exact tested commit/path/commands and clean status are in clean-checkout.txt.
Two same-named Isolation.lean files in different workspaces are additionally
queried via Lean MCP to check root-specific goal state; logs retain replies.
Isolation.lean is an intentional failing diagnostic fixture, outside builds.

All work is local on branch benchmark/six-point-validation. No Git remote is
configured and nothing was pushed. The deliverable includes a Git bundle for
backup as well as source and logs. Original starter Challenge/Proofs files
remain as they were and are unrelated to the six-vertex comparator configs.
