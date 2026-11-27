# Exact decision model and measured search

Run these commands from this directory with Python 3.13 and Z3 4.16 on PATH. All inputs are fixed ordinary boards. All SMT runs use seed 0 for both the SAT and SMT random seeds. There is no symmetry restriction.

## Formula and correspondence

There is one Boolean q for each in-board square. Group square variables by row, column, ordinary (signed) difference and sum. For each group L, assert that at most two variables are true, and define a Boolean abbreviation s(L) for at least two true variables. For each board square x, assert the disjunction of q(x) and the four s(L) for its incident lines. If k is specified, impose both exact cardinality inequalities on the entire list of q. Short groups and tautological/impossible cardinality bounds are simplified in the generator.

Every legal maximal placement gives a satisfying assignment by setting its occupied squares true. Each empty square must acquire a triple on insertion, so one of its four groups already has two queens. Conversely, take the squares whose variables are true. The bounds ensure legality, no duplicate square is representable, and each unoccupied square has a line containing two true squares. Inserting it creates a triple. Counting the selected square variables gives the cardinality of this same placement. The line abbreviations are functions of the placement only, so blocking square assignments enumerates the intended projections exactly.

`python3 model.py 30 --size 30 --emit > instance.smt2` emits a replayable, unrestricted instance. `python3 model.py 6 --size 6` solves and extracts a board. The model is also usable with a varying number of queens. A Z3 UNSAT status is an observation. No proof trace or independently checked Z3 refutation is supplied.

## Small equivalence and mutation checks

`python3 projected.py` compares *sets* of masks. The oracle precomputes forbidden triples by a geometric determinant and a queen-direction check on a pair. It scans every subset for containment of such triples and explicitly tests adding each missing square. The SMT path builds line sums instead and uses a blocking clause for every square assignment. Both sets, with all cardinalities, agreed for n=1,2,3,4. See projected.jsonl for counts, sorted-mask SHA-256 digests and elapsed wall time. `python3 mutations.py` deliberately weakens the model on three fixed inputs and strengthens it on a fourth. The original and perturbed decisions must flip. See mutations.jsonl. The independent shared validator handles malformed coordinate lists.

## Calibration and decision

To reproduce calibration.jsonl, run `python3 model.py N --size N --timeout-ms T` for (N,T) = (5,10000), (6,10000), (7,5000), (8,5000), (10,5000), in order. The first two quickly gave UNSAT and SAT respectively. Z3 timed out on all three latter boards, including the known feasible size ten. A five-second decision limit measures this configuration, not worst-case complexity. These results do not warrant a longer unrestricted run at n=30. Instead, exact search below targets a neighborhood of a verified upper-bound placement.

## Complete swap neighborhoods

Relative to a fixed size-(k+1) seed S, each size-k placement T determines removed subset R=S minus T and inserted subset I=T minus S, with sizes d and d−1 respectively. For fixed R start with S minus R and permit additions only outside S. Currently addable cells form F. This includes removed seed queens when addable, since maximality must hold on the original board. Adding a queen i removes i from F along with all cells on each incident line that already held one queen. A cell's addability only decreases as the retained placement grows.

Pick a hole h in F. A completion must occupy h or select a new queen on a line through h. Therefore it needs a candidate in the inclusive queen-neighborhood of h. Branch on each such candidate in increasing board-index order, assigning each solution to its least chosen candidate in that particular domain. Earlier members of the domain are excluded from later branches. All other still-eligible candidates remain available. No candidate or too few remaining candidates closes a branch. At the exact target cardinality the acceptance test is F empty. This enumerates every successful T in the specified shell once. Branching on the smallest domain only changes traversal order.

`python3 repair_check.py` checks shell counts for **every** seed, shell and smaller target on every board through 4×4 against direct exhaustive geometric placements. The n=4 check covers 2,208 shells and 27,332 directed (seed,target) pairs. `python3 repair.py SEED.json D1 D2 ...` reports full-shell counts and a witness if successful. `python3 local_pb.py SEED.json D1 D2 ... --timeout-ms 10000` issues independent restricted SMT queries using exact sums inside and outside S.

## Research ledger and certificates

All budgets below are single-worker wall limits or measured wall times. CPU and memory figures were not recorded for the custom enumerator. The historical timings are rounded, and rerunning a timed-out model can traverse a different number of nodes. Python checks must run with assertions enabled. The 31-queen seed in construction/witness31.json is an independent instantiation of the reported construction family.

| Question | Configuration and resource allocation | Observation and decision |
|---|---|---|
| Can projected PB models match every small placement? | Unrestricted, every cardinality, n through 4, 10s per incremental query | Exact model sets agreed, including 347 on 4×4. Retain as a change detector. |
| Will weakened or strengthened requirements change answers? | Four targeted pinned instances through 4×4, subsecond | All flipped as predicted. In particular an isolated queen must be permitted under the general specification. |
| Will unrestricted n-queen search scale? | 5, 6, 7, 8, 10 as in calibration.jsonl | Known SAT and UNSAT both reproduced at 5 and 6. Timeouts starting at 7 led to complete local search and structural projection. |
| Do the analytical profile cuts alone suffice? | Size 30, baseline, first cut, and refined cut, seed 0, 5s each; profile_pb.jsonl and profile_refined.jsonl | Each returned timeout. Internal counters reveal different search paths but do not measure distance to solution. Retain the refined cut for focused subcases. |
| Can removing a few seed queens lead to size 30? | Every delete-d, insert-(d−1) repair, d=1..4, one core; initial planning estimate roughly 4 CPU minutes for this experimental line | Completed in under 235s of enumerator wall time. Counts 31, 465, 4,495, 31,465 removal sets respectively; zero valid completions in each observed shell. d=4 required 40,629,567 nodes and 231.92s vs 440,975 nodes and 2.36s for d=3. Stop here. |
| Can small repair exclusions be independently certified? | Exhaust all 496 cases for d≤2, generate hole cores, check via direct triple geometry; independent PB at 1s per d=1,2,3 | Checker accepted proof and rejected corruption. Z3 reproduced the first two exclusions; d=3 timed out. d=3,4 lack independent finite certificates here. |
| Can the axes alone kill a case before choosing queens? | 3,000 seeded draws across three distributions; all interval/parity pairs and known 4,6 fixtures; under 1s total | Raw matching sizes exceeded 30 on every sampled uniform, identical, and perturbed pair. Four centered interval pairs and all exact parity pairs survived the basic tests. Pivot to rigorous family exclusions and moment tests. |
| Do the four interval survivors admit a placement? | One reflection orbit, direct second-moment bound; checked exclusion for all 36 interval-pair orbits | No. The certificate reduces 35 orbits to a forced-line count or an uncoverable square, and the last to 1414 < 2240. |
| Can the near-parity sample result become a finite conditional proof? | All one-step parity perturbations on one or both axes; normalize parity by reflection and exchange axes by transpose; ~1.5s generation and subsecond check | 25,650 orbits cover 204,300 oriented axis pairs. Each certificate contains 1 or 31 holes. A new minority-color bound, if independently established, also subsumes this result. |

The six-point reference uses the same solve, independently enumerate, then distinguish intentional control failures workflow. The project-level Lean checks have their own replay. The search programs here need no network or additional Python modules.

### Profile comparison

`python3 profile_pb.py`, `python3 profile_pb.py --cut`, and `python3 profile_pb.py --refined` reproduce the three query types. Add `--emit` to any for a complete SMT-LIB instance. Both cuts apply solely at n=k=30 and rely on the coordinator's mathematical arguments under structure/. The first requires every queen to lie on a pair-line and imposes a disjunction on counts of saturated lines. The refined version requires both axes to have 15 full lines, at least one diagonal family to have 15, the other at least 13, and 10, 12, 14, 16, 18, or 20 even-colored squares occupied. The unrestricted formula remains independently tested.

### Local certificates

The seed file SHA-256 used for all local runs is `a6fef7fdc272192e4ec8f332c92b17d6f40f80a8665c0cdc9093c60b7a37cae7`. The certificate embeds all its coordinates. For every choice of one or two removed queens the certificate lists addable holes in the retained board. In the first case we need one hole. In the second, for each legal candidate outside the original seed, at least one listed hole must remain addable after the candidate is inserted. The independent verifier computes legal insertions and surviving holes using directions of pairs of points.

```sh
python3 repair_check.py
python3 repair.py ../construction/witness31.json 1 2 3
# Historical long experiment, approximately 4 min.
python3 repair.py ../construction/witness31.json 4
python3 local_pb.py ../construction/witness31.json 1 2 3 --timeout-ms 1000
python3 radius_certificate.py ../construction/witness31.json > /tmp/queens-radius.json
python3 check_certificate.py radius_certificate.json
cmp /tmp/queens-radius.json radius_certificate.json
```

### Checking a row and column profile

Assume exactly 15 occupied rows R and exactly 15 occupied columns C with 30 queens. Every active axis then contains two queens, and all queens lie in R×C. Every square in the complement-row by complement-column product is empty and must be covered diagonally. Form a bipartite graph with a difference and sum key as the endpoints of each such hole. At most 15 diagonals of either slope can be saturated. Their keys must be a vertex cover. Thus a matching with 31 edges excludes the profile. The lower bound only requires distinct endpoints; optimality of a computed matching is unnecessary. A diagonal containing fewer than two points of R×C is ineligible, so holes can force other keys or be uncoverable.

Each source of samples is explicit in axis_matching.py. The random seed is 300031 and a single Python PRNG is consumed in the specified order. Sampling a set equal to its transpose, prescribing intervals or near-pure parity are restrictions. The first trial mislabeled axes {0,2} on side 4 as a feasible reference. The detector rejected it and exhaustive placements identified the correct axes {0,3} and {1,2}. The failed reference remains a negative control in the replay.

For 15 consecutive rows and columns the starts lie in 0..15. Reflections map each start i to 15−i and transposition exchanges the axes. Of 36 orbits the sole survivor of the first exclusions has both active axes 7..21. Its mandatory difference keys are −7..7 and its mandatory sum keys are 22..35. Setting d=r−c and t=r+c−28, sum(d²+t²) over queens must equal 8 sum_{a=−7}⁷ a² = 2240, because each axis coordinate occurs twice. All 30 difference occurrences and 28 sum occurrences are forced, contributing 560 and 462. The final two sum occurrences contribute at most 2·14², yielding at most 1414. check_intervals.py verifies the general orbit data, support deficiencies, and integer inequality from the compact certificate.

For perturbations of parity axes choose 15 even or 15 odd active positions and exchange one active for one inactive position on at least one axis, permitting either zero or one exchange on the other axis. There are 204,300 oriented pairs. Reflecting each axis to make the majority even and transposing yields 25,425 double-change and 225 single-change representatives. The stored certificate for each is either one uncovered hole with neither diagonal eligible or 31 holes with pairwise distinct difference keys and pairwise distinct sum keys. Checking these cases does not assume that an arbitrary placement is symmetry-invariant. The small certificate records one-hole proofs for 25,026 representatives and 31-hole matchings for 624. The all-parity unperturbed profiles are outside this exclusion.

```sh
python3 axis_matching.py --seed 300031 --draws 1000 --examples /tmp/queens-matching-examples.json
python3 interval_proof.py > /tmp/queens-intervals.json
cmp /tmp/queens-intervals.json interval_certificate.json
python3 check_intervals.py interval_certificate.json
python3 perturbed_axes.py /tmp/queens-perturbed.json.gz
python3 check_perturbed.py perturbed_cert.json.gz
```

The compact certificate checkers also reject corrupted or incomplete examples. Exact axis-family exclusions are conditional on the specified axes. None decides m₃(30). A next experiment can enumerate mixed-color low-matching axis products before solving for queens. The small-board reference, especially n=6, should be kept when changing that projection.

### Clipped periodic unused axes with a 12×12 control

The size-12 solution's unused indices are {2,3,5,6,8,9} on each axis. This is an interval intersected with two residue classes modulo three. Test all unused 15-sets on the size-30 board that are the intersection of an arbitrary interval with an arbitrary word of period at most five. Row and column choices are independent. Reflection preserves this class because the residue set, interval and phase can all vary. Transposition permits sorting a pair of canonical axes. There are 164 raw axes, 82 axis representatives and 3,403 pair representatives. This class includes axes for which clipping breaks global periodicity.

| Question | Configuration / budget | Evidence and decision |
|---|---|---|
| Can clipping reproduce the known control and isolate promising 30-boards? | Periods 1..5; at most 45s for screening; duplicate masks removed; all 3,403 axis pairs | The basic screen took 0.786 process seconds. It excluded 948 pairs by an uncoverable hole, 969 by a forced-line limit and 1,443 by a matching, leaving 43. |
| Can queens realize the surviving fixed-axis profiles? | Set every active row and column to exactly two; just 225 square variables at n=30; capacities for ordinary diagonals; require diagonal coverage on the 225 holes; no other cuts; seed 0; 350ms per pair (1s for n=12) | Produced the original 12-queen control within 0.035s; separate pair-based audit found no addable square. At n=30 the 43 calls took 6.528s combined wall time, with 33 solver UNSAT and 10 timeouts. Pivot to diagonal counts without further solver time. |
| Do the hole covers fit the marginal moments of the axes? | Complete recursive split on a diagonal key; maximum 30s, measured 0.096 process seconds on the 43 pairs | No marginal pair survived. The 12-control has one marginal pair, the witnessed one. The independent finite-certificate checker verifies the entire clipped family, including all earlier matchings and forced-line rejections. |

At a node retain sets D,S of diagonals forced to be saturated. On an uncovered hole choose one endpoint of its diagonal edge, for example a difference key d. Every cover either uses d or must use all sum keys adjacent to d in the still-uncovered graph. Both child branches are therefore necessary to exclude possibilities. More than n/2 forced keys in either slope contradicts capacity. At a node covering all holes, each forced key supplies two diagonal occurrences among n queens. Every remaining key has multiplicity bounded by two and by the number of active squares on that diagonal, and a forced key cannot receive further occurrences.

For active axes R,C, summing over the queens gives the three necessary identities

```
sum d = 2*(sum R - sum C)
sum s = 2*(sum R + sum C)
sum (d² + s²) = 4*(sum_{r in R} r² + sum_{c in C} c²)
```

Here d=r−c and s=r+c. The last identity follows from (r−c)²+(r+c)²=2r²+2c² and the multiplicity two of each axis value. The short lists of remaining occurrences permit direct enumeration. In the independent proof checker 1,331 leaves exceed quotas and 159 leaves have incompatible moments. This establishes a conditional impossibility for the full stated clipped family. The host Python runtime, checker and elementary correspondence above form its trust basis. No certificate for unrestricted axes follows. The bottleneck in scaling the approach now lies in representing or classifying unrestricted axis pairs before checking their diagonal covers.

```sh
python3 clipped.py
python3 clipped_realize.py > /tmp/queens-clipped-realize.jsonl
python3 clipped_control.py
python3 clipped_moments.py
python3 clipped_proof.py
python3 check_clipped.py
```

clipped_control.py checks the recorded clipped_realize.jsonl, so solver timing variation on replay does not affect the recorded control. clip certificates freeze the screen and cover splits. check_clipped.py reads these without importing the generator, solver or matching algorithm, regenerates the complete finite domain by a different method, checks every orbit exactly once, and rejects a damaged split.

### The near-tight frame with 15 and 14 saturated diagonals

Assume 15 paired rows and columns, 15 saturated ordinary differences, and 14 saturated ordinary sums. The structural argument supplies equal spans and equal sums of the two unused axis sets, reflecting first to put the complete family in the difference direction if necessary. Call their common span e. Normalize the unused axes separately to start at zero, then collapse their common endpoints 0,e modulo e. This gives sets U,V of size 14 in the cyclic group. Ordinary board lines are still the lines in the problem. Their residues supply only necessary conditions.

The 29 diagonals cover 56 distinct perimeter points, and each hits at most two. Thus at most two diagonals hit fewer than two perimeter points. A twice-hitting diagonal through (x,y) must satisfy one of the following modular conditions: either x+y lies in U and V, or x−y lies in U and y−x lies in V. The two boundary hits determine the two memberships; corner cases have residue zero. A modular target that fails both alternatives can only be covered by one of the two exceptional diagonals. Their two typed residue keys therefore cover all graph edges ((x−y) mod e, (x+y) mod e) from failing targets.

There is a fast necessary test on a single axis. Define F_U(y) as the set of x in U for which neither x+y nor x−y belongs to U modulo e. Each y of V needs at most two such x, since a fixed diagonal meets a fixed column in at most one residue. Moreover a **single common** pair of typed exceptional keys must cover all these failures for at least 14 columns. To test this without knowing V, count the clean shifts, then for each of the at most 2e labels record which shifts with one failure it can repair. For shifts with two failures, record which two-label pairs can repair both. At least one pair must produce 14 clean or repaired shifts. The paired-axis follow-up checks the original, stronger, two-axis membership condition. A bipartite edge set has a cover of size at most two only if one endpoint of its first edge, together with at most one more key, covers it. This can be tested directly.

frame29_axes.cpp enumerates the 13 nonzero entries of each 14-set containing zero by the fixed-popcount binary successor. With masks U,V sorted to quotient transpose, all translations satisfy t+e<30, b+e<30 and 15(b−t)=sum(U)−sum(V). Recording all these shifts suffices; no assumption on the symmetry of queen positions is used. The near-tight downstream proof checks all listed translations individually. The global completeness of this projection rests on the mathematics above and the mask/pair generator. The separate construction-side audit reproduces the domain with a different algorithm.

| Experiment | Configuration, resource cap | Result and decision |
|---|---|---|
| Can two exceptional lines leave a useful unary filter? | All axes e≤19 and 100,000 uniformly sampled 14-subsets containing 0 per span e=20..29, fixed MT19937 seed 291514; cap 30s | At e=29, 1083 permitted 14 individually repairable shifts and just 7 passed the common pair test. This justified exhaustive generation. |
| Can we enumerate every profile under the near-tight restrictions? | All 77,558,760 normalized axes over spans 14..29; cap 45s; include all compatible translations | 9,016 input pairs. Of these 2,404 have zero modular failures and 6,612 require two exceptional residues; the zero-exception test alone would incorrectly skip the latter. A fresh generator replay took about 9s. Full per-span counts in frame29_full.log. |
| Do any of these axes support the required diagonal moments? | Ordinary support, forced lines, matching and cover splits; cap 35s | 612 reached cover splitting. Across these, 45,422 nodes ended in 960 completed covers with no admissible marginal pair. Measured 2.589 CPU s. Local certificates checked every supplied case, including 22,057 over-capacity leaves. |
| Can independent code reproduce the finite domain? | General search-side known answers 6,10,18,26 and direct stronger two-axis checks, all translated pairs for e≤17, plus independent construction-side all-span audit | Known cases pass. The exact module's brute check matches 16,210,1,522,660 translations for e=14,15,16,17. Independent complete regeneration is recorded under construction/. |

For a concrete filter regression use e=16, U=V={0,…,13}. The modular failure edges are (1,15), (2,14), (14,14), (15,15). They need exactly two keys. The pair is locally excluded only later by board geometry. The small positive controls happen to have zero modular failures and thus do not exercise this distinction by themselves.

### The fully paired case with equal unused spans

For 30 saturated diagonals the joint two-key bound above does not follow. On the **two extreme columns**, there are 30 targets. A diagonal hits at most one of these except for either of the two long corner diagonals, each of which can hit both. Consequently at most two saturated diagonals miss both extreme columns. At any target with x in F_U(y), both the sum and difference line miss the extreme columns' target rows, hence it must lie on one of those two exceptional lines. Exchanging row and column gives a second 1D condition with its own exceptional lines. This proves applicability of the unary filter to each axis and the one-sided pair test in both directions. No shared joint two-line budget is imposed. The structural polynomial calculation independently supplies equality of H=21A²−5A₂ for the two active axes, with A the sum and A₂ the sum of squares of their centered coordinates 2i−29.

frame30eq_axes.cpp enumerates the same unary masks, inserts both endpoints, tries all board translations, and keeps one representative per axis reflection by comparing the actual 30-bit mask with its reversal. H is unchanged under this reflection, and either reflection preserves full pairing of both diagonal slopes. Equal-H buckets are paired with replacement, quotienting transposition. Each ordered side test independently checks coverage of its failures by at most two typed exceptional residues. Each pair surviving both tests is sent to ordinary geometry.

| Experiment | Resource limit | Result and decision |
|---|---|---|
| Can the full equal-span case be screened using separate exception budgets plus the invariant? | 55s generation cap, 45s for moments; budget one core, three minutes including audit | 11,691 axis-pair representatives reached geometry. Of these 775 reached marginal enumeration, which took 3.566 CPU s overall. Across 64,277 nodes and 1,072 complete covers no marginal pair survived. |
| Do independently checked local certificates justify all the profile rejections? | Regenerate hole/forced-line/matching proofs and cover trees, then check geometry, quotas and brute multinomial completions | 11,691 supplied pairs checked, 31,454 quota leaves and 1,072 incompatible-moment leaves. Independent symmetry and H checks are applied to every pair; omission control rejected. See frame30eq_check.log. |

For both full-coverage experiments the marginal checker permits extra singly occupied diagonals when completing an axis cover. Its negative findings thus exclude the required fully paired diagonals as well. Every classified item uses ordinary geometry after axis projection. Looking only at summed profile statistics would not suffice.

```sh
bash replay_frames.sh
# Saved-instance certifiers can be run individually.
python3 check_frame29.py
python3 check_frame30eq.py
```

To reconstruct the data files from the generators, run frame29_finish.py or frame30eq_finish.py with its respective full.txt as argument, then run frame29_certs.py or frame30eq_certs.py. The checker scripts read the shipped data and compressed certificates. The full-domain shape audit is separate from these local checks. Generator wall/CPU measurements are retained in frame29_gen.time and frame30eq_gen.time. Compiler selection uses the Nix store path recorded in replay_frames.sh.

### Kernel-checked moment obstruction

From the repository root run `lake env lean Gardner/exact/Marginal.lean`. The theorem Gardner.Marginal.paired_moments proves both first-moment identities and the joint second-moment identity for an arbitrary list of integer coordinate pairs whose row and column projections are permutations of two copies of the corresponding active axes. Gardner.Marginal.incompatible_moment_sets proves that such a placement cannot realize second moments constrained to incompatible sets. Both depend only on propext, Classical.choice and Quot.sound, as reported in marginal_lean.log. The separate finite checkers establish the allowed marginal values on each terminal cover.

### Full local certificates executed in Lean

From the repository root run `bash Gardner/exact/replay_local_lean.sh`. It compiles LocalCertificates.lean with the project Lean compiler and leanc, then recomputes the verdicts for every local axis/certificate pair in frame29 and frame30eq. local_lean_stream.py joins matching rows with strict length checking and serializes the original header, rejection label and proof as JSON lines. Its full 20,707-row output has SHA-256 eaa7e9bc46b7c0af004fe267f5efc8eb8989ace535d9de78af6dd1007f826a70. Python supplies no derived verdicts or precomputed moment sets.

The Lean executable reconstructs both active and unused axes, diagonal support and forced keys over all 900 ordinary cells. It checks each matching and forcing witness. At a split it computes the uncovered neighbors, follows both children, and accepts a Q leaf only when a family exceeds 15 saturated lines. At each M leaf it checks that all 225 targets are covered. It enumerates possible remaining diagonal keys in increasing order, respecting active support and multiplicity, with exact first moments and the joint second-moment exclusion. It checks duplicate rows, counts, span/axis invariants and one-to-one membership against both separately supplied domain files. Hash and set comparisons do not replace local proof traversal.

A 20-record sample touching all five verdicts in each family completed in 54 ms under `lean --run`, justifying the full native run. The two full-case statistics agreed with the independent Python checker, including 53,511 quota and 2,032 moment leaves. The native run took 4.37 user seconds (4.42s wall, 76,428 KiB peak), under its 115s limit. The replay also rejects a fake quota proof on an actual tree and an incomplete stream in full mode. Source, measured full and sample logs, and the replay command are preserved. This is bounded execution of a Lean implementation. The general moment identities are separate kernel theorems; the full-domain enumeration and the reduction to these local records remain separate components of the argument.
