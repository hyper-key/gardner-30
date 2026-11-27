# Gardner’s 30×30 queen-placement problem

Research record, 27 November 2026

**The computer-assisted proof gives m₃(30)=31.** Lean proves that the attained minimum is either 30 or 31. An exhaustive case reduction and independently checked certificates exclude 30. The fixed specification, proof, and replay scripts are included. The published sources located in this investigation predate this result. Independent scholarly review and a single end-to-end Lean theorem for equality remain outstanding.

## What the literature establishes

Cooper, Pikhurko, Schmitt and Warrington proved the lower bound n for even boards by elementary counting and gave a polynomial proof of a more general theorem. Their explicit search took about 900 CPU-hours to rule out 11 queens on the 11 board. The original paper also gives a good placement with an isolated queen, an important specification test. [2014 paper, Theorem 1 and Sections 2–4](https://arxiv.org/abs/1206.5350v2)

Pratt formulated the problem as an integer linear program, using one occupation variable per square and one pair indicator per line. Knuth used SAT and found size-n examples for n=10,18,26 in the same row-and-column parity class. Knuth also reported one-color placements with n+1 queens through n=30. His correspondence describes finding an 18-queen example quickly in a search allowing 19, then getting no solution for hours under the tighter limit. This is a warning against interpreting first-solution time as an estimate of infeasibility. [Pratt’s formulation and Knuth’s report](https://oeis.org/A219760) · [Schmitt’s slides reproducing the correspondence, slides 25–30](https://community.middlebury.edu/~jschmitt/talks/No3talk-Feb%2719.pdf)

Oh, Schmitt and Wang used a zero-sum grid to strengthen the lower bound for n congruent to 1 modulo 4. The hypothesis excludes 30. Huchala extended the sequence through n=29. The last two reported values are 29 for n=28 and 30 for n=29. Schmitt’s 2025 table explicitly marks n=30 unknown. The OEIS entry, revision 84 dated 30 May 2026, still ends at n=29. [Oh–Schmitt–Wang](https://doi.org/10.1016/j.ejc.2024.104095) · [Huchala’s program](https://oeis.org/A219760/a219760_1.py.txt) · [Schmitt’s 2025 table](https://www.algebra.uni-linz.ac.at/Students/Seminare/s25/No3Talk_Extended.pdf) · [OEIS record and revision date](https://oeis.org/A219760/internal)

## Independently verified bounds

The saved placement has 31 distinct in-board queens. It has 60 saturated lines. All 869 empty cells lie on at least one of them. The source for the upper bound gives an existence statement without a coordinate list. The saved coordinates are an independent reconstruction of Knuth’s reported family. The even-even block has two queens in every even row and every even column, with one additional queen at (11,1). The coordinate origin is the upper left.

The checker in validation/check.py tests pairs of points geometrically. The Lean proof validates the coordinate list, the saturated-line certificate and the full board. Lean also proves, for an arbitrary legal placement, that failure of an insertion is equivalent to saturation of one of the four lines through that square. The separate perimeter proof starts from an arbitrary placement satisfying the same literal maximality predicate. Both bound theorems passed the paranoid comparator and its six configured kernels. The conventional axioms listed for these proofs are propext, Classical.choice and Quot.sound.

On boards of side 1 through 4, the solver and a direct enumeration agreed on every maximal placement, with respective counts 1, 1, 23 and 347. The 4×4 check examined all 65,536 subsets. A published 4×4 example contains an isolated queen, so requiring saturation at occupied cells would reject a valid placement. Deliberate controls also tested duplicates, coordinates outside the board, triples in each direction, ordinary attack by a single queen, and dropping maximality.

## What the structural arguments establish

* **Axes.** Any 30-queen solution occupies exactly 15 rows and 15 columns, with two queens on each. All 225 intersections of the other 15 rows with the other 15 columns are empty. Each needs a diagonal already containing two queens.
* **Colors.** The only possible unordered splits are 10+20, 12+18 and 14+16. In particular an optimum of 30 cannot come from a one-color search. A one-color 31-queen seed requires at least 11 deletions and 10 insertions to reach a solution.
* **Diagonal counts.** The cover polynomial forces 15 saturated diagonals of one slope. The 56 boundary cells of the unused product force at least 13 of the other slope. The tight 15+13 case is eliminated by the finite verification described below. The 15+14 and 15+15 cases are excluded by the complete finite proof below.
* **Scope of formalization.** Lean theorems establish the two initial bounds, the centered-grid coefficient test, the degree-58 obstruction for actual padded line covers, coarse saturation assuming no isolated queen, the projection moment identities and several arithmetic steps. The argument that excludes isolated queens, the higher-degree intercept specializations and the reductions to exhaustive axis lists are given in the detailed proof. These links, including domain completeness, would still need to be formalized for a single kernel theorem asserting the exact value.

## Why the research direction changed

Searching for coordinates first asks the solver to choose 30 of 900 cells. The projected small-board models were exact, yet the same solver timed out on the known feasible 10-queen case. The explicit 31 witness arrived after separating diagonal coverage from placing queens and checking moment constraints before calling the solver. The unit of search then became a set of rows, columns and diagonal counts.

This change also resolved several false leads. Exhaustive local repair required over 40 million nodes at four deletions, up from 441 thousand at three. The color result subsequently excluded that entire neighborhood through ten deletions. The complete-row and complete-column theorem likewise explains why a 28-queen core with all its used axes already paired cannot take two extra queens and give a solution. The experiments and their discarded hypotheses remain in the ledger.

For the tight 15+13 case, every one of the 28 diagonal lines must hit two boundary cells. This made a modular boundary test developed for queen domination relevant. Two independent enumerations of the eligible axis sets agreed on 46 representatives after translations fixed by the mean and exchange of the two axes. Of these, 43 have explicit matchings of 29 holes requiring at least 29 distinct lines, one has an uncoverable cell, one forces 14 sum diagonals, and one reduces to the excluded monochromatic case. The computation uses the authors’ boundary condition and a separate centroid proof for this board. It uses none of their symmetry conjectures. [Karandikar–Dutta, Section 5](https://doi.org/10.37236/12003)

A second experiment tested 3,403 symmetry classes where each unused axis is a periodic pattern of period at most five restricted to an interval. This family includes the mixed-color optimum at n=12. A geometric filter left 43 classes. Direct fixed-axis PB timed out on ten. Diagonal-cover branching followed by first and second moments excluded all 43, with checkable finite trees, in about 0.1 CPU seconds of search. The number of unrestricted axis pairs remains the main bottleneck.

## The computation that decides the value

Each of the 225 intersections of unused rows and columns gives an edge between its two diagonal keys. Its endpoints are eligible only if the corresponding lines contain at least two possible queen sites on the active rows and columns. A set of saturated diagonal keys must cover all those edges, obey line capacities, and have moments fixed by the active axes. This provides short countercertificates for each possible pair of axes.

| Saturated diagonals | Why the axis enumeration is finite and small | Axis pairs left by enumeration | Final check |
|---|---|---:|---|
| Fewer than 30 | Equal spans and sums; at most two diagonals can fail to hit two of the 56 perimeter targets. | 9,016 | 8,404 direct geometric obstructions and 612 cover trees. |
| 30, with equal spans | Equal second-order axis invariant H. Each of the two opposite-side tests has its own budget of two exceptional lines. | 11,691 | 10,916 direct geometric obstructions and 775 cover trees. |
| 30, with unequal spans | Each diagonal hits exactly one of the 30 extreme-column targets. The longer span can only be 18, 22 or 26. | 0 | Endpoint reachability and H equality are incompatible. |

The two equal-span domains were generated independently using fixed-size bit masks and cyclic-word enumeration. The representative sets agreed. An independent ordinary-coordinate scan for the unequal-span case visited **all 155,117,520 possible unused row sets**. It made 44,576 comparisons of H after the endpoint tests, with zero matches. Matching certificates give explicit sets of squares that require distinct diagonal lines. Cover trees split on whether a line is saturated and check every remaining diagonal count consistent with the required first and second moments.

As a check on the modular reductions, direct enumeration on boards of sides 6, 8 and 10 reproduced the small projected domains. A separate test compared modular predictions with physical lines meeting zero, one or two marked boundary points. All 8,330 comparisons satisfied the required implications.

Independent Python and native Lean checkers accepted all 20,707 local rejection records. The Lean checker matched them one-for-one to the two domain files and verified 53,511 capacity leaves and 2,032 moment leaves. It rejected a false capacity leaf and an incomplete collection. This is executable verification of the certificates. The marginal moment identities themselves also have kernel proofs.

The three cases exhaust every legal maximal placement of size 30. The known valid 31-queen placement therefore attains the minimum. No timeout, solver-only infeasibility result, or conjectured symmetry is used in this deduction. The detailed proof below states the symmetry maps, the connection from the original board to each finite test, and the certificate checks. Related studies of spaced grids supplied the modular boundary condition. [Karandikar–Dutta, Section 5](https://doi.org/10.37236/12003)

## Replay on the provisioned development box

The Git bundle contains the research branch, the six-vertex benchmark, its pinned Lean environment, and all research source and evidence. The source ZIP provides the same checked-out files. From the parent directory of the downloaded bundle:

```sh
git clone -b research/gardner-m3-30 gardner-m3-30.bundle gardner-replay
cd gardner-replay
mkdir -p .lake
cp -a /home/dev/projects/proofs/.lake/packages .lake/
bash Gardner/replay.sh
```

The replay runs malformed-witness and model controls, both independent domain generators, the finite certificates, the unequal-span checks, the Lean proofs and the six-vertex comparator controls. A fresh checkout of code revision 5e95a78 completed this replay in 198.22 seconds. The full terminal record is in records/clean-replay.txt. The experiment ledger gives separate commands for historical exploratory runs. Nested bubblewrap must work normally on the host. The solver logs record observational timeouts; exact timings are machine-dependent. The original host repository has no external remote configured. The dedicated research branch was pushed to that local repository. The bundle can restore its history independently.
