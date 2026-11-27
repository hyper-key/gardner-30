# Proof that m₃(30) = 31

All coordinates and directions refer to SPEC.md. These are mathematical arguments. The Lean files named below verify particular algebraic and arithmetic steps. The full translations from geometry into the hypotheses of those steps are proved here on paper.

## A polynomial test for a cover by lines

Use centered coordinates x = 2r−29, y = 2c−29. Each ranges over the 30 odd integers from −29 to 29. A line has one of the four equations x=a, y=b, x−y=d, x+y=s. Write X,Y,D,S for the families in this order.

Take a product P of one defining linear factor per covering line, allowing additional factors. It vanishes at all 900 grid points. For total degree at most 59 its coefficient of x²⁹y²⁹ must vanish. To see this, apply the 29th forward difference separately in x and y on the centered grid. In one variable the signed binomial weights annihilate powers below 29, return a nonzero constant on the 29th power, and annihilate the 30th power by reflection (even power and antisymmetric weights). Among bivariate monomials of total degree at most 59 this leaves only x²⁹y²⁹. This centered-grid version of the polynomial method was prompted by Oh–Schmitt–Wang. The calculation here is for the even board. The Lean file GridFunctional.lean checks coefficient extraction with finite integer term lists.

Consider a product of degree 58 with the family sizes obtained from (15,15,15,15) by removing two slots. Its tested coefficient depends only on the four counts a,b,d,s. It is the coefficient of t^(29−a) in (t−1)^d (t+1)^s. Thus the following table is independent of intercepts.

| Removed slots | XX | XY | XD | XS | YY | YD | YS | DD | DS | SS |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Coefficient | −6435 | 0 | −3432 | −3432 | 6435 | −3432 | 3432 | 0 | −3432 | 0 |

A nonzero entry forbids a grid cover whose counts fit within those quotas. Pad with arbitrary factors to fill the quotas. The binomial expansion gives the table, and cover_coefficients.py also tests it by grid differences on actual shifted factors.

## Lower bound and saturation when equality holds

Say a queen is isolated if none of its four lines contains another queen. All saturated lines together cover every grid point except possibly the isolated queens. For q queens of which l are isolated, each family has at most floor((q−l)/2) saturated lines. One extra line in any chosen family can cover each isolated queen.

For q≤29 the quota (14,15,14,15) fits every family's saturated lines and has at least l spare slots in total, since 58−4 floor((29−l)/2)≥l. Choose slots for all l queens, then pad. The XD entry contradicts coverage. This also derives the published lower bound 30 directly for the fixed specification.

For q=30 and l≥1 the same quota works: each family has at most 14 full lines and 58−4 floor((30−l)/2)≥l. Hence **a hypothetical 30-queen placement has no isolated queens**. In particular all 900 squares are covered by full lines.

Call a family complete if it has 15 saturated lines. Every queen then belongs to one of its 15 pairs. From XX and YY each axis has at least 14 saturated lines. From DS at least one diagonal family is complete. The four mixed nonzero entries imply that if either axis has just 14 saturated lines, both diagonal families are complete.

Suppose X has just 14. There are two singletons on separate rows. Denote their centered row keys by u,v and the sum of the 14 full row keys by A. Form a degree-59 cover at quotas (14,15,15,15), padding Y if needed. Write D₁,S₁ for the sums of the 15 full diagonal keys of each kind. To obtain a degree-58 term take the constant part of exactly one linear factor. The first row of the table then gives

    6435 A + 3432(D₁+S₁) = 0.

Each diagonal has exactly two queens, so D₁+S₁ = Σ_Q x = 2A+u+v. Simplification gives 31A+8(u+v)=0. Thus u+v is a multiple of 31. It is even with absolute value at most 58, hence zero. This gives A=0 and Σ_Q x=0.

On the other hand, (x−y)/2 = r−c and (x+y)/2 = r+c−29 have opposite parity at every queen. Counting odd keys with multiplicity gives 30 occurrences. Each full diagonal repeats its key twice, so among the 30 distinct *family-labeled* diagonal keys divided by two, exactly 15 are odd. Their sum is odd. That sum equals (D₁+S₁)/2, contradicting D₁+S₁=0. Transposition treats Y. Therefore **both axes are complete**.

Let R,C denote the 15 unused rows and columns. The queens lie on the complementary 15×15 product, twice per active row and column. The 225 squares of R×C are empty and need diagonal coverage. Its perimeter has 56 distinct squares, and each straight diagonal meets the boundary of the bounding rectangle in at most two points. At least 28 saturated diagonals are required, of which 15 have one slope and 13, 14 or 15 the other.

Two further constraints are useful for searches. If there are fewer than 30 saturated diagonals, the spans of R and C must coincide. Otherwise the two extreme sides farther apart than their transverse span contain 30 target points, and each diagonal meets at most one of them. Also, after reflection assume D is complete and S deficient. Pad S to 14 for a (15,15,15,14) degree-59 cover. Write A,B for the two sums of full centered axis keys. The XS,YS,DS,SS entries yield A−B+D₁=0. Since D is complete, D₁=A−B, hence A=B. Consequently the two active index sets have the same sum in this orientation.

## The fully paired case with 15 and 15 diagonals

There is an additional constraint even when all four families have 15 pairs. Let A,B be the sums of the 15 centered X and Y keys; let A₂,B₂ denote their respective sums of squares. Then

    21(A²−B²) = 5(A₂−B₂).

To prove this, take the actual degree-60 product P of all 60 line equations. Its homogeneous term of degree 60 is x¹⁵y¹⁵(x²−y²)¹⁵, antisymmetric under swapping x and y. The grid functional is symmetric in x and y, so it kills that term. The remainder, P minus this term, has zero functional. Apply coefficient extraction through degree 59 to the remainder. The resulting central coefficient of degree 58 must be zero.

For two omissions in one family the coefficient multiplier is its second elementary symmetric sum. For omissions in two distinct families it is the product of their first sums. By pairing, D₁=A−B and S₁=A+B. Substitution into the degree-58 table gives

    −6435 e₂(X) + 6435 e₂(Y) − 10296(A²−B²) = 0.

Here 2e₂(X)=A²−A₂ and 2e₂(Y)=B²−B₂, giving the stated identity. Thus row and column sets must have the same integer value of H=21A²−5A₂. The independent centered-grid tests in cover_coefficients.py check the expanded identity on four shifted products. full_axes.cpp measures exactly how many ordered axis pairs survive this necessary test; the surviving pairs are not candidate queen placements until their diagonal coverage and realizability have also been checked.

## Finite proof that the resulting cases are empty

Let R and C be the UNUSED index sets, of size 15 each. Every square in R×C needs a saturated diagonal. Let N be the total number of saturated diagonals. We proved 28≤N≤30. Each of the following reductions is necessary for a placement; a surviving axis pair still has to be realized by queens. The final certificate check rejects even the relaxed diagonal count requirements on each listed pair.

### Fewer than 30 diagonal lines

After reflecting one axis if necessary, the difference family has 15 full lines, the sum family at most 14. Padding the latter to 14 gave equality of the active axis sums, hence also of the unused sums. The unused spans coincide, say e, by the 30-target argument. Normalize the minimum of each unused axis to 0 for the moment. Merge 0 and e modulo e, obtaining sets U,V of 14 residues including 0. Offsets are restored when testing the original board.

A saturated diagonal hitting two of the 56 perimeter targets must meet a horizontal and a vertical side, counting opposite corners as endpoints on both. Thus for a target (u,v) such a diagonal can cover it only when one of the following holds modulo e:

    u+v belongs to U and V, or
    u−v belongs to U and v−u belongs to V.

These are necessary conditions on an ordinary line, obtained by intersecting it with the four edge lines. We make no sufficiency assumption. A selected diagonal hitting fewer than two perimeter targets loses at least one possible incidence. Since N≤29 and 56 distinct perimeter targets must be covered, at most 2N−56≤2 selected lines can do so. Therefore all failures of the displayed condition can be covered by at most two family-labeled residue keys d or s. The 28-line case also satisfies this test, with no failures.

Enumerate e=14,…,29, both 14-residue sets containing 0 and all offsets that restore the endpoints within 0,…,29 and make the two sums equal. Retain pairs passing this two-key test. Transposition exchanges U,V and preserves the full difference orientation. There are **9,016 representatives**. The original loop chooses fixed-size subsets in increasing bit-mask order. The independent loop generates cyclic words and restores all anchored rotations. It checks the number of distinct anchored words against the binomial count and tests coverage with a separate bipartite-graph implementation. Both output the same pairs. This one computation covers both 15+13 and 15+14; the separate tight-case computation is a cross-check.

### Thirty diagonal lines and equal spans

Now all four families have 15 saturated lines. H(active rows)=H(active columns) by the degree-60 calculation. For the 30 targets on the two extreme unused columns, at most two diagonals can hit both columns at targets, the two long corner diagonals. Thus among the 30 selected diagonals at most two can miss all 30 column-side targets. Indeed with z misses there are at most 30−z+2 incidences on these columns. Interchanging the axes gives the same bound for the two extreme rows.

If u+v and u−v both lie outside U modulo e, neither ordinary diagonal through the target can hit a column-side target. All such target failures must be covered by at most two diagonal residues. Impose this test for U and independently the transposed test for V. The exceptions may be different for the two tests. Imposing a shared two-line budget here would invalidate completeness.

Enumerate lengths, residues and translations as above, keeping H equal and applying the two separate tests. Reflections of individual axes preserve all four complete families and H, and transposition exchanges the axes. These operations identify equivalent pairs without requiring invariant placements. Two implementations agree on **11,691 representatives** after these identifications.

For both equal-span loops the early filter for a single axis has the following justification. Fix U. For each column residue v list the u in U for which neither u+v nor u−v belongs to U. A possible V requires 14 distinct v values for which all listed failures can be hit by the same two typed residues. Each failure (u,v) offers exactly its difference and sum residue. One implementation tests candidate pairs of residues against the columns; the other tests what could still be covered after choosing the first residue. This discards only axes that cannot occur. Exhaustively generating the partner V and imposing the stated pairwise test completes the projection.

### Thirty diagonal lines and unequal spans

Transpose so the shorter unused span lies on the row axis and the longer span e on the column axis. An ordinary diagonal now meets at most one of the 30 targets on the two extreme columns. Therefore the 30 saturated lines meet those targets bijectively.

Work in original uncentered coordinates for this calculation. Let j be the number of right-column targets assigned a difference line, so 15−j left-column targets are assigned a difference line. Add the labels of the 15 difference and 15 sum lines in two ways. Pairing over the queens gives 2 times the sum of the active row indices. Adding at the 30 endpoints gives 2 times the sum of the unused row indices plus (15−2j)e. Since all row indices sum to 435,

    870−4 ΣR = (15−2j)e,    0≤j≤15.

The left side is 2 modulo 4 and the factor of e is odd. With 14<e≤29, only 18, 22 and 26 remain. Every needed diagonal must hit an actual target on one extreme column. Normalize the axes to start at zero, and let U be the 15 distinct short-row residues modulo e (its span is smaller than e). A possible column offset v must have, for every u in U, at least one of u+v and u−v in U modulo e. The two column extremes use residue 0, and the other 13 columns require 13 further offsets.

The first enumerator applied the balance, residue and H conditions with individual axis reversal normalization and obtained zero pairs. The second independently considered every one of the 155,117,520 actual 15-row masks. It computed endpoint reach using the ordinary diagonal equations on both extreme columns, restored all allowed column sets, and used direct centered sums for H. It made 34,944, 7,392 and 2,240 H comparisons at the three respective spans. Every comparison failed. The balance arithmetic and individual endpoint shifts are also checked in Unequal.lean.

### Certificate check on the two nonempty lists

For a retained representative, let I and J be its active axes, the complements of R,C. The full rows and columns force all 30 queens into I×J. For each empty target in R×C, create an edge between its uncentered difference and sum keys. The saturated keys must be a vertex cover of these edges.

1. A key supported at fewer than two points of I×J cannot be saturated. A square with both keys unsupported immediately rejects a case. If just one key is unsupported its other key is forced. More than 15 forced keys in one direction is impossible.
2. A matching of more than 30 target edges needs more than 30 distinct keys. After forcing keys, a matching among edges incident to none of them needs one additional key per edge. The checker verifies each matching from the actual target coordinates.
3. For the remaining cases a certificate is a binary tree. Branch on a key of an uncovered edge. If this key is chosen, impose it. If it is absent, impose the opposite keys of all still-uncovered incident edges. This covers every possible set of saturated keys. A leaf either exceeds capacity or covers every target and requires the following arithmetic check.
4. Count each required key twice. In each direction enumerate every multiset of remaining keys of the required length from I×J, with each multiplicity bounded by both two and the number of support squares. Once the sum of each multiset is fixed, form the set of possible sums of its squares. For any placement R and C being unused imply that each active index occurs twice. Hence, writing d=r−c, s=r+c, the complete lists of 30 values must obey

       Σd = 2(ΣI−ΣJ),    Σs = 2(ΣI+ΣJ),
       Σd² + Σs² = 4(Σᵢ∈I i² + Σⱼ∈J j²).

   All moment leaves fail this necessary test. The checker uses multiset enumeration independently of the search that generated the trees. Extra saturations remain possible at a leaf until these tests rule them out.

| Case | Axis pairs | Uncoverable target | Forced-line excess | Matching | Matching after forcing | Pairs needing trees | Moment leaves |
|---|---:|---:|---:|---:|---:|---:|---:|
| N<30 | 9,016 | 1,278 | 2,980 | 3,844 | 302 | 612 | 960 |
| N=30, equal spans | 11,691 | 1,286 | 3,724 | 5,505 | 401 | 775 | 1,072 |
| N=30, unequal spans | 0 | | | | | | |

The independent Python and native Lean checkers accepted all 20,707 records. The Lean implementation matched each record to the supplied domains and independently enumerated admissible residual moments. It checked 53,511 over-capacity leaves and 2,032 moment leaves, and rejected both a false leaf and a missing-record control. Marginal.lean proves the displayed moment identities from the projection multisets.

This exhausts every placement of size 30 satisfying the structural theorem. Together with the independently established lower bound 30 and the explicit upper bound 31, it yields **m₃(30)=31**. This is a computer-assisted proof. Lean checks the bounds and several structural identities. The written cover reductions, exhaustive projection programs, and finite-certificate checkers are also part of the proof.

# Additional deductions and cross-checks

## Excluding all one-color placements

Suppose every queen has one checkerboard color. No diagonal through a queen reaches the other color. R×C must have the queen color, so each of R,C has just one index parity. Since each has size 15, independent axis reflections normalize the active axes to the even indices. This does not assume transpose symmetry of the queens.

Write an actual queen as (2i,2j) and compress to 0≤i,j≤14. Define d=i−j and s=i+j−14. Each i and each j occurs twice. Over the queens,

    Σd = Σs = 0,       Σ(d²+s²) = 2Σ_Q ((i−7)²+(j−7)²) = 2240.

An unused target (2i+1,2j+1) needs a saturated compressed line of key d=i−j or s=i+j−13. On a target difference of absolute value t the necessary sum keys, when this difference is unsaturated, are every other integer from t−13 to 15−t. This interval is centered at 1 and has length 15−t.

Let e be the least absolute even target difference with an unsaturated line, and o the analogous odd value, using 15 for o if all odd lines are saturated. Difference ±14 is unsaturable in the queen block (length one). A missing difference 0 would require sum 15, outside the block; a missing difference of absolute value 1 would require sum 14, of length one. Thus e belongs to {2,4,…,14} and o to {3,5,…,15}. The d keys forced saturated are all even keys with |d|<e and all odd keys with |d|<o, a total of e+o−2. The two forced s intervals from e,o have opposite parities and force 30−e−o keys, with the interval for o=15 empty. Both totals are at most 15, hence the odd number e+o is 15 or 17. In the first case all 15 s keys are paired, and their mean is 1 by symmetry of each forced interval. This contradicts Σs=0. In the second case exactly 15 d and 13 s keys are forced. The remaining four s entries have sum −26.

For each e subtract twice the squares of the forced d and s keys from 2240. This gives the required sum of squares of the four remaining entries.

| e | 2 | 4 | 6 | 8 | 10 | 12 | 14 |
|---|---:|---:|---:|---:|---:|---:|---:|
| o | 15 | 13 | 11 | 9 | 7 | 5 | 3 |
| Required sum of squares | −1062 | 170 | 954 | 1290 | 1178 | 618 | −390 |

The allowable range is 0 to 784. For 170, the four values z give Σ(z+6)(z+7)=0. Each summand is nonnegative for an integer, so only −6 and −7 occur, twice each. But −7 lies on the already saturated sum interval for e=4. For 618 write w=z+14. The four nonnegative integers w sum to 30, and their squares sum to 674. If the largest is at most 22, the square sum is at most 22·30. If it is at least 26, its own square exceeds 674. For a largest value k of 23, 24 or 25 the square sum is at most k²+(30−k)²≤650. This excludes the last possibility. The Lean files Moment.lean and Arithmetic.lean check the moment and the arithmetic tail. The rows of the table can be regenerated with tail_table.py.

## The remaining color distributions

Completeness of at least one diagonal family forces each color population to be even. Let k be the smaller population in a mixed placement. A minority-color target can only be covered diagonally by the k minority queens, who define at most k saturated diagonal lines across both slopes.

If k≤8, a homogeneous unused row set together with a mixed unused column set gives a column of 15 minority targets, already impossible. The transposed argument deals with the other axis. Two homogeneous unused axis sets force a one-color placement. Thus both parities occur in each unused axis set. For each parity group of unused rows, some unused column forms minority squares with that whole group. Each diagonal meets that column at most once, so both row parity groups have size ≤8, hence ≥7. The column groups have the same bounds. One minority parity rectangle therefore has at least seven rows and seven columns. Its perimeter has at least 24 points and requires at least 12 diagonal lines. This contradicts k≤8.

The only remaining unordered color splits are **10+20, 12+18 and 14+16**. No assumption on the distribution of queens across the two colors entered the argument before the one-color case split.

## Consequences for the constructive experiments

Every candidate has at most 20 queens of either color. Relative to the saved one-color 31-queen witness, any successful change must delete at least 11 of its queens and insert at least 10 others. This rules out all repairs through ten deletions by an argument independent of the local enumerator. Keeping an intact monochromatic 26-queen seed is also impossible, regardless of its coordinates or translation. The experiments on both constructions can be retired.

A legal 28-queen core with every used row and column already paired cannot extend to a 30-queen solution. Adding two queens would require both additions in a single new row and both in a single new column, whose intersection is only one square. In particular this explains the failure of every eightfold-invariant 28-queen core: on an even board vertical and horizontal reflections give each queen a distinct partner on its row and column. The argument does not require the completed placement to be symmetric.

## The tight perimeter case with 15 and 13 diagonals

Reflect to make the complete diagonal family D. Let T be the sum of the 13 saturated centered S keys. We already have A=B and D₁=0. Form the unpadded cover polynomial P with quotas (15,15,15,13). Now xP vanishes on the grid and has degree 59. The coefficient of x²⁸y²⁹ in P must therefore be zero. Dropping one factor of each kind in turn in its top form gives the four coefficients 0, 3432, −1716, 1980, by the same binomial formula with target x-degree 28. Taking account of the minus intercept in each linear factor gives 3432A+1980T=0, or 26A+15T=0. Hence A=15k and T=−26k for an integer k. A is the sum of 15 odd numbers, so k is odd. The four queens on unsaturated S lines have total centered S key 4A−2T=112k. Each key has absolute value at most 58, which forces k=±1. The active row and column means are therefore both 14 or both 15 in original zero-based coordinates. Simultaneous reversal of both axes exchanges these cases. We can take the two unused means to be 15.

The 28 diagonals cover the 56 points on the perimeter of the unused 15×15 product. Each must hit exactly two of them. The spans of the unused axes are equal, say e. Translate each unused axis separately so its least element is 0. The two normalized sets contain 0 and e. Merge the endpoints modulo e, obtaining 14-element sets U,V. For each u∈U and v∈V, at least one of the following holds:

* u+v modulo e belongs to both U and V.
* u−v modulo e belongs to U, and v−u modulo e belongs to V.

Indeed the diagonal covering the target must meet the two edges at target coordinates. A sum diagonal meets edges at their common sum residue. A difference diagonal meets them at opposite residues. This uses modular coordinates only to constrain the two boundary hits. Actual queen diagonals still use ordinary integer coordinates. Karandikar and Dutta formulated this boundary condition for a related covering problem in Section 5. Their symmetry conjectures are unnecessary for this deduction. [Improved lower bounds for Queen’s Domination via a relaxation](https://doi.org/10.37236/12003)
