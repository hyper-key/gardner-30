// Standalone Typst source. Compile with Typst 0.14.2 or later.
// All coordinates that produce the witness figure and table are below.
#set document(title: "Thirty-one queens on a 30 × 30 board",
  date: datetime(year: 2026, month: 11, day: 27),
  description: "A computer-assisted proof for Gardner’s minimum no-three-in-a-line problem.",
  keywords: ("extremal combinatorics", "queen placements", "computer-assisted proof", "A219760"))
#let ink = rgb("#192a35")
#let accent = rgb("#23544f")
#let rule = rgb("#9aaba9")
#let quiet = rgb("#475d62")
#let label-font = "Libertinus Serif"
#set page(paper: "a4", margin: (top: 20mm, bottom: 20mm, x: 24mm),
  header: context if counter(page).get().first() > 1 {
    set text(font: label-font, size: 8.3pt, fill: quiet)
    [Gardner’s minimum no-three-in-a-line problem #h(1fr) $m_3(30) = 31$]
  },
  footer: context {
    set text(font: label-font, size: 8.3pt, fill: quiet)
    line(length: 100%, stroke: 0.4pt + rule)
    v(3pt)
    [Research preprint · 27 November 2026 #h(1fr) #counter(page).display("1")]
  })
#set text(font: "Libertinus Serif", size: 12pt, fill: ink, lang: "en")
#show math.equation: set text(font: "New Computer Modern Math")
#set par(justify: true, leading: 0.66em, spacing: 0.76em)
#set heading(numbering: "1.")
#show heading.where(level: 1): set text(size: 19pt, fill: accent)
#show heading.where(level: 2): set text(size: 13.5pt)
#show heading: set block(above: 0.9em, below: 0.45em)
#let cite(n) = link(label("ref" + str(n)), text("[" + str(n) + "]"))
#let ext(url, body) = link(url, text(fill: accent, body))
#let small(body) = text(size: 9.5pt, body)
#let w = (
  (0,(2,8)), (2,(0,22)), (4,(16,24)), (6,(6,10)), (8,(0,24)),
  (10,(6,26)), (11,(1,)), (12,(14,18)), (14,(12,20)), (16,(4,28)),
  (18,(12,22)), (20,(14,28)), (22,(2,18)), (24,(4,8)), (26,(10,26)), (28,(16,20)),
)
#let points = w.fold((), (xs,row) => xs + row.at(1).map(c => (row.at(0),c)))
#let keys(r,c) = (r, c, r - c, r + c)
#let counts = range(4).map(k => {
  let h = (:)
  for (r,c) in points {
    let z = str(keys(r,c).at(k))
    h.insert(z, h.at(z, default: 0) + 1)
  }
  h
})
#assert(points.len() == 31 and points.dedup().len() == 31)
#assert(points.all(p => p.all(i => 0 <= i and i < 30)))
#assert(counts.all(h => h.values().all(i => i <= 2) and h.values().filter(i => i == 2).len() == 15))
#for r in range(30) {
  for c in range(30) {
    assert((r,c) in points or range(4).any(k => counts.at(k).at(str(keys(r,c).at(k)), default: 0) == 2))
  }
}
#let board() = {
  let s = 6.15pt
  let cells = ()
  for r in range(30) {
    for c in range(30) {
      cells.push(box(width: s, height: s, baseline: 0pt,
        fill: if calc.rem(r+c,2)==0 { rgb("#eeefe8") } else { rgb("#bfcfc6") },
        if (r,c) in points { align(center+horizon, circle(radius: 2.32pt, fill: ink, stroke: none)) }))
    }
  }
  box(stroke: 0.5pt + quiet, grid(columns: (s,)*30, rows: (s,)*30, ..cells))
}
#let col-list(row) = row.at(1).map(str).join(", ")
#let coordinates() = {
  set text(size: 10.2pt)
  table(columns: (auto,auto,auto,auto), column-gutter: (0pt, 10pt, 0pt), align: left,
    stroke: none, inset: (x: 4pt, y: 2pt),
    table.header([*Row*],[*Columns*],[*Row*],[*Columns*]),
    table.hline(stroke: 0.5pt+rule),
    ..range(8).map(i => (str(w.at(i).at(0)),col-list(w.at(i)),str(w.at(i+8).at(0)),col-list(w.at(i+8)))).flatten())
}

#text(font: label-font, size: 9.5pt, fill: quiet)[Research preprint · 27 November 2026]
#v(4pt)
#text(size: 26pt, weight: "bold")[Thirty-one queens on a $30 times 30$ board]
#v(3pt)
#text(size: 14pt)[Gardner’s minimum no-three-in-a-line problem]
#v(8pt)

*Abstract.* The minimum size of a maximal queen placement on the $30 times 30$ board with at most two queens on any queen line is 31. The upper bound was known. To exclude 30, a polynomial argument forces all queens into fifteen occupied rows and fifteen occupied columns, with two on each. Boundary incidences constrain the diagonals that can cover the 225 intersections of unused rows and columns. Two finite lists of axis pairs remain. Support counts, matchings and moment certificates exclude every pair.

= The problem and a witness
Index rows and columns from 0 to 29. A _queen line_ has constant $r$, $c$, $r-c$, or $r+c$. A placement is _legal_ if each such line contains at most two queens. A line containing two is _saturated_. Adding one queen breaks legality exactly when its square lies on a saturated line. A legal placement is _maximal_ when this holds at every empty square. Write $m_3(n)$ for the smallest size of a maximal placement on the $n times n$ board.

Cooper, Pikhurko, Schmitt and Warrington proved $m_3(n) >= n$ for even $n$. Knuth reported one-color placements of size $n+1$ through $n=30$. The OEIS table gives $m_3(26)=26$ and ends at $n=29$ in its May 2026 revision. Schmitt’s 2025 table marks $n=30$ open. #cite(1) #cite(2) #cite(3)

#figure(
  grid(columns: (auto,auto), column-gutter: 18pt, align: horizon, board(), coordinates()),
  kind: image, supplement: [Figure],
  caption: [A 31-queen placement. Row 0 is at the top and column 0 at the left. The table gives all occupied squares.],
) <witness>

Each of the four families in @witness has fifteen saturated lines. Together they meet all 869 empty squares. The coordinates can be checked by counting the four keys of each queen and testing the four keys at each empty square. It remains to exclude a maximal placement of size 30. If thirty queens sufficed, there would be fifteen empty rows and fifteen empty columns, and their intersections would have to be covered entirely by diagonals.

#pagebreak()
= A 30-queen placement would use fifteen rows and fifteen columns

Use centered coordinates $x=2r-29$, $y=2c-29$. Write $X,Y,D,S$ for lines of constant $x,y,x-y,x+y$, respectively. A cover of the board by lines gives a polynomial vanishing on the board by multiplication of their defining forms, such as $x-y-d$. Adding further factors preserves vanishing. The coefficient test below uses the symmetry of the centered grid, following the zero-sum-grid approach of Oh, Schmitt and Wang. #cite(4)

*Coefficient test.* For a polynomial $P$ of total degree at most 59, its coefficient of $x^29 y^29$ vanishes if $P$ vanishes on the grid. In one variable apply the functional
$ L(f) = sum_(i=0)^29 (-1)^(29-i) binom(29,i) f(2i-29). $
The 29th finite difference kills degrees below 29 and is nonzero on $x^29$. Reflection kills $x^30$ because its values are even and the weights are antisymmetric. Applying $L$ in each variable therefore kills every monomial of total degree at most 59 except $x^29 y^29$.

Start with fifteen slots in each family, then remove two. In the remaining product of degree 58, let $a,b,d,s$ be the four slot counts. The tested coefficient is that of $t^(29-a)$ in $(t-1)^d (t+1)^s$. The intercepts disappear because only the top homogeneous part contributes. The binomial expansion gives the following values.
#align(center, small(table(
  columns: (auto,)*11, align: center+horizon, inset: (x: 3pt, y: 3pt), stroke: none,
  [Omitted], [XX], [XY], [XD], [XS], [YY], [YD], [YS], [DD], [DS], [SS],
  table.hline(stroke: 0.45pt+rule),
  [Value], [−6435], [0], [−3432], [−3432], [6435], [−3432], [3432], [0], [−3432], [0],
)))
A nonzero entry forbids a cover fitting those slots, since any unused slots can be filled with arbitrary factors.

Suppose there are 30 queens, of which $ell >= 1$ are isolated, meaning that no saturated line contains them. Each family has at most $h=floor((30-ell)/2) <= 14$ saturated lines. These lines cover every square except the isolated queens. The $X D$ quotas $(14,15,14,15)$ have at least $58-4h >= ell$ free slots. Use any one slot per isolated queen for a line through it, then fill the remaining slots. This contradicts the $X D$ entry. Hence the saturated lines cover the whole board.

Call a family _complete_ if it has fifteen saturated lines. The $X X$ and $Y Y$ entries force at least fourteen pairs on each axis. The $D S$ entry forces a complete diagonal family. The mixed entries force both diagonal families to be complete if one axis has just fourteen pairs.

Suppose $X$ has fourteen. Write $A$ for the sum of its paired row keys and $u,v$ for its singleton row keys. Let $D_1,S_1$ sum the distinct saturated diagonal keys of the respective families. Use quotas $(14,15,15,15)$, padding $Y$ if needed. The term of degree 58 omits one linear part, giving $6435 A+3432(D_1+S_1)=0$ by the table. Complete pairing gives $D_1+S_1=sum_Q x=2A+u+v$. Hence $31A+8(u+v)=0$. The even multiple of 31 given by $u+v$ has absolute value at most 58, so $u+v=A=0$.

At each queen, $(x-y)/2=r-c$ and $(x+y)/2=r+c-29$ have opposite parity. Among the thirty distinct half-keys counted by family, exactly fifteen are odd, since the thirty odd occurrences over the queens come in pairs. Their sum $(D_1+S_1)/2$ is therefore odd, a contradiction. Transposition gives the same conclusion for columns. Both axes are complete.

#pagebreak()
= The boundary of the unused grid

Let $R,C$ be the fifteen unused row and column indices and $I,J$ their complements. Every square of $R times C$ must be covered by a saturated diagonal. The bounding rectangle has 56 target squares on its boundary, fifteen on each side with the four corners counted once. A diagonal meets at most two of them. Thus the number $N$ of saturated diagonals lies between 28 and 30, and at least one slope contributes fifteen. Write the _span_ of a set for its largest index minus its smallest.

== Two identities for the occupied axes
Write $A,B$ for the sums of the centered occupied row and column keys, and $A_2,B_2$ for their sums of squares. When $N<30$, reflect one axis if necessary so that the difference family is complete. Pad the sum family to fourteen lines. In the degree-59 product with quotas $(15,15,15,14)$, taking one constant part gives $A-B+D_1=0$ by the $X S,Y S,D S,S S$ entries. Pairing gives $D_1=A-B$. Thus $A=B$, and the two unused axes also have equal sums in ordinary coordinates.

When $N=30$, all four families are complete. The degree-60 term in the cover product is $x^15 y^15 (x^2-y^2)^15$, antisymmetric in $x,y$. The product functional of §2 is symmetric and kills this term. It kills the full product by vanishing, so coefficient extraction applies to the remainder of degree at most 59. The degree-58 term now takes two constants. Write $e_2(X)$ for the sum of pairwise products of distinct occupied row keys, and similarly for $Y$. Substitution of $D_1=A-B$ and $S_1=A+B$ in the coefficient table yields
$ -6435 e_2(X) + 6435 e_2(Y) - 10296(A^2-B^2) = 0. $
Using $2e_2(X)=A^2-A_2$ and its column analogue gives the invariant
$ 21A^2-5A_2 = 21B^2-5B_2. $
Write $H(I)$ and $H(J)$ for these two quantities.

== Equal spans
Suppose both unused axes have span $e$. Translate their minima to zero, then merge $0$ and $e$ modulo $e$. This gives two 14-element residue sets $U,V$, each containing zero. The two original endpoints and all admissible offsets are restored in the enumeration. This boundary test uses the spaced-grid method of Karandikar and Dutta. #cite(5)

*Case 1. $N=28$ or $29$.* The spans must be equal. If one were longer, each diagonal could meet at most one of the 30 targets on the two sides farther apart. For a target $(u,v)$, a line meeting two boundary targets must meet both a horizontal and a vertical side. In the square, a diagonal meeting opposite sides of the same orientation can do so only corner to corner. Its side intersections therefore imply at least one of
$ u+v in U inter V, quad "or" quad u-v in U " and " v-u in V quad (mod e). $
At most $2N-56 <= 2$ diagonals can lose a boundary incidence. All target pairs failing both tests must therefore lie on at most two exceptional residue keys, each labeled by its slope. Together with equality of the two unused sums, this leaves 9,016 axis pairs up to transposition.

#pagebreak()
= Completing the enumeration of axes

*Case 2. $N=30$, equal spans.* Consider just the 30 boundary targets on the extreme columns. At most two diagonals can meet both columns at targets, namely the two corner diagonals. If $z$ of the 30 diagonals miss those columns at targets, the other lines contribute at most $30-z+2$ incidences. Hence $z<=2$.

If both $u+v$ and $u-v$ are outside $U$ modulo $e$, neither line through $(u,v)$ meets a target on an extreme column. Such failures must all be covered by at most two labeled residue keys. Transposing gives a second test on $V$, with its *own* two exceptions. The row test and the column test may require different exceptional lines. Imposing both tests and $H(I)=H(J)$ leaves 11,691 representatives. Transposition and reversal of either axis preserve the four complete families and permit these identifications.

*How the two lists are generated.* For $e=14,dots,29$, generate each 14-element subset of the residues containing zero and restore each in-board translation. To filter a prospective $U$ before choosing $V$, list, for every $v$, the $u in U$ for which both $u+v$ and $u-v$ miss $U$. Each failure offers two labeled keys. A viable partner must have fourteen distinct $v$ values whose failures two fixed keys cover. Testing that necessary condition, and then testing the partners explicitly, preserves every viable pair. In Case 1 the final joint test is the one on the previous page. In Case 2 the final tests are the separate opposite-side conditions. One implementation enumerates fixed-size bit masks. A second enumerates cyclic words and restores all anchored rotations. Their representative lists agree in each case. Symmetry is used only to choose representatives of equivalent boards.

*Case 3. $N=30$, unequal spans.* Transpose so the columns have the longer span $e$. Each diagonal meets at most one of the 30 targets on the extreme columns, so the lines and those targets are in bijection. Let $j$ count the right-side targets assigned a difference line. Then $15-j$ left-side targets are assigned a difference line.

In ordinary coordinates the sum of all thirty saturated diagonal keys equals $2 sum_(i in I) i$, by pairing. At the endpoints the very same sum is $2 sum_(r in R) r+(15-2j)e$. Row indices appear twice, and the net column contribution is the right offset minus the left, multiplied by $15-2j$. Since all row indices sum to 435,
$ 870 - 4 sum_(r in R) r = (15-2j)e. $
The left side is 2 modulo 4 and the multiplier of $e$ is odd. As $14<e<=29$, the only possible spans are 18, 22 and 26.

For a column at offset $t$ from the left endpoint and any $r in R$, at least one of $r plus.minus t$, $r plus.minus (e-t)$ must belong to $R$. Otherwise neither diagonal through that target reaches a target on an extreme column. Enumerate each 15-row set, apply the span and balance tests, then choose thirteen surviving interior columns and restore the two endpoints and every in-board translation. Testing $H(I)=H(J)$ finishes this case.
#align(center, small(table(
  columns: (auto,auto,auto,auto), align: center+horizon, inset: (x: 9pt,y: 3pt), stroke: none,
  [Longer span], [18], [22], [26], table.hline(stroke: 0.45pt+rule),
  [$H$ comparisons], [34,944], [7,392], [2,240],
  [Equal values], [0], [0], [0],
)))
The ordinary-coordinate implementation scanned all $binom(30,15)=155 117 520$ row sets. A separate implementation using residue sets also found no admissible pair.

#pagebreak()
= Certificates for the surviving axis pairs

For each of the 20,707 pairs from Cases 1 and 2, form a bipartite graph. Its two vertex classes are the ordinary keys $d=r-c$ and $s=r+c$. Each target in $R times C$ gives an edge between its two keys. Every actual placement would make its saturated diagonal keys a vertex cover of this graph, with at most fifteen keys of each kind. Each queen must lie in $I times J$.

*Support and matchings.* A key meeting fewer than two sites in $I times J$ cannot be saturated. An edge with two such endpoints excludes the pair. With exactly one such endpoint, the other is forced. Sixteen forced vertices in a single class are impossible. A matching of $k$ edges with distinct endpoints needs $k$ distinct saturated lines. After forcing vertices one may also take a matching among edges disjoint from all forced vertices. If forced vertices plus the size of this matching exceed thirty, the axis pair is excluded.

*Cover trees.* For an uncovered edge choose one endpoint $v$. One child of the tree requires $v$. The other requires every opposite endpoint of a still-uncovered edge incident to $v$, as would be necessary if $v$ were absent. Every actual cover is consistent with at least one child. A leaf either exceeds a family capacity or already covers the targets and proceeds to the following arithmetic test.

*Moments.* Count every required key twice. In each family, enumerate multisets that complete the list to thirty entries. For each remaining key the multiplicity is bounded by two and by the number of support sites in $I times J$. Required keys have already used their two occurrences. This permits additional saturated keys. Because every occupied row and column occurs exactly twice, the full lists satisfy
$ sum_Q d = 2 (sum_(i in I) i - sum_(j in J) j), quad
  sum_Q s = 2 (sum_(i in I) i + sum_(j in J) j), $
$ sum_Q d^2 + sum_Q s^2 = 4 (sum_(i in I) i^2 + sum_(j in J) j^2). $
The last equation follows from $(r-c)^2+(r+c)^2=2(r^2+c^2)$. Keeping only multisets with the required first moments, one forms the attainable square sums for each family. At every arithmetic leaf the two sets contain no pair adding to the required total.

#figure(
  table(columns: (1fr, auto, auto), align: (left,right,right), stroke: none, inset: (x: 6pt,y: 3pt),
    table.header([*Certificate or count*], [*$N<30$*], [*$N=30$, equal spans*]),
    table.hline(stroke: 0.6pt+rule),
    [Uncoverable target], [1,278], [1,286],
    [Too many forced lines], [2,980], [3,724],
    [Matching], [3,844], [5,505],
    [Matching after forcing], [302], [401],
    [Pairs requiring cover trees], [612], [775],
    table.hline(stroke: 0.4pt+rule), [*All axis pairs*], [*9,016*], [*11,691*],
    [Over-capacity leaves in the trees], [22,057], [31,454],
    [Arithmetic leaves in the trees], [960], [1,072]),
  caption: [Counts from the certificate check. The first five rows partition the axis pairs. The last two count leaves within the trees.],
)

Case 3 has no surviving axes. Every pair in Cases 1 and 2 has a checked obstruction. This excludes size 30. The even-board lower bound and @witness now give $m_3(30)=31$. #h(1fr) $square.stroked$

#pagebreak()
= Verification and research materials

*Scope of the proof.* The initial bounds $30 <= m_3(30) <= 31$ passed the six-kernel comparator. The follow-up Lean development derives the paired axes, the 28–30 diagonal count and the equal-sums condition and the quadratic invariant from the original insertion predicate. It also kernel-checks all 2,032 arithmetic leaves in their paired-axis contexts. The boundary projections, completeness of the generated domains, and the outer matching and cover-tree exclusions enter the result through the written arguments and executable checks. An end-to-end Lean theorem asserting the equality remains open.

*Independent checks.* Python and compiled Lean programs each verified every local certificate. The Lean program matched the certificates one-for-one to the domain lists and rejected a false capacity leaf and an incomplete collection. A separate agent audit directly inserted a queen at each of the 869 vacant witness squares and rechecked all 20,707 records with a standard-library Python implementation using a different residual-multiset algorithm. On boards of side 1, 2, 3 and 4 a solver and direct enumeration also agreed on all maximal placements, respectively 1, 1, 23 and 347. These small boards test the meaning of maximality independently of the size-30 proof.

*Reproduction.* The accompanying source archive includes the search programs, compressed certificates, validators, Lean sources and replay logs. The original proof has Git revision #raw("974663a") and the later kernel development #raw("aea95e9"). From the archive root, the following commands check the witness and all local records using only Python 3.10 or newer and its standard library.
#block(inset: (x: 8pt), text(size: 8.5pt, raw(block: true,
"python3 Gardner/validation/check.py Gardner/construction/witness31.json --expect 31
python3 Gardner/paper/audit/independent_audit.py .")))
The full replay runs with #raw("bash Gardner/replay.sh") in the provisioned Lean 4.35.0 environment. Its recorded clean run took 198 seconds. The additional kernel checks have their own script, #raw("bash Gardner/kernel/replay.sh"), and validation record in #raw("Gardner/kernel/VALIDATION.txt").

*AI use and review status.* The investigation used OpenAI Codex agents to develop the arguments, implement the searches and checkers, and draft this manuscript. A separate AI agent audited the proof. This version records computational and formal checks and is awaiting scholarly peer review.

#heading(level: 2, numbering: none)[References]
#let entry(n, body) = block(above: 3pt, below: 3pt, grid(columns: (17pt,1fr), text(size: 9.5pt,"[" + str(n) + "]"), text(size: 9.5pt,body)))
#entry(1)[A. S. Cooper, O. Pikhurko, J. R. Schmitt and G. S. Warrington. #ext("https://doi.org/10.4169/amer.math.monthly.121.03.213")[Martin Gardner’s minimum no-3-in-a-line problem.] _American Mathematical Monthly_ *121* (2014), 213–221.] <ref1>
#entry(2)[OEIS Foundation. #ext("https://oeis.org/A219760")[A219760, Martin Gardner’s minimal no-3-in-a-line problem.] D. E. Knuth’s 2014 remarks and A. Huchala’s 2024 extension through $n=29$.] <ref2>
#entry(3)[J. R. Schmitt. #ext("https://www.algebra.uni-linz.ac.at/Students/Seminare/s25/No3Talk_Extended.pdf")[Repeatedly applying the Combinatorial Nullstellensatz for zero-sum grids to Martin Gardner’s minimum no-3-in-a-line problem.] Seminar slides (2025).] <ref3>
#entry(4)[S. Oh, J. R. Schmitt and X. Wang. #ext("https://doi.org/10.1016/j.ejc.2024.104095")[Repeatedly applying the Combinatorial Nullstellensatz for zero-sum grids to Martin Gardner’s minimum no-3-in-a-line problem.] _European Journal of Combinatorics_ *125* (2025), 104095.] <ref4>
#entry(5)[A. Karandikar and A. Dutta. #ext("https://doi.org/10.37236/12003")[Improved lower bounds for queen’s domination via an exactly-solvable relaxation.] _Electronic Journal of Combinatorics_ *31* (2024), P4.38.] <ref5>
