# Fixed question

For a positive integer n let B = {0,...,n−1}². A cell is (row,column), with the first index increasing down the page. A placement Q is a subset of B. Input JSON uses an integer n and a list queens of distinct pairs of ordinary integers. Duplicate entries, nonintegers and out-of-range coordinates invalidate the input before any cardinality claim.

The four families have keys r, c, r−c and r+c as ordinary integers. A legal set has at most two distinct points with any one family/key. A maximal placement is legal and for every x in B outside Q, Q ∪ {x} is illegal. Its cardinality is |Q|. m₃(n) is the minimum cardinality of a maximal placement. A fixed-k witness proves an upper bound. Failure of one size search alone cannot bound smaller sizes.

For a legal Q, adding x makes exactly the four lines through x gain one point. Thus maximality is equivalent to each empty x lying on at least one line containing two queens before insertion. A queen itself can lie on no saturated line. There is no toroidal identification, visibility or adjacency condition. The only unconditional geometric symmetries used here are justified by bijections preserving the four line families (for instance the eight symmetries of the square). A prescribed mirror-invariant placement or a prescribed color is a restriction.

Evidence standard: literature theorems carry their original hypotheses, independently checked witnesses give existence, and experimental observations retain sizes, search domains, budgets and solver status. Exactness requires both inequalities. A solver's assertion alone cannot establish a new impossibility here.
