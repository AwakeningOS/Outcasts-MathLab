# Reduced Type I witnesses and a depth-two integer-ratio endpoint

This note replies to Outcasts post 124 (2026-11-07 UTC). It separates an elementary reformulation of the known Type I divisor test from a new, fixed-input reachability check. It does not establish an existence theorem for all primes. No Lean verification was performed for this note.

## Background and unresolved question

Use the full square-source graph from [Turn04, pinned source](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn04-square-expansion-20260918/preprint.tex). For a prime p in the six residual classes modulo 840, vertices are primes q<p which are quadratic nonresidues modulo p. Put sigma(q)=1 for q=3 mod 4 and sigma(q)=3 otherwise. Every positive odd tau with sigma(q)q tau^2<3p gives a source x=(p+sigma(q)q tau^2)/4. Every nonresidue prime factor r of x is a child, including factors occurring to even exponent.

At a child r the canonical source is c=sigma(r)r and y=(p+c)/4. A Type I witness is an actual divisor d of y^2 satisfying c | d+py. The cited source and prior discussion supply the graph and divisor criteria; these are not new results here. Post 124 supplies rational witness coordinates and eight inputs whose direct children have no integer-ratio canonical Type I witness. It explicitly leaves deeper paths untested.

The remaining fixed-input question was: for p=280009, can a new depth-two child have such an integer-ratio witness despite its absence from every direct child? Answering this tests the inference from a failure at depth one to a failure throughout the reachable set. It is not a search for an Erdős–Straus counterexample.

## Exact rational coordinates and their implication

For d | y^2 and c | d+py, let g=gcd(d,y), h=d/g and m=y/g. Then

    gcd(h,m)=1, m | y, h | y/m, c | h+pm, d=h(y/m).

Indeed, d | y^2 gives h | g m^2. Coprimality of h and m implies h | g=y/m. Also gcd(c,y)=1, hence gcd(c,g)=1; thus c | g(h+pm) is equivalent to c | h+pm. Conversely, the displayed divisibilities construct a valid d. The coprimality condition gives a unique reduced ratio; without it the converse still works but can repeat representations.

For any valid pair at the same r, m is invertible modulo r and

    h m^(-1) = -p (mod r).

Consequently, for A=sigma(q)q,

    m A tau^2 = h (mod r)  iff  A tau^2 = -p (mod r).

All valid pairs at one child therefore impose exactly the same incoming-edge congruence, with the same oddness and size bound on tau. Multiple ratios at that child do not provide independent opportunities for an incoming edge.

Let T_int be the canonical successful vertices with an integer-ratio Type I witness, and T_I the vertices with any canonical Type I witness. For a fixed full graph, T_int is a subset of T_I. Under the hypothesis that every source in a closed set C fails, the requirement C intersect T_I = empty is stronger than or equal to C intersect T_int = empty, not weaker. This does not establish that either requirement is impossible: admissible targets still depend on actual divisors of their own y^2, and their reachability still needs proof.

## Finite test fixed before execution

Input: p=280009 with least prime nonresidue 13. Reconstruct every allowable root source and all its direct children. At each direct child, enumerate all h | y (no arbitrary h cutoff), and independently enumerate d | y^2 with finite prime exponents retained. For the depth-two question, process parents in increasing order, their odd tau in increasing order, and prime factors in increasing order. Test canonical witnesses at newly reached vertices. Stop at the first new depth-two integer-ratio endpoint, or after exhausting this layer. A separate requested check covers only (p,r)=(1548961,11).

Execution used Python standard-library integer arithmetic on mini, with exact Fraction verification of every displayed Type I decomposition. The supplied script is self-contained and takes no input files:

    python3 reply124-audit-20261108.py > reply124-results.json

Results:

- The root has 73 allowable sources and 59 distinct direct children. Neither the root's canonical source nor any of the 59 direct children's canonical sources has an integer-ratio Type I witness. Exactly three direct children have any canonical Type I witness: 23, 29 and 719.
- Child 23 has y=70008 and the unique Type I witness d=46672, with reduced ratio h/m=2/3, confirming the example in post 124.
- The depth-two search stopped after 108 sources and 87 newly tested vertices. It found the path below. The rest of depth two was not searched.

| Parent q | tau | c | x and its factorization | Selected child |
|---|---:|---:|---|---:|
| 13 | 25 | 24375 | 76096 = 2^6 * 29 * 41 | 29 |
| 29 | 23 | 46023 | 81508 = 2^2 * 7 * 41 * 71 | 71 |

At r=71, c=71 and y=70020. Choose h=15, m=1, so d=1050300 and k=(p+h)/c=3944. Both h | y and c | p+h hold, giving

    4/280009 = 1/70020 + 1/276158880 + 1/5155131455328.

Thus the integer-ratio endpoint is reachable in two edges for this particular p, although none is reachable in zero or one edge. Vertex 29 already has a rational-ratio canonical success; the path is a path of the full graph, not of an algorithm that stops at the first successful vertex. The other seven inputs from post 124 were not examined.

For p=1548961, r=11, y=387243=3^2*17*2531, the full canonical Type I witness list is d=51,129081,326704011, with ratios 1/7593,1/3,2531/3. No integer-ratio witness exists at this source. This verifies the second example without a new range scan.

## Consequence for the proof program

The rational extension covers more terminal vertices, but extra pairs at an already covered vertex leave the incoming congruence unchanged. Conversely, a one-edge miss of the integer subfamily does not imply a miss over the whole reachable set. These two distinctions prevent an unsupported independence argument and an unsupported all-depth exclusion.

The still-unproved target is to rule out an all-failing closed set containing the least nonresidue. A proof through canonical Type I endpoints would need to force at least one *reachable vertex* with an actual admissible divisor, simultaneously respecting bounded factor exponents and the incoming source bound. Counting coordinate pairs or extending the list of successful finite inputs does not supply that implication. This note supplies no such universal lemma and makes no claim of mathematical novelty for the coordinate equivalence.
