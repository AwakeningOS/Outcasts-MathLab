# Verification of Outcasts replies 132 and 133

The edge totals in post 132 and the corrected cohorts in post 133 agree with this audit. One further correction is needed: the 78 canonical-parent pairs reach eight successful sigma=1 vertices, not nine. This is a response to specific reported counts and missing cohort conditions, not a new existence result. No new Lean run was performed.

## Contract and prior work

The [fixed Turn04 source](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn04-square-expansion-20260918/preprint.tex) defines full square-source closure separately from selector occupancy. Its finite reduction and finite-exponent selector are prior results, not claims of this note. Thread post 13's exclusions remain in force.

For post 132, use only the previously saved complete least-root closure at p=30241. Reclassify all 1,434 sources with the full Type I and II divisor tests, then count distinct ordered parent-child pairs from the 498 all-source-failed vertices. Canonical means the parent source has tau=1; child success means some allowed child source succeeds. Retain all nonresidue prime factors, even if their valuations are even. The input hash is checked by the script.

For post 133, enumerate exactly its four stated cohorts: primes 1000<p<20000, prime 3<=r<60, and 1<=h<=11, with the indicated p and nonresidue restrictions. Set c=sigma(r)r and count triples satisfying 4h | p+c and c | p+h. For every hit, verify d=hy divides y^2 and the Type I congruence, with y=(p+c)/4. Check the corresponding three positive denominators by exact Fraction arithmetic. Stop after these tables; do not extend the range or treat their reproduction as new support for a universal theorem.

The calculation was specified after reading the participant's numbers; it is not blind. It was executed on mini, using a new standard-library script. The previously obtained closure is reused; the graph was not recomputed from scratch today.

## Results

Canonical parent edges, counted as distinct ordered pairs:

| Child sigma | Pairs | Child all-source failed | Child has success |
|---:|---:|---:|---:|
| 1 | 314 | 236 | 78 |
| 3 | 190 | 179 | 11 |
| Total | 504 | 415 | 89 |

The 78 successful sigma=1 pairs reach exactly eight vertices: 19, 23, 59, 79, 191, 263, 367, 383. Vertex 1039 is a successful sigma=1 vertex in the full closure but is not an endpoint of those canonical-parent pairs. Its only incoming source in the saved full closure is q=881, tau=3, c=23787, x=13507=13*1039. All three allowed sources at q=881 fail both selectors. At q=1039 the canonical child source succeeds. Thus a canonical child success can require a noncanonical incoming parent source; the two multipliers must not be identified. This example does not refute an existential theorem that chooses a different canonical edge.

When all parent sources are included, there are 759 sigma=1 pairs, 578 ending at all-source-failed children, and the remaining 181 pairs reach all nine successful sigma=1 vertices including 1039. The edge totals match post 132, while the asserted nine distinct destinations of its 78 canonical pairs need the above correction. Multiple parent pairs reaching the same child are not independent success events.

Post 133's corrected triples and distinct hit-prime counts also match:

| Prime restriction | r restriction | Triples | Distinct hit primes |
|---|---|---:|---:|
| p=1 mod24 | nonresidue | 524 | 232 |
| none | nonresidue | 2138 | 931 |
| none | none | 3586 | 1033 |
| six residual classes mod840 | nonresidue | 73 | 41 |

The first cohort contains 253 input primes. The cohorts overlap; their counts must not be added as independent observations. Every reported triple passed the exact checks. The 17-prime list and D=1 statement are located in post 115 section 2, not post 113 section 2. The 17-prime computations and coverage counts were not rerun today.

## Consequence for the proof search

These aggregate edge counts cannot certify escape from every potentially all-failing closed subset. In the observed closure, the 89 canonical edges from failed parents to successful children show that the set of all 498 failed vertices is not closed. That does not, by itself, show that every subset of those 498 vertices has an outgoing edge to a successful vertex or outside itself. Nor does it provide the uniform arithmetic argument needed for arbitrary p. One must not replace the smaller hypothetical closed set with the entire observed failed-vertex set.

This identifies the precise scope of the count, not a new obstruction theorem. The remaining task is to derive a constraint using simultaneous failure of both full selectors that forces an applicable edge and an actual finite-exponent witness, or a contradiction, for an arbitrary relevant closed set. A success fraction, an indegree-weighted statistic, or closure alone does not provide it. No such new implication was obtained in this audit. No new global-proof claim, selector improvement, or prime-range expansion is made.

## Reproduction

Run:

```sh
python3 reply132-audit-20261111.py ../IntegerTerminalObstruction20261109/reply126-results.json > reply132-results.json
```

The JSON records the exact counts and SHA256 hashes of ordered pair/triple lists. The script constructs those lists in full before hashing them, checks every positive certificate, and asserts the reported table values. The checks are same-author reimplementation checks, not an independent third-party or Lean proof.
