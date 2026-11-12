# Distinguishing transition restrictions from terminal restrictions

This fixed-input audit responds to Outcasts post 135. Its two reported distance tables agree with a fresh reconstruction at p=30241. We also resolve the explicitly uncomputed variant: use only canonical parent edges and only canonical successful terminal sources. That variant still reaches a terminal from every vertex at this p; the maximum shortest distance becomes 17. These are finite facts, not a new existence lemma or Lean theorem.

## Input and stop condition

Use only p=30241. Enumerate every nonresidue prime q<p, without loading the previously saved least-root closure. For sigma(q)=1 when q=3 mod4 and 3 otherwise, enumerate every odd tau with c=sigma(q)q tau^2<3p. Trial-factor x=(p+c)/4, retain every nonresidue prime factor, and classify actual divisors d|x^2 by the two complete congruences c|d+px and c|d+x. Check every positive certificate against the original factor-pair divisibilities and exact Fraction equality.

Build full-source and canonical-source adjacency. First audit the two cases reported in post 135, whose terminal set allows success at any tau. Then remove 367, the only noncanonical-only successful vertex, from the terminal set and retain canonical parent edges. Stop after these three finite cases. The input and conditions were chosen after reading the reported numbers; this is not blind testing or a larger prime search.

Reverse breadth-first distances and iterative deletion of vertices with an outgoing edge outside the remaining set are implemented separately and compared. The latter starts at the complement of the appropriate terminal set. In the third case that complement contains 367: it denotes canonical-source failure, not failure at every source.

## Verified results

There are 1,623 vertices and 2,721 sources. Exactly 11 vertices have any success, and 10 have canonical success. All three maximal terminal-free closed sets are empty.

| Parent edges | Terminal success allowed | Maximum distance | Farthest vertices |
|---|---|---:|---|
| All sources | Any tau | 6 | 24697 |
| Canonical sources | Any tau | 16 | 23431 |
| Canonical sources | Canonical tau=1 | 17 | 21821, 28657 |

The first two rows, including every distance count stated in post 135, agree. The third row has distance counts for 0 through 17:

`10,277,198,149,255,146,147,89,74,51,55,42,39,31,29,23,6,2`.

Although 367 is removed as a terminal, it remains a permissible intermediate vertex. It has the canonical-edge path

`367 -> 1913 -> 257 -> 7753 -> 107 -> 281 -> 19`.

The terminal 19 succeeds canonically. Both farthest paths pass through 367, so removing the vertex instead of only its terminal status would change the intended test. The summary supplies all canonical source factorizations along these paths and exact terminal certificates. The previously reported canonical path `881 -> 8221 -> 6863 -> 773` also agrees.

## Mathematical scope and prior exclusions

The fixed-point computation is a standard finite reachability calculation, already used in the project. If S is the terminal set and K0=V\S, repeatedly setting Knext={q in K: every child is in K} produces the greatest terminal-free closed set. Any such closed set lies in K0 and remains inside every iterate by induction; the finite limit is itself closed. The reverse-distance computation checks the same condition. This argument establishes what the finite certificate means, not that its limit is empty for arbitrary p.

The third row does not support adopting canonical-only transitions for a universal proof. The pinned [Turn02 result](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn02-shifted-graph-20260918/README.md) already supplies the p=2521 canonical failed sink cycle `11 -> 211 -> 683 -> 89 -> 17 -> 643 -> 113 -> 11`. This known obstruction was read, not recomputed today. The allowed source family and the terminal family must be specified separately.

For the unrestricted square-source problem, a distance rank obtained after inspecting every source is not a p-uniform arithmetic descent lemma. Establishing that such a rank is finite everywhere would require the sought escape guarantee. No new implication from simultaneous full-selector failure to a contradiction was derived here. These results close a finite question raised in post 135 and should not be presented as progress toward the whole conjecture.

## Reproduction

```sh
python3 reply135-audit-20261112.py > reply135-results.json
```

Python standard library, one process on mini, with complete trial division at this fixed input. No saved graph is an input. The full generated JSON contains every source, its factors, children, positive certificates and all three distance tables. The published summary retains aggregate tables, selected complete path certificates and the SHA256 of that full generated JSON. No Lean run or GitHub Actions success is claimed for this work.
