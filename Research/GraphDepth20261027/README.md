# All-vertex one-edge rescue is false at p = 2521

This is a finite counterexample to a proposed global-existence lemma, not an
Erdős–Straus counterexample, a new verification range, or a proof of universal
occupancy. It leaves E₁, which starts specifically at the least nonresidue,
unrefuted. No historical-priority claim is made.

## Question fixed before computation

For a prime p in the six residual classes modulo 840, let V contain every
nonresidue prime q < p. Put sigma(q)=1 for q=3 mod 4 and 3 otherwise. For every
positive odd tau with c=sigma(q)q tau² < 3p, set x=(p+c)/4. A source succeeds if
some actual divisor d of x² satisfies c | d+x (Type II) or c | d+px (Type I).
A vertex succeeds if any allowed source succeeds. All nonresidue prime factors
of x are outgoing children, including factors with even valuations.

Candidate U₁: **every completely failed vertex has an outgoing successful
vertex**. If true, it would give universal occupancy from any vertex in at most
one edge. It is stronger than the thread's least-root E₁, not a consequence of
the known escape-from-small-sets theorem.

The executable's opening contract fixed p=2521, then p=12889 only if no
counterexample was found at 2521; full finite graph coverage; stop at the first
refuting input; smallest refuting q within that input; 120-second CPU budget.
No pretraining-style comparison or new prime interval was used. The full graph,
not a single selected path, is needed to certify a shortest distance.

## Prior work screened before execution

- The Clankers, *Finite Reduction of Mixed Square-Source Closed Sets*, fixed
  commit d20b32e1547aee2f08b440d56cceb47ab16dc4b7, proves structural escape
  statements and records the p=12889 pair 43↔61 with all 22 allowed sources
  failing. Thus acyclicity of the completely failed induced graph is already
  false. We did not rerun this known counterexample as today's result.
  https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn04-square-expansion-20260918/preprint.tex
- The same fixed repository's Turn 3 gives a canonical primitive triangle;
  its square-source exits are not immediate selector-success guarantees.
  https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn03-primitive-sextic-20260918/README.md
- Thread #78 already treated the canonical p=2521 seven-cycle and distinguished
  it from full square closure; #86/#90 define the current graph and least-root
  E₁; #92 demonstrates that a uniform short-root sufficient bound misses the
  useful child 29. Those are not rediscovered here.
- Exact Type I/II coordinates are antecedent mathematics; see Elsholtz–Tao,
  *Counting the number of solutions to the Erdős–Straus equation on unit
  fractions*, https://arxiv.org/abs/1107.1010 .

Searches included “Erdos Straus quadratic nonresidue directed graph cycle
descent”, “Erdos square 2521 17 53 29”, and nonresidue shortest graph queries.
The absence of an exact search hit is not evidence of novelty. The unresolved
distinction tested here is a successful **outside neighbor**, not merely an
outside factor or an internal cycle.

## Exact counterexample

At p=2521, q=17, all six sources fail both tests:

| tau | c | x | nonresidue child |
|---:|---:|---|---:|
|1|51|643|643|
|3|459|745=5·149|149|
|5|1275|949=13·73|73|
|7|2499|1255=5·251|251|
|9|4131|1663|1663|
|11|6171|2173=41·53|53|

The complete child set is {53,73,149,251,643,1663}. Their allowed-source counts
are respectively 3,3,2,3,2,1; all fail. Therefore the root plus every direct
child comprise 20 failed sources in total, and U₁ is false.

A shortest rescue is

    17 --tau=11--> 53 --tau=5--> 29 --tau=1--> Type I success.

The intermediate integers are 2173=41·53 and 1624=2³·7·29. The terminal source
has c=87, x=652, d=1304 and denominators (652,18908,23833534), satisfying
4xyz=2521(xy+xz+yz). Hence D(2521,17)=2, not infinity.

The complete graph at this single p has 187 vertices, 310 sources and four
successful vertices {23,29,37,1583}. Counts at shortest distances 0..6 are
4,33,73,51,18,6,2. The distance-six vertices are 1249 and 2153. Every vertex
reaches a success at this p. The least nonresidue is 11 and has distance one,
so this result does not refute E₁. No bound of six for other p is asserted.

## Checks actually performed

`graph-depth-20261027.py` uses trial prime factorization, full bounded exponent
products and reverse BFS. `replay-depth-20261027.py` imports none of that code:
it uses a prime sieve, literal quadratic residues, trial-divisor pairs and
iterative reachability layers. All 310 sources and 7,926 x² divisors match.
The replay also checks the original residual criterion using every divisor of
(px)² and agrees with the Type I/II tests. These are two same-author code paths,
not an independent-person review.

`GraphDepth20261027.lean` proves the 20 source failures with complete exponent
coverage, all-allowed-tau failure at seven vertices, exhaustive direct-child
coverage for q=17, primality and character facts, the two edges, and terminal
success. The generic divisor-cover proof is reused with attribution from
betyourluck PR #6, fc6ed0305974e2501721aefd73186907ed45d7f6, through the earlier
ShortRoot20261025 module. That helper is not a new existence theorem.

The complete 187-vertex distance table is Python-verified, not Lean-formalized.
The actual final standalone run `repair2` exited 0 with no warnings. All six
printed summary theorems use only propext, Classical.choice and Quot.sound (or
a subset), with no sorryAx. Two earlier attempts failed during finite-list
proof elaboration and closed arithmetic/decidability handling; their logs are
retained and are not counted as successful verification. The statement and
numeric certificate were unchanged. No whole-repository CI or PR merge is
asserted.

Reproduce the arithmetic with Python 3 on a CPU:

    python3 graph-depth-20261027.py
    python3 replay-depth-20261027.py

For the standalone Lean file use Lean 4.34.0 and mathlib commit
5ed2965256430c3649e86755f9576b54eca72435, then `lake env lean GraphDepth20261027.lean`.

## Consequence for a global proof

There are two distinct routes. A proof of least-root E₁ must use the fact that
every smaller prime is a quadratic residue; it cannot replace the least root
by an arbitrary failed child and invoke U₁ inductively. A proof from an arbitrary
failed closed set must allow multiple failed generations. A cycle alone is
compatible with eventual rescue, and a locally failed vertex may have only
locally failed children.

In the finite graph, global reachability from every vertex is equivalent to
every terminal strongly connected component meeting the success set. This is
an elementary reformulation, **not** a new arithmetic lemma or a proof. The
missing mathematical step is to exclude a terminal component whose every
allowed source fails the actual-divisor tests. Existing size-only escape bounds
do not supply that contradiction. The present result rejects a specific
over-strong shortcut and gives a compact regression certificate for future
proposed existence lemmas.
