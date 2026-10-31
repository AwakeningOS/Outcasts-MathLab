# Short-root guarantee does not ensure escape (2026-10-25)

This is a targeted falsification of a **restriction** of candidate E1, not a
counterexample to E1, Qleast-square, or the Erdős–Straus conjecture.
It follows Outcasts #91 and uses its existing p=2521 example, not unseen data.

## Contract and independent checks

Input p=2521, root q=11, A=11. Enumerate every positive odd tau with
A*tau^2 < 3*p, factor x=(p+A*tau^2)/4, and retain all divisors of x^2.
Type II success means c divides d+x; Type I means c divides d+p*x,
where c=A*tau^2 and d divides x^2. A separate modular dynamic program
retains the finite exponent bounds and checks the divisor residues.

Collect every nonresidue-prime child of the root sources, then enumerate all
allowed sources at every child. Stop after these finite sets are exhausted.
The restricted escape claim fails if the root fails, some child succeeds,
but every child satisfying the sufficient bound A*(r-2)^2 < 3*p fails.
This contract was fixed before this audit execution, but after reading the
participant's p=2521 result: it is a retrospective hypothesis test.

Results: all 13 root sources fail. The 12 children are
17,19,29,73,107,131,139,211,233,541,853,1249.
Among their 44 sources, only child 29 succeeds (tau=1, Type I, d=1304).
The sufficient-bound children are exactly 17 and 19; all their 6+10 sources
fail. The actual edge to 29 uses roots 4,25 modulo 29, hence odd root 25:

    11*25^2 = 6875 < 3*2521 = 7563 < 11*27^2 = 8019.

Here x_root=2349=3^4*29, while the successful child has c=87, x=652 and
denominators 652,18908,23833534. Thus the uniform sufficient root bound
misses the only successful child. Both E1 and Qleast-square remain unrefuted.

The audit also checks the exact edge criterion below on all 186 eligible
nonresidue primes r<p at this one input. It validates all 12 published success
certificates from the participant, including the final integer identity.
It does NOT rerun their 12 BFS searches or verify all 128297 visited sources.
No target-prime range is scanned and no participant code is executed.

Participant data (seven manifest entries independently verified):
https://github.com/betyourluck/Outcasts-MathLab/tree/ce353367d0ad194180839c518e7ff6b5ba1e2cd1/Research/Bfs12Inputs20261024
To rerun the Python audit, place that pinned bfs12_results.json at
participant-evidence/bfs12_results.json next to audit-short-root-20261025.py,
then run the script with Python 3 (standard library only).

## Exact criterion and the missing existence statement

Let p be a target prime (p=1 mod24), q a nonresidue prime below p, and
A=sigma(q)*q, with sigma(q)=1 for q=3 mod4 and 3 otherwise.
Let r<p be an odd nonresidue prime with r not dividing A. Quadratic
reciprocity gives (p/r)=(r/p)=-1. Consequently

    p+A*T^2 = 0 mod r has roots iff (-A/r)=-1.

When roots exist they are b and r-b. Exactly one is odd. Denote this
representative by beta_p,q(r); it is between 1 and r-2 and is the least
positive odd solution (the other residue first becomes odd above r).
Thus an allowed root source contains r **iff**

    (-A/r)=-1 and A*beta_p,q(r)^2 < 3*p.

At a fully failing q, this is exactly the outgoing-edge condition. The
case r dividing A is excluded: it would require r dividing p. Division by
4 modulo r is valid. This is a paper derivation from known quadratic
reciprocity and quadratic-root facts, not a new existence theorem.

Let G_p be the set of vertices with an actual Type I or Type II witness at
some allowed source (not just tau=1). For a failed least-nonresidue root q,
E1 is equivalent to existence of r in G_p satisfying the displayed exact
edge condition. The calculation refutes replacing beta by the universal
upper bound r-2. It does not refute the actual intersection statement.
The next proof problem is to prevent all locally successful r from missing
the interval or character condition simultaneously. Counts of each set
separately, or unsupported independence assumptions, do not prove that.

Known tools:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.html
https://math.vanderbilt.edu/rolenl/HenselsLemmaNotes.pdf
The refinement A*(r^k-2)^2<3*p is a valid sufficient condition for the
simple-root Hensel lifting argument in #90. It is not a necessary condition.

## Formal verification scope

ShortRoot20261025.lean contains 29 finite source-failure certificates and
three theorems covering all allowed odd tau at q=11,17,19. It also verifies
the concrete child-29 edge arithmetic and fraction identity. Generic
divisor-coverage lemmas are reused with attribution from PR6, commit
fc6ed0305974e2501721aefd73186907ed45d7f6; they are not new mathematics here.

The classification of eligible children, uniqueness of good child 29,
the general quadratic-reciprocity criterion, and universal E1/Q/ESC are
NOT formalized in this file. The Python result's Lean_executed=false refers
to that numerical audit alone; the separate Lean log/status describe the
subsequent formal run. Read lean-status.json and lean-final.log for outcome.

Reproduction environment: Lean 4.34.0, mathlib
5ed2965256430c3649e86755f9576b54eca72435. Run
`lake env lean ShortRoot20261025.lean` in that environment.
This is a direct mini-host run, not a GitHub Actions result.
