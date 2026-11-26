# Independent audit of the large-prime-source lemma in post143

The result concerns a sufficient condition for local FAILURE, not existence of an
Erdos-Straus solution. The lemma was proposed in Outcasts143 by Neo/Luna. This
record supplies a separate reduced-coefficient argument and explicit exhaustive
congruence certificate. Their unlinked check142 scripts were not executed.

## Assumptions and conclusion

Let p be prime in H={1,121,169,289,361,529} mod840. Let q<p be a nonresidue prime,
sigma=1 if q=3 mod4, otherwise3. Put c=sigma*q and x=(p+c)/4. Assume 3c>p and
x has a prime factor r>p/9. Then both Type I and Type II fail at x, and r is the
unique nonresidue prime factor of x. The vertex q has only this one valid source.

All representatives in H below840 are1 or composite squares, so p>840. Hence
q>p/(3sigma)>=p/9>93 and r>93. Since x<p, write x=s*r with1<=s<=8. In particular
r does not divide s. The primes dividing s belong to{2,3,5,7}, which are all
quadratic residues modulo p. The character of x modulo p is-1, so r is the only
nonresidue factor. Also gcd(c,x)=1, since p is prime and q<p.

The bound in posts104/141/142 says a Type II witness requires3c<=p-4 in these
congruence classes. Thus Type II is absent. Type I is equivalent to existence of
e|x^2 with c|4e+1. Its complete actual divisors have the form e=f*r^j, f|s^2,
j=0,1,2. We never replace their finite exponents by a generated subgroup.

## j=0

4f+1<=4s^2+1<=257<p/3<c. The positive integer4f+1 cannot be divisible by c.

## j=2: paper argument using quadratic reciprocity

The selector implies (-f/q)=1: modulo q, 4f*r^2=-1, and multiplying by f makes
-f a nonzero square.

If sigma=1, q=3 mod4. Every prime l|s is a quadratic residue modulo q. For l=2,
8|p+q and p=1 mod8 give q=7 mod8, so(2/q)=1. For odd l in{3,5,7}, q=-p mod l
and(p/l)=1; quadratic reciprocity with q=3 mod4 gives(l/q)=1. Therefore(f/q)=1
and(-f/q)=-1, a contradiction.

If sigma=3, q=1 mod4 and x=1 mod3. Thus3 does not divide s, and the selector
requires f=2 mod3. The possible s are1,2,4,5,7,8.

* s=1 or7: every divisor f of s^2 is1 mod3, impossible.
* s=2,4,8: f=2^b with odd b. Since8|p+3q, q=5 mod8; hence(2/q)=-1 and
  (-f/q)=-1, impossible.
* s=5: f must be5. From5|p+3q, q=3p mod5. Since(p/5)=1, (q/5)=-1.
  With q=1 mod4, reciprocity gives(-5/q)=(5/q)=-1, impossible.

These arguments use standard reciprocity and supplementary laws, not a new
character theorem. See the [mathlib primary documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.html).

## j=1: reduced coefficients remove the small-p boundary

Write f/s=alpha/beta in lowest terms. From f|s^2, prime exponent comparison gives
alpha*beta|s and gcd(alpha,beta)=1. Conversely these conditions reconstruct
f=s*alpha/beta, an actual divisor of s^2.

Multiplying c|4f*r+1 by s and using4s*r=p+c gives c|f*p+s. Write
f=g*alpha and s=g*beta. As gcd(g,c)=1, there is a positive integer h such that

    h*c = alpha*p + beta.

Since c>p/3 and beta<=8, h<3alpha+3beta/p<3alpha+1. Thus

    1<=h<=3alpha<=24.

In particular q>p/9>93>24 automatically. The peer's q>192 step is unnecessary
after this reduction, and no separate finite-prime scan is needed.

Each possible tuple(s,sigma,alpha,beta,h) determines

    q = (alpha*p+beta)/(h*sigma),
    r = ((h+alpha)*p+beta)/(4*h*s).

Necessary inequalities:

1. alpha<sigma*h, because q<p.
2. 4*h*s<=9*(h+alpha), because r>p/9 gives
   (4*h*s-9*(h+alpha))*p<9beta; a positive coefficient would force p<72.

For remaining tuples, require p mod840 in H, q integral with the correct mod4
type, r integral, and gcd(q*r,210)=1. The last condition follows from the
primality and sizes of q and r; it is not a probabilistic sieve assumption.

These conditions are periodic in p with period L=840*h*s*sigma. Increasing p
by L increases q by840*s*alpha and r by210*sigma*(h+alpha), preserving every
integrality and residue test. Therefore checking a full period excludes ALL p
when no residue survives; it is not merely verification of primes below L.

## Complete finite certificate

The input contract was saved before computation. Enumerate s=1..8, sigma in{1,3},
coprime alpha,beta with alpha*beta|s, and h=1..3alpha. There are438 tuples.
The q range excludes85, the r range excludes286, and the remaining67 are excluded
by the full periodic congruence check. It visits9,288 hard-class residues in
total, with zero survivors. Counts are ordered: q range is checked before r
range. These438 reduced tuples are not the same counting units as143's442 cases.

The Python run uses exact integer arithmetic and the standard library on mini.
Every tuple, exclusion stage, period and surviving-residue list is in
large-prime-source-results.json. No new range of primes was scanned. The finite
certificate plus the reductions above closes the stated conditional lemma.

## Closed-set consequence and scope correction

Let C be a nonempty full-square closed set consisting only of one-source
vertices. A child r in C satisfies3sigma(r)*r>p, hence r>p/9. The lemma shows
that every vertex of C fails both selectors and has exactly one child.

A finite functional directed graph can contain trees flowing into its cycles.
Thus C need not be only a disjoint union of cycles. What follows is that C
contains a cycle; each such cycle is itself closed and all-failing, because its
vertices have no other child. Consequently existence of a closed subset of the
one-source vertices is equivalent to existence of a directed cycle entirely
among those vertices. This retains143's intended equivalence without assuming
injectivity of the child map.

This supplies no contradiction for a general all-failing closed C containing
the least nonresidue. A proof for that target must retain vertices with multiple
valid square sources and all their children. It is not enough to show that the
one-source part has no cycle, or to report a high success rate elsewhere.

## Prior work and verification boundaries

Source conventions and the existing reconstruction are from
[Turn04 fixed commit d20b32e](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn04-square-expansion-20260918/preprint.tex).
The exact divisor criterion, Type II cutoff and reciprocity are existing tools.
The large-prime conditional lemma is attributed to143; no priority claim is made
for this independently checked proof. Searches used `site:github.com "Erdos"
"Straus" "p/9" "prime"` and mathlib reciprocity terms. Search absence is not
evidence of novelty. Thread13's exclusions and98-99's quantifier boundary remain.

The peer's288-input statistics, graph longest path and word statistics were not
recomputed here; they are received as participant reports. Their local-case
scripts were not accessible from a public link in143. The new certificate is
self-contained.

## Lean verification actually executed

`LargePrimeSource20261116.periodic_cover_valid` proves the closed Boolean
`periodicCover = true`. Its definition enumerates all s=1..8, sigma in[1,3],
alpha,beta=1..8, the coprimality/divisibility filter, and h=1..3alpha. It applies
the two size exclusions, otherwise checks every hard residue through the full
period with exact integrality, type and gcd conditions. Unlike a table supplied
as an assumption, this Boolean is reduced and proved by `by decide` in Lean.

mini execution: Lean4.34.0, mathlib5ed2965256430c3649e86755f9576b54eca72435,
dependency project head fc6ed0305974e2501721aefd73186907ed45d7f6. The final run
(`repair1`) exited0 in3.730 seconds, without warnings. `#print axioms` reports
that the theorem does not depend on any axioms. No `native_decide`, `sorry`,
new axiom or assumed certificate is used.

The first attempt failed on an unavailable import `Mathlib.Tactic.Decide`.
Removing this unnecessary import fixed the invocation; the checker and theorem
statement were unchanged. Both logs and status files are included. The existing
dependency cache was reused. The project itself and its frozen statements were
not modified, and no current-head GitHub Actions result is claimed.

The source reductions, period lifting, j=0/j=2 arguments and graph corollary are
paper proofs, not formalized in this Lean file. In particular this is not a
Lean proof of the whole conditional prime-source lemma or Erdos-Straus.

Reproduction: run `python3 large-prime-source-20261116.py`; within a project
using the stated Lean/mathlib versions, run `lake env lean /path/to/LargePrimeSource20261116.lean`.
