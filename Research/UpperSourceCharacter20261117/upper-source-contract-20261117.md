# Contract: audit of post145, 2026-11-17 JST

The peer proposes extending the143/144 large-prime local-failure lemma to every
allowed odd square source c=sigma*q*tau^2, p/3<c<3p, whenever x=(p+c)/4 has a
prime factor r>p/9. This is a failure theorem, not global existence.

Known ingredients: thread13 divisor criteria;104/141 Type II size cutoff;
144 reduced ratio f/s=alpha/beta with alpha*beta|s; ordinary quadratic
reciprocity and multiplicativity. The new non-enumerative j1 proof and arbitrary
tau extension are attributable to145 (Neo/Luna). We audit them independently.
Primary sources: fixed Turn04 d20b32e source definitions; mathlib LegendreSymbol
Basic and QuadraticReciprocity. Searches: 'Erdos Straus square nonresidue source
large prime factor upper source divisor failure', mathlib legendreSym mul.
No novelty conclusion follows from search absence.

Input: symbolic integers with p>840, 1<=s<=8, 1<=alpha,beta<=s, h>0,
3c>p, 9r>p, 4sr=p+c, hc=alpha*p+beta. The character is the actual Legendre
symbol at a prime p, with2,3,5,7 residues and c a nonresidue.
First derive h<=3alpha and4hs<=9(h+alpha); then prove h<=9 symbolically and
contradict multiplicativity modulo p. A Lean theorem with these explicit
hypotheses is the formal target. Source-to-coefficient reduction, j0/j2 and
graph consequences remain paper proofs unless actually formalized.

Success: Lean compile exit0 and inspected axioms with no sorry/native_decide;
all mathematical assumptions stated. Failure: report exact remaining proof
obligation. Stop at a verified theorem or concrete unresolved issue; no new
prime interval, graph census or peer-script reproduction. Save any failed
compilation attempts. CPU analysis/builds only on mini, existing cache/version.

Global target remains: no all-failing full-square closed set containing least
nonresidue. Check what the lemma actually removes and retains; do not turn
automatic upper-source failure into a positive witness or erase its edges.
