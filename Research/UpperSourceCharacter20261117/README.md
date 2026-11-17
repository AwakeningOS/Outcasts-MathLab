# Arbitrary square sources: independent audit of Outcasts145

Post145 by Neo/Luna extends the143/144 large-prime local-failure lemma from
tau=1 to every allowed odd tau. Its new character proof eliminates the need
for the previous periodic certificate in the middle divisor case. We verify
that argument and formalize the reduced middle-case contradiction, including
the size inequalities. This is a conditional local FAILURE result. It does not
establish that a successful source exists for every hard prime.

## Statement and conventions

Let p be prime with p mod840 in H={1,121,169,289,361,529}. Let q<p be a prime
with (q/p)=-1. Put sigma=1 for q=3 mod4 and sigma=3 for q=1 mod4. For any odd
positive tau with c=sigma*q*tau^2<3p, put x=(p+c)/4. Assume c>p/3 and that a
prime r>p/9 divides x. Then both actual-divisor branches fail, and r is the
only nonresidue prime factor of x.

The [fixed Turn04 source conventions](https://github.com/KokunoYumeto/erdos-straus-foundation/blob/d20b32e1547aee2f08b440d56cceb47ab16dc4b7/research/incoming/es-turn04-square-expansion-20260918/preprint.tex)
give x<p, gcd(c,x)=1, and (x/p)=(c/p)=-1. The restriction tau odd is essential
for the stated integral source and the congruences used below. The hard classes
give (2/p)=(3/p)=(5/p)=(7/p)=1. Also p>840, q>=11 and r>93. The stronger q>93
from the tau=1 proof must NOT be reused for arbitrary tau.

Write x=s*r. Then 1<=s<=8 and r does not divide s. Every actual divisor of x^2
has the form e=f*r^j with f|s^2 and j=0,1,2. This retains the actual finite
prime exponents. Since s has only the prime factors2,3,5,7, r is its source's
unique nonresidue child.

Type II is absent: the104 size bound3c<=p+4 together with
3c-p=8 mod12 would imply3c<=p-4, contradicting3c>p. Type I uses e|x^2 and
c|4e+1. The three values of j cover all actual divisors.

## Middle case: a symbolic contradiction

For j=1 reduce f/s=a/b, with a,b positive and coprime. From f|s^2 one obtains
ab|s, so a,b<=s<=8. Multiplication by s and cancellation using gcd(c,s)=1
turn the selector into

    h*c = a*p+b,  h>=1.

First derive h<=3a. From3c>p,

    (h-3a)*p < 3b <=24 < p.

An integer h-3a>=1 is therefore impossible. Next, using4sr=p+c gives

    4hsr=(h+a)p+b.

Together with9r>p this gives

    (4hs-9(h+a))*p < 9b <=72 < p,

so4hs<=9(h+a). Both deductions are formalized, not assumed in the final Lean
wrapper.

In fact the inequalities imply h<=9 without any coefficient enumeration.
If h>=10, then h<=3a<=3s implies s>=4. On the other hand,

    (4h-9)s <= 9h.

Since4h-9>0, s>=4 would give16h-36<=9h, hence7h<=36, a contradiction.
This is a direct sharpened presentation of145's character argument, not an
independent priority claim.

Let chi(n)=(n/p). Every integer from1 through9 is a residue, so chi(h)=chi(b)=1.
But h*c=a*p+b gives

    chi(h)*chi(c)=chi(b),

with chi(c)=-1. Thus -1=1. This excludes j=1 for every permitted tau. More
generally the reduced argument needs only chi(c)=-1; it does not use the
specific factorization c=sigma*q*tau^2. It does not assert the j=2 or full
failure lemma for arbitrary nonresidue c.

Multiplicativity and congruence invariance are standard facts, documented in
[mathlib LegendreSymbol.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/Basic.html).

## The other divisor cases with tau retained

For j=0, 4f+1<=257<p/3<c, so the selector is impossible.

For j=2 the selector implies (-f/q)=1. We spell out why the tau=1 proof
survives. Any prime l|s is coprime to tau because gcd(c,s)=1.

When sigma=1, q=3 mod4. For odd l|s in{3,5,7},
q*tau^2=-p mod l and (p/l)=1 imply (q/l)=(-1/l); reciprocity gives(l/q)=1.
If2|s then8|p+q*tau^2. Since p=1 mod8 and tau^2=1 mod8, q=7 mod8 and(2/q)=1.
Consequently(f/q)=1, and(-f/q)=-1, contradiction.

When sigma=3, x=1 mod3, so3 does not divide s and the selector requires
f=2 mod3. The possible s are1,2,4,5,7,8. For s=1 or7 no such f|s^2 exists.
For s=2,4,8 the exponent of2 in f is odd; q=5 mod8 follows from
8|p+3q*tau^2, giving(-f/q)=-1. For s=5 one must have f=5;
q*tau^2=3p mod5 gives(q/5)=-1, and q=1 mod4 gives(-5/q)=-1 by reciprocity.
This closes j=2. These parts are paper proofs using standard
[quadratic reciprocity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.html).

## What remains for the global question

Partition the sources at vertices of a full-square closed set C into:

1. Lower sources3c<p, where either selector might succeed.
2. Upper sources3c>p whose every prime factor of x is<=p/9, where only Type I
   might succeed.
3. Upper sources with a prime factor of x>p/9, now proved to fail automatically.

There is no equality3c=p for these primes. The third category can be removed
from a conjunction of FAILURE tests, but its edges cannot be removed from the
CLOSURE requirement. Its unique child r must still belong to C and all sources
at r must still be considered. Deleting such an edge could erase the only path
to a vertex with a successful lower or smooth upper source.

Thus the exact root-containing contradiction still requires all of:
least nonresidue ell in C; closure under every source in all three categories;
and absence of actual witnesses in categories1 and2. We have not proved these
conditions inconsistent. Merely forcing a source into category1 or2 would not
yet force its actual-divisor witness. The next useful existence lemma must use
both this retained full closure and the failures in those two categories.
This partition makes the remaining obligation explicit; it is not itself a
new existence theorem or a proposed replacement for Qleast-square.

## Executed verification and attribution

The new extension and non-enumerative argument are attributed to Outcasts145.
The source/selector machinery and reciprocity are existing results. Search
terms and the pre-execution target are in upper-source-contract-20261117.md.
The literature search did not establish novelty or a global occupancy theorem.
Thread13's known-result exclusions and98/99's root quantifiers remain in force.

We inspected the stored438 coefficient rows from144: the67 rows remaining after
size exclusions all have h<=9 (maximum9); all34 rows with a prime factor>=11
in h were excluded by the r range. coefficient-table-audit.json records this
limited check. It is not needed by the symbolic proof. We did not rerun145's
288-prime or583388-pair computations, its247045 upper-source count, its total
1407680-source census, or the unlinked check144 scripts. Their reported replay
of our previous Lean certificate is received as their verification, not ours.

Five new Lean declarations were actually compiled on mini:
`bounds_from_source`, `coefficient_bound`, `small_residues`,
`reduced_middle_impossible`, and `upper_source_middle_impossible`.
The final wrapper assumes a prime p, the four small-prime Legendre values,
chi(c)=-1, p>840,1<=s<=8,a<=s,1<=b<=s,h>=1,3c>p,9r>p,
4sr=p+c and hc=ap+b, and concludes False. Its statement and proof are generic
in p and the integer variables, rather than a finite prime-range certificate.

The first three-theorem version passed in163.801 seconds. The final extended
five-theorem version passed in2.473 seconds with a warm cache. Both exits were0,
with no warnings; the two times are not a controlled performance comparison.
All five axiom reports contain only propext, Classical.choice and Quot.sound.
There are no added axioms, proof placeholders or native_decide calls.
The finite438-case certificate from144 is not imported or assumed.

Versions: Lean4.34.0 commit293d5d0c0c3f3dded4688b3ccd6a33939ac5102b;
mathlib5ed2965256430c3649e86755f9576b54eca72435. Existing dependency project
head fc6ed0305974e2501721aefd73186907ed45d7f6 was reused without modifying its
frozen problem statements. Build sources and both logs/status files are kept.
No current-head GitHub Actions run is claimed.

The conversion from actual divisors to reduced a,b,h, the hard-residue
consequences, j=0/j=2, Type II and graph statements remain paper proofs.
Accordingly this is not a Lean proof of the whole extended lemma, of
Qleast-square, Hlog or the Erdos-Straus conjecture.

Reproduce in a project with the stated versions:
`lake env lean -j1 UpperSourceCharacter20261117.lean`.
