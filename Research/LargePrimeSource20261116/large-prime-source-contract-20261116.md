# Audit of post143, fixed before computation

Question: can the Type I j=1 case for x=s*r, 1<=s<=8, r>p/9, c>p/3,
be excluded for every hard prime p using a complete finite congruence cover,
without the peer's q>192 condition or a small-p scan?

Existing facts: TypeII bound from104/141/142; exact TypeI selector e|x^2,
c|4e+1. Post143 claims the full large-prime-source lemma with442 cases.
Its check142 scripts are not publicly linked in that post; do not claim to
have executed or audited them. Standard quadratic reciprocity handles j=2
on paper. Existing Turn04 supplies graph/source conventions, not this lemma.

Reduction: e=f*r with f|s^2; write f/s=alpha/beta in lowest terms.
Then alpha*beta|s and h*c=alpha*p+beta for an integer 1<=h<=3alpha<=24.
All hard primes exceed840 because the six representatives below840 are1 or
composite squares. Thus q,r>p/9>93, and none divides210. In particular q>24,
so the peer's small-q boundary does not arise after reduction.

Test every s=1..8, sigma=1,3, coprime positive alpha,beta with alpha*beta|s,
h=1..3alpha. Derived necessary size conditions: alpha<sigma*h (q<p), and
4*h*s<=9*(h+alpha) (r>p/9, since otherwise p<9beta<=72).
For surviving tuples enumerate all six hard p classes through a full period
L=840*h*s*sigma. Require integral q=(alpha*p+beta)/(h*sigma), q typemod4,
integral r=((h+alpha)*p+beta)/(4*h*s), and gcd(q*r,210)=1.
Adding L preserves all these conditions: q increases by840*s*alpha,
r by210*sigma*(h+alpha). Therefore empty residue lists exclude all p,
not just p<L. Stop after all tuples, retain every survivor and all counts.

Success: all cases eliminated, completing j=1 when combined with the paper
j=0/j=2 arguments. If some survive, report exact missing cases; no universal
claim from finite primes. No new prime-range scan, no assumption of random
factors, no conclusion about existence of a successful source in every closed C.
mini CPU, Python standard library. Optional verification uses a second residue
parameterization of the same finite congruence problem, not extra prime scans.
