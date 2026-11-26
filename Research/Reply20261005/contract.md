# Reply #27: preregistered exact verification contract

Frozen before the new arithmetic run on 2026-10-05 JST.

Input p=1740481. Test DivisorWitness: positive a,u,s, s divides ap+u,
and 4au divides s+1. Known criterion, not a new existence theorem.

- u=1: a=1..101. #24 says only2521,66529 have unrestricted-a u=1
  absence among80 budget failures. Find the first a in this prefix; if none,
  do not assert global u=1 absence or a minimum-u conclusion.
- u=2: every a=1..floor((p+17)/8)=217562.
- u=3: every a=1..floor((p+37)/12)=145043.
- Positive cost12 witness (a,u,s)=(3,4,3311) is checked separately.

For EACH a, compare two complete actual-divisor sets (finite exponents):
1. Prime progression sieve factorization of ap+u, followed by full divisor
   expansion. All primes up to sqrt(max(ap+u)); leftover factors are prime.
2. Exhaustive integer-divisor traversal in transposed order. Every integer
   d from1 to sqrt(max(ap+u)), including composites, visits ALL a for which
   d divides ap+u AND d*d<=ap+u. Add both d and its complementary divisor.
   This is the entire 1..sqrt(ap+u) traversal per row, not random sampling.
   Because p is verified prime and p>sqrt(max(ap+u)), gcd(p,d)=1; the
   progression a=-u/p mod d is exact. The d*d lower bound avoids omissions
   or duplicate counting from the transpose.

Success: every row's sorted divisor sets equal; complete loop termination;
each positive witness has exact integer reconstruction and sorted x<=y<=z.
Failure: mismatch, invalid factors, missing u=1 prefix rescue, timeout, or
wrong stated first witness. Any failure is reported, not converted to proof.
Logs retain factorization, both full divisor lists, and all qualifying s.
No ESC counterexample search, subgroup-only proxy, or range extension.
CPU only on mini /mnt/hdd1t, one process, timeout300 seconds, no GPU changes.

Additional cost-minimum check registered after the full fixed-u audit and
before this check: all positive pairs a*u<=11 (29 pairs), full trial-prime
factor expansion versus direct integer divisor traversal per pair. No witness
must exist there; actual (3,4,3311) then establishes C(p)=12 as a finite
certificate. This negative certificate is not Lean-formalized.

Separate PR5 review: exact ccea7147314f83d1835818e3f90a7136e4df02ac,
fresh project generated objects, fixed Lean4.34.0/mathlibv4.34.0 dependency
cache, full lake build, policy, all9 printed axiom dependencies and source
specification comparison. No merge, adoption, or new pointwise existence.
