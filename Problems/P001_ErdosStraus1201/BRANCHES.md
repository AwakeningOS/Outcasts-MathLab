# Bounded factor witnesses reduced to divisors of x²

## Question and scope

Can the bounded factor witness from the existing reconstruction be represented
using only divisors of `x²`, without discarding either branch or the order bound?
Yes, mathematically, by removing factors of the prime `p`. The new Lean module
`PrimeDivisorBranches.lean` formalizes this equivalence. Its verification status
is recorded against the exact commit in PR #3 and the linked CI run.

This is a normal form for a known criterion, not a new existence theorem.
It does not change the frozen P001 statement, the Python enumerator, or the
project's acceptance status. The author has written both specification and
proof; independent specification review is pending.

## Exact specification

All variables in this module are natural numbers. Let `p` be prime, `x<p`,
and `gcd(c,p)=1`. Define the factor witness for `a` by

```text
0<a, a≤px, a | (px)², c | (a+px), cx≤a+px.
```

The last inequality expresses `x≤y` for the exact quotient `y=(a+px)/c`
when `c>0`. Writing it without subtraction avoids Nat's truncated subtraction.

`factor_witness_iff_branches` proves that this witness is equivalent to
the following disjunction:

| Branch | Parameter and divisibility | Congruence and order bound |
| --- | --- | --- |
| I | `a=t`, `0<t≤px`, `t | x²` | `c | (t+px)`, `cx≤t+px` |
| II | `a=pt`, `0<t≤x`, `t | x²` | `c | (t+x)`, `cx≤p(t+x)` |

No positivity of `c` is needed for this algebraic equivalence itself. Its
Erdős–Straus application uses `c=4x-p>0`, `p<4x≤3p`, and odd primality.
The coprimality needed there follows from the preceding `PrimeCoprimality`
module. The new module does **not** formalize the Nat/Int interface to that
module or assert a theorem about the reconstructed denominators' Type labels.

## Derivation

If `p` does not divide `a`, primality gives `gcd(a,p)=1`. Cancellation of `p²`
from `a | p²x²` gives `a | x²` (Branch I).

If `p | a`, write `a=pt`. From `a≤px` obtain `t≤x<p`. Since `t>0`, `p` does
not divide `t`, so cancellation from `t | px²` yields `t | x²`. Finally,
`c | a+px` becomes `c | p(t+x)`. Coprimality of `c,p` lets us cancel `p`,
giving Branch II. The order bound is preserved exactly, not dropped.

Conversely, each branch supplies a divisor of `(px)²`, the original bounds,
and the original congruence. These are all the requirements of the factor
witness. In particular this is an iff, not merely two sufficient recipes.

For the positive prime-range application, the familiar Type interpretation
is a paper-level consequence: in Branch I, `p∤a` and the complementary factor
has two factors of `p`; in Branch II, both factors have one. Modulo `p` in
`cy=a+px, cz=b+px`, with `p∤c`, this means respectively only `z` is divisible
by `p`, or both `y,z` are divisible by `p`. This interpretation is not counted
as one of today's three Lean theorems.

## Literature and remaining question

Search terms: Erdős–Straus Type I Type II divisor criterion, fixed shift,
bounded factor-pair parametrization, smallest denominator p/2. Primary
references inspected:

- [Kyle Bradford, v1, Propositions 1–4](https://arxiv.org/html/2403.16047v1):
  states these same two `d | x²` congruences and reconstructs the two Types.
  That paper uses the sharper range `ceil(p/4)≤x≤ceil(p/2)`. We do not import
  that range theorem here: our equivalence retains the order bound explicitly
  and assumes only `x<p` and `gcd(c,p)=1`. The congruences themselves are
  therefore already published, not merely analogous to prior work.
- [Elsholtz–Tao, v6, Introduction and §2](https://arxiv.org/html/1107.1010v6):
  the standard prime-denominator Type I/II classification.
- [Dahan, v1, §2.3, Corollary 2.7 and Definition 2.8](https://arxiv.org/html/2608.24035v1#S2.SS3):
  the complete two-branch fixed-shift criterion using coprime divisors of `x`.
  The present `x²` form instead starts from our bounded factor `a | (px)²`.

These references do not supply the missing universal witness in every prime case.
Local mathlib source inspection found and reused the standard prime/coprime
and divisibility lemmas; no claim of first formalization is made.

The next existence target is explicit: for each remaining prime `p`, find
an allowed `x` and a positive divisor `t` of `x²` satisfying at least one row.
Showing a residue belongs to a generated multiplicative group is still
insufficient: `t` must divide `x²` with bounded prime exponents, and must meet
the row's numerical bounds. This theorem does not prove such a `t` exists.

## Validation contract

- Three general theorems: `remove_coprime_square`, `bounded_divisor_split`,
  `factor_witness_iff_branches`.
- Success requires the exact module imported by the root, a successful pinned
  Lean 4.34.0/mathlib v4.34.0 build, and inspection of all three axiom reports.
- Full build on GitHub Actions; no expanded finite search. The existing CI
  finite regression remains 2,324 inputs and 970 solutions.
- This work has no stochastic experiment or training run. CI retries are
  limited to correcting concrete compiler diagnostics; no acceptance-state
  changes or PR merges are part of it.
