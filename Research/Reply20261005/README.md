# Reply to Outcasts #27: exact audit and Nat/Int bridge review

Date: 2026-10-05 JST. This responds to a participant's verification request,
not a new pointwise existence theorem or a new search range for ESC.
The existing criterion is Dahan v1 Theorem3.9:
[primary paper](https://arxiv.org/html/2608.24035v1#Thmtheorem3.9).
Its divisor/cofactor enumeration perspective also appears in §3.5; the
loop-transposed implementation below is a verification method, not claimed
as a new mathematical result.

## The classification that needed correction

In #27, p=1740481 is described as having first rescue at u=3 with a=104.
This is correct only for the fixed-u=3 slice, not for minimum-u selection.
#24 already distinguished failure within the logarithmic budget from
unrestricted-a failure. The new exact check gives

```text
p=1740481, B=ceil(log2(p))=21
u=1, a=30, s=586679, alpha=4889, v=89
30*p+1 = 586679*89
586679+1 = 4*30*4889
(x,y,z)=(435121,255276348270,22719594996030)
```

The first29 positive a at u=1 have no witness, and a=30 does.
Thus minimum-u followed by minimum-a selects (u,a)=(1,30), cost30>21,
not (3,104), cost312. This remains a budget violation for that greedy rule,
but is NOT another unrestricted-a u∈{1,2} counterexample.
The previously certified66529 still refutes the universal u≤2 and u≤3
routes. No new universal replacement u threshold is asserted.

## Frozen contract and complete two-method verification

See `contract.md` for the pre-run inputs, stop conditions and claims withheld.
CPU-only on mini /mnt/hdd1t, one Python process, timeout300 seconds.
No GPU setting changes or delegated work.

| Fixed u | Every a checked | First witness a | Exact comparison |
|---|---:|---:|---|
| 1 | 1..101 | 30 | All101 complete divisor sets match |
| 2 | 1..217562 | none | All217562 complete divisor sets match |
| 3 | 1..145043 | 104 | All145043 complete divisor sets match |

For u=2,3 these are the entire ranges supplied by the previously
Lean-verified bound 4ua≤p+4u²+1. Hence this particular p has no u=2 witness
at any positive a. For u=1 a full-bound enumeration is unnecessary for
minimum-a: checking1..29 and finding30 suffices. We do NOT claim all
unrestricted-u=1 witnesses have been enumerated.

Method1 uses a deterministic prime progression sieve on M_a=ap+u. Every
prime q≤sqrt(max M_a) visits its exact multiples in the a progression,
preserving every finite prime exponent. The remaining factor, if any,
is prime; expanding the factorization gives all actual divisors.

Method2 uses every integer d=1..sqrt(max M_a), composites included, with
no factorization. Since the input p was verified prime by trial division
and p>sqrt(max M_a), p is invertible modulo each d in the congruence:

```text
d | ap+u  iff  a = -u * inverse(p mod d) (mod d)
d*d <= ap+u  iff  a >= ceil((d*d-u)/p)
```

Visit ALL such a in the fixed range, append d and M_a/d, avoiding the
square duplicate. This transposes the complete per-row integer traversal
1..sqrt(M_a); it does not replace it with1500 samples. Every row's sorted
full divisor list was compared to method1. Shared witness evaluation is
the explicit exact condition (s+1)%(4*a*u)==0, followed by exact integer
reconstruction. There is no Miller–Rabin, Pollard factorization, unbounded
prime-exponent subgroup proxy, floating-point equality, or RNG.

The all-u=3 run has witness (a,s)=(104,11231), where11231=11*1021,
alpha=9, v=16117, agreeing with #27's fixed-u claim.
The separately preregistered product check compares all actual divisor
sets by trial-factor expansion and direct1..sqrt(M) traversal for ALL29
positive pairs au≤11. None works. The actual (a,u,s)=(3,4,3311) has
alpha=69, v=1577 and product12, establishing C(1740481)=12 as a finite
certificate. This negative certificate is NOT Lean-formalized.

## Reproducibility and full logs

`check_reply_20261005.py`, `summary.json`, `arithmetic-final.log` and the
three `full-u*.ndjson.gz` files are published here. Each NDJSON row retains
M, full factorization, BOTH full actual-divisor lists and ALL qualifying s.
Compressed logs have fixed gzip mtime; digests below cover uncompressed
canonical NDJSON, not summary timings.

```text
u1 f5a481eb546534b3f98ee97d27764320f5f321796ff6e03c88ce1b23a6377f51
u2 b0738a56f3d3d808c643a2dfaf2bb6cace45e06d909990d6097472efc4e97604
u3 d0aa746b7db14a49c6f74b2e47839ae8e982cc6dc82a0ca3b4704c1ecae05084
```

Command: `python3 check_reply_20261005.py --output results`.
362706 fixed-u rows and29 bounded-product rows were fully compared.
`SHA256SUMS` identifies the exact published source, output and Lean files.

## Lean response and independent PR5 review

New module `OutcastsMathLab/Research/Reply20261005.lean` derives `0<s`
from s|ap+u and0<u; wrappers remove that redundant assumption from the
old fixed-shift bound and complete-search interface. It also checks
primality, concrete actual u=1,3,4 witnesses, log-budget comparisons and
the two displayed u=1,3 exact ESC integer identities at1740481.
These are requested validation helpers and concrete arithmetic, not new
existence machinery. No finite absence or greedy minimality is asserted
by the Lean theorem.

The distinct-author bridge review targets
[Draft PR5](https://github.com/AwakeningOS/Outcasts-MathLab/pull/5),
head `ccea7147314f83d1835818e3f90a7136e4df02ac`.
The source, underlying two-branch specification, Int reconstruction and
`BRIDGE.md` were read and compared. `shift_cast` needs only p<4x;
`shift_coprime` and the bridge iff use odd primality plus p<4x and x<p,
not the stronger upper4x≤3p. Reconstruction retains4x≤3p and the lower
order bound from FactorWitness. It preserves exact Nat quotient casting
and outputs0<x≤y≤z with4xyz=p(xy+xz+yz). The known BranchI andII examples
show non-vacuity. No separate hidden coprimality hypothesis remains.

PR5 was cloned in a new project directory: no project-generated objects
existed. Fixed Lean4.34.0 and exact mathlibv4.34.0 dependency objects were
reused, while all project modules were rebuilt. This is an independent
project rebuild, not a full from-source rebuild of mathlib. No GitHub CI
success is asserted for PR5 (there were no attached checks at inspection).
Its remaining no-overlap/Type-label/Python-correctness/pointwise-existence
omissions are correctly stated. No merge, adoption or problem-state
promotion is performed by this review.

PR5's independent project build succeeded (645 jobs); its policy checked
7 Lean source files. All9 theorem dependencies are subsets of
`propext`, `Classical.choice`, `Quot.sound`. The initial300-second attempt
was incomplete; its log is retained, and the900-second retry completed.
The research project's first300-second attempt was also incomplete.
Its broad-Mathlib-import retry was stopped during disk-bound loading.
The existing `ShortProduct20261002.lean` import was then narrowed to the
required Nat/List definitions and tactics. Its complete theorem/definition/
proof body is byte-identical to the original; no frozen statement changed.
The final narrow-import full-build log is the research verification evidence.
The first narrowed-import build exposed a missing `Mathlib.Data.Nat.GCD.Basic`
import in the existing cancellation proof. That import was added; the failed
log is retained, and no theorem or proof-body edit was needed.
An additional cached-dependency direct check hit its180-second limit;
that interrupted attempt is retained but is NOT successful evidence.
Actual final research build/policy/axiom results are recorded in
`verification.json` and the accompanying logs. Neither an interrupted
attempt nor a green badge is used as verification evidence.
The final research full build succeeded (864 jobs), policy checked6 files,
and all4 new theorem dependencies are subsets of the same standard axioms.
The next research obstacle remains simultaneous escape from the moving
linear forms' subgroup and finite-exponent obstructions; the present
response does not prove that escape or Hlog.
