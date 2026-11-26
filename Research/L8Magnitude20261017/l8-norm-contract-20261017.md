# Contract: reply66-68, one counterexample and a phase-discarding L8 lower bound

Saved before this run. Standard tools: character orthogonality (NIST DLMF27.8.6), Jacobi multiplicativity and reciprocity (27.9), triangle inequality. No priority claim; no new ESC prime-range verification. The target is a pointwise existence obstruction and a prospective certificate, not a proof from finite success rates.

1. Independently check p38296729: primality, residual class, all73 coprime log-box pairs, all81 E pairs (overlap allowed), full divisors by direct integer division/factor construction/bounded residue DP, and exact character values in66's four positive rows. Reconcile the 9/36/36 layer counts and the outside-E group obstruction from the earlier610 rows. Replaying66's inline code is optional and must be distinguished from independent checks. Do not rerun the179468-prime or5625-prime scans; receive their totals as participant reports.

2. Necessary condition68: for p in residual6 classes, p>120, lambda(4au)=8 => au in{8,24,40,120}, every possible u has Legendre symbol1. A target divisor has symbol-1, so its cofactor also has symbol-1; N has at least2 nonresidue prime factors counted with actual multiplicity. Paper derivation by reciprocity, plus exact checks of these statements on the fixed inputs below. This condition alone is not a sufficient guarantee.

3. Prototype c_mag (fixed now): lambda(m)=8, R=W_H/|H| from the square-coset quotient. Keep the order4 conjugate-pair signed sum T4 exactly. For each order8 conjugate-pair representative, discard the phase of F_chi and retain only a rational upper bound rho_chi on |F_chi|. Define

  c_mag=max(0, R+(T4-2*sum rho_chi)/phi(m)).

Each local factor S=sum_{j=0}^e zeta8^(j*h) has squared magnitude g+d*sqrt2, from
  (e+1)+2*sum_{j=1}^e(e+1-j)*cos(pi*h*j/4).
Multiply these nonnegative local squared norms in Q(sqrt2). For the result G+D*sqrt2, use U=G+(3/2)D if D>=0, else G+(7/5)D; 7/5<sqrt2<3/2. Let rho=ceil(1024*sqrt(U))/1024, using integer/rational square comparisons only. This bound is computed from factor residues/exponents, not W, divisors, or the order8 argument; the latter loss makes it a genuine lower bound rather than full W reconstruction. Exact order4 terms are a lower-dimensional retained component, not the whole spectrum. No sum of order8 rational parts or irrational cancellation is used in the certificate.

4. Success/failure questions fixed before computation: is c_mag sound (0<=c_mag<=W) on every checked row? Does it rescue ANY row with W>0 and old c=0? Does its positivity survive at least some previously positive L8 rows? Record gains and losses separately; never replace the old bound just because the new one is valid. New prospective strengthening Qmag: every L8 row with at least2 nonresidue factors, -1 in generated K, and W>0 is certified by c_mag. One failed actual row refutes this completeness strengthening, not soundness or ESC. If no rescue is found, do not scan a new range or tune the bound on held-out data.

5. Inputs: p38296729 plus the earlier10 fixed discovery inputs. First evaluate all log-box L8 rows for them. Then the entire published development subset from participant67's gtest_rows.csv.gz where L=8, W>0, old c=0; use every such row in its existing order. These are development/comparison data, not holdout. Download/check the pinned SHA256 before reading. Recompute factors, bound, W by factor divisors and residue DP, exact old certificate and its reported W/eta/c on each selected row; direct division on at most the first20 rows and any disagreement/counterexample. Record actual subset size, not assume16,809 are all L8. No new primes, MC, or full cohort replay.

Stop on inconsistency (factor product, divisors/DP, old values, positivity with fewer than2 nonresidue factors, bound>W) or180seconds elapsed;1 mini CPU process. A normal failure of Qmag is a research result and does not authorize retuning. Save row outputs and arithmetic proof of bound. Lean only if a new candidate requires it; this contract does not claim new formal verification.
