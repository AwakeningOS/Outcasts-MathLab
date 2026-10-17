# L8 magnitude lower bound and replies66-68 (2026-10-17)

## Outcome and scope

The two log-budget strengthenings proposed in65 are REFUTED at p38296729: no E witness in the73-pair box, and no positive old certificate from any eta-zero row. This does not refute Hlog, unrestricted E, TypeII existence or ESC. All73 pairs and all81 E pairs for this one prime were independently checked with direct division, factor-generated divisors, bounded residue DP, and exact character values. The successful E pair outside the budget is (14,9), target divisor544319. We did not rerun the179468-prime or5625-prime scans; their totals remain participant reports, with pinned README/contracts read at1b5239164f1fdbf5b7c914511cac1c6ee803f112.

Correct layer pair counts are9/36/36, and the unique outside-E remaining group obstruction in the old610 rows is (18490201,1,13), product13,mod52,Hcard6. These match67's corrections of66. A bookkeeping detail:18490201 is within the G cohort16million<p<19million, so the earlier10 inputs are not all outside that cohort. This does not change the stated reused-development-data status.

## General lower-bound derivation

Let N's relevant unit prime factors be q^e with their actual exponents, m=4au, and lambda(m)=8. Let F_chi=product_q sum_(j=0)^e chi(q)^j, and phi=phi(m). Let R be the signed sum of all real-character products divided by phi, equivalently W_H/|H| for H=G². R is computed from the real characters only in the certificate implementation, not from a full residue DP.

Let T4 be the unnormalized signed sum chi(-1)(F_chi+F_conjugate) over exact-order4 conjugate-pair representatives. For the exact-order8 representatives, choose rational rho_chi>=|F_chi|. Orthogonality and Re(z)>=-|z| imply

W >= R + (T4 - 2 sum rho_chi)/phi,

so c_mag=max(0, right side) satisfies0<=c_mag<=W. The old certificate and this certificate can be retained together by taking max(c_old,c_mag); no claim that the new bound dominates the old one is needed.

For zeta8=exp(pi*i/4), a local factor S(h,e)=sum_(j=0)^e zeta8^(hj) has

|S|²=(e+1)+2 sum_(d=1)^e(e+1-d)cos(pi*h*d/4)=g+d0*sqrt2.

The integer pair (g,d0) is obtained using cos values1,-1,0,+sqrt2/2,-sqrt2/2. Multiply the local pairs in Q(sqrt2), using (g,d)(g',d')=(gg'+2dd',gd'+dg'), giving G+D*sqrt2=|F_chi|². With7/5<sqrt2<3/2, use U=G+(3/2)D for D>=0, else U=G+(7/5)D. Define rho=ceil(1024*sqrt(U))/1024, implemented through integer-square comparisons, not floating point. Then rho²>=U>=|F|².

This is an application of standard orthogonality/triangle bounds, not a priority claim for a new Fourier theorem. It discards the order8 argument and does not sum the order8 rational parts or cancel their irrational coefficients. The retained order4 component and real-character baseline do not reconstruct the remaining spectrum. The bound can be zero even when W>0; explicit examples below demonstrate this information loss. Its only inputs are factorization and modulus. During every certificate call, the old full-W character oracle and full-divisor functions are replaced with functions that raise an error if called. Validation computes W separately after/beside that boundary.

Sources: [NIST DLMF27.8.6](https://dlmf.nist.gov/27.8) for orthogonality; [27.9](https://dlmf.nist.gov/27.9) for Jacobi characters and reciprocity. The local-norm formula is derived by expanding S times its conjugate. The bound and its exact rational constants were fixed before this calculation in the contract.

## The two-nonresidue necessary condition

For the residual6 prime classes, p>120, lambda(4au)=8 iff au in{8,24,40,120}; these products have18 coprime pairs. Every u has only factors2,3,5, whose symbols modulo p are1. A target divisor s congruent-1 mod4au has symbol(s/p)=chi_(-au)(s)=-1 by reciprocity and the odd quadratic character already used in the thread. Since N=ap+u has symbol1, its cofactor N/s also has symbol-1. Thus N contains at least2 nonresidue prime factors counted with actual multiplicity. This is necessary, not sufficient. In the fixed pilot27 rows with fewer than2 all give c_mag0. The condition was also checked on every selected development row.

E and this L8 family combined still have only99 coprime pairs globally; adding L8 alone does not yield a family that keeps growing with p. The uniform moving-parameter existence lemma remains missing. No random/independent-factor assumption is introduced.

## Executed development evaluation

Fixed11 inputs = the earlier10 plus38296729, all log-box L8 rows:42 rows,4 with W>0. The old and new bounds are positive on1 row each, no rescue and no lost old-positive row in this pilot. No general no-loss claim follows.

For participant67's existing cohort, pinned gtest_rows.csv.gz SHA2562851fb4611be7461ddc92d63d94ba9939b071c2fba236d9f353c01b44a43b8b1 matched its manifest. Read587689 saved rows without rerunning the full cohort. Of16809 old W-positive/c-zero rows across all L,4709 have L8. Recomputed every selected row's factorization, exact old W/eta/c, bounded DP and the new bound. The new bound is positive on355 of4709;4354 remain0. This is row-level improvement on development data, not new prime coverage or independent holdout validation. The old G cohort already had a positive box certificate for every p.

First rescued row: p16000609,(a,u)=(3,8),m96,N=5*7*53*113*229. R1,T4=16,old eta1,c_old0; new c_mag=363/2048>0, while W1 and target84959 verified separately. The order8 squared norms are0 (four pairs) and32±16sqrt2 (two pairs each). No target divisor is supplied to the certificate.

At the original discovery p38296729,(8,1), old c1 and new c_mag10451/8192>1, so W>=ceil(c_mag)=2 follows from the lower bound and integrality. Nonresidue factors are199 and229 as68 stated. However,(3,8) remains0 under both bounds. The new bound is not a complete L8 decision method.

Qmag (the attempted completeness strengthening, not a soundness theorem) is REFUTED already by p670849,(1,8): N=3*11*29*701,m32,R1,T4=0,nonresidue multiplicity2,target in K,W2 but c_mag0,raw lower-8937/8192. This refutes a guarantee that all actual L8 successes with two nonresidues/group reachability are captured. Separately,p66529,(8,1),N=3²*13*4549 has two nonresidue factors and target in K but W0, illustrating that the necessary conditions do not imply existence.

Final run one mini CPU process3.342seconds, initial3.265seconds. After the initial run, implementation was changed only to compute R via real characters and enforce the forbidden-W/oracle boundary; all preexisting result fields matched. No numerical constants, inputs or success criteria were retuned. Initial source/results preserved.422 row-check calls, including repeats (fixed/direct-check rows, first20 development rows, all positive new certificates, plus the selected counterexample), had their local-norm formula verified by an independent exact cyclotomic product. All candidate bounds satisfy c_mag<=W in the checked data. No new standalone Lean theorem, manual full build, MC or new prime range scan was run. PR updates trigger the existing repository CI automatically; its status is recorded separately. A successful repository workflow does not constitute Lean formalization of this new research bound.

## Replay

The copied portable bundle was executed with the pinned development file; exit0 and every mathematical result field except timing matched. See portable-replay.json for source/log hashes and runtime.

Python3 standard library. The two helper files are copied from the previous reviewed ExactFamily bundle; character_helper has no old top-level research loop.

`python3 check-l8-norm-20261017.py`

This runs the fixed counterexample and42-row pilot. To include the4709 development comparisons, download the pinned public gtest_rows.csv.gz from

https://raw.githubusercontent.com/betyourluck/Outcasts-MathLab/1b5239164f1fdbf5b7c914511cac1c6ee803f112/Research/CertificateRate20261016/gtest_rows.csv.gz

and run

`python3 check-l8-norm-20261017.py --development-file /absolute/path/gtest_rows.csv.gz`

The SHA256 is checked before selecting rows. The gzip is not republished here. l8-development-results.csv stores every selected input and both certificate values. l8-additional-audit.json stores direct verification of the first gain and the earlier layer corrections. The audit script is scoped to the original mini paths; use the main script for a portable replay. The public README and contract distinguish empirical checks, the paper lower-bound derivation, and unproved pointwise existence.
