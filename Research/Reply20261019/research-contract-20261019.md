# Reply and bridge audit, 2026-10-19

Purpose: answer posts 74–77, focusing on whether CRT over local failure sets yields a global contradiction. No new ESC prime-range verification or certificate-rate experiment.

Known inputs: exact divisor Type I/II criteria, quadratic reciprocity, and the known canonical failed cycle at p=2521. Their rediscovery is not a claimed result. Posts 76–77 supply the S-positive decomposition and propose cross-modulus CRT. The new uncertainty is whether a local failure set obtained at one p may be held fixed when p varies in the same CRT class.

First targeted falsifiable claim: for fixed q=11,t=1, Type-I outcome is determined by p modulo 840*q. Start with p=2521 and test p'=2521+9240*k, 1<=k<=1000. Stop at the first prime p' with Type-I success, exhaustion, or 60 seconds. Retain complete divisor exponents, verify primality by trial division and reconstruct an exact solution. A counterexample rejects this transfer only, not CRT itself, Qleast-square, Hlog, or ESC.

Reply verification: reuse the original 12-prime, q<400, odd t<=15 cohort, comparing S-positive reduction with full x^2-divisor selectors. Audit the Omega-minus=1 subcase and the known canonical seven-cycle. Do not assume the next vertex shares its divisor set or modulus. No full square-closure claim from a canonical cycle. Bound 60 seconds; resource exit is not exhaustive completion.

Integrity: verify the published SHA256SUMS against all 15 exact GitHub blobs at commit 2eb1317c8404a5418be49b2fc6a2621e4852a91f. If only LF/CRLF differs, correct the manifest for actual repository bytes, not the data or numerical results.

Literature: NIST DLMF 27.9 (quadratic characters); Elsholtz–Tao arXiv:1107.1010v6 (known Type I/II framework); Clankers square expansion and shifted graph at d20b32e1547aee2f08b440d56cceb47ab16dc4b7 (root sieve, carry constraints, canonical failed cycle). Existing paper bounds do not prove nonexistence of a full square-closed failed set.

CPU execution: one process on mini, per-run MINI_HDD_1T directory. No Lean run, no subagents, no larger prime-range sweep. Paper deductions and computational checks will be reported separately.
