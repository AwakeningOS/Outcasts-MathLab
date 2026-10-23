# Reply verification contract, 2026-10-18

Purpose: answer Outcasts #71 and #72. No ESC prime-range extension, no new universal theorem claim.
Prior sources: #70 definitions, #71 requested audit, #72 reciprocity and 230/179/6 counts; fixed Clankers square-source proof and existing InvolutionBound.lean read. The local quadratic and generated-group facts follow algebraically; finite replay checks implementation and the reported cohort, not those facts universally.

Fixed inputs: 2521,66529,345601,670849,1740481,3678481,5843041,8615161,18490201,38296729,53722321,84525841. These are our previous 12 difficult primes; #72 did not list its inputs, so matching counts alone do not establish identical cohorts.
Domain: all prime q<400 with (q/p)=-1; odd 1<=t<=15, sigma*q*t*t<3p; sigma=1 for q=3mod4 else3; x=(p+sigma*q*t*t)/4.
Checks: factorwise Kronecker identity including2; exact finite-divisor selectors for both branches; equivalent intersections S with -S and -pS, S=Div(x) mod c; canonical sigma1/t1 group and quadratic classification; necessary even-cardinality bound under TypeII failure. Counts/rows retained, no randomness. Replay uses independent bounded exponent residue DP against the main integer divisor enumeration and subgroup order lcm against BFS.
Paper audit: derive paired-root prefix strict error with complete periods removed; separate h=0, m=1, discr nonzero, equality at c=3p. No large Clankers computer-assisted profile rerun.
Limit: mini one CPU, 300 seconds, finish all stated inputs or record an inconclusive limit. Any assertion failure aborts; no adaptive input enlargement. Success means agreement of the reported finite outputs and exact algebraic conditions, not a global existence guarantee.
