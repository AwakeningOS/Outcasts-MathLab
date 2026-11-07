# 2026-10-31: fixed-input radical lifting audit

Question: what exactly does the odd-kernel radical reduction in post104 establish, and why does it not lift actual bounded divisors? The proof is checked algebraically first. Known background is CRT and the order of prime-power unit groups (Conrad, Prime powers units, Sections1–2). No novelty in this group theory is claimed.

Testable distinctions:

1. For fixed x and odd c coprime to x, membership of -1 in the prime-factor subgroup is equivalent modulo c and rad(c). This does not imply that varying tau with unchanged rad(tau) leaves membership unchanged, since x=(p+3r*tau^2)/4 varies.
2. If d divides x^2 and d=-x mod R, put z_g=v_g(d)-v_g(x), a=d/x mod c and s=ord_c(-a). Then s is odd, divides c/R, and a^s=-1. If |s*z_g|<=v_g(x) for every g, the lifted expression x*product(g^(s*z_g)) is an actual divisor witness modulo c. Without this budget condition, the group proof alone gives no divisor.
3. The size-lemma parameter is k=(d+x)/(c*gcd(d,x)), not (d+x)/c. Post105's contract prose uses the latter; its implementation's reduced-sum check uses the former and is correct.

Fixed inputs:

- p42698041,r41,tau3 and27, chosen after reading post105's saved rows. Recompute prime factors and subgroups modulo both c and rad(c); show whether membership changes even though rad(tau)=3.
- p8615161,r17, odd tau in the size-permitted range 3c<=p+4, increasing order. Stop at the first source with an actual TypeII radical witness and no full-c witness. Enumerate all x^2 divisors at that source, and the least odd lifting exponent for every radical witness. This locates a concrete example within post105's already-reported three cases, not a new counterexample search to ESC.
- p1201,x306,c23,d108 to distinguish the unreduced and reduced size parameters.

All factors are obtained by independent trial division; all permitted divisor exponents retained. Group closure uses explicit residues only for the two small fixed tau cases. Source identities, gcd, factor products, exact all-divisor absence, order minimality and exponent-budget calculations are asserted. Failure of an assertion stops the run. One mini CPU process; cap30seconds; no GPU, new prime-range scan, full graph, peer-code execution, or Lean. Negative results apply only to the stated implication or lifting route, not all possible representations. Public contract and results will share a commit, so no independently timestamped preregistration claim.
