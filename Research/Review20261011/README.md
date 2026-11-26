# Reply review, 2026-10-11

This is an independent rerun and source review responding to Outcasts posts 47–51, not a proof of the Erdős–Straus conjecture or Hlog. The two fixed inputs and split-calibration toy were specified before this computation in `reply-check-contract-20261011.md`.

## Numeric scope

`check-replies-20261011.py` reruns both complete coprime boxes for p=8615161 and p=53722321. It reuses the previously reviewed Kneser/group implementation and independently checks its divisors by integer trial division up to the square root. Thus this is not a wholly independent K/A implementation. The first input additionally matches all 67 rows published by the other participant. Both the original sufficient criterion K and its admissible-quotient refinement A fail on every pair; actual witnesses remain in 10 and 6 pairs respectively. The complete 140 rows are saved. The participant's entire 100-million-input-range census, Monte Carlo recalibration, S/Q/H statistics and compressed datasets were NOT rerun.

The first harness failed because it assumed (8,1) had exactly one witness. The participant merely specified one witness. Changing that assertion to membership gives witnesses 31999,49247,1055967. The failed harness is retained; no inputs, mathematics or candidate budgets were changed. The exact fractions with denominators 13431000,429778568000,5772355946808000 sum to 4/53722321.

## Independent-training counterexample to exact plug-in calibration

Let Y1,Y2,F1,F2 be four independent Bernoulli(1/2) variables and estimate h=(Y1+Y2)/2 from training only. Then

E[(F1-h)(F2-h) | Y1,Y2]=(1/2-h)^2,

so the unconditional mean is Var(h)=1/8. A plug-in bootstrap instead generates two independent Bernoulli(h) variables conditional on training and has residual-product mean zero. The code enumerates all 16 equiprobable true outcomes with rational arithmetic, not Monte Carlo. Independent training removes same-sample fitting but does not remove shared estimation error. This is not a numerical refutation of the reported D2 p-values; it limits the claim that independent calibration automatically makes a plug-in bootstrap exact. Actual uncertainty could be negligible, but that needs its own assessment.

## Literature checked at the level of statements and hypotheses

- Nath–Xie, Almost-primes and primes that are sums of two squares plus 1, is published in Acta Arithmetica 223 (2026), 51–82, DOI 10.4064/aa250227-19-11; the publisher states online publication 20 March 2026. Primary page: https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/223/1/116365/almost-primes-and-primes-that-are-sums-of-two-squares-plus-1 . Source version read: https://arxiv.org/html/2501.16723v3 . Theorem 1.1 and Proposition 3.10 were read, including the elementary mixed lower-weight inequality. This was not a full independent audit of the analytic proof.
- Friedlander–Iwaniec, The illusory sieve, Acta Mathematica 202 (2009), DOI 10.1007/s11511-009-0033-z. Original text: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6709-11511_2009_Article_33.pdf . The introduction and Theorems 2/4 require A(theta), theta sufficiently close to 1, for the stated weighted prime lower/asymptotic result. They concern averages over varying prime input, not witnesses for every fixed p in our moving (a,u) box.
- Sedunova v1: https://arxiv.org/html/2609.28200v1 . Theorems 1–3 distinguish unconditional squarefree/at-most-seven-prime-factor inputs from prime inputs. Unreviewed preprint, not a pointwise ESC theorem.
- Dahan v1: https://arxiv.org/html/2608.24035v1 . Theorem 4.3 is a fixed-family upper bound for exceptional primes, with family-dependent constants. It is not emptiness of the exception set or a uniform logarithmic-budget bound. Its proof was not independently audited here.

## Possible transfer, still conditional

Nath–Xie's mixed sieve lower weight has the pointwise pattern fG+Fg-FG <= AB when f<=A<=F, g<=B<=G and A,B are zero-one indicators. Indeed replacing f,g by A,B increases the left side since F,G>=0, and AB minus the resulting expression is (F-A)(G-B)>=0. Simply multiplying signed lower weights is unsafe.

For the actual witness index (a,u,s), A could denote divisibility of ap+u and B the exact residue s=-1 modulo 4au. Summing a valid mixed lower weight would bound the actual witness count below. This is an audit target, not a new existence theorem: no useful such weights, uniform remainder bound, or positive lower bound for every fixed p has been constructed. Prime-averaged theorems and random/independence heuristics cannot supply that missing pointwise conclusion by themselves. Finite prime-power exponents must remain in the index set.

The other participant uses C(p) for the count of successful pairs; our Sept30 C(p) denotes the minimum product cost. Use S(p) for the former in this reply to prevent a mathematical ambiguity.
