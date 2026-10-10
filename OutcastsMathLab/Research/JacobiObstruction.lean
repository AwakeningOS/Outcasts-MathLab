import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# The quadratic-residue obstruction in Dahan's divisor normal form

This module formalizes a KNOWN obstruction; it is not a new result.
The obstruction goes back to Schinzel and Yamamoto (1965) and appears as
Elsholtz–Tao, arXiv:1107.1010, Proposition 1.6 (no Type I/II solutions for
odd squares). Here it is restated for the Type II criterion in the normal form
of Dahan, arXiv:2608.24035, Theorem 3.9(ii): a witness is a divisor `s` of
`a p + u` with `s ≡ -1 (mod 4 a u)`.

Main statements:
* `witness_jacobi_eq_neg_one`: every witness satisfies `J(p | s) = -1`.
* `no_witness_of_square`: a perfect square has no witness at all.
* `no_witness_of_mod_eq_one`: `p ≡ 1 (mod s)` rules out the divisor `s`.
* `finite_witnesses_miss_infinitely_many_primes`: no finite list of witnesses
  `(a, u, s)` covers all primes (via Dirichlet's theorem in Mathlib).

None of these is an existence statement for the Erdős–Straus equation.
-/

namespace OutcastsMathLab.Research.JacobiObstruction

/-- Dahan v1 Theorem 3.9(ii): `s ∣ a p + u` and `s ≡ -1 (mod 4 a u)`.
    Same shape as `DivisorWitness` in the witness-budget research modules. -/
def DivisorWitness (p a u s : ℕ) : Prop :=
  s ∣ a * p + u ∧ 4 * a * u ∣ s + 1

/-- If `s ≡ -1 (mod 4 a)` with `a > 0`, then `J(a | s) = 1`. -/
theorem jacobi_eq_one_of_dvd_succ :
    ∀ (a s : ℕ), 0 < a → 4 * a ∣ s + 1 → jacobiSym a s = 1 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro s ha hs
    have h4 : 4 ∣ s + 1 := dvd_trans (Dvd.intro a rfl) hs
    have hs4 : s % 4 = 3 := by omega
    have hsodd : Odd s := Nat.odd_iff.mpr (by omega)
    rcases Nat.even_or_odd a with ⟨b, rfl⟩ | hodd
    · have hb : 0 < b := by omega
      have h8 : 8 ∣ s + 1 := dvd_trans ⟨b, by ring⟩ hs
      have hb4 : 4 * b ∣ s + 1 := dvd_trans ⟨2, by ring⟩ hs
      have hcast : ((b + b : ℕ) : ℤ) = 2 * (b : ℤ) := by push_cast; ring
      have hs8 : s % 8 = 7 := by omega
      rw [hcast, jacobiSym.mul_left, jacobiSym.at_two hsodd, ih b (by omega) s hb hb4,
        ZMod.χ₈_nat_eq_if_mod_eight]
      simp [hs8, show s % 2 = 1 by omega]
    · have hda : (a : ℤ) ∣ (s : ℤ) + 1 := by
        exact_mod_cast dvd_trans (Dvd.intro_left 4 rfl) hs
      have hmod : (s : ℤ) % (a : ℤ) = (-1 : ℤ) % (a : ℤ) := by
        have h' : (a : ℤ) ∣ (-1 : ℤ) - (s : ℤ) := by
          rw [show (-1 : ℤ) - (s : ℤ) = -((s : ℤ) + 1) by ring]
          exact (dvd_neg).mpr hda
        exact Int.modEq_iff_dvd.mpr h'
      have hJ : jacobiSym s a = ZMod.χ₄ a := by
        rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hodd]
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with ha1 | ha3
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four ha1 hsodd, hJ,
          ZMod.χ₄_nat_one_mod_four ha1]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four ha3 hs4, hJ,
          ZMod.χ₄_nat_three_mod_four ha3]
        norm_num

/-- Every Dahan witness forces `p` to be a Jacobi non-residue modulo `s`. -/
theorem witness_jacobi_eq_neg_one {p a u s : ℕ} (ha : 0 < a) (hu : 0 < u)
    (hw : DivisorWitness p a u s) : jacobiSym p s = -1 := by
  obtain ⟨hdvd, hcong⟩ := hw
  have hsa : 4 * a ∣ s + 1 := dvd_trans ⟨u, by ring⟩ hcong
  have hsu : 4 * u ∣ s + 1 := dvd_trans ⟨a, by ring⟩ hcong
  have h4 : 4 ∣ s + 1 := dvd_trans (Dvd.intro a rfl) hsa
  have hs4 : s % 4 = 3 := by omega
  have hsodd : Odd s := Nat.odd_iff.mpr (by omega)
  have hmod : ((a : ℤ) * p) % (s : ℤ) = (-(u : ℤ)) % (s : ℤ) := by
    have hd : (s : ℤ) ∣ (a : ℤ) * p + u := by exact_mod_cast hdvd
    have h' : (s : ℤ) ∣ -(u : ℤ) - (a : ℤ) * p := by
      rw [show -(u : ℤ) - (a : ℤ) * p = -((a : ℤ) * p + u) by ring]
      exact (dvd_neg).mpr hd
    exact Int.modEq_iff_dvd.mpr h'
  have key := jacobiSym.mod_left' hmod
  rw [jacobiSym.mul_left, jacobi_eq_one_of_dvd_succ a s ha hsa, one_mul,
    jacobiSym.neg _ hsodd, jacobi_eq_one_of_dvd_succ u s hu hsu,
    ZMod.χ₄_nat_three_mod_four hs4] at key
  simpa using key

/-- A perfect square has no Dahan witness (Type II case of Elsholtz–Tao
    Proposition 1.6, in Dahan's normal form). -/
theorem no_witness_of_square (m a u s : ℕ) (ha : 0 < a) (hu : 0 < u) :
    ¬ DivisorWitness (m ^ 2) a u s := by
  intro hw
  have h := witness_jacobi_eq_neg_one ha hu hw
  push_cast at h
  rw [jacobiSym.pow_left] at h
  nlinarith [sq_nonneg (jacobiSym (m : ℤ) s)]

/-- If `p ≡ 1 (mod s)`, then `s` is not a witness for `p` at any `(a, u)`. -/
theorem no_witness_of_mod_eq_one {p a u s : ℕ} (ha : 0 < a) (hu : 0 < u)
    (h : p % s = 1) : ¬ DivisorWitness p a u s := by
  intro hw
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := hw.1
    rw [zero_dvd_iff] at this
    omega
  have hs1 : s ≠ 1 := by
    rintro rfl
    omega
  have hJ := witness_jacobi_eq_neg_one ha hu hw
  have hmod : (p : ℤ) % (s : ℤ) = (1 : ℤ) % (s : ℤ) := by
    rw [← Int.natCast_mod, h, Int.emod_eq_of_lt (by norm_num) (by omega)]
    rfl
  rw [jacobiSym.mod_left' hmod, jacobiSym.one_left] at hJ
  norm_num at hJ

/-- No finite list of witnesses `(a, u, s)` covers all primes: for every bound `N`
    there is a prime `p > N` with `p ≡ 1 (mod ∏ s)`, and no listed witness works for it.
    This is the covering-congruence obstruction; it says nothing about witnesses
    whose `s` grows with `p`. -/
theorem finite_witnesses_miss_infinitely_many_primes (S : Finset (ℕ × ℕ × ℕ))
    (hpos : ∀ w ∈ S, 0 < w.1 ∧ 0 < w.2.1 ∧ 0 < w.2.2) (N : ℕ) :
    ∃ p > N, p.Prime ∧ ∀ w ∈ S, ¬ DivisorWitness p w.1 w.2.1 w.2.2 := by
  have hL : (∏ w ∈ S, w.2.2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w hw => (Nat.pos_iff_ne_zero.mp (hpos w hw).2.2)
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N hL (Nat.coprime_one_left _)
  refine ⟨p, hpN, hp, fun w hw hwit => ?_⟩
  obtain ⟨ha, hu, hs⟩ := hpos w hw
  have hps : p ≡ 1 [MOD w.2.2] := Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem (fun w : ℕ × ℕ × ℕ => w.2.2) hw) hmod
  by_cases hs1 : w.2.2 = 1
  · have hc := hwit.2
    rw [hs1] at hc
    have hle := Nat.le_of_dvd (by norm_num) hc
    have : 4 ≤ 4 * w.1 * w.2.1 := by
      have : 1 ≤ w.1 * w.2.1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    omega
  · have h1 : p % w.2.2 = 1 := by
      rw [hps]
      exact Nat.mod_eq_of_lt (by omega)
    exact no_witness_of_mod_eq_one ha hu h1 hwit

/-- Non-vacuity: Dahan Proposition 3.13, `n = 409` with `(u, a) = (1, 2)`, `s = 7`. -/
theorem witness_409 : DivisorWitness 409 2 1 7 := by
  unfold DivisorWitness
  norm_num

/-! ## Proposition N: a witness has a non-residue prime factor

(Outcasts, 2026-10-10, conditional-independence note.)  `witness_jacobi_eq_neg_one` and the
multiplicativity of the Jacobi symbol give a prime factor `q` of `s` with `J(p | q) = -1`.
Consequences: a prime `p` that is a quadratic residue modulo every prime `q ≤ T` has no witness
built from primes `≤ T` alone, so conditioning on small prime factors cannot by itself decide the
existence of a witness; and `s = 11` can be a witness only when `p` is a non-residue modulo `11`
(the S test of the fork, `Research/Simultaneity20261010/`). -/

/-- If `J(a | s) = -1`, some prime factor `q` of `s` has `J(a | q) = -1`. -/
theorem exists_prime_dvd_jacobiSym_eq_neg_one {a : ℤ} :
    ∀ s : ℕ, jacobiSym a s = -1 → ∃ q, q.Prime ∧ q ∣ s ∧ jacobiSym a q = -1 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro h
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [jacobiSym.zero_right] at h
      norm_num at h
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [jacobiSym.one_right] at h
      norm_num at h
    have hqp : (Nat.minFac s).Prime := Nat.minFac_prime hs1
    obtain ⟨t, ht⟩ := Nat.minFac_dvd s
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero] at ht
      exact hs0 ht
    have : NeZero (Nat.minFac s) := ⟨hqp.ne_zero⟩
    have : NeZero t := ⟨ht0⟩
    have hmul : jacobiSym a s = jacobiSym a (Nat.minFac s) * jacobiSym a t := by
      conv_lhs => rw [ht]
      exact jacobiSym.mul_right a _ t
    rcases jacobiSym.trichotomy a (Nat.minFac s) with h0 | h1 | hm
    · rw [hmul, h0, zero_mul] at h
      norm_num at h
    · rw [hmul, h1, one_mul] at h
      have htlt : t < s := by
        have h2 := hqp.two_le
        have htpos := Nat.pos_of_ne_zero ht0
        rw [ht]
        nlinarith
      obtain ⟨r, hr, hrt, hrj⟩ := ih t htlt h
      exact ⟨r, hr, ht ▸ Dvd.dvd.mul_left hrt _, hrj⟩
    · exact ⟨Nat.minFac s, hqp, Nat.minFac_dvd s, hm⟩

/-- **Proposition N.** Every Dahan witness `s` has a prime factor `q` with `J(p | q) = -1`. -/
theorem witness_has_nonresidue_prime_factor {p a u s : ℕ} (ha : 0 < a) (hu : 0 < u)
    (hw : DivisorWitness p a u s) : ∃ q, q.Prime ∧ q ∣ s ∧ jacobiSym p q = -1 :=
  exists_prime_dvd_jacobiSym_eq_neg_one s (witness_jacobi_eq_neg_one ha hu hw)

/-- If `p` is not a non-residue modulo any prime `q ≤ T`, there is no witness all of whose prime
factors are `≤ T`. -/
theorem no_smooth_witness {p a u s T : ℕ} (ha : 0 < a) (hu : 0 < u)
    (hres : ∀ q, q.Prime → q ≤ T → jacobiSym p q ≠ -1)
    (hsmooth : ∀ q, q.Prime → q ∣ s → q ≤ T) : ¬ DivisorWitness p a u s := by
  intro hw
  obtain ⟨q, hq, hqs, hj⟩ := witness_has_nonresidue_prime_factor ha hu hw
  exact hres q hq (hsmooth q hq hqs) hj

/-- For a prime `p ≡ 1 (mod 4)`, the prime factor of Proposition N is a quadratic non-residue
modulo `p` (quadratic reciprocity); in particular it is at least the least non-residue of `p`. -/
theorem witness_prime_factor_nonsquare {p a u s : ℕ} [Fact p.Prime] (hp4 : p % 4 = 1)
    (ha : 0 < a) (hu : 0 < u) (hw : DivisorWitness p a u s) :
    ∃ q, q.Prime ∧ q ∣ s ∧ ¬ IsSquare ((q : ℤ) : ZMod p) := by
  obtain ⟨q, hq, hqs, hj⟩ := witness_has_nonresidue_prime_factor ha hu hw
  have hs4 : s % 4 = 3 := by
    have h4 : 4 ∣ s + 1 := dvd_trans ⟨a * u, by ring⟩ hw.2
    omega
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with h2 | hodd
    · subst h2
      obtain ⟨k, hk⟩ := hqs
      omega
    · exact hodd
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hp4 hqodd,
    ← jacobiSym.legendreSym.to_jacobiSym] at hj
  exact ⟨q, hq, hqs, (legendreSym.eq_neg_one_iff p).mp hj⟩

/-- `s = 11` is a witness only when `p ≡ 2, 6, 7, 8, 10 (mod 11)`, the non-residues modulo `11`. -/
theorem witness_eleven_nonresidue {p a u : ℕ} (ha : 0 < a) (hu : 0 < u)
    (hw : DivisorWitness p a u 11) :
    p % 11 = 2 ∨ p % 11 = 6 ∨ p % 11 = 7 ∨ p % 11 = 8 ∨ p % 11 = 10 := by
  have h := witness_jacobi_eq_neg_one ha hu hw
  rw [jacobiSym.mod_left] at h
  have hr : ((p : ℤ) % ((11 : ℕ) : ℤ)) = ((p % 11 : ℕ) : ℤ) := by push_cast; rfl
  rw [hr] at h
  have hlt : p % 11 < 11 := Nat.mod_lt _ (by norm_num)
  generalize p % 11 = r at h hlt ⊢
  interval_cases r <;> first | omega | (norm_num at h)

/-- Non-vacuity: `p = 1009` (hard class `169 mod 840`, `1009 ≡ 8 mod 11`) has the witness
`s = 11` at `(a, u) = (1, 3)`. -/
theorem witness_1009_eleven : DivisorWitness 1009 1 3 11 := by
  unfold DivisorWitness
  norm_num

#print axioms jacobi_eq_one_of_dvd_succ
#print axioms witness_jacobi_eq_neg_one
#print axioms no_witness_of_square
#print axioms no_witness_of_mod_eq_one
#print axioms finite_witnesses_miss_infinitely_many_primes
#print axioms witness_409
#print axioms exists_prime_dvd_jacobiSym_eq_neg_one
#print axioms witness_has_nonresidue_prime_factor
#print axioms no_smooth_witness
#print axioms witness_prime_factor_nonsquare
#print axioms witness_eleven_nonresidue
#print axioms witness_1009_eleven

end OutcastsMathLab.Research.JacobiObstruction
