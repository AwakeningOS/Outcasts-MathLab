import OutcastsMathLab.Research.ESReduction
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log

/-!
# The Type II witness target, stated on top of the reduction

Outcasts >>39 proposed the target: for each hard prime `p`, a candidate set of shifts `(a, u)`
contains at least one actual Type II witness, i.e. `∑_{(a,u) ∈ C_p} W(p; a, u) > 0` with
`W(p; a, u) = #{s ∣ a p + u : s ≡ -1 (mod 4 a u)}`.  This file fixes that target as Lean
propositions and proves that it implies the Erdős–Straus conjecture through
`es_all_iff_hard_primes`.  **It does not prove the target**; `Hlog` below is an open, stronger
candidate (it fixes the budget `a u ≤ ⌈log₂ p⌉`).

The target is sufficient, not necessary: a prime could have only Type I solutions.
-/

namespace OutcastsMathLab.Research.ESWitnessTarget

open OutcastsMathLab.Research.ESReduction

/-- Number of actual Type II witnesses for the shift `(a, u)`: divisors `s` of `a p + u`
with `4 a u ∣ s + 1` (Dahan, Theorem 3.9(ii)).  Every divisor is counted, with no order bound. -/
def W (p a u : ℕ) : ℕ := ((a * p + u).divisors.filter (fun s => 4 * a * u ∣ s + 1)).card

theorem W_pos_iff {p a u : ℕ} (hM : a * p + u ≠ 0) :
    0 < W p a u ↔ ∃ s, s ∣ a * p + u ∧ 4 * a * u ∣ s + 1 := by
  unfold W
  rw [Finset.card_pos]
  constructor
  · rintro ⟨s, hs⟩
    rw [Finset.mem_filter, Nat.mem_divisors] at hs
    exact ⟨s, hs.1.1, hs.2⟩
  · rintro ⟨s, h1, h2⟩
    exact ⟨s, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨h1, hM⟩, h2⟩⟩

/-- The product budget box `{(a, u) : 1 ≤ a, 1 ≤ u, a u ≤ B}`. -/
def box (B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 B ×ˢ Finset.Icc 1 B).filter (fun au => au.1 * au.2 ≤ B)

theorem mem_box {B a u : ℕ} : (a, u) ∈ box B ↔ 1 ≤ a ∧ 1 ≤ u ∧ a * u ≤ B := by
  unfold box
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, -⟩, hu, -⟩, h⟩
    exact ⟨ha, hu, h⟩
  · rintro ⟨ha, hu, h⟩
    have hab : a ≤ a * u := Nat.le_mul_of_pos_right a hu
    have hub : u ≤ a * u := Nat.le_mul_of_pos_left u ha
    exact ⟨⟨⟨ha, by omega⟩, hu, by omega⟩, h⟩

/-- Total number of Type II witnesses over the budget box. -/
def WSum (p B : ℕ) : ℕ := ∑ au ∈ box B, W p au.1 au.2

theorem WSum_pos_iff {p B : ℕ} : 0 < WSum p B ↔ ∃ au ∈ box B, 0 < W p au.1 au.2 :=
  Finset.sum_pos_iff

theorem es_of_W_pos {p a u : ℕ} (hp : 0 < p) (ha : 0 < a) (hu : 0 < u)
    (h : 0 < W p a u) : ES p := by
  obtain ⟨s, h1, h2⟩ := (W_pos_iff (by positivity)).mp h
  exact es_of_witness hp ha hu h1 h2

theorem es_of_WSum_pos {p B : ℕ} (hp : 0 < p) (h : 0 < WSum p B) : ES p := by
  obtain ⟨⟨a, u⟩, hau, hw⟩ := WSum_pos_iff.mp h
  obtain ⟨ha, hu, -⟩ := mem_box.mp hau
  exact es_of_W_pos hp ha hu hw

/-- A single witness inside the box makes the sum positive. -/
theorem WSum_pos_of_witness {p B a u s : ℕ} (hau : (a, u) ∈ box B)
    (hs : s ∣ a * p + u) (hm : 4 * a * u ∣ s + 1) : 0 < WSum p B := by
  obtain ⟨-, hu, -⟩ := mem_box.mp hau
  refine WSum_pos_iff.mpr ⟨(a, u), hau, (W_pos_iff (by omega)).mpr ⟨s, hs, hm⟩⟩

/-- **Any budget function works.** If every hard prime has a Type II witness in the box of
budget `B p`, the conjecture holds for every `n ≥ 2`. -/
theorem es_all_of_budget (B : ℕ → ℕ)
    (h : ∀ p, p.Prime → p % 840 ∈ hardResidues → 0 < WSum p (B p)) :
    ∀ n, 2 ≤ n → ES n :=
  es_all_iff_hard_primes.mpr fun p hp hh => es_of_WSum_pos hp.pos (h p hp hh)

/-- Unbudgeted form: a Type II witness for every hard prime suffices. -/
theorem es_all_of_typeII
    (h : ∀ p, p.Prime → p % 840 ∈ hardResidues →
      ∃ a u s, 0 < a ∧ 0 < u ∧ s ∣ a * p + u ∧ 4 * a * u ∣ s + 1) :
    ∀ n, 2 ≤ n → ES n :=
  es_all_iff_hard_primes.mpr fun p hp hh => by
    obtain ⟨a, u, s, ha, hu, hs, hm⟩ := h p hp hh
    exact es_of_witness hp.pos ha hu hs hm

/-- `Hlog` (open, stronger than needed): every hard prime has a Type II witness with
`a u ≤ ⌈log₂ p⌉`.  Stated, not proved. -/
def Hlog : Prop :=
  ∀ p, p.Prime → p % 840 ∈ hardResidues → 0 < WSum p (Nat.clog 2 p)

theorem es_all_of_Hlog (h : Hlog) : ∀ n, 2 ≤ n → ES n :=
  es_all_of_budget (fun p => Nat.clog 2 p) h

/-- `2^k < p` gives `k + 1 ≤ ⌈log₂ p⌉`. -/
theorem le_clog_two {p k : ℕ} (h : 2 ^ k < p) : k + 1 ≤ Nat.clog 2 p := by
  by_contra hc
  have hle : Nat.clog 2 p ≤ k := by omega
  rw [Nat.clog_le_iff_le_pow (by norm_num)] at hle
  omega

/-! Sanity checks: the `Hlog` condition holds at P001's 1201 and at the primes discussed in the
thread (smallest product `a u` with a witness; witnesses computed in Python, checked here). -/

theorem hlog_at_1201 : 0 < WSum 1201 (Nat.clog 2 1201) :=
  WSum_pos_of_witness (a := 4) (u := 1) (s := 31)
    (mem_box.mpr ⟨by norm_num, by norm_num, le_trans (by norm_num) (le_clog_two (k := 3) (by norm_num))⟩)
    (by norm_num) (by norm_num)

theorem hlog_at_2521 : 0 < WSum 2521 (Nat.clog 2 2521) :=
  WSum_pos_of_witness (a := 1) (u := 2) (s := 87)
    (mem_box.mpr ⟨by norm_num, by norm_num, le_trans (by norm_num) (le_clog_two (k := 1) (by norm_num))⟩)
    (by norm_num) (by norm_num)

theorem hlog_at_66529 : 0 < WSum 66529 (Nat.clog 2 66529) :=
  WSum_pos_of_witness (a := 1) (u := 5) (s := 39)
    (mem_box.mpr ⟨by norm_num, by norm_num, le_trans (by norm_num) (le_clog_two (k := 4) (by norm_num))⟩)
    (by norm_num) (by norm_num)

theorem hlog_at_345601 : 0 < WSum 345601 (Nat.clog 2 345601) :=
  WSum_pos_of_witness (a := 1) (u := 9) (s := 107)
    (mem_box.mpr ⟨by norm_num, by norm_num, le_trans (by norm_num) (le_clog_two (k := 8) (by norm_num))⟩)
    (by norm_num) (by norm_num)

theorem hlog_at_670849 : 0 < WSum 670849 (Nat.clog 2 670849) :=
  WSum_pos_of_witness (a := 1) (u := 8) (s := 319)
    (mem_box.mpr ⟨by norm_num, by norm_num, le_trans (by norm_num) (le_clog_two (k := 7) (by norm_num))⟩)
    (by norm_num) (by norm_num)

theorem hlog_at_1740481 : 0 < WSum 1740481 (Nat.clog 2 1740481) :=
  WSum_pos_of_witness (a := 3) (u := 4) (s := 3311)
    (mem_box.mpr ⟨by norm_num, by norm_num, le_trans (by norm_num) (le_clog_two (k := 11) (by norm_num))⟩)
    (by norm_num) (by norm_num)

theorem hlog_at_5843041 : 0 < WSum 5843041 (Nat.clog 2 5843041) :=
  WSum_pos_of_witness (a := 1) (u := 5) (s := 7359)
    (mem_box.mpr ⟨by norm_num, by norm_num, le_trans (by norm_num) (le_clog_two (k := 4) (by norm_num))⟩)
    (by norm_num) (by norm_num)

/-! ## Coprime normalisation of the box (Outcasts >>45)

`box B` contains shifts with `gcd a u > 1`, while the earlier finite checks (PR #4, the failure
atlas) used coprime boxes.  The witness *counts* of the two boxes can differ
(`WSumCop_lt_WSum_4201`), but their positivity is the same: a witness `s` for `(a, u)` is coprime
to `g = gcd a u` (because `g ∣ s + 1`), so the same `s` is a witness for `(a / g, u / g)`, whose
product is at most `a u`.  The argument was given in Outcasts >>45; this section checks it in Lean. -/

/-- A Type II witness for `(a, u)` is also a witness for the coprime shift `(a / g, u / g)`,
`g = gcd a u`. -/
theorem witness_div_gcd {p a u s : ℕ} (hs : s ∣ a * p + u) (hm : 4 * a * u ∣ s + 1) :
    s ∣ a / Nat.gcd a u * p + u / Nat.gcd a u ∧
      4 * (a / Nat.gcd a u) * (u / Nat.gcd a u) ∣ s + 1 := by
  have hga : Nat.gcd a u ∣ a := Nat.gcd_dvd_left a u
  have hgu : Nat.gcd a u ∣ u := Nat.gcd_dvd_right a u
  have hg1 : Nat.gcd a u ∣ s + 1 :=
    hga.trans ((Dvd.intro_left 4 rfl).trans ((Dvd.intro u rfl).trans hm))
  have hcop : Nat.Coprime s (Nat.gcd a u) :=
    Nat.dvd_one.mp ((Nat.dvd_add_right (Nat.gcd_dvd_left _ _)).mp
      ((Nat.gcd_dvd_right _ _).trans hg1))
  refine ⟨?_, ?_⟩
  · have heq : a * p + u = (a / Nat.gcd a u * p + u / Nat.gcd a u) * Nat.gcd a u :=
      calc a * p + u
          = a / Nat.gcd a u * Nat.gcd a u * p + u / Nat.gcd a u * Nat.gcd a u := by
            rw [Nat.div_mul_cancel hga, Nat.div_mul_cancel hgu]
        _ = (a / Nat.gcd a u * p + u / Nat.gcd a u) * Nat.gcd a u := by ring
    exact hcop.dvd_of_dvd_mul_right (heq ▸ hs)
  · exact (Nat.mul_dvd_mul (Nat.mul_dvd_mul (dvd_refl 4) (Nat.div_dvd_of_dvd hga))
      (Nat.div_dvd_of_dvd hgu)).trans hm

/-- The coprime part of the product budget box. -/
def coprimeBox (B : ℕ) : Finset (ℕ × ℕ) :=
  (box B).filter (fun au => Nat.Coprime au.1 au.2)

theorem mem_coprimeBox {B a u : ℕ} :
    (a, u) ∈ coprimeBox B ↔ 1 ≤ a ∧ 1 ≤ u ∧ a * u ≤ B ∧ Nat.Coprime a u := by
  unfold coprimeBox
  rw [Finset.mem_filter, mem_box]
  tauto

/-- Total number of Type II witnesses over the coprime box. -/
def WSumCop (p B : ℕ) : ℕ := ∑ au ∈ coprimeBox B, W p au.1 au.2

/-- The full box splits into its coprime and non-coprime parts. -/
theorem WSum_eq_WSumCop_add (p B : ℕ) :
    WSum p B = WSumCop p B +
      ∑ au ∈ (box B).filter (fun au => ¬ Nat.Coprime au.1 au.2), W p au.1 au.2 :=
  (Finset.sum_filter_add_sum_filter_not (box B) _ _).symm

theorem WSumCop_le_WSum (p B : ℕ) : WSumCop p B ≤ WSum p B := by
  rw [WSum_eq_WSumCop_add p B]
  exact Nat.le_add_right _ _

/-- **Positivity does not depend on the box convention.** -/
theorem WSum_pos_iff_WSumCop_pos {p B : ℕ} : 0 < WSum p B ↔ 0 < WSumCop p B := by
  constructor
  · intro h
    obtain ⟨⟨a, u⟩, hau, hw⟩ := WSum_pos_iff.mp h
    obtain ⟨ha, hu, hB⟩ := mem_box.mp hau
    obtain ⟨s, hs, hm⟩ := (W_pos_iff (by omega)).mp hw
    obtain ⟨hs', hm'⟩ := witness_div_gcd hs hm
    have hg : 0 < Nat.gcd a u := Nat.gcd_pos_of_pos_left u ha
    have ha0 : 1 ≤ a / Nat.gcd a u := Nat.div_pos (Nat.gcd_le_left u ha) hg
    have hu0 : 1 ≤ u / Nat.gcd a u := Nat.div_pos (Nat.gcd_le_right (m := a) hu) hg
    have hle : a / Nat.gcd a u * (u / Nat.gcd a u) ≤ B :=
      le_trans (Nat.mul_le_mul (Nat.div_le_self a _) (Nat.div_le_self u _)) hB
    exact Finset.sum_pos_iff.mpr ⟨(a / Nat.gcd a u, u / Nat.gcd a u),
      mem_coprimeBox.mpr ⟨ha0, hu0, hle, Nat.coprime_div_gcd_div_gcd hg⟩,
      (W_pos_iff (by omega)).mpr ⟨s, hs', hm'⟩⟩
  · intro h
    exact lt_of_lt_of_le h (WSumCop_le_WSum p B)

/-- The budget theorem with the coprime box (same strength as `es_all_of_budget`). -/
theorem es_all_of_budget_coprime (B : ℕ → ℕ)
    (h : ∀ p, p.Prime → p % 840 ∈ hardResidues → 0 < WSumCop p (B p)) :
    ∀ n, 2 ≤ n → ES n :=
  es_all_of_budget B fun p hp hh => WSum_pos_iff_WSumCop_pos.mpr (h p hp hh)

/-- The counts can differ: at `p = 4201` (`≡ 1 mod 840`, budget `⌈log₂ p⌉ = 13`) the
non-coprime shift `(2, 2)` has the witness `s = 191` (`8404 = 191 · 44`, `16 ∣ 192`), which the
coprime box does not count.  Witness found in Python, checked here. -/
theorem WSumCop_lt_WSum_4201 : WSumCop 4201 13 < WSum 4201 13 := by
  rw [WSum_eq_WSumCop_add]
  refine Nat.lt_add_of_pos_right (Finset.sum_pos_iff.mpr ⟨(2, 2), ?_, ?_⟩)
  · exact Finset.mem_filter.mpr ⟨mem_box.mpr ⟨by norm_num, by norm_num, by norm_num⟩, by decide⟩
  · exact (W_pos_iff (by norm_num)).mpr ⟨191, by norm_num, by norm_num⟩

theorem clog_two_4201 : Nat.clog 2 4201 = 13 := by
  refine le_antisymm ((Nat.clog_le_iff_le_pow (by norm_num)).mpr (by norm_num)) ?_
  exact le_clog_two (k := 12) (by norm_num)

#print axioms W_pos_iff
#print axioms mem_box
#print axioms WSum_pos_iff
#print axioms es_of_W_pos
#print axioms es_of_WSum_pos
#print axioms WSum_pos_of_witness
#print axioms es_all_of_budget
#print axioms es_all_of_typeII
#print axioms es_all_of_Hlog
#print axioms le_clog_two
#print axioms hlog_at_1201
#print axioms hlog_at_2521
#print axioms hlog_at_66529
#print axioms hlog_at_345601
#print axioms hlog_at_670849
#print axioms hlog_at_1740481
#print axioms hlog_at_5843041
#print axioms witness_div_gcd
#print axioms mem_coprimeBox
#print axioms WSum_eq_WSumCop_add
#print axioms WSumCop_le_WSum
#print axioms WSum_pos_iff_WSumCop_pos
#print axioms es_all_of_budget_coprime
#print axioms WSumCop_lt_WSum_4201
#print axioms clog_two_4201

end OutcastsMathLab.Research.ESWitnessTarget
