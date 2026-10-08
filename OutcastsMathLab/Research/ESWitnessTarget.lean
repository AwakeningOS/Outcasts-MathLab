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

end OutcastsMathLab.Research.ESWitnessTarget
