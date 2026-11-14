import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Finite falsification component for the sufficient-bound-only child route.
Generic factor coverage below is reused from PR6, commit
fc6ed0305974e2501721aefd73186907ed45d7f6,
OutcastsMathLab/Research/DeterministicFailure.lean (betyourluck).
This standalone module has no import dependency on that research branch.
We prove full allowed-source failure for q=11,17,19 at p=2521.
The classification of all eligible child primes is checked by the accompanying
Python audit, not formalized here. No universal ESC or E1 claim is proved.
-/
namespace ShortRoot20261025
/-- `∏ qᵢ^{eᵢ}` for a list of `(qᵢ, eᵢ)`. -/
def prodPow (L : List (ℕ × ℕ)) : ℕ := (L.map fun qe => qe.1 ^ qe.2).prod

/-- All sub-products `∏ qᵢ^{fᵢ}` with `fᵢ ≤ eᵢ`. -/
def subProducts : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (q, e) :: L => (subProducts L).flatMap fun d => (List.range (e + 1)).map fun f => d * q ^ f

/-- The certificate check: no sub-product `d` has `m ∣ d + 1`. -/
def noWitnessCert (L : List (ℕ × ℕ)) (m : ℕ) : Bool :=
  (subProducts L).all fun d => (d + 1) % m != 0

theorem prodPow_nil : prodPow [] = 1 := rfl

theorem prodPow_cons (q e : ℕ) (L : List (ℕ × ℕ)) :
    prodPow ((q, e) :: L) = q ^ e * prodPow L := by
  simp [prodPow]

/-- Splitting a divisor of a product in `ℕ`: `s ∣ m n → s = y z` with `y ∣ m`, `z ∣ n`. -/
theorem dvd_mul_split {s m n : ℕ} (h : s ∣ m * n) : ∃ y z, y ∣ m ∧ z ∣ n ∧ s = y * z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨s, 1, dvd_zero s, one_dvd n, (mul_one s).symm⟩
  · obtain ⟨z, hz⟩ := Nat.gcd_dvd_left s m
    obtain ⟨m', hm'⟩ := Nat.gcd_dvd_right s m
    have hy : 0 < Nat.gcd s m := Nat.gcd_pos_of_pos_right s hm
    refine ⟨Nat.gcd s m, z, Nat.gcd_dvd_right s m, ?_, hz⟩
    have h1 : Nat.gcd s m * z ∣ Nat.gcd s m * (m' * n) := by
      rw [← hz, ← mul_assoc, ← hm']
      exact h
    have h2 : z ∣ m' * n := Nat.dvd_of_mul_dvd_mul_left hy h1
    have h3 : Nat.Coprime z m' := by
      have := Nat.gcd_mul_left (Nat.gcd s m) z m'
      rw [← hz, ← hm'] at this
      exact Nat.eq_of_mul_eq_mul_left hy (by rw [mul_one]; exact this.symm)
    exact (Nat.Coprime.dvd_mul_left h3).mp h2

/-- Every divisor of `∏ qᵢ^{eᵢ}` (all `qᵢ` prime) is one of the sub-products. -/
theorem mem_subProducts_of_dvd :
    ∀ (L : List (ℕ × ℕ)), (∀ qe ∈ L, Nat.Prime qe.1) →
      ∀ s, s ∣ prodPow L → s ∈ subProducts L
  | [], _, s, hs => by
      rw [prodPow_nil] at hs
      simp [subProducts, Nat.dvd_one.mp hs]
  | (q, e) :: L, hL, s, hs => by
      rw [prodPow_cons] at hs
      obtain ⟨y, z, hy, hz, rfl⟩ := dvd_mul_split hs
      have hq : Nat.Prime q := hL (q, e) (by simp)
      obtain ⟨f, hf, rfl⟩ := (Nat.dvd_prime_pow hq).mp hy
      have hz' := mem_subProducts_of_dvd L (fun qe h => hL qe (by simp [h])) z hz
      simp only [subProducts, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨z, hz', f, Nat.lt_succ_of_le hf, mul_comm _ _⟩


def noResidueCert (L : List (ℕ × ℕ)) (c t : ℕ) : Bool :=
  (subProducts L).all fun d => (d + t) % c != 0

theorem no_residue_of_cert {L : List (ℕ × ℕ)}
    (hL : ∀ qe ∈ L, Nat.Prime qe.1) {c t : ℕ}
    (hc : noResidueCert L c t = true) :
    ∀ d, d ∣ prodPow L → ¬ c ∣ d + t := by
  intro d hd hbad
  have hmem := mem_subProducts_of_dvd L hL d hd
  have h := List.all_eq_true.mp hc d hmem
  rw [Nat.mod_eq_zero_of_dvd hbad] at h
  simp at h

def SourceFails (p A t : ℕ) : Prop :=
  ∀ d, d ∣ ((p + A*t^2)/4)^2 →
    ¬ A*t^2 ∣ d + (p + A*t^2)/4 ∧
    ¬ A*t^2 ∣ d + p*((p + A*t^2)/4)

theorem source_fails_of_cert {p A t : ℕ} {L : List (ℕ × ℕ)}
    (hL : ∀ qe ∈ L, Nat.Prime qe.1)
    (hf : ((p + A*t^2)/4)^2 = prodPow L)
    (hII : noResidueCert L (A*t^2) ((p+A*t^2)/4) = true)
    (hI : noResidueCert L (A*t^2) (p*((p+A*t^2)/4)) = true) :
    SourceFails p A t := by
  intro d hd
  rw [hf] at hd
  exact ⟨no_residue_of_cert hL hII d hd, no_residue_of_cert hL hI d hd⟩

theorem fails_11_1 : SourceFails 2521 11 1 := by
  apply source_fails_of_cert (L := [(3, 2), (211, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_3 : SourceFails 2521 11 3 := by
  apply source_fails_of_cert (L := [(5, 2), (131, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_5 : SourceFails 2521 11 5 := by
  apply source_fails_of_cert (L := [(3, 2), (233, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_7 : SourceFails 2521 11 7 := by
  apply source_fails_of_cert (L := [(3, 4), (5, 2), (17, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_9 : SourceFails 2521 11 9 := by
  apply source_fails_of_cert (L := [(853, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_11 : SourceFails 2521 11 11 := by
  apply source_fails_of_cert (L := [(3, 4), (107, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_13 : SourceFails 2521 11 13 := by
  apply source_fails_of_cert (L := [(3, 2), (5, 2), (73, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_15 : SourceFails 2521 11 15 := by
  apply source_fails_of_cert (L := [(1249, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_17 : SourceFails 2521 11 17 := by
  apply source_fails_of_cert (L := [(3, 2), (5, 4), (19, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_19 : SourceFails 2521 11 19 := by
  apply source_fails_of_cert (L := [(3, 2), (541, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_21 : SourceFails 2521 11 21 := by
  apply source_fails_of_cert (L := [(19, 2), (97, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_23 : SourceFails 2521 11 23 := by
  apply source_fails_of_cert (L := [(3, 2), (5, 2), (139, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_11_25 : SourceFails 2521 11 25 := by
  apply source_fails_of_cert (L := [(3, 8), (29, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_11 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 11*t^2 < 3*2521) : SourceFails 2521 11 t := by
  have hbound : t ≤ 26 := by
    by_contra h
    have hlarge : 27 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fails_11_1
  · exact fails_11_3
  · exact fails_11_5
  · exact fails_11_7
  · exact fails_11_9
  · exact fails_11_11
  · exact fails_11_13
  · exact fails_11_15
  · exact fails_11_17
  · exact fails_11_19
  · exact fails_11_21
  · exact fails_11_23
  · exact fails_11_25

theorem fails_17_1 : SourceFails 2521 51 1 := by
  apply source_fails_of_cert (L := [(643, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_17_3 : SourceFails 2521 51 3 := by
  apply source_fails_of_cert (L := [(5, 2), (149, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_17_5 : SourceFails 2521 51 5 := by
  apply source_fails_of_cert (L := [(13, 2), (73, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_17_7 : SourceFails 2521 51 7 := by
  apply source_fails_of_cert (L := [(5, 2), (251, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_17_9 : SourceFails 2521 51 9 := by
  apply source_fails_of_cert (L := [(1663, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_17_11 : SourceFails 2521 51 11 := by
  apply source_fails_of_cert (L := [(41, 2), (53, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_17 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 51*t^2 < 3*2521) : SourceFails 2521 51 t := by
  have hbound : t ≤ 12 := by
    by_contra h
    have hlarge : 13 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3, 5, 7, 9, 11] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fails_17_1
  · exact fails_17_3
  · exact fails_17_5
  · exact fails_17_7
  · exact fails_17_9
  · exact fails_17_11

theorem fails_19_1 : SourceFails 2521 19 1 := by
  apply source_fails_of_cert (L := [(5, 2), (127, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_3 : SourceFails 2521 19 3 := by
  apply source_fails_of_cert (L := [(673, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_5 : SourceFails 2521 19 5 := by
  apply source_fails_of_cert (L := [(7, 2), (107, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_7 : SourceFails 2521 19 7 := by
  apply source_fails_of_cert (L := [(863, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_9 : SourceFails 2521 19 9 := by
  apply source_fails_of_cert (L := [(5, 2), (7, 2), (29, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_11 : SourceFails 2521 19 11 := by
  apply source_fails_of_cert (L := [(5, 2), (241, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_13 : SourceFails 2521 19 13 := by
  apply source_fails_of_cert (L := [(1433, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_15 : SourceFails 2521 19 15 := by
  apply source_fails_of_cert (L := [(1699, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_17 : SourceFails 2521 19 17 := by
  apply source_fails_of_cert (L := [(2003, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_19_19 : SourceFails 2521 19 19 := by
  apply source_fails_of_cert (L := [(5, 2), (7, 2), (67, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_19 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 19*t^2 < 3*2521) : SourceFails 2521 19 t := by
  have hbound : t ≤ 19 := by
    by_contra h
    have hlarge : 20 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3, 5, 7, 9, 11, 13, 15, 17, 19] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fails_19_1
  · exact fails_19_3
  · exact fails_19_5
  · exact fails_19_7
  · exact fails_19_9
  · exact fails_19_11
  · exact fails_19_13
  · exact fails_19_15
  · exact fails_19_17
  · exact fails_19_19

theorem child_29_actual_root_outside_bound :
    (2521 + 11*25^2)/4 = 2349 ∧ 29 ∣ (2349 : ℕ) ∧
    11*25^2 < 3*2521 ∧ ¬ 11*(29-2)^2 < (3*2521 : ℕ) := by norm_num

theorem child_29_type_I_certificate :
    1304 ∣ (652 : ℕ)^2 ∧ 87 ∣ (1304 + 2521*652 : ℕ) ∧
    4*652*18908*23833534 = (2521 : ℕ)*(652*18908 + 652*23833534 + 18908*23833534) := by norm_num

#print axioms no_residue_of_cert
#print axioms source_fails_of_cert
#print axioms all_allowed_fail_11
#print axioms all_allowed_fail_17
#print axioms all_allowed_fail_19
#print axioms child_29_actual_root_outside_bound
#print axioms child_29_type_I_certificate
end ShortRoot20261025
