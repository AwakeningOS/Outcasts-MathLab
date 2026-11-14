import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Exact finite counterexample to the all-vertex one-edge rescue candidate.
Generic divisor coverage reuses betyourluck PR6 fc6ed0305974e2501721aefd73186907ed45d7f6,
DeterministicFailure.lean, via our ShortRoot20261025.lean. Not new mathematics.
Proves all allowed-source failure at q=17 and all six outgoing vertices,
exhaustiveness of q=17's children, and an actual two-edge successful path.
Does not formalize the complete 187-vertex distance table or universal ESC.
-/
namespace GraphDepth20261027
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
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

theorem fails_53_1 : SourceFails 2521 159 1 := by
  apply source_fails_of_cert (L := [(2, 2), (5, 2), (67, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_53_3 : SourceFails 2521 159 3 := by
  apply source_fails_of_cert (L := [(2, 4), (13, 2), (19, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_53_5 : SourceFails 2521 159 5 := by
  apply source_fails_of_cert (L := [(2, 6), (7, 2), (29, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_53 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 159*t^2 < 3*2521) : SourceFails 2521 159 t := by
  have hbound : t ≤ 6 := by
    by_contra h
    have hlarge : 7 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3, 5] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact fails_53_1
  · exact fails_53_3
  · exact fails_53_5

theorem fails_73_1 : SourceFails 2521 219 1 := by
  apply source_fails_of_cert (L := [(5, 2), (137, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_73_3 : SourceFails 2521 219 3 := by
  apply source_fails_of_cert (L := [(1123, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_73_5 : SourceFails 2521 219 5 := by
  apply source_fails_of_cert (L := [(1999, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_73 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 219*t^2 < 3*2521) : SourceFails 2521 219 t := by
  have hbound : t ≤ 5 := by
    by_contra h
    have hlarge : 6 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3, 5] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact fails_73_1
  · exact fails_73_3
  · exact fails_73_5

theorem fails_149_1 : SourceFails 2521 447 1 := by
  apply source_fails_of_cert (L := [(2, 2), (7, 2), (53, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_149_3 : SourceFails 2521 447 3 := by
  apply source_fails_of_cert (L := [(2, 4), (409, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_149 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 447*t^2 < 3*2521) : SourceFails 2521 447 t := by
  have hbound : t ≤ 4 := by
    by_contra h
    have hlarge : 5 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact fails_149_1
  · exact fails_149_3

theorem fails_251_1 : SourceFails 2521 251 1 := by
  apply source_fails_of_cert (L := [(3, 4), (7, 2), (11, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_251_3 : SourceFails 2521 251 3 := by
  apply source_fails_of_cert (L := [(5, 2), (239, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_251_5 : SourceFails 2521 251 5 := by
  apply source_fails_of_cert (L := [(3, 2), (733, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_251 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 251*t^2 < 3*2521) : SourceFails 2521 251 t := by
  have hbound : t ≤ 5 := by
    by_contra h
    have hlarge : 6 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3, 5] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl
  · exact fails_251_1
  · exact fails_251_3
  · exact fails_251_5

theorem fails_643_1 : SourceFails 2521 643 1 := by
  apply source_fails_of_cert (L := [(7, 2), (113, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem fails_643_3 : SourceFails 2521 643 3 := by
  apply source_fails_of_cert (L := [(31, 2), (67, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_643 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 643*t^2 < 3*2521) : SourceFails 2521 643 t := by
  have hbound : t ≤ 3 := by
    by_contra h
    have hlarge : 4 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1, 3] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact fails_643_1
  · exact fails_643_3

theorem fails_1663_1 : SourceFails 2521 1663 1 := by
  apply source_fails_of_cert (L := [(2, 2), (523, 2)])
  · norm_num
  · norm_num [prodPow]
  · decide
  · decide

theorem all_allowed_fail_1663 (t : ℕ) (hpos : 0 < t) (hodd : Odd t)
    (hsize : 1663*t^2 < 3*2521) : SourceFails 2521 1663 t := by
  have hbound : t ≤ 2 := by
    by_contra h
    have hlarge : 3 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl
  · exact fails_1663_1

def sigma (q : ℕ) : ℕ := if q % 4 = 3 then 1 else 3
def Allowed (p q t : ℕ) : Prop := 0 < t ∧ Odd t ∧ sigma q*q*t^2 < 3*p
def Edge (p q r : ℕ) : Prop :=
  ∃ t, Allowed p q t ∧ Nat.Prime r ∧ r < p ∧
    r ^ ((p-1)/2) % p = p-1 ∧ r ∣ (p + sigma q*q*t^2)/4
def VertexFails (p q : ℕ) : Prop :=
  ∀ t, Allowed p q t → SourceFails p (sigma q*q) t

theorem q17_all_children (r : ℕ) (h : Edge 2521 17 r) :
    r ∈ ([53,73,149,251,643,1663] : List ℕ) := by
  obtain ⟨t, ⟨hpos, hodd, hsize⟩, hr, _, hnr, hd⟩ := h
  norm_num [sigma] at hsize hd
  have hbound : t ≤ 12 := by
    by_contra h
    have hlarge : 13 ≤ t := by omega
    have hp := Nat.pow_le_pow_left hlarge 2
    norm_num at hp
    omega
  obtain ⟨k, hk⟩ := hodd
  have ht : t ∈ ([1,3,5,7,9,11] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · have hf : r ∣ prodPow [(643, 1)] := by norm_num [prodPow] at hd ⊢; exact hd
    have hm := mem_subProducts_of_dvd [(643, 1)] (by norm_num) r hf
    change r ∈ ([1, 643] : List ℕ) at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · norm_num at hr
    · norm_num
  · have hf : r ∣ prodPow [(5, 1), (149, 1)] := by norm_num [prodPow] at hd ⊢; exact hd
    have hm := mem_subProducts_of_dvd [(5, 1), (149, 1)] (by norm_num) r hf
    change r ∈ ([1, 5, 149, 745] : List ℕ) at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · norm_num at hr
    · norm_num at hnr
    · norm_num
    · norm_num at hr
  · have hf : r ∣ prodPow [(13, 1), (73, 1)] := by norm_num [prodPow] at hd ⊢; exact hd
    have hm := mem_subProducts_of_dvd [(13, 1), (73, 1)] (by norm_num) r hf
    change r ∈ ([1, 13, 73, 949] : List ℕ) at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · norm_num at hr
    · norm_num at hnr
    · norm_num
    · norm_num at hr
  · have hf : r ∣ prodPow [(5, 1), (251, 1)] := by norm_num [prodPow] at hd ⊢; exact hd
    have hm := mem_subProducts_of_dvd [(5, 1), (251, 1)] (by norm_num) r hf
    change r ∈ ([1, 5, 251, 1255] : List ℕ) at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · norm_num at hr
    · norm_num at hnr
    · norm_num
    · norm_num at hr
  · have hf : r ∣ prodPow [(1663, 1)] := by norm_num [prodPow] at hd ⊢; exact hd
    have hm := mem_subProducts_of_dvd [(1663, 1)] (by norm_num) r hf
    change r ∈ ([1, 1663] : List ℕ) at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · norm_num at hr
    · norm_num
  · have hf : r ∣ prodPow [(41, 1), (53, 1)] := by norm_num [prodPow] at hd ⊢; exact hd
    have hm := mem_subProducts_of_dvd [(41, 1), (53, 1)] (by norm_num) r hf
    change r ∈ ([1, 41, 53, 2173] : List ℕ) at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · norm_num at hr
    · norm_num at hnr
    · norm_num
    · norm_num at hr

theorem q17_and_every_child_fail :
    VertexFails 2521 17 ∧ ∀ r, Edge 2521 17 r → VertexFails 2521 r := by
  constructor
  · intro t ht
    simp only [Allowed, sigma] at ht
    norm_num at ht
    exact all_allowed_fail_17 t ht.1 ht.2.1 ht.2.2
  · intro r hr t ht
    have hm := q17_all_children r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Allowed, sigma] at ht
      norm_num at ht
      exact all_allowed_fail_53 t ht.1 ht.2.1 ht.2.2
    · simp only [Allowed, sigma] at ht
      norm_num at ht
      exact all_allowed_fail_73 t ht.1 ht.2.1 ht.2.2
    · simp only [Allowed, sigma] at ht
      norm_num at ht
      exact all_allowed_fail_149 t ht.1 ht.2.1 ht.2.2
    · simp only [Allowed, sigma] at ht
      norm_num at ht
      exact all_allowed_fail_251 t ht.1 ht.2.1 ht.2.2
    · simp only [Allowed, sigma] at ht
      norm_num at ht
      exact all_allowed_fail_643 t ht.1 ht.2.1 ht.2.2
    · simp only [Allowed, sigma] at ht
      norm_num at ht
      exact all_allowed_fail_1663 t ht.1 ht.2.1 ht.2.2

theorem p2521_prime_q17_nonresidue :
    Nat.Prime 2521 ∧ Nat.Prime 17 ∧ 17 < (2521 : ℕ) ∧
    17^1260 % 2521 = (2520 : ℕ) ∧ 2521 % 840 = (1 : ℕ) := by decide

theorem two_edge_path : Edge 2521 17 53 ∧ Edge 2521 53 29 := by
  constructor
  · refine ⟨11, ?_⟩
    simp only [Allowed]
    decide
  · refine ⟨5, ?_⟩
    simp only [Allowed]
    decide

theorem q29_success :
    Allowed 2521 29 1 ∧ ¬ SourceFails 2521 (sigma 29*29) 1 := by
  constructor
  · norm_num [Allowed, sigma]
  · intro h
    have hf := h 1304 (by norm_num [sigma])
    norm_num [sigma] at hf

theorem terminal_integer_identity :
    4*652*18908*23833534 = (2521 : ℕ)*(652*18908 + 652*23833534 + 18908*23833534) := by norm_num

#print axioms q17_all_children
#print axioms q17_and_every_child_fail
#print axioms p2521_prime_q17_nonresidue
#print axioms two_edge_path
#print axioms q29_success
#print axioms terminal_integer_identity
end GraphDepth20261027
