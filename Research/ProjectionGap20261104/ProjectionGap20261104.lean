import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum.Prime

/-! A concrete failure of combining separate actual-divisor hits mod3 and mod73.
Divisor coverage reuses betyourluck PR6 fc6ed0305974e2501721aefd73186907ed45d7f6,
DeterministicFailure.lean, via our GraphDepth20261027.lean. This helper is known.
New target is the fixed p1548961 parent/child example, not universal ESC.
The Legendre-symbol and least-root checks are in the independent Python audit;
they are not claimed as declarations of this file. No native_decide or sorry.
-/
namespace ProjectionGap20261104
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def prodPow (L : List (ℕ × ℕ)) : ℕ := (L.map fun qe => qe.1 ^ qe.2).prod
def subProducts : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (q,e)::L => (subProducts L).flatMap fun d => (List.range (e+1)).map fun f => d*q^f

theorem prodPow_cons (q e : ℕ) (L : List (ℕ × ℕ)) :
    prodPow ((q,e)::L) = q^e * prodPow L := by simp [prodPow]

theorem dvd_mul_split {s m n : ℕ} (h : s ∣ m*n) :
    ∃ y z, y ∣ m ∧ z ∣ n ∧ s=y*z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨s,1,dvd_zero s,one_dvd n,(mul_one s).symm⟩
  · obtain ⟨z,hz⟩ := Nat.gcd_dvd_left s m
    obtain ⟨m',hm'⟩ := Nat.gcd_dvd_right s m
    have hy : 0 < Nat.gcd s m := Nat.gcd_pos_of_pos_right s hm
    refine ⟨Nat.gcd s m,z,Nat.gcd_dvd_right s m,?_,hz⟩
    have h1 : Nat.gcd s m*z ∣ Nat.gcd s m*(m'*n) := by
      rw [← hz, ← mul_assoc, ← hm']
      exact h
    have h2 : z ∣ m'*n := Nat.dvd_of_mul_dvd_mul_left hy h1
    have h3 : Nat.Coprime z m' := by
      have := Nat.gcd_mul_left (Nat.gcd s m) z m'
      rw [← hz, ← hm'] at this
      exact Nat.eq_of_mul_eq_mul_left hy (by rw [mul_one]; exact this.symm)
    exact (Nat.Coprime.dvd_mul_left h3).mp h2

theorem mem_subProducts_of_dvd :
    ∀ (L : List (ℕ × ℕ)), (∀ qe ∈ L, Nat.Prime qe.1) →
      ∀ s, s ∣ prodPow L → s ∈ subProducts L
  | [],_,s,hs => by
      have h : s ∣ 1 := hs
      simp [subProducts,Nat.dvd_one.mp h]
  | (q,e)::L,hL,s,hs => by
      rw [prodPow_cons] at hs
      obtain ⟨y,z,hy,hz,rfl⟩ := dvd_mul_split hs
      have hq : Nat.Prime q := hL (q,e) (by simp)
      obtain ⟨f,hf,rfl⟩ := (Nat.dvd_prime_pow hq).mp hy
      have hz' := mem_subProducts_of_dvd L (fun qe h => hL qe (by simp [h])) z hz
      simp only [subProducts,List.mem_flatMap,List.mem_map,List.mem_range]
      exact ⟨z,hz',f,Nat.lt_succ_of_le hf,mul_comm _ _⟩

def noResidueCert (L : List (ℕ × ℕ)) (c t : ℕ) : Bool :=
  (subProducts L).all fun d => (d+t)%c != 0
theorem no_residue_of_cert {L : List (ℕ × ℕ)}
    (hL : ∀ qe ∈ L, Nat.Prime qe.1) {c t : ℕ}
    (hc : noResidueCert L c t = true) :
    ∀ d, d ∣ prodPow L → ¬ c ∣ d+t := by
  intro d hd hbad
  have hmem := mem_subProducts_of_dvd L hL d hd
  have h := List.all_eq_true.mp hc d hmem
  rw [Nat.mod_eq_zero_of_dvd hbad] at h
  simp at h

theorem parent_failure : ∀ d : ℕ, d ∣ 387265^2 →
    ¬ 99 ∣ d+387265 ∧ ¬ 99 ∣ d+1548961*387265 := by
  intro d hd
  have hL : ∀ qe ∈ ([(5,2),(73,2),(1061,2)] : List (ℕ × ℕ)), Nat.Prime qe.1 := by norm_num
  have hf : (387265:ℕ)^2 = prodPow [(5,2),(73,2),(1061,2)] := by norm_num [prodPow]
  rw [hf] at hd
  exact ⟨no_residue_of_cert hL (by decide) d hd, no_residue_of_cert hL (by decide) d hd⟩

theorem child_failure : ∀ d : ℕ, d ∣ 387295^2 →
    ¬ 219 ∣ d+387295 ∧ ¬ 219 ∣ d+1548961*387295 := by
  intro d hd
  have hL : ∀ qe ∈ ([(5,2),(29,2),(2671,2)] : List (ℕ × ℕ)), Nat.Prime qe.1 := by norm_num
  have hf : (387295:ℕ)^2 = prodPow [(5,2),(29,2),(2671,2)] := by norm_num [prodPow]
  rw [hf] at hd
  exact ⟨no_residue_of_cert hL (by decide) d hd, no_residue_of_cert hL (by decide) d hd⟩

theorem separate_occupancy :
    (∃ d : ℕ, d ∣ 387295^2 ∧ 73 ∣ d+387295) ∧
    (∃ d : ℕ, d ∣ 387295^2 ∧ 3 ∣ d+387295) := by
  exact ⟨⟨2671,by norm_num,by norm_num⟩,⟨5,by norm_num,by norm_num⟩⟩

theorem no_simultaneous_divisor : ¬ ∃ d : ℕ, d ∣ 387295^2 ∧ 219 ∣ d+387295 := by
  rintro ⟨d,hd,hc⟩
  exact (child_failure d hd).1 hc

theorem prime_and_edge_data :
    Nat.Prime 1548961 ∧ Nat.Prime 11 ∧ Nat.Prime 73 ∧
    1548961 % 840 = (1:ℕ) ∧
    4*387265 = (1548961:ℕ)+11*3^2 ∧
    73 ∣ (387265:ℕ) ∧
    4*387295 = (1548961:ℕ)+3*73 ∧
    ¬ 73 ∣ (387295:ℕ) ∧ 99 < 3*(1548961:ℕ) ∧ 219 < 3*(1548961:ℕ) := by
  norm_num

#print axioms parent_failure
#print axioms child_failure
#print axioms separate_occupancy
#print axioms no_simultaneous_divisor
#print axioms prime_and_edge_data
end ProjectionGap20261104
