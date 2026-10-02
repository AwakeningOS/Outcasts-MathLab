import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum.Prime
import OutcastsMathLab.Problems.P001_ErdosStraus1201.PrimeCoprimality
import OutcastsMathLab.Problems.P001_ErdosStraus1201.PrimeDivisorBranches

namespace OutcastsPrimeBranchBridge

open OutcastsPrimeDivisorBranches

-- In the prime range p < 4x, Nat subtraction 4*x-p is not truncated.
theorem shift_cast (p x : Nat) (hlo : p < 4 * x) :
    ((4 * x - p : Nat) : Int) = 4 * (x : Int) - (p : Int) := by
  omega

-- Nat coprimality of the shift with p, taken from the Int-level theorem.
theorem shift_coprime (p x : Nat) (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hlo : p < 4 * x) (hhi : 4 * x ≤ 3 * p) :
    Nat.Coprime (4 * x - p) p := by
  have hx : 0 < x := by omega
  have hxp : x < p := by omega
  have h := OutcastsPrimeCoprimality.odd_prime_coprimality p x hp hodd hx hxp
  rw [← shift_cast p x hlo, ← Int.natCast_mul, Int.gcd_natCast_natCast] at h
  exact Nat.Coprime.coprime_dvd_right (Nat.dvd_mul_right p x) h

-- The two-branch equivalence with c = 4*x-p; no coprimality hypothesis remains.
theorem prime_factor_witness_iff_branches (p x a : Nat)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hlo : p < 4 * x) (hhi : 4 * x ≤ 3 * p) :
    FactorWitness p x (4 * x - p) a ↔
      BranchI p x (4 * x - p) a ∨
        ∃ t, a = p * t ∧ BranchII p x (4 * x - p) t :=
  factor_witness_iff_branches p x (4 * x - p) a hp (by omega)
    (shift_coprime p x hp hodd hlo hhi)

-- A Nat factor witness yields the Int reconstruction of PrimeCoprimality.
-- The complementary factor b is the exact Nat quotient (px)^2 / a.
theorem factor_witness_reconstruction (p x a : Nat)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hlo : p < 4 * x) (hhi : 4 * x ≤ 3 * p)
    (hw : FactorWitness p x (4 * x - p) a) :
    let b : Int := (((p * x) * (p * x) / a : Nat) : Int)
    let y := ((a : Int) + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    let z := (b + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    0 < (x : Int) ∧ (x : Int) ≤ y ∧ y ≤ z ∧
      4 * (x : Int) * y * z =
        (p : Int) * ((x : Int) * y + (x : Int) * z + y * z) := by
  obtain ⟨ha, haM, hd, hcong, hbound⟩ := hw
  have hc := shift_cast p x hlo
  have hab : (a : Int) * (((p * x) * (p * x) / a : Nat) : Int) =
      ((p : Int) * (x : Int)) * ((p : Int) * (x : Int)) := by
    exact_mod_cast Nat.mul_div_cancel' hd
  have hda : (4 * (x : Int) - (p : Int)) ∣ (a : Int) + (p : Int) * (x : Int) := by
    rw [← hc]
    exact_mod_cast hcong
  have hlower : (4 * (x : Int) - (p : Int)) * (x : Int) -
      (p : Int) * (x : Int) ≤ (a : Int) := by
    have h : (((4 * x - p : Nat) : Int)) * (x : Int) ≤ (a : Int) + (p : Int) * (x : Int) := by
      exact_mod_cast hbound
    rw [hc] at h
    omega
  exact OutcastsPrimeCoprimality.odd_prime_reconstruction p x (a : Int) _
    hp hodd hlo hhi (by exact_mod_cast ha) (by exact_mod_cast haM) hab hda hlower

-- Branch I: the factor is t itself.
theorem branchI_reconstruction (p x t : Nat)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hlo : p < 4 * x) (hhi : 4 * x ≤ 3 * p)
    (h : BranchI p x (4 * x - p) t) :
    let b : Int := (((p * x) * (p * x) / t : Nat) : Int)
    let y := ((t : Int) + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    let z := (b + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    0 < (x : Int) ∧ (x : Int) ≤ y ∧ y ≤ z ∧
      4 * (x : Int) * y * z =
        (p : Int) * ((x : Int) * y + (x : Int) * z + y * z) :=
  factor_witness_reconstruction p x t hp hodd hlo hhi
    ((prime_factor_witness_iff_branches p x t hp hodd hlo hhi).mpr (Or.inl h))

-- Branch II: the factor is p*t.
theorem branchII_reconstruction (p x t : Nat)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hlo : p < 4 * x) (hhi : 4 * x ≤ 3 * p)
    (h : BranchII p x (4 * x - p) t) :
    let b : Int := (((p * x) * (p * x) / (p * t) : Nat) : Int)
    let y := (((p * t : Nat) : Int) + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    let z := (b + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    0 < (x : Int) ∧ (x : Int) ≤ y ∧ y ≤ z ∧
      4 * (x : Int) * y * z =
        (p : Int) * ((x : Int) * y + (x : Int) * z + y * z) :=
  factor_witness_reconstruction p x (p * t) hp hodd hlo hhi
    ((prime_factor_witness_iff_branches p x (p * t) hp hodd hlo hhi).mpr
      (Or.inr ⟨t, rfl, h⟩))

-- Non-vacuity: the known solution 4/1201 = 1/306 + 1/21618 + 1/61251
-- is Branch II with t = 108 (a = 1201*108), and the bridge reproduces it.
theorem example_1201_branchII :
    BranchII 1201 306 (4 * 306 - 1201) 108 ∧
      (((1201 * 108 : Nat) : Int) + 1201 * 306) / (4 * 306 - 1201) = 21618 ∧
      ((((1201 * 306) * (1201 * 306) / (1201 * 108) : Nat) : Int) + 1201 * 306) /
        (4 * 306 - 1201) = 61251 := by
  refine ⟨?_, by decide, by decide⟩
  unfold BranchII
  decide

theorem example_1201_reconstruction :
    let y : Int := 21618
    let z : Int := 61251
    0 < (306 : Int) ∧ (306 : Int) ≤ y ∧ y ≤ z ∧
      4 * (306 : Int) * y * z = (1201 : Int) * (306 * y + 306 * z + y * z) := by
  have h := branchII_reconstruction 1201 306 108 (by norm_num) (by decide)
    (by decide) (by decide) example_1201_branchII.1
  have hy := example_1201_branchII.2.1
  have hz := example_1201_branchII.2.2
  simp only [Nat.cast_ofNat] at h hy hz ⊢
  rw [hy, hz] at h
  exact h

-- Branch I is inhabited too: 4/1201 = 1/306 + 1/15980 + 1/172727820 has t = 34.
theorem example_1201_branchI :
    BranchI 1201 306 (4 * 306 - 1201) 34 ∧
      (((34 : Nat) : Int) + 1201 * 306) / (4 * 306 - 1201) = 15980 ∧
      ((((1201 * 306) * (1201 * 306) / 34 : Nat) : Int) + 1201 * 306) /
        (4 * 306 - 1201) = 172727820 := by
  refine ⟨?_, by decide, by decide⟩
  unfold BranchI
  decide

end OutcastsPrimeBranchBridge

#print axioms OutcastsPrimeBranchBridge.shift_cast
#print axioms OutcastsPrimeBranchBridge.shift_coprime
#print axioms OutcastsPrimeBranchBridge.prime_factor_witness_iff_branches
#print axioms OutcastsPrimeBranchBridge.factor_witness_reconstruction
#print axioms OutcastsPrimeBranchBridge.branchI_reconstruction
#print axioms OutcastsPrimeBranchBridge.branchII_reconstruction
#print axioms OutcastsPrimeBranchBridge.example_1201_branchII
#print axioms OutcastsPrimeBranchBridge.example_1201_reconstruction
#print axioms OutcastsPrimeBranchBridge.example_1201_branchI
