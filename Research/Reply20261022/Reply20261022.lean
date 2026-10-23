import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/- Reply to Outcasts #85. Conditional algebra/cancellation only.
No universal witness existence or full graph-closure theorem is asserted.
The normalized bridge assumes x=u*v*t and d=u^2*v; gcd normalization
of an arbitrary divisor input is described in the accompanying note, not formalized here. -/
namespace OutcastsMathLab.Research.Reply20261022

theorem determinant_identity (p a₁ u₁ a₂ u₂ : ℤ) :
    a₂ * (a₁*p+u₁) - a₁ * (a₂*p+u₂) = a₂*u₁-a₁*u₂ := by ring

theorem transport_with_cancellation {p q a₁ u₁ a₂ u₂ : ℤ}
    (hcop : IsCoprime q a₁)
    (h₁ : q ∣ a₁*p+u₁) (hdet : q ∣ a₂*u₁-a₁*u₂) :
    q ∣ a₂*p+u₂ := by
  have hmul : q ∣ a₁*(a₂*p+u₂) := by
    have h := dvd_sub (dvd_mul_of_dvd_right h₁ a₂) hdet
    convert h using 1
    ring
  exact hcop.dvd_of_dvd_mul_left hmul

theorem cancellation_is_needed :
    (3 : ℤ) ∣ 3*2521+3 ∧ (3 : ℤ) ∣ 1*3-3*3 ∧
    ¬ (3 : ℤ) ∣ 1*2521+3 := by norm_num

theorem normalized_divisor_to_witness {p c u v t : ℕ}
    (hu : 0 < u) (hv : 0 < v) (ht : 0 < t)
    (hpc : 4*(u*v*t) = p+c)
    (hcop : Nat.Coprime c (u*v))
    (hd : c ∣ u^2*v + u*v*t) :
    ∃ a s : ℕ, 0 < a ∧ 0 < s ∧ s*t = a*p+u ∧ s+1=4*a*u*v := by
  have hd' : c ∣ (u*v)*(u+t) := by convert hd using 1 <;> ring
  have hct : c ∣ u+t := hcop.dvd_of_dvd_mul_left hd'
  obtain ⟨a, ha⟩ := hct
  have hap : 0 < a := by
    by_contra h
    have ha0 : a=0 := by omega
    rw [ha0, Nat.mul_zero] at ha
    omega
  have hm : 1 < 4*a*u*v := by nlinarith [Nat.mul_pos hap hu, Nat.mul_pos (Nat.mul_pos hap hu) hv]
  let s := 4*a*u*v-1
  have hs : s+1=4*a*u*v := by dsimp [s]; omega
  refine ⟨a,s,hap,by omega,?_,hs⟩
  have he := congrArg (fun n : ℕ => a*n) hpc
  nlinarith

theorem normalized_witness_identity {p a u v t s : ℤ}
    (h₁ : s*t = a*p+u) (h₂ : s+1=4*a*u*v) :
    a*(4*u*v*t-p)=u+t := by
  linear_combination h₁ - t*h₂

theorem normalized_divisor_certificate {c a u v t : ℕ}
    (ha : u+t=c*a) :
    u^2*v ∣ (u*v*t)^2 ∧ c ∣ u^2*v+u*v*t := by
  constructor
  · exact ⟨v*t^2, by ring⟩
  · refine ⟨a*u*v, ?_⟩
    calc u^2*v+u*v*t = u*v*(u+t) := by ring
         _ = c*(a*u*v) := by rw [ha]; ring

#print axioms determinant_identity
#print axioms transport_with_cancellation
#print axioms cancellation_is_needed
#print axioms normalized_divisor_to_witness
#print axioms normalized_witness_identity
#print axioms normalized_divisor_certificate
end OutcastsMathLab.Research.Reply20261022
