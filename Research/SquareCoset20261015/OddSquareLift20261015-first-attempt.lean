import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum

namespace OddSquareLift20261015

variable {G : Type*} [CommGroup G]

theorem involution_odd_power (t : G) (k : ℕ) (ht : t^2 = 1) :
    t^(2*k+1) = t := by
  rw [pow_add, pow_mul, ht]
  simp

theorem odd_lift_power (t h : G) (k : ℕ) (ht : t^2 = 1)
    (hh : h^(2*k+1) = 1) : (t*h)^(2*k+1) = t := by
  rw [mul_pow, involution_odd_power t k ht, hh, mul_one]

theorem odd_lift_membership (K : Subgroup G) (t h : G) (k : ℕ)
    (ht : t^2 = 1) (hh : h^(2*k+1) = 1) (hx : t*h ∈ K) : t ∈ K := by
  have hp := K.pow_mem hx (2*k+1)
  rwa [odd_lift_power t h k ht hh] at hp

theorem odd_card_lift (H K : Subgroup G) [Fintype H] (t : G) (h : H)
    (k : ℕ) (hcard : Fintype.card H = 2*k+1) (ht : t^2 = 1)
    (hx : t*(h : G) ∈ K) : t ∈ K := by
  have hh : (h : G)^(2*k+1) = 1 := by
    have hp := pow_card_eq_one h
    rw [hcard] at hp
    exact congrArg (fun z : H => (z : G)) hp
  exact odd_lift_membership K t (h : G) k ht hh hx

theorem numeric_group_obstruction_factorization :
    (665291 : ℕ) = 11*31*1951 := by norm_num

theorem numeric_odd_lift_but_no_divisibility :
    (83 : ℕ)^3 % 36 = 35 ∧ ¬ 83^3 ∣ 598762 := by norm_num

#print axioms involution_odd_power
#print axioms odd_lift_power
#print axioms odd_lift_membership
#print axioms odd_card_lift
#print axioms numeric_group_obstruction_factorization
#print axioms numeric_odd_lift_but_no_divisibility

end OddSquareLift20261015
