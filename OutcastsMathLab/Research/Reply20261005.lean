import OutcastsMathLab.Research.JointShift20261004

/- Reply to Outcasts #27. The bounds are validation helpers, not new
   existence results. No finite negative enumeration is encoded as an axiom. -/
namespace OutcastsMathLab.Research.Reply20261005

open OutcastsMathLab.Research.Reply20261003
open OutcastsMathLab.Research.JointShift20261004
set_option maxHeartbeats 4000000

/-- A divisor of the positive linear form cannot be zero. -/
theorem witness_s_pos (p a u s : ℕ) (hu : 0<u)
    (hw : DivisorWitness p a u s) : 0<s := by
  have hpos : 0<a*p+u := by omega
  exact Nat.pos_of_dvd_of_pos hw.1 hpos

/-- The old fixed-shift bound without its redundant s-positive hypothesis. -/
theorem fixed_shift_bound_auto (p a u s : ℕ) (ha : 0<a) (hu : 0<u)
    (hw : DivisorWitness p a u s) : 4*u*a ≤ p+4*u*u+1 :=
  fixed_shift_bound p a u s ha hu (witness_s_pos p a u s hu hw) hw

theorem fixed_shift_search_complete_auto (p a u s : ℕ) (ha : 0<a) (hu : 0<u)
    (hw : DivisorWitness p a u s) : a ≤ (p+4*u*u+1)/(4*u) :=
  fixed_shift_search_complete p a u s ha hu (witness_s_pos p a u s hu hw) hw

/-- p has an actual u=1 witness. It is NOT a second u=1-or-2 counterexample.
    Minimality of a=30 and C=12 are separately checked finite results. -/
theorem witnesses_1740481 :
    Nat.Prime 1740481 ∧ (1740481:ℕ)%840=1 ∧
    (2:ℕ)^20<1740481 ∧ 1740481≤(2:ℕ)^21 ∧
    DivisorWitness 1740481 30 1 586679 ∧
    30*1740481+1=586679*89 ∧ 586679+1=4*30*4889 ∧
    (21:ℕ)<30 ∧
    DivisorWitness 1740481 104 3 11231 ∧
    (11231:ℕ)=11*1021 ∧ 104*1740481+3=11231*16117 ∧
    11231+1=4*104*3*9 ∧
    DivisorWitness 1740481 3 4 3311 ∧
    3*1740481+4=3311*1577 ∧ 3311+1=4*3*4*69 ∧
    (3:ℕ)*4≤21 ∧
    4*(435121:ℕ)*255276348270*22719594996030 =
      1740481*(255276348270*22719594996030+
        435121*22719594996030+435121*255276348270) ∧
    4*(435159:ℕ)*4887270648*26256047011272 =
      1740481*(4887270648*26256047011272+
        435159*26256047011272+435159*4887270648) := by
  norm_num [DivisorWitness]

#print axioms witness_s_pos
#print axioms fixed_shift_bound_auto
#print axioms fixed_shift_search_complete_auto
#print axioms witnesses_1740481

end OutcastsMathLab.Research.Reply20261005
