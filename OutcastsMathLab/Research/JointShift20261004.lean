import OutcastsMathLab.Research.Reply20261003

/- A completeness lemma used to falsify the proposed u=1-or-2 escape route.
   It is NOT a pointwise existence theorem. The new finite negative rows are
   independently audited in Python, not assumed or encoded as Lean axioms. -/
namespace OutcastsMathLab.Research.JointShift20261004

open OutcastsMathLab.Research.Reply20261003
set_option maxHeartbeats 4000000

/-- Every fixed-u actual witness has a finite a search bound, with no
    primality, coprimality, or prime-factor-count assumption. -/
theorem fixed_shift_bound (p a u s : ℕ) (ha : 0<a) (hu : 0<u)
    (hs : 0<s) (hw : DivisorWitness p a u s) :
    4*u*a ≤ p+4*u*u+1 := by
  obtain ⟨v,heq⟩ := hw.1
  have hsv : s*v = a*p+u := by simpa using heq.symm
  have hv : 0<v := by nlinarith
  have hslo : 4*a*u ≤ s+1 := Nat.le_of_dvd (by omega) hw.2
  have had : a ∣ s+1 := dvd_trans (show a ∣ 4*a*u from ⟨4*u,by ring⟩) hw.2
  have hatotal : a ∣ a*p+(u+v) := by
    have ht : a ∣ (s+1)*v := dvd_mul_of_dvd_left had v
    convert ht using 1; nlinarith [hsv]
  have hav : a ∣ u+v := (Nat.dvd_add_iff_right (dvd_mul_right a p)).mpr hatotal
  have hvlo : a ≤ u+v := Nat.le_of_dvd (by omega) hav
  by_cases hau : a ≤ u
  · nlinarith
  · have hsl : 4*a*u-1 ≤ s := by omega
    have hvl : a-u ≤ v := by omega
    have hprod := Nat.mul_le_mul hsl hvl
    have hmu : 0<4*a*u := Nat.mul_pos (by omega : 0<4*a) hu
    have hfour : 4*a*u-1+1=4*a*u := Nat.sub_add_cancel (by omega)
    have hone : a-u+u=a := by omega
    by_contra hn
    have hp : p+4*u*u+2 ≤ 4*u*a := by omega
    have ht := Nat.mul_le_mul_left a hp
    nlinarith [hprod,hsv,ht]

theorem fixed_shift_search_complete (p a u s : ℕ) (ha : 0<a) (hu : 0<u)
    (hs : 0<s) (hw : DivisorWitness p a u s) :
    a ≤ (p+4*u*u+1)/(4*u) := by
  exact (Nat.le_div_iff_mul_le (by omega : 0<4*u)).mpr
    (by simpa [Nat.mul_comm] using fixed_shift_bound p a u s ha hu hs hw)

/-- Concrete rescue at u=4, outside product log-budget 17.
    The all-depth u=2,3 negative results are not formalized by this theorem. -/
theorem rescue_66529 :
    Nat.Prime 66529 ∧ (66529:ℕ)%840=169 ∧
    DivisorWitness 66529 11 4 703 ∧ (703:ℕ)=19*37 ∧
    11*66529+4=703*1041 ∧ 703+1=4*11*4*4 ∧
    DivisorWitness 66529 1 5 39 ∧ (17:ℕ)<11*4 ∧
    (2:ℕ)^16<66529 ∧ 66529≤(2:ℕ)^17 ∧
    4*(16656:ℕ)*11709104*3047294316 =
      66529*(11709104*3047294316+16656*3047294316+16656*11709104) := by
  norm_num [DivisorWitness]

#print axioms fixed_shift_bound
#print axioms fixed_shift_search_complete
#print axioms rescue_66529

end OutcastsMathLab.Research.JointShift20261004
