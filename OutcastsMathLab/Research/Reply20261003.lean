import OutcastsMathLab.Research.ShortProduct20261002

/- Response to Outcasts #22 and #24. These are validation and closure lemmas,
   not a proof of pointwise Type II existence or of the conjecture. -/
namespace OutcastsMathLab.Research.Reply20261003

open OutcastsMathLab.Research.ShortProduct20261002

set_option maxHeartbeats 4000000

def DivisorWitness (p a u s : ℕ) : Prop :=
  s ∣ a*p+u ∧ 4*a*u ∣ s+1

/-- Dahan v1 Lemma 3.10: cancel a common factor without changing s. -/
theorem divisor_witness_cancel_factor (p d a u s : ℕ)
    (hw : DivisorWitness p (d*a) (d*u) s) :
    DivisorWitness p a u s := by
  have hdmod : d ∣ 4*(d*a)*(d*u) := ⟨4*d*a*u, by ring⟩
  have hds : d ∣ s+1 := dvd_trans hdmod hw.2
  have hcs : Nat.Coprime s (s+1) := by simp
  have hcd : Nat.Coprime s d := hcs.of_dvd_right hds
  have hlin : s ∣ d*(a*p+u) := by
    convert hw.1 using 1; ring
  have hsmallmod : 4*a*u ∣ 4*(d*a)*(d*u) := ⟨d*d, by ring⟩
  exact ⟨hcd.dvd_of_dvd_mul_left hlin, dvd_trans hsmallmod hw.2⟩

theorem short_witness_cancel_factor (p d a u : ℕ)
    (hw : ShortWitness p (d*a) (d*u)) : ShortWitness p a u := by
  rcases hw with ⟨q,hq,hd,hm⟩ | ⟨q,r,hq,hr,hd,hm⟩
  · have h := divisor_witness_cancel_factor p d a u q
      ⟨hd, Nat.dvd_of_mod_eq_zero hm⟩
    exact Or.inl ⟨q,hq,h.1,Nat.mod_eq_zero_of_dvd h.2⟩
  · have h := divisor_witness_cancel_factor p d a u (q*r)
      ⟨hd, Nat.dvd_of_mod_eq_zero hm⟩
    exact Or.inr ⟨q,r,hq,hr,h.1,Nat.mod_eq_zero_of_dvd h.2⟩

/-- Normalization preserves the same prime or prime-product witness and does
    not increase a product budget. -/
theorem short_witness_normalize (p a u B : ℕ) (ha : 0<a) (hu : 0<u)
    (hb : a*u ≤ B) (hw : ShortWitness p a u) :
    ∃ a' u', 0<a' ∧ 0<u' ∧ Nat.Coprime a' u' ∧
      a'*u' ≤ B ∧ ShortWitness p a' u' := by
  let d := Nat.gcd a u
  have haeq : d*(a/d) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a u)
  have hueq : d*(u/d) = u := Nat.mul_div_cancel' (Nat.gcd_dvd_right a u)
  have hsmall : ShortWitness p (a/d) (u/d) := by
    apply short_witness_cancel_factor p d (a/d) (u/d)
    simpa only [haeq,hueq] using hw
  refine ⟨a/d,u/d,Nat.div_gcd_pos_of_pos_left u ha,
    Nat.div_gcd_pos_of_pos_right a hu,?_,?_,hsmall⟩
  · exact Nat.gcd_div_gcd_div_gcd_of_pos_left ha
  · exact le_trans (Nat.mul_le_mul (Nat.div_le_self a d) (Nat.div_le_self u d)) hb

/-- Closes the noncoprime gap noted in #22: ALL positive pairs, not just 63. -/
theorem no_short_witness_budget23_all (a u : ℕ) (ha : 0<a) (hu : 0<u)
    (hb : a*u ≤ 23) : ¬ShortWitness 5843041 a u := by
  intro hw
  obtain ⟨a',u',ha',hu',hc,hb',hw'⟩ :=
    short_witness_normalize 5843041 a u 23 ha hu hb hw
  exact no_short_witness_budget23 a' u' ha' hu' hb' hc hw'

/-- The same prime has semiprime witnesses in a BOX of side 23, outside the
    product budget. Neither the box hypothesis nor ESC is refuted here. -/
theorem box_short_witnesses :
    (578519:ℕ)=23*25153 ∧ ¬Nat.Prime 578519 ∧
    DivisorWitness 5843041 10 9 578519 ∧
    (116087:ℕ)=29*4003 ∧ ¬Nat.Prime 116087 ∧
    DivisorWitness 5843041 3 14 116087 ∧
    23 < (10:ℕ)*9 ∧ 23 < (3:ℕ)*14 := by
  norm_num [DivisorWitness]

theorem box_short_witnesses_predicate :
    ShortWitness 5843041 10 9 ∧ ShortWitness 5843041 3 14 := by
  constructor
  · exact Or.inr ⟨23,25153,by norm_num,by norm_num,by norm_num,by norm_num⟩
  · exact Or.inr ⟨29,4003,by norm_num,by norm_num,by norm_num,by norm_num⟩

/-- #24's finite search bound, with no primality assumption on p.
    It applies to ANY actual divisor witness, not merely a short product. -/
theorem modulator_only_bound (p a s : ℕ) (ha : 0<a)
    (hs : 0<s) (hw : DivisorWitness p a 1 s) : 4*a ≤ p+5 := by
  obtain ⟨v,heq⟩ := hw.1
  have hsv : s*v = a*p+1 := by simpa using heq.symm
  have hv : 0<v := by nlinarith
  have hmod : 4*a ∣ s+1 := by simpa using hw.2
  have hslo : 4*a ≤ s+1 := Nat.le_of_dvd (by omega) hmod
  have had : a ∣ s+1 := dvd_trans (show a ∣ 4*a from ⟨4,by ring⟩) hmod
  have hatotal : a ∣ a*p+(v+1) := by
    have ht : a ∣ (s+1)*v := dvd_mul_of_dvd_left had v
    convert ht using 1; nlinarith [hsv]
  have hav : a ∣ v+1 := (Nat.dvd_add_iff_right (dvd_mul_right a p)).mpr hatotal
  have hvlo : a ≤ v+1 := Nat.le_of_dvd (by omega) hav
  have hsl : 4*a-1 ≤ s := by omega
  have hvl : a-1 ≤ v := by omega
  have hprod := Nat.mul_le_mul hsl hvl
  have hfour : 4*a-1+1=4*a := by omega
  have hone : a-1+1=a := by omega
  by_contra hn
  have hp : p+6 ≤ 4*a := by omega
  have ht := Nat.mul_le_mul_left a hp
  nlinarith [hprod,hsv,ht]

theorem modulator_only_search_complete (p a s : ℕ) (ha : 0<a)
    (hs : 0<s) (hw : DivisorWitness p a 1 s) : a ≤ (p+5)/4 := by
  exact (Nat.le_div_iff_mul_le (by norm_num : 0<(4:ℕ))).mpr
    (by simpa [Nat.mul_comm] using modulator_only_bound p a s ha hs hw)

#print axioms divisor_witness_cancel_factor
#print axioms short_witness_cancel_factor
#print axioms short_witness_normalize
#print axioms no_short_witness_budget23_all
#print axioms box_short_witnesses
#print axioms box_short_witnesses_predicate
#print axioms modulator_only_bound
#print axioms modulator_only_search_complete

end OutcastsMathLab.Research.Reply20261003
