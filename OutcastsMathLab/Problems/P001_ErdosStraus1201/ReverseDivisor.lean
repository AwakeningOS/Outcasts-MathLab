import Std

namespace OutcastsReverseDivisor

-- The general reverse specification reviewed in Outcasts #11.
theorem reconstruct (c M a b : Int)
    (hc : 0 < c) (hM : 0 < M) (ha : 0 < a) (haM : a ≤ M)
    (hab : a * b = M * M) (hda : c ∣ a + M) (hdb : c ∣ b + M) :
    let y := (a + M) / c
    let z := (b + M) / c
    0 < y ∧ y ≤ z ∧ c * y * z = M * (y + z) ∧
      c * y - M = a ∧ c * z - M = b := by
  dsimp
  have hy := Int.mul_ediv_cancel_of_dvd hda
  have hz := Int.mul_ediv_cancel_of_dvd hdb
  have hb : 0 < b := by
    have hMM := Int.mul_pos hM hM
    have habpos : 0 < a * b := by omega
    exact Int.pos_of_mul_pos_right habpos (by omega)
  have haborder : a ≤ b := by
    have haa := Int.mul_self_le_mul_self (Int.le_of_lt ha) haM
    have habineq : a * a ≤ a * b := by omega
    exact Int.le_of_mul_le_mul_left habineq ha
  have hyp : 0 < (a + M) / c := by
    have hp : 0 < c * ((a + M) / c) := by omega
    exact Int.pos_of_mul_pos_right hp (by omega)
  have hyz : (a + M) / c ≤ (b + M) / c := by
    apply Int.le_of_mul_le_mul_left (a := c) _ hc
    omega
  have hid :
      c * (c * ((a + M) / c) * ((b + M) / c) -
        M * (((a + M) / c) + ((b + M) / c))) = 0 := by grind
  have heq := (Int.mul_eq_zero.mp hid).resolve_left (Int.ne_of_gt hc)
  exact ⟨hyp, hyz, Int.eq_of_sub_eq_zero heq, by omega, by omega⟩

-- Cancellation is valid only under coprimality.
theorem second_divisibility (c M a b : Int)
    (hcop : Int.gcd c M = 1) (hab : a * b = M * M)
    (hda : c ∣ a + M) : c ∣ b + M := by
  have hpow : Int.gcd c (M * M) = 1 := by
    simpa [Int.pow_succ, Int.pow_zero] using Int.gcd_pow_right_of_gcd_eq_one (k := 2) hcop
  have had : a ∣ M * M := ⟨b, hab.symm⟩
  have hcad : Int.gcd c a ∣ 1 := by
    simpa [hpow] using Int.gcd_dvd_gcd_of_dvd_right c had
  have hca : Int.gcd c a = 1 := Nat.eq_one_of_dvd_one hcad
  have hmul : c ∣ a * (b + M) := by
    have hd : c ∣ M * (a + M) := Int.dvd_mul_of_dvd_right hda
    have hid : a * (b + M) = M * (a + M) := by grind
    exact hid.symm ▸ hd
  have hg := Int.dvd_gcd_mul_iff_dvd_mul.mpr hmul
  simpa [hca] using hg

theorem reconstruct_coprime (c M a b : Int)
    (hc : 0 < c) (hM : 0 < M) (ha : 0 < a) (haM : a ≤ M)
    (hab : a * b = M * M) (hcop : Int.gcd c M = 1) (hda : c ∣ a + M) :
    let y := (a + M) / c
    let z := (b + M) / c
    0 < y ∧ y ≤ z ∧ c * y * z = M * (y + z) ∧
      c * y - M = a ∧ c * z - M = b :=
  reconstruct c M a b hc hM ha haM hab hda
    (second_divisibility c M a b hcop hab hda)

-- The extra lower bound required for a sorted triple x ≤ y ≤ z.
theorem first_denominator_bound (c M a x : Int) (hc : 0 < c)
    (hda : c ∣ a + M) : x ≤ (a + M) / c ↔ c * x - M ≤ a := by
  have hy := Int.mul_ediv_cancel_of_dvd hda
  constructor
  · intro h
    have hmul := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hc)
    omega
  · intro h
    apply Int.le_of_mul_le_mul_left (a := c) _ hc
    omega

theorem noncoprime_counterexample :
    (4 : Int) * 9 = 6 * 6 ∧ 0 < (4 : Int) ∧ (4 : Int) ≤ 6 ∧
    (2 : Int) ∣ 4 + 6 ∧ ¬ (2 : Int) ∣ 9 + 6 := by decide

-- Conditional construction, not universal existence of the parameters.
theorem erdos_straus_reconstruction (p x a b : Int)
    (hx : 0 < x) (hc : 0 < 4 * x - p) (hM : 0 < p * x)
    (ha : 0 < a) (haM : a ≤ p * x)
    (hab : a * b = (p * x) * (p * x))
    (hcop : Int.gcd (4 * x - p) (p * x) = 1)
    (hda : (4 * x - p) ∣ a + p * x)
    (hlower : (4 * x - p) * x - p * x ≤ a) :
    let y := (a + p * x) / (4 * x - p)
    let z := (b + p * x) / (4 * x - p)
    0 < x ∧ x ≤ y ∧ y ≤ z ∧
      4 * x * y * z = p * (x * y + x * z + y * z) := by
  dsimp
  have hr := reconstruct_coprime (4 * x - p) (p * x) a b
    hc hM ha haM hab hcop hda
  dsimp at hr
  have hxy := (first_denominator_bound (4 * x - p) (p * x) a x hc hda).mpr hlower
  refine ⟨hx, hxy, hr.2.1, ?_⟩
  have heq := hr.2.2.1
  grind

end OutcastsReverseDivisor

#print axioms OutcastsReverseDivisor.reconstruct
#print axioms OutcastsReverseDivisor.second_divisibility
#print axioms OutcastsReverseDivisor.reconstruct_coprime
#print axioms OutcastsReverseDivisor.first_denominator_bound
#print axioms OutcastsReverseDivisor.noncoprime_counterexample
#print axioms OutcastsReverseDivisor.erdos_straus_reconstruction
