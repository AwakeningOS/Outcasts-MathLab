import Mathlib.Data.Nat.Prime.Defs
import OutcastsMathLab.Problems.P001_ErdosStraus1201.ReverseDivisor

namespace OutcastsPrimeCoprimality

-- A general coprimality identity; primality is unnecessary here.
theorem gcd_shift_product (p x : Int)
    (hpx : Int.gcd p x = 1) (hp4 : Int.gcd p 4 = 1) :
    Int.gcd (4 * x - p) (p * x) = 1 := by
  have hcx : Int.gcd (4 * x - p) x = 1 := by
    simpa using hpx
  have hxp : Int.gcd x p = 1 := by
    simpa [Int.gcd_comm] using hpx
  have h4xp : Int.gcd (4 * x) p = 1 := by
    rw [Int.gcd_mul_left_left_of_gcd_eq_one hxp]
    simpa [Int.gcd_comm] using hp4
  have hcp : Int.gcd (4 * x - p) p = 1 := by
    simpa using h4xp
  rw [Int.gcd_mul_right_right_of_gcd_eq_one hcp]
  exact hcx

-- Use mathlib's standard primality predicate. Subtraction takes place in Int.
theorem odd_prime_coprimality (p x : Nat)
    (hp : Nat.Prime p) (hodd : p ≠ 2) (hx : 0 < x) (hxp : x < p) :
    Int.gcd (4 * (x : Int) - (p : Int)) ((p : Int) * (x : Int)) = 1 := by
  have hnotx : ¬ p ∣ x := by
    intro h
    have hle := Nat.le_of_dvd hx h
    omega
  have hnot2 : ¬ p ∣ 2 := by
    intro h
    have hle := Nat.le_of_dvd (by decide : 0 < (2 : Nat)) h
    have hp2 := hp.two_le
    omega
  have hnot4 : ¬ p ∣ 4 := by
    intro h
    have h' : p ∣ 2 * 2 := h
    exact (hp.dvd_mul.mp h').elim hnot2 hnot2
  have hpx : Nat.gcd p x = 1 := hp.coprime_iff_not_dvd.mpr hnotx
  have hp4 : Nat.gcd p 4 = 1 := hp.coprime_iff_not_dvd.mpr hnot4
  apply gcd_shift_product
  · exact (Int.gcd_natCast_natCast p x).trans hpx
  · exact (Int.gcd_natCast_natCast p 4).trans hp4

-- The prime-range wrapper no longer assumes coprimality separately.
theorem odd_prime_reconstruction (p x : Nat) (a b : Int)
    (hp : Nat.Prime p) (hodd : p ≠ 2)
    (hlo : p < 4 * x) (hhi : 4 * x ≤ 3 * p)
    (ha : 0 < a) (haM : a ≤ (p : Int) * (x : Int))
    (hab : a * b = ((p : Int) * (x : Int)) * ((p : Int) * (x : Int)))
    (hda : (4 * (x : Int) - (p : Int)) ∣ a + (p : Int) * (x : Int))
    (hlower : (4 * (x : Int) - (p : Int)) * (x : Int) -
      (p : Int) * (x : Int) ≤ a) :
    let y := (a + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    let z := (b + (p : Int) * (x : Int)) / (4 * (x : Int) - (p : Int))
    0 < (x : Int) ∧ (x : Int) ≤ y ∧ y ≤ z ∧
      4 * (x : Int) * y * z = (p : Int) * ((x : Int) * y + (x : Int) * z + y * z) := by
  have hp2 := hp.two_le
  have hx : 0 < x := by omega
  have hxp : x < p := by omega
  have hp0 : 0 < (p : Int) := by omega
  have hx0 : 0 < (x : Int) := by omega
  exact OutcastsReverseDivisor.erdos_straus_reconstruction
    (p : Int) (x : Int) a b hx0 (by omega) (Int.mul_pos hp0 hx0)
    ha haM hab (odd_prime_coprimality p x hp hodd hx hxp) hda hlower

end OutcastsPrimeCoprimality

#print axioms OutcastsPrimeCoprimality.gcd_shift_product
#print axioms OutcastsPrimeCoprimality.odd_prime_coprimality
#print axioms OutcastsPrimeCoprimality.odd_prime_reconstruction
