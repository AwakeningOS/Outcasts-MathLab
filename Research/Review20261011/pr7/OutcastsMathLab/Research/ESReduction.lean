import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Reduction of the Erdős–Straus conjecture to six residue classes modulo 840

Known mathematics (Mordell; see also Elsholtz–Tao, arXiv:1107.1010, §1), formalized as the
skeleton into which an existence argument for the remaining primes would plug.  This file does
**not** prove the conjecture and makes no claim of progress on it.

* `ES n` : `4/n = 1/x + 1/y + 1/z` has a solution in positive integers (cleared denominators);
  `es_iff_rat` checks this against the rational statement.
* `es_mul` : a solution for `n` gives one for every multiple of `n`.
* `es_of_witness` : Dahan's Type II criterion (arXiv:2608.24035, Theorem 3.9(ii)) in one
  direction, with the explicit solution `x = u v t`, `y = a u v n`, `z = a v t n`
  where `s * t = a * n + u` and `s + 1 = 4 * a * u * v`.
* `es_of_not_hard` : every prime outside the six classes `1, 121, 169, 289, 361, 529 (mod 840)`
  has a solution (identities for `n ≡ 3 (mod 4)`, `n ≡ 5 (mod 8)`, and witnesses covering
  `n ≡ 2 (mod 3)`, `n ≡ 7, 13 (mod 15)`, `n ≡ 3, 5, 6 (mod 7)`).
* `es_all_iff_hard_primes` : the conjecture for all `n ≥ 2` is equivalent to the conjecture for
  primes in the six classes.
-/

namespace OutcastsMathLab.Research.ESReduction

/-- `4/n = 1/x + 1/y + 1/z` with positive integers, denominators cleared. -/
def ES (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ 4 * x * y * z = n * (x * y + x * z + y * z)

/-- The six residue classes modulo 840 left open by Mordell's identities. -/
def hardResidues : Finset ℕ := {1, 121, 169, 289, 361, 529}

/-- The cleared form agrees with the rational equation. -/
theorem es_iff_rat {n : ℕ} (hn : 0 < n) :
    ES n ↔ ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
      (4 : ℚ) / n = 1 / x + 1 / y + 1 / z := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hq : (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z) := by exact_mod_cast h
    field_simp
    linear_combination hq
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    refine ⟨x, y, z, hx, hy, hz, ?_⟩
    have hn' : (n : ℚ) ≠ 0 := by positivity
    have hx' : (x : ℚ) ≠ 0 := by positivity
    have hy' : (y : ℚ) ≠ 0 := by positivity
    have hz' : (z : ℚ) ≠ 0 := by positivity
    field_simp at h
    exact_mod_cast (by linear_combination h : (4 : ℚ) * x * y * z = n * (x * y + x * z + y * z))

/-- Scaling: a solution for `n` gives a solution for `n * m`. -/
theorem es_mul {n : ℕ} (h : ES n) {m : ℕ} (hm : 0 < m) : ES (n * m) := by
  obtain ⟨x, y, z, hx, hy, hz, he⟩ := h
  refine ⟨x * m, y * m, z * m, by positivity, by positivity, by positivity, ?_⟩
  have : 4 * (x * m) * (y * m) * (z * m) = (4 * x * y * z) * m ^ 3 := by ring
  rw [this, he]
  ring

theorem es_two : ES 2 := ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `n = 4k + 3`: `4/n = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1))`. -/
theorem es_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine ⟨k + 1, 2 * (4 * k + 3) * (k + 1), 2 * (4 * k + 3) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  ring

/-- `n = 8k + 5`: `4/n = 1/(2k+2) + 1/(n(k+1)) + 1/(2n(k+1))`. -/
theorem es_of_mod_eight_eq_five {n : ℕ} (h : n % 8 = 5) : ES n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
  refine ⟨2 * k + 2, (8 * k + 5) * (k + 1), 2 * (8 * k + 5) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  ring

/-- Dahan's Type II witness gives an explicit solution. -/
theorem es_of_witness {n a u s : ℕ} (hn : 0 < n) (ha : 0 < a) (hu : 0 < u)
    (hs : s ∣ a * n + u) (hm : 4 * a * u ∣ s + 1) : ES n := by
  obtain ⟨t, ht⟩ := hs
  obtain ⟨v, hv⟩ := hm
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0, mul_zero] at ht; omega
    · exact h0
  have hvpos : 0 < v := by
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · rw [h0, mul_zero] at hv; omega
    · exact h0
  refine ⟨u * v * t, a * u * v * n, a * v * t * n,
    by positivity, by positivity, by positivity, ?_⟩
  have ht' : (a : ℤ) * n + u = s * t := by exact_mod_cast ht
  have hv' : (s : ℤ) + 1 = 4 * a * u * v := by exact_mod_cast hv
  have key : (4 : ℤ) * (u * v * t) * (a * u * v * n) * (a * v * t * n) =
      n * ((u * v * t) * (a * u * v * n) + (u * v * t) * (a * v * t * n) +
        (a * u * v * n) * (a * v * t * n)) := by
    linear_combination (-(a : ℤ) * u * v ^ 2 * t * n ^ 2) * ht' +
      (-(a : ℤ) * u * v ^ 2 * t ^ 2 * n ^ 2) * hv'
  exact_mod_cast key

/-- Residue bookkeeping: what survives the identities modulo 8, 3, 5, 7 is the six classes. -/
theorem hard_of_residues (r : ℕ) (hr : r < 840) (h8 : r % 8 = 1) (h3 : r % 3 = 1)
    (h5 : r % 5 = 1 ∨ r % 5 = 4) (h7 : r % 7 = 1 ∨ r % 7 = 2 ∨ r % 7 = 4) :
    r ∈ hardResidues := by
  simp only [hardResidues, Finset.mem_insert, Finset.mem_singleton]
  omega

/-! Small residue facts, each stated with only the hypotheses it needs (keeps `omega` fast). -/

theorem mod_ne_zero_of_prime {p q : ℕ} (hp : p.Prime) (hq : 1 < q) (hpq : p ≠ q) :
    p % q ≠ 0 := by
  intro h0
  rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h0) with h | h
  · omega
  · exact hpq h.symm

theorem mod8_eq_one {p : ℕ} (hodd : p % 2 = 1) (h4 : p % 4 ≠ 3) (h85 : p % 8 ≠ 5) :
    p % 8 = 1 := by omega

theorem mod3_eq_one {p : ℕ} (h0 : p % 3 ≠ 0) (h2 : p % 3 ≠ 2) : p % 3 = 1 := by omega

theorem mod5_cases {p : ℕ} (h0 : p % 5 ≠ 0) (h2 : p % 5 ≠ 2) (h3 : p % 5 ≠ 3) :
    p % 5 = 1 ∨ p % 5 = 4 := by omega

theorem mod7_cases {p : ℕ} (h0 : p % 7 ≠ 0) (h3 : p % 7 ≠ 3) (h5 : p % 7 ≠ 5)
    (h6 : p % 7 ≠ 6) : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 := by omega

theorem dvd_mod3 {p : ℕ} (h : p % 3 = 2) : 3 ∣ 1 * p + 1 := by omega
theorem dvd_mod15_a {p : ℕ} (h3 : p % 3 = 1) (h5 : p % 5 = 2) : 15 ∣ 2 * p + 1 := by omega
theorem dvd_mod15_b {p : ℕ} (h3 : p % 3 = 1) (h5 : p % 5 = 3) : 15 ∣ 1 * p + 2 := by omega
theorem dvd_mod7_a {p : ℕ} (h : p % 7 = 3) : 7 ∣ 2 * p + 1 := by omega
theorem dvd_mod7_b {p : ℕ} (h : p % 7 = 5) : 7 ∣ 1 * p + 2 := by omega
theorem dvd_mod7_c {p : ℕ} (h : p % 7 = 6) : 7 ∣ 1 * p + 1 := by omega

/-- Every prime outside the six classes modulo 840 has a solution. -/
theorem es_of_not_hard {p : ℕ} (hp : p.Prime) (hh : p % 840 ∉ hardResidues) : ES p := by
  have hp0 : 0 < p := hp.pos
  by_contra hne
  apply hh
  -- each identity or witness that applies would give `ES p`
  have h4 : p % 4 ≠ 3 := fun h => hne (es_of_mod_four_eq_three h)
  have h85 : p % 8 ≠ 5 := fun h => hne (es_of_mod_eight_eq_five h)
  have h2 : p ≠ 2 := fun h => hne (h ▸ es_two)
  have h32 : p % 3 ≠ 2 := fun h =>
    hne (es_of_witness (a := 1) (u := 1) (s := 3) hp0 one_pos one_pos (dvd_mod3 h) (by norm_num))
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
  have h8 : p % 8 = 1 := mod8_eq_one hodd h4 h85
  have h3 : p % 3 = 1 :=
    mod3_eq_one (mod_ne_zero_of_prime hp (by norm_num) (fun h => h4 (by rw [h]))) h32
  have h52 : p % 5 ≠ 2 := fun h =>
    hne (es_of_witness (a := 2) (u := 1) (s := 15) hp0 (by norm_num) one_pos
      (dvd_mod15_a h3 h) (by norm_num))
  have h53 : p % 5 ≠ 3 := fun h =>
    hne (es_of_witness (a := 1) (u := 2) (s := 15) hp0 one_pos (by norm_num)
      (dvd_mod15_b h3 h) (by norm_num))
  have h5 : p % 5 = 1 ∨ p % 5 = 4 :=
    mod5_cases (mod_ne_zero_of_prime hp (by norm_num) (fun h => h85 (by rw [h]))) h52 h53
  have h73 : p % 7 ≠ 3 := fun h =>
    hne (es_of_witness (a := 2) (u := 1) (s := 7) hp0 (by norm_num) one_pos
      (dvd_mod7_a h) (by norm_num))
  have h75 : p % 7 ≠ 5 := fun h =>
    hne (es_of_witness (a := 1) (u := 2) (s := 7) hp0 one_pos (by norm_num)
      (dvd_mod7_b h) (by norm_num))
  have h76 : p % 7 ≠ 6 := fun h =>
    hne (es_of_witness (a := 1) (u := 1) (s := 7) hp0 one_pos one_pos
      (dvd_mod7_c h) (by norm_num))
  have h7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4 :=
    mod7_cases (mod_ne_zero_of_prime hp (by norm_num) (fun h => h4 (by rw [h]))) h73 h75 h76
  have e8 : p % 840 % 8 = p % 8 := Nat.mod_mod_of_dvd p (by norm_num)
  have e3 : p % 840 % 3 = p % 3 := Nat.mod_mod_of_dvd p (by norm_num)
  have e5 : p % 840 % 5 = p % 5 := Nat.mod_mod_of_dvd p (by norm_num)
  have e7 : p % 840 % 7 = p % 7 := Nat.mod_mod_of_dvd p (by norm_num)
  exact hard_of_residues (p % 840) (Nat.mod_lt _ (by norm_num)) (e8 ▸ h8) (e3 ▸ h3)
    (e5 ▸ h5) (e7 ▸ h7)

/-! Sanity checks on the definition: it is satisfiable, and not trivially true. -/

/-- The P001 example `4/1201 = 1/306 + 1/21618 + 1/61251`. -/
theorem es_1201 : ES 1201 :=
  ⟨306, 21618, 61251, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `4 = 1/x + 1/y + 1/z` has no solution, since the right side is at most 3. -/
theorem not_es_one : ¬ ES 1 := by
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  have hxy : x * y ≤ x * y * z := Nat.le_mul_of_pos_right _ hz
  have hxz : x * z ≤ x * y * z := by
    calc x * z = x * z * 1 := by ring
      _ ≤ x * z * y := Nat.mul_le_mul_left _ hy
      _ = x * y * z := by ring
  have hyz : y * z ≤ x * y * z := by
    calc y * z = 1 * (y * z) := by ring
      _ ≤ x * (y * z) := Nat.mul_le_mul_right _ hx
      _ = x * y * z := by ring
  have hpos : 0 < x * y * z := by positivity
  have : 4 * x * y * z = 4 * (x * y * z) := by ring
  omega

/-- **Reduction.** The Erdős–Straus conjecture for every `n ≥ 2` is equivalent to the
conjecture for the primes in the six residue classes `1, 121, 169, 289, 361, 529 (mod 840)`. -/
theorem es_all_iff_hard_primes :
    (∀ n, 2 ≤ n → ES n) ↔ (∀ p, p.Prime → p % 840 ∈ hardResidues → ES p) := by
  constructor
  · intro h p hp _
    exact h p hp.two_le
  · intro h n hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; omega
      · exact h0
    have hesp : ES p := by
      by_cases hh : p % 840 ∈ hardResidues
      · exact h p hp hh
      · exact es_of_not_hard hp hh
    exact es_mul hesp hm

#print axioms es_iff_rat
#print axioms es_mul
#print axioms es_two
#print axioms es_of_mod_four_eq_three
#print axioms es_of_mod_eight_eq_five
#print axioms es_of_witness
#print axioms hard_of_residues
#print axioms mod_ne_zero_of_prime
#print axioms mod8_eq_one
#print axioms mod3_eq_one
#print axioms mod5_cases
#print axioms mod7_cases
#print axioms dvd_mod3
#print axioms dvd_mod15_a
#print axioms dvd_mod15_b
#print axioms dvd_mod7_a
#print axioms dvd_mod7_b
#print axioms dvd_mod7_c
#print axioms es_of_not_hard
#print axioms es_all_iff_hard_primes
#print axioms es_1201
#print axioms not_es_one

end OutcastsMathLab.Research.ESReduction
