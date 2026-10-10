import OutcastsMathLab.Research.ESReduction
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Small shifts on the hard primes: the Mordell obstruction left by `a u ≤ 3`

Elementary facts behind `Research/SmallShifts20261008/` (finite data on the `luna/p001-failure-atlas`
fork branch).  For the shifts `(a, u) = (1,1)`, `(1,2)`, `(2,1)` the Type II witness condition
`s ∣ a n + u, 4 a u ∣ s + 1` is characterised by the residues of the prime factors of `a n + u`
(likewise `(1,3)`, `(3,1)` for `n ≡ 1 (mod 24)`),
and for every `n ≡ 1 (mod 24)` (in particular every prime in the six hard classes mod 840) the
"global sign" is the one that does **not** guarantee a witness.  Known mathematics; not progress
on the conjecture.

* `mod_mem_of_prime_factors`: if every prime factor of `a ≠ 0` has residue in a multiplicatively
  closed set `S ∋ 1`, then so does `a`.
* `witness_one_one_iff`: `(∃ s, s ∣ n + 1 ∧ 4 ∣ s + 1) ↔ ∃ prime q ∣ n + 1, q ≡ 3 (mod 4)`.
* `witness_mod_eight_iff`: for `N ≡ 3 (mod 8)`,
  `(∃ s, s ∣ N ∧ 8 ∣ s + 1) ↔ ∃ prime q ∣ N, q ≡ 5 or 7 (mod 8)`;
  applied to `N = n + 2` and `N = 2 n + 1` (shifts `(1,2)` and `(2,1)`).
* `witness_mod_twelve_iff`: for `3 ∤ N`, `(∃ s, s ∣ N ∧ 12 ∣ s + 1) ↔`
  `N` has a prime factor `≡ 3 (mod 4)` and a prime factor `≡ 5 (mod 6)`;
  applied to `N = n + 3` and `N = 3 n + 1` (shifts `(1,3)` and `(3,1)`), and, for `n ≡ 9 (mod 16)`,
  reduced to the second condition alone (`witness_one_three_iff_of_mod16`, `witness_three_one_iff_of_mod16`).
* `global_signs_of_mod24`: for `n ≡ 1 (mod 24)`, `(n+1)/2 ≡ 1 (mod 4)`, `n + 2 ≡ 2 n + 1 ≡ 3 (mod 8)`,
  and `n + 3`, `3 n + 1` are `4 k` with `k ≡ 1 (mod 3)`.
* `mod24_of_hard`: primes in the six classes satisfy `p ≡ 1 (mod 24)`.
* `es_of_divisor_three_mod_four`: a divisor `≡ 3 (mod 4)` of `p + 1` gives a solution (shift `(1,1)`).
-/

namespace OutcastsMathLab.Research.ESSmallShifts

open OutcastsMathLab.Research.ESReduction

/-- Residues of products stay in a multiplicatively closed set. -/
theorem mod_mem_of_prime_factors (m : ℕ) (S : Finset ℕ) (h1 : 1 % m ∈ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, (x * y) % m ∈ S) :
    ∀ a : ℕ, a ≠ 0 → (∀ q, q.Prime → q ∣ a → q % m ∈ S) → a % m ∈ S := by
  intro a
  induction a using induction_on_primes with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; exact h1
  | prime_mul p a hp ih =>
    intro hpa hq
    have ha : a ≠ 0 := by rintro rfl; simp at hpa
    have hpS : p % m ∈ S := hq p hp (dvd_mul_right p a)
    have haS : a % m ∈ S := ih ha fun q hq' hqa => hq q hq' (dvd_mul_of_dvd_right hqa p)
    rw [Nat.mul_mod]
    exact hS _ hpS _ haS

/-- An odd number `≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`. -/
theorem exists_prime_mod_four_three {s : ℕ} (hs : s % 4 = 3) :
    ∃ q, q.Prime ∧ q ∣ s ∧ q % 4 = 3 := by
  by_contra hne
  push Not at hne
  have hS := mod_mem_of_prime_factors 4 {1} (by decide) (by decide) s (by omega) (fun q hq hqs => by
    have hodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · subst h; omega
      · exact h
    have := hne q hq hqs
    simp only [Finset.mem_singleton]
    omega)
  simp only [Finset.mem_singleton] at hS
  omega

/-- **Shift `(1,1)`.** A Type II witness for `(a,u) = (1,1)` exists iff `n + 1` has a prime
factor `≡ 3 (mod 4)`. -/
theorem witness_one_one_iff (n : ℕ) :
    (∃ s, s ∣ n + 1 ∧ 4 ∣ s + 1) ↔ ∃ q, q.Prime ∧ q ∣ n + 1 ∧ q % 4 = 3 := by
  constructor
  · rintro ⟨s, hs, h4⟩
    obtain ⟨q, hq, hqs, hq4⟩ := exists_prime_mod_four_three (s := s) (by omega)
    exact ⟨q, hq, dvd_trans hqs hs, hq4⟩
  · rintro ⟨q, hq, hqn, hq4⟩
    exact ⟨q, hqn, by omega⟩

/-- A number `≡ 7 (mod 8)` has a prime factor `≡ 5` or `≡ 7 (mod 8)`. -/
theorem exists_prime_mod_eight_five_or_seven {s : ℕ} (hs : s % 8 = 7) :
    ∃ q, q.Prime ∧ q ∣ s ∧ (q % 8 = 5 ∨ q % 8 = 7) := by
  by_contra hne
  push Not at hne
  have hS := mod_mem_of_prime_factors 8 {1, 3} (by decide) (by decide) s (by omega) (fun q hq hqs => by
    have hodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · subst h; omega
      · exact h
    have := hne q hq hqs
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  omega

/-- A number `≡ 3 (mod 8)` has a prime factor `≡ 3` or `≡ 7 (mod 8)`. -/
theorem exists_prime_mod_eight_three_or_seven {N : ℕ} (hN : N % 8 = 3) :
    ∃ q, q.Prime ∧ q ∣ N ∧ (q % 8 = 3 ∨ q % 8 = 7) := by
  by_contra hne
  push Not at hne
  have hS := mod_mem_of_prime_factors 8 {1, 5} (by decide) (by decide) N (by omega) (fun q hq hqs => by
    have hodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · subst h; omega
      · exact h
    have := hne q hq hqs
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hS
  omega

/-- **Shifts with `4 a u = 8`.** For `N ≡ 3 (mod 8)`, a divisor `s ≡ 7 (mod 8)` exists iff `N`
has a prime factor `≡ 5` or `≡ 7 (mod 8)`. -/
theorem witness_mod_eight_iff {N : ℕ} (hN : N % 8 = 3) :
    (∃ s, s ∣ N ∧ 8 ∣ s + 1) ↔ ∃ q, q.Prime ∧ q ∣ N ∧ (q % 8 = 5 ∨ q % 8 = 7) := by
  constructor
  · rintro ⟨s, hs, h8⟩
    obtain ⟨q, hq, hqs, hq8⟩ := exists_prime_mod_eight_five_or_seven (s := s) (by omega)
    exact ⟨q, hq, dvd_trans hqs hs, hq8⟩
  · rintro ⟨q, hq, hqN, hq8 | hq8⟩
    · obtain ⟨r, hr, hrN, hr8 | hr8⟩ := exists_prime_mod_eight_three_or_seven hN
      · have hne : q ≠ r := by intro h; subst h; omega
        refine ⟨q * r, Nat.Prime.dvd_mul_of_dvd_ne hne hq hr hqN hrN, ?_⟩
        have : (q * r) % 8 = 7 := by rw [Nat.mul_mod, hq8, hr8]
        omega
      · exact ⟨r, hrN, by omega⟩
    · exact ⟨q, hqN, by omega⟩

/-- Shift `(1,2)`: `4 a u = 8`, `a n + u = n + 2`. -/
theorem witness_one_two_iff {n : ℕ} (hn : n % 8 = 1) :
    (∃ s, s ∣ 1 * n + 2 ∧ 4 * 1 * 2 ∣ s + 1) ↔
      ∃ q, q.Prime ∧ q ∣ n + 2 ∧ (q % 8 = 5 ∨ q % 8 = 7) := by
  simp only [one_mul, show 4 * 1 * 2 = 8 by norm_num]
  exact witness_mod_eight_iff (by omega)

/-- Shift `(2,1)`: `4 a u = 8`, `a n + u = 2 n + 1`. -/
theorem witness_two_one_iff {n : ℕ} (hn : n % 8 = 1) :
    (∃ s, s ∣ 2 * n + 1 ∧ 4 * 2 * 1 ∣ s + 1) ↔
      ∃ q, q.Prime ∧ q ∣ 2 * n + 1 ∧ (q % 8 = 5 ∨ q % 8 = 7) := by
  simp only [show 4 * 2 * 1 = 8 by norm_num]
  exact witness_mod_eight_iff (by omega)

/-- A number `≡ 2 (mod 3)` has a prime factor `≡ 2 (mod 3)`. -/
theorem exists_prime_mod_three_two {s : ℕ} (hs : s % 3 = 2) :
    ∃ q, q.Prime ∧ q ∣ s ∧ q % 3 = 2 := by
  by_contra hne
  push Not at hne
  have hS := mod_mem_of_prime_factors 3 {1} (by decide) (by decide) s (by omega) (fun q hq hqs => by
    have h3 : q % 3 ≠ 0 := by
      intro h0
      have hq3 : q = 3 := by
        rcases hq.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0) with h | h
        · omega
        · exact h.symm
      subst hq3
      omega
    have := hne q hq hqs
    simp only [Finset.mem_singleton]
    omega)
  simp only [Finset.mem_singleton] at hS
  omega

/-- **Shifts with `4 a u = 12`.** If `3 ∤ N`, a divisor `s ≡ 11 (mod 12)` of `N` exists iff `N` has a
prime factor `≡ 3 (mod 4)` and an odd prime factor `≡ 2 (mod 3)` (i.e. `≡ 5 (mod 6)`). -/
theorem witness_mod_twelve_iff {N : ℕ} (h3 : N % 3 ≠ 0) :
    (∃ s, s ∣ N ∧ 12 ∣ s + 1) ↔
      (∃ q, q.Prime ∧ q ∣ N ∧ q % 4 = 3) ∧ (∃ q, q.Prime ∧ q ∣ N ∧ q % 6 = 5) := by
  constructor
  · rintro ⟨s, hs, h12⟩
    obtain ⟨q1, hq1, hq1s, hq14⟩ := exists_prime_mod_four_three (s := s) (by omega)
    obtain ⟨q2, hq2, hq2s, hq23⟩ := exists_prime_mod_three_two (s := s) (by omega)
    have hq2odd : q2 % 2 = 1 := by
      rcases hq2.eq_two_or_odd with h | h
      · subst h
        have : 2 ∣ s := hq2s
        omega
      · exact h
    exact ⟨⟨q1, hq1, dvd_trans hq1s hs, hq14⟩, ⟨q2, hq2, dvd_trans hq2s hs, by omega⟩⟩
  · rintro ⟨⟨q1, hq1, hq1N, hq14⟩, ⟨q2, hq2, hq2N, hq26⟩⟩
    have hq1ne3 : q1 % 3 ≠ 0 := by
      intro h0
      have hq13 : q1 = 3 := by
        rcases hq1.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h0) with h | h
        · omega
        · exact h.symm
      subst hq13
      exact h3 (Nat.mod_eq_zero_of_dvd hq1N)
    by_cases h1 : q1 % 3 = 2
    · exact ⟨q1, hq1N, by omega⟩
    by_cases h2 : q2 % 4 = 3
    · exact ⟨q2, hq2N, by omega⟩
    have hne : q1 ≠ q2 := by intro h; subst h; omega
    refine ⟨q1 * q2, Nat.Prime.dvd_mul_of_dvd_ne hne hq1 hq2 hq1N hq2N, ?_⟩
    have hm1 : q1 % 12 = 7 := by omega
    have hm2 : q2 % 12 = 5 := by omega
    have : (q1 * q2) % 12 = 11 := by rw [Nat.mul_mod, hm1, hm2]
    omega

/-- Shift `(1,3)`: `4 a u = 12`, `a n + u = n + 3`. -/
theorem witness_one_three_iff {n : ℕ} (hn : n % 24 = 1) :
    (∃ s, s ∣ 1 * n + 3 ∧ 4 * 1 * 3 ∣ s + 1) ↔
      (∃ q, q.Prime ∧ q ∣ n + 3 ∧ q % 4 = 3) ∧ (∃ q, q.Prime ∧ q ∣ n + 3 ∧ q % 6 = 5) := by
  simp only [one_mul, show 4 * 1 * 3 = 12 by norm_num]
  exact witness_mod_twelve_iff (by omega)

/-- Shift `(3,1)`: `4 a u = 12`, `a n + u = 3 n + 1`. -/
theorem witness_three_one_iff {n : ℕ} (hn : n % 24 = 1) :
    (∃ s, s ∣ 3 * n + 1 ∧ 4 * 3 * 1 ∣ s + 1) ↔
      (∃ q, q.Prime ∧ q ∣ 3 * n + 1 ∧ q % 4 = 3) ∧ (∃ q, q.Prime ∧ q ∣ 3 * n + 1 ∧ q % 6 = 5) := by
  simp only [show 4 * 3 * 1 = 12 by norm_num]
  exact witness_mod_twelve_iff (by omega)

/-- When `n ≡ 9 (mod 16)` the `χ₋₄` condition is automatic for `(1,3)`: `(n+3)/4 ≡ 3 (mod 4)`. -/
theorem witness_one_three_iff_of_mod16 {n : ℕ} (hn : n % 24 = 1) (h16 : n % 16 = 9) :
    (∃ s, s ∣ 1 * n + 3 ∧ 4 * 1 * 3 ∣ s + 1) ↔ ∃ q, q.Prime ∧ q ∣ n + 3 ∧ q % 6 = 5 := by
  rw [witness_one_three_iff hn]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨q, hq, hqk, hq4⟩ := exists_prime_mod_four_three (s := (n + 3) / 4) (by omega)
    exact ⟨q, hq, dvd_trans hqk ⟨4, by omega⟩, hq4⟩

/-- Same for `(3,1)`: `(3n+1)/4 ≡ 3 (mod 4)` when `n ≡ 9 (mod 16)`. -/
theorem witness_three_one_iff_of_mod16 {n : ℕ} (hn : n % 24 = 1) (h16 : n % 16 = 9) :
    (∃ s, s ∣ 3 * n + 1 ∧ 4 * 3 * 1 ∣ s + 1) ↔ ∃ q, q.Prime ∧ q ∣ 3 * n + 1 ∧ q % 6 = 5 := by
  rw [witness_three_one_iff hn]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨q, hq, hqk, hq4⟩ := exists_prime_mod_four_three (s := (3 * n + 1) / 4) (by omega)
    exact ⟨q, hq, dvd_trans hqk ⟨4, by omega⟩, hq4⟩

/-- The "global signs" for `n ≡ 1 (mod 24)`: none of them forces a witness for `a u ≤ 3`.
`(n+1)/2 ≡ 1 (mod 4)` (so `χ₋₄ = +1` on the odd part of `n + 1`); `n + 2` and `2 n + 1` are
`≡ 3 (mod 8)` (so `χ₋₈ = +1`); `n + 3` and `3 n + 1` are `4 k` with `k ≡ 1 (mod 3)`
(so `χ₋₃ = +1` on the part prime to 6). -/
theorem global_signs_of_mod24 {n : ℕ} (hn : n % 24 = 1) :
    (n + 1) = 2 * ((n + 1) / 2) ∧ ((n + 1) / 2) % 4 = 1 ∧
    (n + 2) % 8 = 3 ∧ (2 * n + 1) % 8 = 3 ∧
    (n + 3) = 4 * ((n + 3) / 4) ∧ ((n + 3) / 4) % 3 = 1 ∧
    (3 * n + 1) = 4 * ((3 * n + 1) / 4) ∧ ((3 * n + 1) / 4) % 3 = 1 := by
  omega

/-- Primes in the six hard classes satisfy `p ≡ 1 (mod 24)`. -/
theorem mod24_of_hard {p : ℕ} (h : p % 840 ∈ hardResidues) : p % 24 = 1 := by
  have e : p % 840 % 24 = p % 24 := Nat.mod_mod_of_dvd p (by norm_num)
  simp only [hardResidues, Finset.mem_insert, Finset.mem_singleton] at h
  omega

/-- The shift `(1,1)` gives a solution as soon as `p + 1` has a divisor `≡ 3 (mod 4)`; for hard
primes, `global_signs_of_mod24` shows this is never forced by congruences alone. -/
theorem es_of_divisor_three_mod_four {p q : ℕ} (hp : 0 < p)
    (hqp : q ∣ p + 1) (hq4 : q % 4 = 3) : ES p :=
  es_of_witness (a := 1) (u := 1) (s := q) hp one_pos one_pos (by simpa using hqp)
    (by norm_num; omega)

/-- Sanity check: `p = 3678481` (hard class `121 mod 840`, the M-test prime whose `ω ≥ 4` shifts all
fail) is solved by the shift `(1,1)`, since `23 ∣ p + 1` and `23 ≡ 3 (mod 4)`. -/
theorem es_3678481 : ES 3678481 :=
  es_of_divisor_three_mod_four (q := 23) (by norm_num) (by norm_num) (by norm_num)

/-! ### The prime `11` (S test, fork `Research/Simultaneity20261010/`)

In the six hard classes `p mod 3, 5, 7` are fixed, so `11` is the first prime that can decide the
small shifts.  Since `11 ≡ 3 (mod 4)` and `11 ≡ -1 (mod 12)`, `s = 11` is a witness for `(1,1)`,
`(1,3)` and `(3,1)` whenever it divides the shifted number, i.e. for `n ≡ 10, 8, 7 (mod 11)`.  It is
not a witness for `(1,2)`, `(2,1)` (`8 ∤ 12`).  The S test observed no wipe-out of the five small
shifts in these classes (1,736 hard primes in `7·10⁶ < p < 10⁷`); this section is the elementary
reason. -/

theorem eleven_residues : 4 ∣ 11 + 1 ∧ 12 ∣ 11 + 1 ∧ ¬ 8 ∣ 11 + 1 := by decide

/-- For `n ≡ 7, 8, 10 (mod 11)` one of the shifts `(3,1)`, `(1,3)`, `(1,1)` has the witness `s = 11`. -/
theorem witness_of_mod_eleven {n : ℕ} (h : n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 10) :
    ∃ a u s, 0 < a ∧ 0 < u ∧ a * u ≤ 3 ∧ s ∣ a * n + u ∧ 4 * a * u ∣ s + 1 := by
  rcases h with h | h | h
  · exact ⟨3, 1, 11, by norm_num, by norm_num, by norm_num, by omega, by norm_num⟩
  · exact ⟨1, 3, 11, by norm_num, by norm_num, by norm_num, by omega, by norm_num⟩
  · exact ⟨1, 1, 11, by norm_num, by norm_num, by norm_num, by omega, by norm_num⟩

theorem es_of_mod_eleven {n : ℕ} (hn : 0 < n) (h : n % 11 = 7 ∨ n % 11 = 8 ∨ n % 11 = 10) :
    ES n := by
  obtain ⟨a, u, s, ha, hu, -, hs, hm⟩ := witness_of_mod_eleven h
  exact es_of_witness hn ha hu hs hm

/-- The hypothesis is not empty inside the hard classes: the smallest hard primes with
`p ≡ 8, 7, 10 (mod 11)` are `1009`, `1129`, `4201`. -/
theorem hard_examples_mod_eleven :
    (Nat.Prime 1009 ∧ 1009 % 840 ∈ hardResidues ∧ 1009 % 11 = 8) ∧
    (Nat.Prime 1129 ∧ 1129 % 840 ∈ hardResidues ∧ 1129 % 11 = 7) ∧
    (Nat.Prime 4201 ∧ 4201 % 840 ∈ hardResidues ∧ 4201 % 11 = 10) := by
  refine ⟨⟨by norm_num, by decide, by norm_num⟩, ⟨by norm_num, by decide, by norm_num⟩,
    ⟨by norm_num, by decide, by norm_num⟩⟩

#print axioms mod_mem_of_prime_factors
#print axioms exists_prime_mod_four_three
#print axioms witness_one_one_iff
#print axioms exists_prime_mod_eight_five_or_seven
#print axioms exists_prime_mod_eight_three_or_seven
#print axioms witness_mod_eight_iff
#print axioms witness_one_two_iff
#print axioms witness_two_one_iff
#print axioms exists_prime_mod_three_two
#print axioms witness_mod_twelve_iff
#print axioms witness_one_three_iff
#print axioms witness_three_one_iff
#print axioms witness_one_three_iff_of_mod16
#print axioms witness_three_one_iff_of_mod16
#print axioms global_signs_of_mod24
#print axioms mod24_of_hard
#print axioms es_of_divisor_three_mod_four
#print axioms es_3678481
#print axioms eleven_residues
#print axioms witness_of_mod_eleven
#print axioms es_of_mod_eleven
#print axioms hard_examples_mod_eleven

end OutcastsMathLab.Research.ESSmallShifts
