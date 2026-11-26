import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace UpperSourceCharacter20261117

theorem coefficient_bound (s a h : ℤ) (ha : a ≤ s)
    (hsmall : h ≤ 3*a) (hsize : 4*h*s ≤ 9*(h+a)) : h ≤ 9 := by
  by_contra hn
  have hh : 10 ≤ h := by omega
  have hs : 4 ≤ s := by omega
  have hp : 0 ≤ (4*h-9)*(s-4) := mul_nonneg (by omega) (by omega)
  nlinarith

theorem small_residues (p : ℕ) [Fact p.Prime]
    (h2 : legendreSym p 2 = 1) (h3 : legendreSym p 3 = 1)
    (h5 : legendreSym p 5 = 1) (h7 : legendreSym p 7 = 1)
    (n : ℤ) (hn : 1 ≤ n) (hn9 : n ≤ 9) : legendreSym p n = 1 := by
  have h4 : legendreSym p 4 = 1 := by
    have hm := legendreSym.mul p 2 2
    norm_num [h2] at hm ⊢
    exact hm
  have h6 : legendreSym p 6 = 1 := by
    have hm := legendreSym.mul p 2 3
    norm_num [h2,h3] at hm ⊢
    exact hm
  have h8 : legendreSym p 8 = 1 := by
    have hm := legendreSym.mul p 2 4
    norm_num [h2,h4] at hm ⊢
    exact hm
  have h9 : legendreSym p 9 = 1 := by
    have hm := legendreSym.mul p 3 3
    norm_num [h3] at hm ⊢
    exact hm
  interval_cases n <;> simp_all [legendreSym.at_one]

theorem reduced_middle_impossible (p : ℕ) [Fact p.Prime]
    (s a b h c : ℤ)
    (h2 : legendreSym p 2 = 1) (h3 : legendreSym p 3 = 1)
    (h5 : legendreSym p 5 = 1) (h7 : legendreSym p 7 = 1)
    (hc : legendreSym p c = -1)
    (hs : s ≤ 8) (ha : a ≤ s) (hb : 1 ≤ b) (hbs : b ≤ s)
    (hh : 1 ≤ h) (hsmall : h ≤ 3*a) (hsize : 4*h*s ≤ 9*(h+a))
    (heq : h*c = a*(p:ℤ)+b) : False := by
  have hh9 := coefficient_bound s a h ha hsmall hsize
  have hrh := small_residues p h2 h3 h5 h7 h hh hh9
  have hrb := small_residues p h2 h3 h5 h7 b hb (by omega)
  have hcmod : legendreSym p (a*(p:ℤ)+b) = legendreSym p b := by
    simp [legendreSym]
  have hz := congrArg (legendreSym p) heq
  rw [legendreSym.mul,hrh,hc,hcmod,hrb] at hz
  norm_num at hz

#print axioms coefficient_bound
#print axioms small_residues
#print axioms reduced_middle_impossible
end UpperSourceCharacter20261117
