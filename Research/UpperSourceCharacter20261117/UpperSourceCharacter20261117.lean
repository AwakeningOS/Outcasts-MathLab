import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace UpperSourceCharacter20261117

theorem bounds_from_source (p s a b h c r : ℤ)
    (hp : 840 < p) (hs : 1 ≤ s) (hs8 : s ≤ 8) (hbs : b ≤ s)
    (hh : 1 ≤ h) (hc : p < 3*c) (hr : p < 9*r)
    (hx : 4*s*r = p+c) (heq : h*c = a*p+b) :
    h ≤ 3*a ∧ 4*h*s ≤ 9*(h+a) := by
  have hcp : (h-3*a)*p < 3*b := by
    nlinarith [mul_pos (show 0 < h by omega) (show 0 < 3*c-p by omega)]
  have hbnd : h ≤ 3*a := by
    by_contra hn
    have hgap : 0 ≤ h-3*a-1 := by omega
    nlinarith [mul_nonneg hgap (show 0 ≤ p by omega)]
  have hsr : 4*h*s*r = (h+a)*p+b := by
    nlinarith [congrArg (fun z : ℤ => h*z) hx]
  have hpos : 0 < 4*h*s := mul_pos (by omega) (by omega)
  have hcross : (4*h*s-9*(h+a))*p < 9*b := by
    nlinarith [mul_pos hpos (show 0 < 9*r-p by omega)]
  have hsize : 4*h*s ≤ 9*(h+a) := by
    by_contra hn
    have hgap : 0 ≤ 4*h*s-9*(h+a)-1 := by omega
    nlinarith [mul_nonneg hgap (show 0 ≤ p by omega)]
  exact ⟨hbnd,hsize⟩

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

theorem upper_source_middle_impossible (p : ℕ) [Fact p.Prime]
    (s a b h c r : ℤ)
    (h2 : legendreSym p 2 = 1) (h3 : legendreSym p 3 = 1)
    (h5 : legendreSym p 5 = 1) (h7 : legendreSym p 7 = 1)
    (hcchar : legendreSym p c = -1)
    (hp : 840 < (p:ℤ)) (hs : 1 ≤ s) (hs8 : s ≤ 8)
    (ha : a ≤ s) (hb : 1 ≤ b) (hbs : b ≤ s) (hh : 1 ≤ h)
    (hc : (p:ℤ) < 3*c) (hr : (p:ℤ) < 9*r)
    (hx : 4*s*r = (p:ℤ)+c) (heq : h*c = a*(p:ℤ)+b) : False := by
  obtain ⟨hsmall,hsize⟩ := bounds_from_source (p:ℤ) s a b h c r hp hs hs8 hbs hh hc hr hx heq
  exact reduced_middle_impossible p s a b h c h2 h3 h5 h7 hcchar hs8 ha hb hbs hh hsmall hsize heq

#print axioms bounds_from_source
#print axioms coefficient_bound
#print axioms small_residues
#print axioms reduced_middle_impossible
#print axioms upper_source_middle_impossible
end UpperSourceCharacter20261117
