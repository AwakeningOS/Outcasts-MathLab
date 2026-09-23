import Std

namespace OutcastsMathLab.P001

/-- 固定した最初の分母に対する、解から因数対への変換。 -/
def SolutionYieldsFactorPair : Prop :=
  ∀ (c M y z : Int),
    0 < c →
    0 < M →
    0 < y →
    y ≤ z →
    c * y * z = M * (y + z) →
    let a : Int := c * y - M
    let b : Int := c * z - M
    0 < a ∧
    a ≤ M ∧
    a * b = M ^ 2 ∧
    c ∣ a + M ∧
    c ∣ b + M

end OutcastsMathLab.P001
