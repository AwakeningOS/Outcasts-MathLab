import OutcastsMathLab.Problems.P000_VerifierSmoke.Statement

namespace OutcastsMathLab.P000

theorem verified : Target := by
  intro a b
  exact Nat.add_comm a b

#print axioms verified

end OutcastsMathLab.P000
