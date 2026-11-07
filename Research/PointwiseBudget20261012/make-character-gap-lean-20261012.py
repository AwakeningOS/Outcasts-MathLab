import json
from pathlib import Path
run=Path('/mnt/hdd1t/outcasts-reply-20261012-ZXux6H')
rows=[r for r in json.loads((run/'character-budget-followup-rows.json').read_text()) if r['p']==66529]
assert len(rows)==43
def rat(s):
    bits=str(s).split('/')
    return '('+bits[0]+' : ℚ)' if len(bits)==1 else '('+bits[0]+' : ℚ) / '+bits[1]
mains=',\n  '.join(rat(r['main']) for r in rows)
counts=', '.join(str(r['W']) for r in rows)
source='''import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NormNum

/- Numeric certificate only. These lists were extracted from the independently
checked43-row table for p66529/B17. Primality, row completeness, factorization,
and general character orthogonality are NOT proved by this Lean file. -/
namespace CharacterGap20261012

def principals : List ℚ := [
  MAIN_LIST
]
def witnessCounts : List ℚ := [COUNT_LIST]
def absoluteErrors : List ℚ :=
  List.zipWith (fun w u => |w-u|) witnessCounts principals

theorem principal_sum : principals.sum = (5717 : ℚ)/240 := by
  norm_num [principals]
theorem absolute_sum : absoluteErrors.sum = (5717 : ℚ)/240 := by
  norm_num [absoluteErrors, witnessCounts, principals, List.zipWith]
theorem actual_sum : witnessCounts.sum = 4 := by
  norm_num [witnessCounts]
theorem no_positive_L1_gap : ¬ (0 < principals.sum - absoluteErrors.sum) := by
  rw [principal_sum, absolute_sum]
  norm_num
theorem actual_count_positive : 0 < witnessCounts.sum := by
  rw [actual_sum]
  norm_num

#print axioms principal_sum
#print axioms absolute_sum
#print axioms actual_sum
#print axioms no_positive_L1_gap
#print axioms actual_count_positive
end CharacterGap20261012
'''.replace('MAIN_LIST',mains).replace('COUNT_LIST',counts)
(run/'CharacterGap20261012.lean').write_text(source)
print(source)
