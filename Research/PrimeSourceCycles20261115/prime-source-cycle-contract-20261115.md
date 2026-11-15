# Prime-source cycle candidate, 2026-11-15

Before running the enumeration: test whether a full square-source closed component
can be constructed with every canonical source equal to its next nonresidue prime.
The equations are p + sigma_i*q_i = 4*q_(i+1), sigma_i in {1,3}.
If such a cycle exists at a hard prime, its minimum exceeds p/3; consequently
only tau=1 is admissible at every vertex. The Type II bound in posts104/141
excludes that branch. Type I will be checked on the actual three divisors of x^2.

Prior sources: Turn04 fixed commit d20b32e1547aee2f08b440d56cceb47ab16dc4b7,
preprint equations(4) and small-closed-set theorem. The source reconstructs cycles
from coefficient words and excludes every closed set of size at most5. We do not
rerun that enumeration. Thread search found no explicit all-cofactor-one case.
Web queries: "Erdos Straus" "prime" "cycle" "cofactor";
"Erdos Straus" "p+q" "4" prime cycles. No priority claim follows from this search.

Input: all primitive binary sigma necklaces of lengths6 through18, cofactors1.
Canonical rotation removes duplicates but not reflection. Reconstruct with exact
integer arithmetic; require hard residue p mod840 in {1,121,169,289,361,529}, prime p,
distinct prime q_i<p, correct sigma types and Legendre symbols, every edge equation.
Then verify all allowed sources, all actual divisors, and closure.
Stop: first valid closed failed cycle, otherwise finish length18. CPU on mini.

Success falsifies the stronger claim that every closed set contains a successful
source, not necessarily least-root Qleast-square and not Erdos-Straus.
No example only rules out this bounded structural family, not all cycles or primes.
If an exact modular obstruction emerges, derive it separately; enumeration cannot
prove it for arbitrary lengths. This is a structural candidate test, not expansion
of the known numerical verification range of Erdos-Straus.
