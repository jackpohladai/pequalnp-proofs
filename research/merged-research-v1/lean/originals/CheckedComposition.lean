import ParityExtraction
import StalledParity
import RankObstruction
import GuardedHall
import PairedUnion

/-! # Checked component imports and the project CNF semantics -/

#check ParityExtraction.replace_parity_subcollection
#check PEqualNP.Outside.StalledParity.padded_satisfiable_iff
#check PEqualNP.Outside.RankObstruction.factorization_width_bound
#check PEqualNP.Outside.GuardedHall.guarded_hall_projection
#check PEqualNP.Outside.PairedUnion.certificate_branch

namespace PEqualNP.Outside.CheckedComposition

open PEqualNP.Search

theorem literalValue_eq_project (assignment : Assignment) (literal : Literal) :
    ParityExtraction.literalValue assignment literal = Literal.eval assignment literal := by
  obtain ⟨index, polarity⟩ := literal
  cases polarity <;> cases h : assignment index <;>
    simp [ParityExtraction.literalValue, Literal.eval, h]

theorem clauseValue_eq_project (assignment : Assignment) (clause : Clause) :
    ParityExtraction.clauseValue assignment clause = Clause.eval assignment clause := by
  have literals : ParityExtraction.literalValue assignment = Literal.eval assignment :=
    funext (literalValue_eq_project assignment)
  simp only [ParityExtraction.clauseValue, Clause.eval, literals]

theorem cnfValue_eq_project (assignment : Assignment) (formula : CNF) :
    ParityExtraction.cnfValue assignment formula = CNF.eval assignment formula := by
  have clauses : ParityExtraction.clauseValue assignment = Clause.eval assignment :=
    funext (clauseValue_eq_project assignment)
  simp only [ParityExtraction.cnfValue, CNF.eval, clauses]

/-- Exact replacement can be applied directly to the project's CNF evaluation. -/
theorem project_parity_replacement (assignment : Assignment) (scope : List Nat)
    (masks : List (List Bool)) (blocked : Bool)
    (covers : ∀ mask, mask ∈ masks ↔
      mask.length = scope.length ∧ ParityExtraction.parity mask = blocked)
    (original other : CNF)
    (selection : original.Perm (masks.map (ParityExtraction.exclude scope) ++ other)) :
    CNF.eval assignment original =
      ((ParityExtraction.parity (scope.map assignment) == !blocked) &&
        CNF.eval assignment other) := by
  simpa only [cnfValue_eq_project] using
    ParityExtraction.replace_parity_subcollection assignment scope masks blocked covers
      original other selection

#print axioms literalValue_eq_project
#print axioms clauseValue_eq_project
#print axioms cnfValue_eq_project
#print axioms project_parity_replacement

end PEqualNP.Outside.CheckedComposition
