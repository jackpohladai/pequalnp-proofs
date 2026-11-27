import FreshGuardedCNF
import CheckedDualHorn
import GreatestGuard

namespace PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Search
open PEqualNP.Outside.GuardedHall
open PEqualNP.Outside.DualHorn
open PEqualNP.Outside.SparseDualHornAlgorithm

variable {r h : Nat}

/-- The actual checked retained solver result determines the complete
constructed CNF's matching question, for positive guard clauses. -/
theorem encoded_sat_at_checked_output (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (positive : ∀ i, Positive (guards i))
    (edge : Edge r h → Nat) (injective : Function.Injective edge)
    (retainedPrivate : PrivateFromCNF edge F)
    (guardsPrivate : ∀ i, PrivateFromClause edge (guards i))
    (T : Finset Nat) (success : checkedSolve F = some (some T)) :
    Satisfiable (encode F N guards edge) ↔
      HasMatching N (fun i => Clause.eval (state (support F) T) (guards i)) := by
  obtain ⟨dual, correct⟩ := checkedSolve_result_correct F (some T) success
  change CNF.eval (state (support F) T) F = true ∧
    Dominates F (state (support F) T) at correct
  have monotone : PEqualNP.Outside.GreatestGuard.GuardsMonotone
      (fun σ : Assignment => fun i => Clause.eval σ (guards i)) :=
    positive_guard_family_monotone guards positive
  have projection := PEqualNP.Outside.GreatestGuard.greatest_matching_iff_feasible_extension
    {σ : Assignment | CNF.eval σ F = true} N
    (fun σ : Assignment => fun i => Clause.eval σ (guards i)) monotone
    (state (support F) T) correct.1 correct.2
  exact (encoded_sat_iff_private_edges F N guards edge injective retainedPrivate guardsPrivate).trans
    projection.symm

theorem checked_unsat_excludes_encoding (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (edge : Edge r h → Nat)
    (unsat : checkedSolve F = some none) : ¬ Satisfiable (encode F N guards edge) := by
  have correct := (checkedSolve_result_correct F none unsat).2
  rintro ⟨σ, hs⟩
  exact correct ⟨σ, ((encode_eval F N guards edge σ).mp hs).1⟩

#print axioms encoded_sat_at_checked_output
#print axioms checked_unsat_excludes_encoding
end PEqualNP.Outside.GuardedCNFEncoding
