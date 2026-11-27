import DualHorn
import GreatestGuard

namespace PEqualNP.Outside.DualHornGreatestGuard

open PEqualNP.Search
open PEqualNP.Outside.DualHorn
open PEqualNP.Outside.GuardedHall

variable {R H : Type*} [Finite R] [DecidableEq R] [DecidableEq H]

/-- The previously assumed greatest-feasible and monotone-guard premises are
derived here from concrete dual-Horn retained syntax and positive guards. -/
theorem restricted_extension_iff_matching {n : Nat} (F : CNF)
    (dual : IsDualHorn F) (bounded : VariablesBelow F n)
    (satisfiable : Satisfiable F) (N : R → Finset H) (guards : R → Clause)
    (positive : ∀ i, Positive (guards i)) :
    ∃ star : Assignment, CNF.eval star F = true ∧
      ((∃ σ : Assignment, CNF.eval σ F = true ∧
        HasPrivateEdges N (fun i => Clause.eval σ (guards i))) ↔
        HasMatching N (fun i => Clause.eval star (guards i))) := by
  obtain ⟨star, model, greatest⟩ := exists_greatest_model F dual bounded satisfiable
  let Models : Set Assignment := {σ | CNF.eval σ F = true}
  let g : Assignment → R → Bool := fun σ i => Clause.eval σ (guards i)
  have monotone : PEqualNP.Outside.GreatestGuard.GuardsMonotone g :=
    positive_guard_family_monotone guards positive
  exact ⟨star, model,
    (PEqualNP.Outside.GreatestGuard.greatest_matching_iff_feasible_extension
      Models N g monotone star model greatest).symm⟩

theorem retained_unsatisfiable_excludes_extension (F : CNF)
    (unsatisfiable : ¬ Satisfiable F) (N : R → Finset H) (guards : R → Clause) :
    ¬ ∃ σ : Assignment, CNF.eval σ F = true ∧
      HasPrivateEdges N (fun i => Clause.eval σ (guards i)) := by
  rintro ⟨σ, model, _⟩
  exact unsatisfiable ⟨σ, model⟩

#print axioms restricted_extension_iff_matching
#print axioms retained_unsatisfiable_excludes_extension

end PEqualNP.Outside.DualHornGreatestGuard
