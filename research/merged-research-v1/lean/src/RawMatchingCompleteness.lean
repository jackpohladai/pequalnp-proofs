import RawMatchingPathComposition
import SearchCorrespondence

namespace PEqualNP.Outside.RawMatchingPathComposition

open PEqualNP.Outside.GuardedHall
open PEqualNP.Outside.MatchingCertificates
open PEqualNP.Outside.MatchingLoop

variable {r h : Nat}

/-- Removing the structural runtime test preserves the complete result of
the matching solver. The plain BFS and the path-carrying BFS agree on
free-hole detection, so the executable loop always returns a certificate. -/
theorem solve_definite (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    solve adj g ≠ .inconclusive := by
  rw [solve_eq_checked adj g]
  exact MatchingCorrespondence.solve_definite adj g

/-- Total certificate correctness for the concrete typed adjacency input. -/
theorem solve_total_correct (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    let N := fun i => (adj i).toFinset
    match solve adj g with
    | .success certificate => successCheck N g certificate = true ∧ HasMatching N g
    | .failure cut => failureCheck N g cut = true ∧ ¬ HasMatching N g
    | .inconclusive => False := by
  have accepted := solve_accepted adj g
  have correct := solve_sound adj g
  cases result : solve adj g with
  | success certificate =>
    exact ⟨by simpa only [result, Result.Accepted] using accepted,
      by simpa only [result, Result.Correct] using correct⟩
  | failure cut =>
    exact ⟨by simpa only [result, Result.Accepted] using accepted,
      by simpa only [result, Result.Correct] using correct⟩
  | inconclusive => exact solve_definite adj g result

#print axioms solve_definite
#print axioms solve_total_correct

end PEqualNP.Outside.RawMatchingPathComposition
