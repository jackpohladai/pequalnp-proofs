import AutomaticConstructor
import RawMatchingCompleteness

namespace PEqualNP.Outside.AutomaticConstructor
open PEqualNP.Search
open PEqualNP.Outside.SparseDualHornAlgorithm
open PEqualNP.Outside.CertifiedConstructorSolver
open PEqualNP.Outside.MatchingLoop

variable {r h : Nat}

def Decisive (result : Outcome) : Prop :=
  result = .unsat ∨ ∃ assignment, result = .sat assignment

theorem Decisive.ne_inconclusive {result : Outcome} (decisive : Decisive result) :
    result ≠ .inconclusive := by
  rcases decisive with same | ⟨assignment, same⟩ <;> simp [same]

theorem Decisive.ne_unsupported {result : Outcome} (decisive : Decisive result) :
    result ≠ .unsupported := by
  rcases decisive with same | ⟨assignment, same⟩ <;> simp [same]

/-- The internal matcher supplies a valid certificate in both branches.
No certificate or successful search is assumed as an input. -/
theorem useMatching_decisive (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (guards : Fin r → Clause) (T : Finset Nat) :
    Decisive (useMatching offset F adj guards T) := by
  have accepted := RawMatchingPathComposition.solve_accepted adj
    (fun i => Clause.eval (state (support F) T) (guards i))
  have definite := RawMatchingPathComposition.solve_definite adj
    (fun i => Clause.eval (state (support F) T) (guards i))
  unfold useMatching
  cases found : RawMatchingPathComposition.solve adj
      (fun i => Clause.eval (state (support F) T) (guards i)) with
  | inconclusive => exact False.elim (definite found)
  | success certificate =>
      have checked : PEqualNP.Outside.MatchingCertificates.successCheck
          (fun i => (adj i).toFinset)
          (fun i => Clause.eval (state (support F) T) (guards i)) certificate = true := by
        simpa only [found, Result.Accepted] using accepted
      simp [processCertificate, checked, convertResult, Decisive]
  | failure rows =>
      have checked : PEqualNP.Outside.MatchingCertificates.failureCheck
          (fun i => (adj i).toFinset)
          (fun i => Clause.eval (state (support F) T) (guards i)) rows = true := by
        simpa only [found, Result.Accepted] using accepted
      simp [processCertificate, checked, convertResult, Decisive]

/-- Unsupported inputs may be rejected, but search cannot become inconclusive. -/
theorem solve_ne_inconclusive (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (guards : Fin r → Clause) : solve offset F adj guards ≠ .inconclusive := by
  by_cases inputs : inputCheck offset F guards = true
  · cases checked : checkedSolve F with
    | none => simp [solve, inputs, checked]
    | some result =>
        cases result with
        | none => simp [solve, inputs, checked]
        | some T =>
            simpa [solve, inputs, checked] using
              (useMatching_decisive offset F adj guards T).ne_inconclusive
  · simp [solve, inputs]

/-- The exact executable syntax and separation checks define supported input.
On that input, the outcome is either UNSAT or a concrete SAT assignment. -/
theorem supported_solve_decisive (offset : Nat) (F : CNF)
    (adj : Fin r → List (Fin h)) (guards : Fin r → Clause)
    (inputs : inputCheck offset F guards = true) (dual : dualHornCheck F = true) :
    Decisive (solve offset F adj guards) := by
  cases result : solveSparse F with
  | none => simp [solve, inputs, checkedSolve, dual, result, Decisive]
  | some T =>
      simpa [solve, inputs, checkedSolve, dual, result] using
        useMatching_decisive offset F adj guards T

theorem supported_solve_ne_unsupported (offset : Nat) (F : CNF)
    (adj : Fin r → List (Fin h)) (guards : Fin r → Clause)
    (inputs : inputCheck offset F guards = true) (dual : dualHornCheck F = true) :
    solve offset F adj guards ≠ .unsupported :=
  (supported_solve_decisive offset F adj guards inputs dual).ne_unsupported

#print axioms useMatching_decisive
#print axioms solve_ne_inconclusive
#print axioms supported_solve_decisive
#print axioms supported_solve_ne_unsupported
end PEqualNP.Outside.AutomaticConstructor
