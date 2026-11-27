import RawMatchingPathComposition
import CertifiedConstructorSolver

namespace PEqualNP.Outside.AutomaticConstructor
open PEqualNP.Search
open PEqualNP.Outside.SparseDualHornAlgorithm
open PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Outside.CertifiedConstructorSolver

variable {r h : Nat}

inductive Outcome where
  | unsupported
  | inconclusive
  | unsat
  | sat (assignment : Assignment)

def Correct (encoded : CNF) : Outcome → Prop
  | .unsupported => True
  | .inconclusive => True
  | .unsat => ¬ Satisfiable encoded
  | .sat assignment => CNF.eval assignment encoded = true

def convertResult : CertifiedConstructorSolver.Result → Outcome
  | .unsupported => .unsupported
  | .invalidCertificate => .inconclusive
  | .unsat => .unsat
  | .sat assignment => .sat assignment

theorem convert_correct (encoded : CNF) (result : CertifiedConstructorSolver.Result)
    (checked : CertifiedConstructorSolver.Correct encoded result) :
    Correct encoded (convertResult result) := by
  cases result <;> exact checked

def encoded (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (guards : Fin r → Clause) : CNF :=
  encode F (fun i => (adj i).toFinset) guards (freshEdge offset)

/-- Compute a matching certificate at the actual retained model. Neither a
matching witness nor a deficient row set is supplied by the caller. -/
def useMatching (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (guards : Fin r → Clause) (T : Finset Nat) : Outcome :=
  match RawMatchingPathComposition.solve adj
      (fun i => Clause.eval (state (support F) T) (guards i)) with
  | .inconclusive => .inconclusive
  | .success certificate => convertResult
      (processCertificate offset F (fun i => (adj i).toFinset) guards T (.success certificate))
  | .failure rows => convertResult
      (processCertificate offset F (fun i => (adj i).toFinset) guards T (.failure rows))

theorem useMatching_correct (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (guards : Fin r → Clause) (T : Finset Nat)
    (inputs : InputConditions offset F guards)
    (solved : checkedSolve F = some (some T)) :
    Correct (encoded offset F adj guards) (useMatching offset F adj guards T) := by
  unfold useMatching
  cases found : RawMatchingPathComposition.solve adj
      (fun i => Clause.eval (state (support F) T) (guards i)) with
  | inconclusive => exact True.intro
  | success certificate =>
      exact convert_correct _ _
        (processCertificate_correct offset F _ guards inputs T solved (.success certificate))
  | failure rows =>
      exact convert_correct _ _
        (processCertificate_correct offset F _ guards inputs T solved (.failure rows))

/-- Automatic solver for the explicit constructor class. All syntax, guard
positivity and variable-separation checks remain in the public interface. -/
def solve (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (guards : Fin r → Clause) : Outcome :=
  if inputCheck offset F guards then
    match checkedSolve F with
    | none => .unsupported
    | some none => .unsat
    | some (some T) => useMatching offset F adj guards T
  else .unsupported

theorem solve_correct (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (guards : Fin r → Clause) :
    Correct (encoded offset F adj guards) (solve offset F adj guards) := by
  by_cases inputs : inputCheck offset F guards = true
  · have valid := (inputCheck_iff offset F guards).mp inputs
    cases solved : checkedSolve F with
    | none => simp [solve, inputs, solved, Correct]
    | some result =>
        cases result with
        | none =>
            simpa [solve, inputs, solved, Correct, encoded] using
              checked_unsat_excludes_encoding F (fun i => (adj i).toFinset) guards
                (freshEdge offset) solved
        | some T =>
            simpa [solve, inputs, solved] using
              useMatching_correct offset F adj guards T valid solved
  · simp [solve, inputs, Correct]

theorem returned_sat_is_model (offset : Nat) (F : CNF)
    (adj : Fin r → List (Fin h)) (guards : Fin r → Clause) (assignment : Assignment)
    (returned : solve offset F adj guards = .sat assignment) :
    CNF.eval assignment (encoded offset F adj guards) = true := by
  simpa [returned, Correct] using solve_correct offset F adj guards

theorem returned_unsat_excludes_models (offset : Nat) (F : CNF)
    (adj : Fin r → List (Fin h)) (guards : Fin r → Clause)
    (returned : solve offset F adj guards = .unsat) :
    ¬ Satisfiable (encoded offset F adj guards) := by
  simpa [returned, Correct] using solve_correct offset F adj guards

#print axioms solve_correct
#print axioms returned_sat_is_model
#print axioms returned_unsat_excludes_models
end PEqualNP.Outside.AutomaticConstructor
