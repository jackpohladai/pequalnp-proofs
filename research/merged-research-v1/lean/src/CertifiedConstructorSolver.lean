import CertifiedCNFConclusions
import CertificateEdges
import ExecutableEdgeLift

namespace PEqualNP.Outside.CertifiedConstructorSolver
open PEqualNP.Search
open PEqualNP.Outside.DualHorn
open PEqualNP.Outside.SparseDualHornAlgorithm
open PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Outside.MatchingCertificates

variable {r h : Nat}

inductive Certificate (r h : Nat) where
  | success (candidate : SuccessCertificate r h)
  | failure (rows : Finset (Fin r))

inductive Result where
  | unsupported
  | invalidCertificate
  | unsat
  | sat (assignment : Assignment)

def InputConditions (offset : Nat) (F : CNF) (guards : Fin r → Clause) : Prop :=
  (∀ C ∈ F, ∀ l ∈ C, l.1 < offset) ∧
  (∀ i, ∀ l ∈ guards i, l.2 = true ∧ l.1 < offset)

def inputCheck (offset : Nat) (F : CNF) (guards : Fin r → Clause) : Bool :=
  F.all (fun C => C.all (fun l => decide (l.1 < offset))) &&
  (List.finRange r).all (fun i => (guards i).all (fun l => l.2 && decide (l.1 < offset)))

theorem inputCheck_iff (offset : Nat) (F : CNF) (guards : Fin r → Clause) :
    inputCheck offset F guards = true ↔ InputConditions offset F guards := by
  simp only [inputCheck, InputConditions, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_true_left, decide_eq_true_eq]

/-- A supplied certificate is checked at the actual computed retained model. -/
def processCertificate (offset : Nat) (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (T : Finset Nat) (certificate : Certificate r h) : Result :=
  let visible := state (support F) T
  let g := fun i => Clause.eval visible (guards i)
  match certificate with
  | .success candidate =>
      if successCheck N g candidate then
        .sat (liftAssignment offset visible (certificateEdges g candidate))
      else .invalidCertificate
  | .failure rows =>
      if failureCheck N g rows then .unsat else .invalidCertificate

/-- Certify the explicit fresh guarded-CNF constructor. No matching search
is hidden here: the success or failure certificate is a supplied input. -/
def certify (offset : Nat) (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (certificate : Certificate r h) : Result :=
  if inputCheck offset F guards then
    match checkedSolve F with
    | none => .unsupported
    | some none => .unsat
    | some (some T) => processCertificate offset F N guards T certificate
  else .unsupported

def Correct (encoded : CNF) : Result → Prop
  | .unsupported => True
  | .invalidCertificate => True
  | .unsat => ¬ Satisfiable encoded
  | .sat assignment => CNF.eval assignment encoded = true

theorem processCertificate_correct (offset : Nat) (F : CNF)
    (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (inputs : InputConditions offset F guards) (T : Finset Nat)
    (solved : checkedSolve F = some (some T)) (certificate : Certificate r h) :
    Correct (encode F N guards (freshEdge offset))
      (processCertificate offset F N guards T certificate) := by
  have positive : ∀ i, Positive (guards i) := fun i l hl => (inputs.2 i l hl).1
  have guardsBelow : ∀ i, ∀ l ∈ guards i, l.1 < offset := fun i l hl => (inputs.2 i l hl).2
  cases certificate with
  | success candidate =>
      by_cases accepted : successCheck N
          (fun i => Clause.eval (state (support F) T) (guards i)) candidate = true
      · simp only [processCertificate, accepted, ↓reduceIte, Correct]
        have retained := (checkedSolve_result_correct F (some T) solved).2
        have witness := accepted_certificate_edges N
          (fun i => Clause.eval (state (support F) T) (guards i)) candidate accepted
        exact lift_witness offset F N guards (state (support F) T) _
          inputs.1 guardsBelow retained.1 witness.2.1
          (fun i j k _ _ => witness.2.2 i j k)
      · simp [processCertificate, accepted, Correct]
  | failure rows =>
      by_cases accepted : failureCheck N
          (fun i => Clause.eval (state (support F) T) (guards i)) rows = true
      · simp only [processCertificate, accepted, ↓reduceIte, Correct]
        apply accepted_failure_encoded_unsat F N guards positive (freshEdge offset)
          (freshEdge_injective offset) _ _ T solved rows accepted
        · intro C hC
          exact freshEdge_private offset C (inputs.1 C hC)
        · intro i
          exact freshEdge_private offset (guards i) (guardsBelow i)
      · simp [processCertificate, accepted, Correct]

/-- Unconditional soundness: all class, positivity and separation premises
needed by the composed theorems are enforced by the executable checks. -/
theorem certify_correct (offset : Nat) (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (certificate : Certificate r h) :
    Correct (encode F N guards (freshEdge offset)) (certify offset F N guards certificate) := by
  by_cases inputs : inputCheck offset F guards = true
  · have valid := (inputCheck_iff offset F guards).mp inputs
    cases solved : checkedSolve F with
    | none => simp [certify, inputs, solved, Correct]
    | some result =>
        cases result with
        | none =>
            simpa [certify, inputs, solved, Correct] using
              checked_unsat_excludes_encoding F N guards (freshEdge offset) solved
        | some T =>
            simpa [certify, inputs, solved] using
              processCertificate_correct offset F N guards valid T solved certificate
  · simp [certify, inputs, Correct]

theorem returned_sat_is_model (offset : Nat) (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (certificate : Certificate r h) (assignment : Assignment)
    (returned : certify offset F N guards certificate = .sat assignment) :
    CNF.eval assignment (encode F N guards (freshEdge offset)) = true := by
  simpa [returned, Correct] using certify_correct offset F N guards certificate

theorem returned_unsat_excludes_models (offset : Nat) (F : CNF)
    (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (certificate : Certificate r h) (returned : certify offset F N guards certificate = .unsat) :
    ¬ Satisfiable (encode F N guards (freshEdge offset)) := by
  simpa [returned, Correct] using certify_correct offset F N guards certificate

#print axioms inputCheck
#print axioms processCertificate
#print axioms certify
#print axioms inputCheck_iff
#print axioms processCertificate_correct
#print axioms certify_correct
#print axioms returned_sat_is_model
#print axioms returned_unsat_excludes_models
end PEqualNP.Outside.CertifiedConstructorSolver
