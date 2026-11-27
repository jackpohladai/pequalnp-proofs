import MatchingCertificates
import CheckedOutputProjection

namespace PEqualNP.Outside.MatchingCertificates
open PEqualNP.Search
open PEqualNP.Outside.GuardedHall
open PEqualNP.Outside.DualHorn
open PEqualNP.Outside.SparseDualHornAlgorithm
open PEqualNP.Outside.GuardedCNFEncoding

variable {r h : Nat}

theorem accepted_success_encoded_sat (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (positive : ∀ i, Positive (guards i))
    (edge : Edge r h → Nat) (injective : Function.Injective edge)
    (retainedPrivate : PrivateFromCNF edge F)
    (guardsPrivate : ∀ i, PrivateFromClause edge (guards i))
    (T : Finset Nat) (solved : checkedSolve F = some (some T))
    (certificate : SuccessCertificate r h)
    (accepted : successCheck N (fun i => Clause.eval (state (support F) T) (guards i))
      certificate = true) : Satisfiable (encode F N guards edge) := by
  apply (encoded_sat_at_checked_output F N guards positive edge injective
    retainedPrivate guardsPrivate T solved).mpr
  exact accepted_success_has_matching N _ certificate accepted

theorem accepted_failure_encoded_unsat (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (positive : ∀ i, Positive (guards i))
    (edge : Edge r h → Nat) (injective : Function.Injective edge)
    (retainedPrivate : PrivateFromCNF edge F)
    (guardsPrivate : ∀ i, PrivateFromClause edge (guards i))
    (T : Finset Nat) (solved : checkedSolve F = some (some T))
    (S : Finset (Fin r))
    (accepted : failureCheck N (fun i => Clause.eval (state (support F) T) (guards i)) S = true) :
    ¬ Satisfiable (encode F N guards edge) := by
  intro model
  apply accepted_failure_no_matching N _ S accepted
  exact (encoded_sat_at_checked_output F N guards positive edge injective
    retainedPrivate guardsPrivate T solved).mp model

#print axioms accepted_success_encoded_sat
#print axioms accepted_failure_encoded_unsat
end PEqualNP.Outside.MatchingCertificates
