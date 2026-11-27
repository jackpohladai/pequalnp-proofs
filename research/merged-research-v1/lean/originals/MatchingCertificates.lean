import GuardedHall

namespace PEqualNP.Outside.MatchingCertificates
open PEqualNP.Outside.GuardedHall

variable {r h : Nat}

/-- Inactive rows may be omitted. In particular this permits no holes when
all guards are true, even if there are rows. -/
abbrev SuccessCertificate (r h : Nat) := Fin r → Option (Fin h)

def RowCondition (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (certificate : SuccessCertificate r h) (i : Fin r) : Prop :=
  g i = false → ∃ k, certificate i = some k ∧ k ∈ N i

def SuccessConditions (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (certificate : SuccessCertificate r h) : Prop :=
  (∀ i, RowCondition N g certificate i) ∧
  (∀ i j, g i = false → g j = false → certificate i = certificate j → i = j)

def rowCheck (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (certificate : SuccessCertificate r h) (i : Fin r) : Bool :=
  if g i then true else
    match certificate i with
    | none => false
    | some k => decide (k ∈ N i)

def successCheck (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (certificate : SuccessCertificate r h) : Bool :=
  (List.finRange r).all (rowCheck N g certificate) &&
  (List.finRange r).all (fun i => (List.finRange r).all (fun j =>
    decide (g i = false → g j = false → certificate i = certificate j → i = j)))

theorem rowCheck_iff (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (certificate : SuccessCertificate r h) (i : Fin r) :
    rowCheck N g certificate i = true ↔ RowCondition N g certificate i := by
  cases hg : g i <;> cases hc : certificate i <;>
    simp [rowCheck, RowCondition, hg, hc]

theorem successCheck_iff (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (certificate : SuccessCertificate r h) :
    successCheck N g certificate = true ↔ SuccessConditions N g certificate := by
  simp only [successCheck, SuccessConditions, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_true_left, rowCheck_iff, decide_eq_true_eq]

theorem accepted_success_has_matching (N : Fin r → Finset (Fin h))
    (g : Fin r → Bool) (certificate : SuccessCertificate r h)
    (accepted : successCheck N g certificate = true) : HasMatching N g := by
  classical
  obtain ⟨rows, unique⟩ := (successCheck_iff N g certificate).mp accepted
  have choices : ∀ i : Active g, ∃ k, certificate i.val = some k ∧ k ∈ N i.val :=
    fun i => rows i.val i.property
  let f : Active g → Fin h := fun i => Classical.choose (choices i)
  have hf : ∀ i, certificate i.val = some (f i) ∧ f i ∈ N i.val :=
    fun i => Classical.choose_spec (choices i)
  refine ⟨f, ?_, fun i => (hf i).2⟩
  intro i j same
  apply Subtype.ext
  apply unique i.val j.val i.property j.property
  rw [(hf i).1, (hf j).1, same]

def FailureConditions (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (S : Finset (Fin r)) : Prop :=
  (∀ i ∈ S, g i = false) ∧ (S.biUnion N).card < S.card

def failureCheck (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (S : Finset (Fin r)) : Bool :=
  (List.finRange r).all (fun i => decide (i ∈ S → g i = false)) &&
    decide ((S.biUnion N).card < S.card)

theorem failureCheck_iff (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (S : Finset (Fin r)) :
    failureCheck N g S = true ↔ FailureConditions N g S := by
  simp only [failureCheck, FailureConditions, Bool.and_eq_true, List.all_eq_true,
    List.mem_finRange, forall_true_left, decide_eq_true_eq]

theorem accepted_failure_no_matching (N : Fin r → Finset (Fin h))
    (g : Fin r → Bool) (S : Finset (Fin r))
    (accepted : failureCheck N g S = true) : ¬ HasMatching N g := by
  obtain ⟨active, deficient⟩ := (failureCheck_iff N g S).mp accepted
  intro matching
  obtain ⟨i, hi, hg⟩ := (guarded_cuts_iff_matching N g).mpr matching S deficient
  have hf := active i hi
  simp [hf] at hg

/-- Existence of a successful certificate, not a certificate search algorithm. -/
theorem matching_iff_success_certificate (N : Fin r → Finset (Fin h))
    (g : Fin r → Bool) :
    HasMatching N g ↔ ∃ certificate, successCheck N g certificate = true := by
  classical
  constructor
  · rintro ⟨f, injective, neighbors⟩
    let certificate : SuccessCertificate r h := fun i =>
      if hi : g i = false then some (f ⟨i, hi⟩) else none
    refine ⟨certificate, (successCheck_iff N g certificate).mpr ⟨?_, ?_⟩⟩
    · intro i hi
      exact ⟨f ⟨i, hi⟩, by simp [certificate, hi], neighbors ⟨i,hi⟩⟩
    · intro i j hi hj same
      have hs : f ⟨i,hi⟩ = f ⟨j,hj⟩ := by simpa [certificate, hi, hj] using same
      exact congrArg Subtype.val (injective hs)
  · rintro ⟨certificate, accepted⟩
    exact accepted_success_has_matching N g certificate accepted

/-- Hall yields a finite failure certificate when no matching exists.
This theorem proves certificate existence, not an executable search. -/
theorem no_matching_iff_failure_certificate (N : Fin r → Finset (Fin h))
    (g : Fin r → Bool) :
    (¬ HasMatching N g) ↔ ∃ S, failureCheck N g S = true := by
  classical
  constructor
  · intro noMatching
    have noCuts : ¬ GuardedCuts N g := fun cuts => noMatching ((guarded_cuts_iff_matching N g).mp cuts)
    obtain ⟨S, bad⟩ := not_forall.mp noCuts
    have deficient : (S.biUnion N).card < S.card := by
      by_contra hn
      exact bad (fun hc => False.elim (hn hc))
    have noneTrue : ¬ ∃ i ∈ S, g i = true := fun found => bad (fun _ => found)
    refine ⟨S, (failureCheck_iff N g S).mpr ⟨?_, deficient⟩⟩
    intro i hi
    cases hg : g i with
    | false => rfl
    | true => exact False.elim (noneTrue ⟨i, hi, hg⟩)
  · rintro ⟨S, accepted⟩
    exact accepted_failure_no_matching N g S accepted

theorem accepted_certificates_cannot_conflict (N : Fin r → Finset (Fin h))
    (g : Fin r → Bool) (certificate : SuccessCertificate r h) (S : Finset (Fin r))
    (yes : successCheck N g certificate = true) : failureCheck N g S ≠ true := by
  intro no
  exact accepted_failure_no_matching N g S no (accepted_success_has_matching N g certificate yes)

#print axioms successCheck_iff
#print axioms failureCheck_iff
#print axioms accepted_success_has_matching
#print axioms accepted_failure_no_matching
#print axioms matching_iff_success_certificate
#print axioms no_matching_iff_failure_certificate
#print axioms accepted_certificates_cannot_conflict
end PEqualNP.Outside.MatchingCertificates
