import AugmentingReassignment
import MatchingCertificates

namespace PEqualNP.Outside.MatchingAugmentation
open PEqualNP.Outside.MatchingCertificates
variable {r h : Nat}

def ActiveOnly (g : Fin r → Bool) (s : State r h) : Prop :=
  ∀ i k, s.rowMatch i = some k → g i = false

theorem move_active_only (g : Fin r → Bool) (s : State r h)
    (active : ActiveOnly g s) (i : Fin r) (k : Fin h) (newActive : g i = false) :
    ActiveOnly g (move s i k) := by
  intro j l assigned
  by_cases same : j = i
  · simpa [same] using newActive
  · exact active j l (by simpa [move, same] using assigned)

theorem augmentRows_active_only (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (path : List (Fin r)) (s : State r h) (k : Fin h) (out : State r h)
    (active : ActiveOnly g s) (pathActive : ∀ i ∈ path, g i = false)
    (returned : augmentRows N path s k = some out) : ActiveOnly g out := by
  induction path generalizing s k out with
  | nil => simp [augmentRows] at returned
  | cons i rest ih =>
      by_cases permitted : s.owner k = none ∧ k ∈ N i
      · simp only [augmentRows, ite_eq_left permitted] at returned
        have nextActive := move_active_only g s active i k (pathActive i (by simp))
        cases old : s.rowMatch i with
        | none =>
            by_cases final : rest = []
            · have same : move s i k = out := by simpa [old, final] using returned
              simpa [← same] using nextActive
            · simp [old, final] at returned
        | some previous =>
            exact ih (move s i k) previous out nextActive
              (fun j hj => pathActive j (List.mem_cons_of_mem i hj))
              (by simpa [old] using returned)
      · simp [augmentRows, permitted] at returned

/-- Once an actual valid partial matching covers all active rows, its row
table is an accepted success certificate. Outer-loop coverage is still to prove. -/
theorem full_coverage_accepted (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (s : State r h) (valid : Valid N s)
    (covered : ∀ i, g i = false → i ∈ matchedRows s) :
    successCheck N g s.rowMatch = true := by
  have rows : ∀ i, g i = false → ∃ k, s.rowMatch i = some k ∧ k ∈ N i := by
    intro i active
    have hi := covered i active
    cases assigned : s.rowMatch i with
    | none => simp [matchedRows, assigned] at hi
    | some k => exact ⟨k,rfl,valid.2 i k assigned⟩
  apply (successCheck_iff N g s.rowMatch).mpr
  refine ⟨rows, ?_⟩
  intro i j hi hj same
  obtain ⟨k, assigned, _⟩ := rows i hi
  exact assigned_rows_injective s valid.1 i j k assigned (same.symm.trans assigned)

#print axioms move_active_only
#print axioms augmentRows_active_only
#print axioms full_coverage_accepted
end PEqualNP.Outside.MatchingAugmentation
