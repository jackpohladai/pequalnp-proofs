import ActiveAugmentation
import BfsClosure

namespace PEqualNP.Outside.MatchingAugmentation
open PEqualNP.Outside.MatchingSearch
open PEqualNP.Outside.MatchingCertificates
open PEqualNP.Outside.GuardedHall
variable {r h : Nat}

theorem empty_active_only (g : Fin r → Bool) : ActiveOnly g (empty : State r h) := by
  intro i k assigned
  simp [empty] at assigned

theorem initial_invariants (N : Fin r → Finset (Fin h)) (g : Fin r → Bool) :
    Valid N (empty : State r h) ∧ ActiveOnly g (empty : State r h) :=
  ⟨empty_valid N, empty_active_only g⟩

theorem typed_bfs_full_budget (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (s : State r h) (valid : Valid (fun i => (adj i).toFinset) s)
    (active : ActiveOnly g s) (root : Fin r) (rootActive : g root = false) :
    explore adj s.owner r (Frontier.start root) ≠ .budget := by
  exact start_full_budget (fun k i owned => active i k ((valid.1 i k).mpr owned)) rootActive

theorem typed_bfs_failure (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (s : State r h) (valid : Valid (fun i => (adj i).toFinset) s)
    (active : ActiveOnly g s) (root : Fin r) (rootActive : g root = false)
    (unmatched : s.rowMatch root = none) (t : Frontier r h)
    (out : explore adj s.owner r (Frontier.start root) = .exhausted t) :
    failureCheck (fun i => (adj i).toFinset) g t.reached = true ∧
      ¬ HasMatching (fun i => (adj i).toFinset) g := by
  exact drained_bfs_certificate r rootActive unmatched
    (fun k i owned => (valid.1 i k).mpr owned) active out

/-- A free outcome still needs parent/path reconstruction before it can be
passed to augmentRows. This theorem deliberately claims only what BFS supplies. -/
theorem typed_bfs_free_hole (adj : Fin r → List (Fin h)) (s : State r h)
    (root : Fin r) (hole : Fin h)
    (out : explore adj s.owner r (Frontier.start root) = .free hole) :
    (∃ row, hole ∈ adj row) ∧ s.owner hole = none :=
  explore_free_hole r out

#print axioms initial_invariants
#print axioms typed_bfs_full_budget
#print axioms typed_bfs_failure
#print axioms typed_bfs_free_hole
end PEqualNP.Outside.MatchingAugmentation
