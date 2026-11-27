import MatchingPathComposition
import RawPathInvariant

namespace PEqualNP.Outside.RawMatchingPathComposition

open PEqualNP.Outside.MatchingAugmentation
open PEqualNP.Outside.MatchingCertificates
open PEqualNP.Outside.MatchingSearch
open PEqualNP.Outside.MatchingLoop
open PEqualNP.Outside.MatchingPaths

variable {r h : Nat}

/-- The outer loop checks cuts and replays paths. The path finder visits only
explicit adjacency entries and omits the structural validator whose
decidable existential can iterate over all holes. -/
def solve (adj : Fin r → List (Fin h)) (g : Fin r → Bool) : Result r h :=
  solveFromBfs adj g (fun s root => rawSearchPath adj s root r)

theorem solve_accepted (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    (solve adj g).Accepted (fun i => (adj i).toFinset) g :=
  solveFromBfs_checked adj g (fun s root => rawSearchPath adj s root r)

theorem solve_sound (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    (solve adj g).Correct (fun i => (adj i).toFinset) g :=
  Result.accepted_correct (solve_accepted adj g)

/-- A returned path with the public search invariants passes the loop's
independent replay and root-coverage checks. -/
theorem raw_returned_path_replays (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (s : State r h) (root : Fin r) (hole : Fin h) (rows : List (Fin r))
    (valid : Valid (fun i => (adj i).toFinset) s) (active : ActiveOnly g s)
    (rootActive : g root = false) (unmatched : s.rowMatch root = none)
    (found : rawSearchPath adj s root r = some (hole, rows)) :
    (tryPath (fun i => (adj i).toFinset) g s root hole rows).isSome = true := by
  have structural := rawSearchPath_certificate adj s valid root unmatched r hole rows found
  cases rows with
  | nil => exact False.elim structural
  | cons row tail =>
    obtain ⟨next, replay, covered⟩ :=
      follows_replay _ s valid root row tail structural.1 structural.2.1
        hole structural.2.2.1 structural.2.2.2
    have allActive : (row :: tail).all (fun i => !g i) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      have checked : g i = false := by
        rcases follows_rows _ s root (row :: tail) structural.1 i hi with same | matched
        · simpa [same] using rootActive
        · cases assigned : s.rowMatch i with
          | none => simp [assigned] at matched
          | some k => exact active i k assigned
      simp [checked]
    have rootCovered : (next.rowMatch root).isSome = true := by
      simpa [matchedRows] using covered
    simp [tryPath, allActive, replay, rootCovered]

/-- Agreement at active unmatched roots in valid active-only states gives
exactly the same result of the finite outer loop. -/
theorem visit_eq (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (left right : State r h → Fin r → Proposal r h)
    (agree : ∀ s i, Valid N s → ActiveOnly g s → g i = false → s.rowMatch i = none →
      left s i = right s i)
    (todo : List (Fin r)) (s : State r h) (valid : Valid N s) (active : ActiveOnly g s) :
    visit N g left todo s = visit N g right todo s := by
  induction todo generalizing s with
  | nil => rfl
  | cons root todo ih =>
    by_cases need : g root = false ∧ s.rowMatch root = none
    · have same := agree s root valid active need.1 need.2
      cases proposal : left s root with
      | inconclusive => simp [visit, need, proposal, ← same]
      | cut rows => simp [visit, need, proposal, ← same]
      | path hole rows =>
        cases replay : tryPath N g s root hole rows with
        | none => simp [visit, need, proposal, ← same, replay]
        | some next =>
          obtain ⟨nextValid, nextActive, _, _⟩ := tryPath_sound valid active replay
          simpa only [visit, ite_eq_left need, ← same, proposal, replay] using
            ih next nextValid nextActive
    · simpa only [visit, ite_eq_right need] using ih s valid active

/-- Equality from the empty state includes the actual matching or Hall cut. -/
theorem solve_eq_checked (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    solve adj g = MatchingPathComposition.solve adj g := by
  unfold solve MatchingPathComposition.solve solveFromBfs solveWith
  refine visit_eq _ g _ _ ?_ _ empty (empty_valid _) (empty_active_only g)
  intro s root valid _ _ unmatched
  cases outcome : explore adj s.owner r (Frontier.start root) <;>
    simp [proposeFromBfs, outcome, searchPath_eq_raw adj s valid root unmatched r]

/-- The conditional completeness statement needs only path discovery,
since every returned path replays correctly. -/
theorem solve_definite_if_path_found (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (findsFreePath : ∀ s root hole,
      Valid (fun i => (adj i).toFinset) s → ActiveOnly g s →
      g root = false → s.rowMatch root = none →
      explore adj s.owner r (Frontier.start root) = .free hole →
      ∃ result, rawSearchPath adj s root r = some result) :
    solve adj g ≠ .inconclusive := by
  apply solveFromBfs_no_inconclusive adj g (fun s root => rawSearchPath adj s root r)
  intro s root hole valid active rootActive unmatched BFS
  obtain ⟨⟨free, rows⟩, found⟩ := findsFreePath s root hole valid active rootActive unmatched BFS
  exact ⟨free, rows, found, raw_returned_path_replays adj g s root free rows valid active rootActive unmatched found⟩

#print axioms raw_returned_path_replays
#print axioms solve_definite_if_path_found
#print axioms visit_eq
#print axioms solve_eq_checked

#print axioms solve_accepted
#print axioms solve_sound

section Examples

private def describe : Result r h → String × List (Option Nat)
  | .success certificate =>
    ("success", (List.finRange r).map (fun i => (certificate i).map Fin.val))
  | .failure cut =>
    ("failure", ((List.finRange r).filter (fun i => i ∈ cut)).map (fun i => some i.val))
  | .inconclusive => ("inconclusive", [])

private def wide : Nat := 2 ^ 80

private def wideLeft : Fin (wide + 2) :=
  ⟨wide, Nat.lt_succ_of_lt (Nat.lt_succ_self wide)⟩

private def wideRight : Fin (wide + 2) :=
  ⟨wide + 1, Nat.lt_succ_self (wide + 1)⟩

private def wideAugment (row : Fin 2) : List (Fin (wide + 2)) :=
  if row = 0 then [wideLeft, wideRight] else [wideLeft]

-- Three explicit edges. Assigning the second row moves the first row to
-- the right index before the second row takes the left one.
example : describe (solve wideAugment (fun _ => false)) =
    ("success", [some (wide + 1), some wide]) := by decide

example : describe (solve (fun (_ : Fin 2) => [wideLeft]) (fun _ => false)) =
    ("failure", [some 0, some 1]) := by decide

/-- Exhaustive matching oracle used only for the tiny execution fixture. -/
private def oracle (adj : Fin r → List (Fin h)) : List (Fin r) → List (Fin h) → Bool
  | [], _ => true
  | row :: rows, used =>
    (adj row).any (fun hole => !used.contains hole && oracle adj rows (hole :: used))

private def agreement (r h edgeBits guardBits : Nat) : Bool :=
  let adj : Fin r → List (Fin h) := fun row =>
    (List.finRange h).filter (fun hole => edgeBits.testBit (row.val * h + hole.val))
  let g : Fin r → Bool := fun row => guardBits.testBit row.val
  let possible := oracle adj ((List.finRange r).filter (fun row => !g row)) []
  match solve adj g with
  | .success cert => possible && successCheck (fun i => (adj i).toFinset) g cert
  | .failure cut => !possible && failureCheck (fun i => (adj i).toFinset) g cut
  | .inconclusive => false

private def tinyResults : List Bool :=
  (List.range 4).flatMap fun r =>
  (List.range 4).flatMap fun h =>
  (List.range (2 ^ (r * h))).flatMap fun edges =>
  (List.range (2 ^ r)).map fun guards =>
    agreement r h edges guards

end Examples
end PEqualNP.Outside.RawMatchingPathComposition
