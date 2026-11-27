import MatchingLoop
import PathCarryingSearch

namespace PEqualNP.Outside.MatchingPathComposition

open PEqualNP.Outside.MatchingAugmentation
open PEqualNP.Outside.MatchingCertificates
open PEqualNP.Outside.MatchingSearch
open PEqualNP.Outside.MatchingLoop
open PEqualNP.Outside.MatchingPaths

variable {r h : Nat}

/-- The executable composition uses the existing drained-cut search for
failure and the path-carrying search for a free-hole round. The loop replays
the path and checks root coverage before using the new matching state. -/
def solve (adj : Fin r → List (Fin h)) (g : Fin r → Bool) : Result r h :=
  solveFromBfs adj g (fun s root => searchPath adj s root r)

theorem solve_accepted (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    (solve adj g).Accepted (fun i => (adj i).toFinset) g :=
  solveFromBfs_checked adj g (fun s root => searchPath adj s root r)

theorem solve_sound (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    (solve adj g).Correct (fun i => (adj i).toFinset) g :=
  Result.accepted_correct (solve_accepted adj g)

/-- A returned path with the public search invariants passes the loop's
independent replay and root-coverage checks. -/
theorem returned_path_replays (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (s : State r h) (root : Fin r) (hole : Fin h) (rows : List (Fin r))
    (valid : Valid (fun i => (adj i).toFinset) s) (active : ActiveOnly g s)
    (rootActive : g root = false) (found : searchPath adj s root r = some (hole, rows)) :
    (tryPath (fun i => (adj i).toFinset) g s root hole rows).isSome = true := by
  obtain ⟨next, replayed, rootCovered⟩ := searchPath_sound adj s root r hole rows valid found
  have pathActive : rows.all (fun i => !g i) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    have checked := searchPath_active adj s g root r hole rows active rootActive found i hi
    simp [checked]
  have covered : (next.rowMatch root).isSome = true := by
    simpa [matchedRows] using rootCovered
  simp [tryPath, pathActive, replayed, covered]

/-- It remains to link the two search implementations on free-hole rounds.
This conditional theorem isolates that completeness obligation. -/
theorem solve_definite_if_path_found (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (findsFreePath : ∀ s root hole,
      Valid (fun i => (adj i).toFinset) s → ActiveOnly g s →
      g root = false → s.rowMatch root = none →
      explore adj s.owner r (Frontier.start root) = .free hole →
      ∃ result, searchPath adj s root r = some result) :
    solve adj g ≠ .inconclusive := by
  apply solveFromBfs_no_inconclusive adj g (fun s root => searchPath adj s root r)
  intro s root hole valid active rootActive unmatched BFS
  obtain ⟨⟨free, rows⟩, found⟩ := findsFreePath s root hole valid active rootActive unmatched BFS
  exact ⟨free, rows, found, returned_path_replays adj g s root free rows valid active rootActive found⟩

#print axioms returned_path_replays
#print axioms solve_definite_if_path_found

#print axioms solve_accepted
#print axioms solve_sound

section Examples

private def describe : Result r h → String × List (Option Nat)
  | .success certificate =>
    ("success", (List.finRange r).map (fun i => (certificate i).map Fin.val))
  | .failure cut =>
    ("failure", ((List.finRange r).filter (fun i => i ∈ cut)).map (fun i => some i.val))
  | .inconclusive => ("inconclusive", [])

private def twoRows (row : Fin 2) : List (Fin 2) :=
  if row = 0 then [0, 1] else [0]

private def diamond (row : Fin 4) : List (Fin 4) :=
  if row = 0 then [0, 1, 2] else if row = 1 then [1, 2] else if row = 2 then [2, 3] else [0, 1]

private def ladder (row : Fin 5) : List (Fin 5) :=
  if row = 0 then [0, 1] else if row = 1 then [1, 2] else
  if row = 2 then [2, 3] else if row = 3 then [3, 4] else [0]

private def properCut (row : Fin 4) : List (Fin 4) :=
  if row = 0 then [0, 1] else if row = 1 then [0] else if row = 2 then [1] else [2, 3]

example : describe (solve twoRows (fun _ => false)) = ("success", [some 1, some 0]) := by decide
example : describe (solve diamond (fun _ => false)) =
    ("success", [some 2, some 1, some 3, some 0]) := by decide
example : describe (solve ladder (fun _ => false)) =
    ("success", [some 1, some 2, some 3, some 4, some 0]) := by decide
example : describe (solve properCut (fun _ => false)) =
    ("failure", [some 0, some 1, some 2]) := by decide
example : describe (solve twoRows (fun i => i == 0)) = ("success", [none, some 0]) := by decide
example : describe (solve (fun (_ : Fin 1) => ([] : List (Fin 0))) (fun _ => false)) =
    ("failure", [some 0]) := by decide

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
end PEqualNP.Outside.MatchingPathComposition
