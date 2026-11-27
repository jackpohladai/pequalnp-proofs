import PathCarryingSearch

namespace PEqualNP.Outside.MatchingPaths.Examples
open PEqualNP.Outside.MatchingAugmentation

def twoAdj (i : Fin 2) : List (Fin 2) := if i = 0 then [0, 1] else [0]
def oneMatched : State 2 2 :=
  ⟨fun i => if i = 0 then some 0 else none,
   fun k => if k = 0 then some 0 else none⟩
def inconsistent : State 2 2 :=
  ⟨fun _ => none, fun k => if k = 0 then some 0 else none⟩

theorem forced_alternating_path :
    searchPath twoAdj oneMatched 1 2 = some (1, [0, 1]) := by decide

theorem replay_covers_selected_root :
    ((augmentRows (fun i => (twoAdj i).toFinset) [0, 1] oneMatched 1).map
      (fun s => ((s.rowMatch 0).map Fin.val, (s.rowMatch 1).map Fin.val))) =
      some (some 1, some 0) := by decide

theorem zero_fuel_inconclusive : searchPath twoAdj oneMatched 1 0 = none := by decide

theorem empty_neighbors_inconclusive :
    searchPath (fun _ : Fin 1 => ([] : List (Fin 0))) empty 0 1 = none := by decide

theorem malformed_raw_path_is_rejected :
    rawSearchPath twoAdj inconsistent 1 2 = some (1, [0, 1]) ∧
    searchPath twoAdj inconsistent 1 2 = none := by decide

theorem repeated_row_path_rejected :
    ¬ ReturnOK (fun i => (twoAdj i).toFinset) oneMatched 1 1 [0, 0, 1] := by decide

theorem wrong_root_path_rejected :
    ¬ ReturnOK (fun i => (twoAdj i).toFinset) oneMatched 0 1 [0, 1] := by decide

def saturated : State 3 2 :=
  ⟨fun i => if i = 0 then some 0 else if i = 1 then some 1 else none,
   fun k => if k = 0 then some 0 else some 1⟩

theorem no_free_hole_inconclusive :
    searchPath (fun _ : Fin 3 => [0, 1]) saturated 2 3 = none := by decide

#print axioms forced_alternating_path
#print axioms replay_covers_selected_root
#print axioms malformed_raw_path_is_rejected
end PEqualNP.Outside.MatchingPaths.Examples
