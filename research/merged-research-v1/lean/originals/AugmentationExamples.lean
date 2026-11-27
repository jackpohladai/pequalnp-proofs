import AugmentingReassignment

namespace PEqualNP.Outside.MatchingAugmentation

def exampleN (i : Fin 3) : Finset (Fin 3) :=
  if i = 0 then {0,1} else if i = 1 then {1,2} else {0}

def exampleState : State 3 3 where
  rowMatch := fun i => if i = 0 then some 0 else if i = 1 then some 1 else none
  owner := fun k => if k = 0 then some 0 else if k = 1 then some 1 else none

def observeRows (s : State 3 3) : List (Option Nat) :=
  (List.finRange 3).map (fun i => (s.rowMatch i).map Fin.val)

def replayRows : List (Option Nat) :=
  match augmentRows exampleN [1,0,2] exampleState 2 with
  | none => []
  | some out => observeRows out

example : Valid exampleN exampleState := by unfold Valid Consistent; decide
example : replayRows = [some 1,some 2,some 0] := by decide
example : (augmentRows exampleN [] exampleState 2).isNone = true := by decide
example : (augmentRows exampleN [1,0] exampleState 2).isNone = true := by decide
example : (augmentRows exampleN [1,0,2,1] exampleState 2).isNone = true := by decide
example : (augmentRows exampleN [0,2] exampleState 1).isNone = true := by decide
example : (augmentRows exampleN [0] exampleState 2).isNone = true := by decide
example : (matchedRows exampleState).card = 2 := by decide

#eval replayRows
#eval match augmentRows exampleN [1,0,2] exampleState 2 with
  | none => false
  | some out =>
      (List.finRange 3).all (fun i => (List.finRange 3).all (fun k =>
        decide ((out.rowMatch i = some k ↔ out.owner k = some i) ∧
          (out.rowMatch i = some k → k ∈ exampleN i)))) &&
      decide ((matchedRows out).card = 3)
#eval [(augmentRows exampleN [] exampleState 2).isNone,
  (augmentRows exampleN [1,0] exampleState 2).isNone,
  (augmentRows exampleN [1,0,2,1] exampleState 2).isNone,
  (augmentRows exampleN [0,2] exampleState 1).isNone,
  (augmentRows exampleN [0] exampleState 2).isNone]
end PEqualNP.Outside.MatchingAugmentation
