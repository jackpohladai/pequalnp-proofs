import SparseDualHornAlgorithm

namespace PEqualNP.Outside.SparseDualHornAlgorithm
open PEqualNP.Search
open PEqualNP.Outside.DualHorn

def dualHornCheck (F : CNF) : Bool :=
  F.all (fun C => decide ((C.filter (fun l => !l.2)).length ≤ 1))

theorem dualHornCheck_iff (F : CNF) : dualHornCheck F = true ↔ IsDualHorn F := by
  simp [dualHornCheck, IsDualHorn, IsDualHornClause, List.all_eq_true]

/-- Outer none means unsupported syntax. Some none means checked UNSAT.
Some (some T) means a satisfying greatest model represented by T. -/
def checkedSolve (F : CNF) : Option (Option (Finset Nat)) :=
  if dualHornCheck F then some (solveSparse F) else none

theorem checkedSolve_result_correct (F : CNF) (result : Option (Finset Nat))
    (success : checkedSolve F = some result) :
    IsDualHorn F ∧ Correct (support F) F result := by
  unfold checkedSolve at success
  split at success
  next h =>
    have dual := (dualHornCheck_iff F).mp h
    have hr := Option.some.inj success
    exact ⟨dual, hr ▸ solveSparse_correct F dual⟩
  next h => simp at success

example : checkedSolve [[(0,false),(1,false)],[(0,true)]] = none := by decide
example : checkedSolve [[(0,false)],[(0,true)]] = some none := by decide
example : checkedSolve [[(1000000000,false)],[(1000000000,true),(7,true)]] =
    some (some {7}) := by decide

#print axioms dualHornCheck_iff
#print axioms checkedSolve_result_correct
end PEqualNP.Outside.SparseDualHornAlgorithm
