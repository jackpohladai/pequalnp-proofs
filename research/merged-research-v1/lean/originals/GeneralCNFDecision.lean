import ZeroHoleCoverage
import MixedGuardSolver

namespace PEqualNP.Outside.ConstructorBoundary
open PEqualNP.Search
open PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Outside.DualHorn

private def noNeighbors (F : CNF) (_ : Fin F.length) : List (Fin 0) := []

theorem zero_hole_checks (F : CNF) :
    mixedInputCheck (visibleOffset F) [] F.get = true := by
  apply (mixedInputCheck_iff _ _ _).mpr
  refine ⟨by simp [VariablesBelow], ?_, by simp [IsDualHorn]⟩
  intro i l hl
  exact visible_below (List.get_mem _ _) hl

theorem zero_hole_formula_eq (F : CNF) :
    AutomaticConstructor.encoded (visibleOffset F) [] (noNeighbors F) F.get = F := by
  have exactRows : (List.finRange F.length).map F.get = F := by
    simp [List.finRange, List.map_ofFn, Function.comp_def, List.get_eq_getElem]
  exact (zero_hole_encode (fun _ : Fin F.length => (∅ : Finset (Fin 0)))
    F.get (freshEdge (visibleOffset F))).trans exactRows

/-- Exhaustive conditioning applied to the zero-hole encoding of an
arbitrary CNF list. The branch count can grow exponentially. -/
def solveCNF (F : CNF) : Option Bool :=
  solveMixed (visibleOffset F) [] (noNeighbors F) F.get

theorem solveCNF_sat (F : CNF) : solveCNF F = some true ↔ Satisfiable F := by
  simpa only [solveCNF, zero_hole_formula_eq] using
    solveMixed_sat (visibleOffset F) [] (noNeighbors F) F.get (zero_hole_checks F)

theorem solveCNF_unsat (F : CNF) : solveCNF F = some false ↔ ¬ Satisfiable F := by
  simpa only [solveCNF, zero_hole_formula_eq] using
    solveMixed_unsat (visibleOffset F) [] (noNeighbors F) F.get (zero_hole_checks F)

theorem solveCNF_ne_none (F : CNF) : solveCNF F ≠ none := by
  simp [solveCNF, solveMixed, zero_hole_checks]

def solveCNFCounted (F : CNF) : Option (Bool × Nat) :=
  solveMixedCounted (visibleOffset F) [] (noNeighbors F) F.get

theorem solveCNFCounted_erases (F : CNF) :
    (solveCNFCounted F).map Prod.fst = solveCNF F :=
  solveMixedCounted_erases _ _ _ _

theorem solveCNFCounted_calls (F : CNF) (verdict : Bool) (calls : Nat)
    (returned : solveCNFCounted F = some (verdict, calls)) :
    calls ≤ 2 ^ (negativeVars F.get).length :=
  solveMixedCounted_calls _ _ _ _ verdict calls returned

private def allSigns : CNF :=
  [[(0,true),(1,true)],[(0,false),(1,true)],[(0,true),(1,false)],[(0,false),(1,false)]]

private def fixtures : List (Option Bool) :=
  [solveCNF [], solveCNF [[]], solveCNF [[(0,true)],[(0,false)]],
    solveCNF [[(0,false),(0,true)]], solveCNF allSigns,
    solveCNF [[(3,true)],[(3,false),(8,true)]]]
#eval fixtures
#eval solveCNFCounted allSigns
#guard fixtures == [some true, some false, some false, some true, some false, some true]
#guard solveCNFCounted allSigns == some (false, 4)

#print axioms zero_hole_checks
#print axioms zero_hole_formula_eq
#print axioms solveCNF_sat
#print axioms solveCNF_unsat
#print axioms solveCNF_ne_none
#print axioms solveCNFCounted_erases
#print axioms solveCNFCounted_calls

end PEqualNP.Outside.ConstructorBoundary
