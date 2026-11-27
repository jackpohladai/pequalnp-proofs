import AutomaticConstructor

namespace PEqualNP.Outside.AutomaticConstructor.Examples
open PEqualNP.Search

def tag : Outcome → Nat
  | .unsupported => 0
  | .inconclusive => 1
  | .unsat => 2
  | .sat _ => 3

def values (result : Outcome) (ids : List Nat) : List Bool :=
  match result with
  | .sat assignment => ids.map assignment
  | _ => []

def modelCheck (result : Outcome) (formula : CNF) : Bool :=
  match result with
  | .sat assignment => CNF.eval assignment formula
  | _ => false

private def twoRows (i : Fin 2) : List (Fin 2) := if i = 0 then [0, 1] else [0]
private def matchingSAT := solve 0 [] twoRows (fun _ => [])
private def matchingUNSAT := solve 0 [] (fun _ : Fin 3 => ([0, 1] : List (Fin 2)))
  (fun _ => [])
private def retainedUNSAT := solve 0 [[]] (fun _ : Fin 0 => ([] : List (Fin 0)))
  (fun _ => [])
private def unsupportedSyntax := solve 2 [[(0,false),(1,false)]]
  (fun _ : Fin 0 => ([] : List (Fin 0))) (fun _ => [])
private def unsupportedGuard := solve 1 [] (fun _ : Fin 1 => ([] : List (Fin 0)))
  (fun _ => [(0,false)])
private def inactive := solve 1 [] (fun _ : Fin 1 => ([] : List (Fin 0)))
  (fun _ => [(0,true)])
private def propagated := solve 1 [[(0,false)]]
  (fun _ : Fin 1 => ([0] : List (Fin 1))) (fun _ => [(0,true)])

example : [matchingSAT, matchingUNSAT, retainedUNSAT, unsupportedSyntax,
    unsupportedGuard, inactive, propagated].map tag = [3,2,2,0,0,3,3] := by decide
theorem matchingSAT_model : modelCheck matchingSAT (encoded 0 [] twoRows (fun _ => [])) = true := by
  have satTag : tag matchingSAT = 3 := by decide
  cases returned : matchingSAT with
  | unsupported => simp [returned, tag] at satTag
  | inconclusive => simp [returned, tag] at satTag
  | unsat => simp [returned, tag] at satTag
  | sat assignment =>
      exact returned_sat_is_model 0 [] twoRows (fun _ => []) assignment returned
example : values propagated [0,1] = [false,true] := by decide
example : modelCheck propagated (encoded 1 [[(0,false)]]
    (fun _ : Fin 1 => ([0] : List (Fin 1))) (fun _ => [(0,true)])) = true := by decide

#print axioms matchingSAT_model
end PEqualNP.Outside.AutomaticConstructor.Examples
