import GuardedCNFEncoding

namespace PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Search

def twoRowCNF : CNF := encode []
  (fun _ : Fin 2 => ({0} : Finset (Fin 1)))
  (fun i : Fin 2 => if i = 0 then [(0,true)] else [(1,false)])
  (fun p : Edge 2 1 => 2 + p.1.val)

theorem twoRowCNF_exact : twoRowCNF =
    [[(0,true),(2,true)],[(1,false),(3,true)],
     [(2,false),(3,false)],[(3,false),(2,false)]] := by decide

def tinyAssignment (x y p q : Bool) : Assignment :=
  fun v => if v = 0 then x else if v = 1 then y else if v = 2 then p else q

theorem twoRowCNF_projection (x y : Bool) :
    (∃ p q : Bool, CNF.eval (tinyAssignment x y p q) twoRowCNF = true) ↔
      (x || !y) = true := by
  cases x <;> cases y <;> decide

#print axioms twoRowCNF_exact
#print axioms twoRowCNF_projection
end PEqualNP.Outside.GuardedCNFEncoding
