import GuardedCNFEncoding
import Mathlib.Data.Nat.Pairing

namespace PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Search
open PEqualNP.Outside.GuardedHall

variable {r h : Nat}

/-- Explicit collision-free variable naming above the retained-variable offset. -/
def freshEdge (offset : Nat) (p : Edge r h) : Nat :=
  offset + Nat.pair p.1.val p.2.val

theorem freshEdge_injective (offset : Nat) :
    Function.Injective (freshEdge (r := r) (h := h) offset) := by
  intro p q eq
  have hp : Nat.pair p.1.val p.2.val = Nat.pair q.1.val q.2.val :=
    Nat.add_left_cancel eq
  have coords := Nat.pair_eq_pair.mp hp
  exact Prod.ext (Fin.ext coords.1) (Fin.ext coords.2)

theorem freshEdge_private (offset : Nat) (C : Clause)
    (below : ∀ l ∈ C, l.1 < offset) :
    PrivateFromClause (freshEdge (r := r) (h := h) offset) C := by
  intro l hl p eq
  have bound := below l hl
  have large : offset ≤ freshEdge offset p := Nat.le_add_right _ _
  rw [eq] at large
  omega

theorem fresh_encoded_sat_iff_matching (offset : Nat) (F : CNF)
    (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (retainedBelow : ∀ C ∈ F, ∀ l ∈ C, l.1 < offset)
    (guardsBelow : ∀ i, ∀ l ∈ guards i, l.1 < offset) :
    Satisfiable (encode F N guards (freshEdge offset)) ↔
      ∃ σ, CNF.eval σ F = true ∧ HasMatching N (fun i => Clause.eval σ (guards i)) := by
  apply encoded_sat_iff_matching F N guards (freshEdge offset) (freshEdge_injective offset)
  · intro C hC
    exact freshEdge_private offset C (retainedBelow C hC)
  · intro i
    exact freshEdge_private offset (guards i) (guardsBelow i)

#print axioms freshEdge_injective
#print axioms freshEdge_private
#print axioms fresh_encoded_sat_iff_matching
end PEqualNP.Outside.GuardedCNFEncoding
