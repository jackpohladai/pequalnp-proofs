import ExplicitConstructorInput
import Init.Data.List.OfFn

namespace PEqualNP.Outside.ConstructorBoundary

open PEqualNP.Search
open PEqualNP.Outside.DualHorn
open PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Outside.GuardedHall
open PEqualNP.Outside.ExplicitConstructorInput
open PEqualNP.Outside.CertifiedConstructorSolver
open PEqualNP.Outside.SparseDualHornAlgorithm

/-- With no private holes the graph contributes only the guards, preserving
their row order and literal lists. -/
theorem zero_hole_encode {r : Nat} (N : Fin r → Finset (Fin 0))
    (g : Fin r → Clause) (edge : Edge r 0 → Nat) :
    encode [] N g edge = (List.finRange r).map g := by
  have rows : rowClause N g edge = g := by
    funext i
    simp [rowClause, neighborList]
  have columns : columnCNF N edge = [] := by
    simp [columnCNF, List.flatMap_eq_nil_iff]
  simp [encode, rowCNF, rows, columns]

def visibleOffset (F : CNF) : Nat :=
  ((F.flatMap (fun C => C.map Prod.fst)).foldr Nat.max 0) + 1

private theorem le_foldMax {xs : List Nat} {x : Nat} (hm : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => simp at hm
  | cons y ys ih =>
    rcases List.mem_cons.mp hm with rfl | member
    · exact Nat.le_max_left _ _
    · exact (ih member).trans (Nat.le_max_right _ _)

theorem visible_below {F : CNF} {C : Clause} (hC : C ∈ F)
    {l : Literal} (hl : l ∈ C) : l.1 < visibleOffset F := by
  apply Nat.lt_succ_of_le
  exact le_foldMax (List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)

def asZeroHoleInput (F : CNF) : Input where
  offset := visibleOffset F
  holeBound := 0
  retained := []
  rows := F.map (fun C => ⟨[], C⟩)

theorem realized_guards (F : CNF) :
    (List.finRange (asZeroHoleInput F).rows.length).map (guards (asZeroHoleInput F)) = F := by
  simp [List.finRange, List.map_ofFn, Function.comp_def, guards, asZeroHoleInput, List.get_eq_getElem]

/-- Every raw CNF is represented by the constructor data if guards may have
either polarity. This is exact equality of CNF lists. -/
theorem realized_formula (F : CNF) : formula (asZeroHoleInput F) = F := by
  change encode [] (fun i => (adjacency (asZeroHoleInput F) i).toFinset)
    (guards (asZeroHoleInput F)) (freshEdge (asZeroHoleInput F).offset) = F
  exact (zero_hole_encode
    (fun i => (adjacency (asZeroHoleInput F) i).toFinset)
    (guards (asZeroHoleInput F)) (freshEdge (asZeroHoleInput F).offset)).trans
      (realized_guards F)

theorem realized_neighborCheck (F : CNF) : neighborCheck (asZeroHoleInput F) = true := by
  simp [neighborCheck, boundedNeighbors, asZeroHoleInput]

theorem realized_inputCheck_iff (F : CNF) :
    inputCheck (asZeroHoleInput F).offset (asZeroHoleInput F).retained
      (guards (asZeroHoleInput F)) = true ↔ ∀ C ∈ F, Positive C := by
  rw [inputCheck_iff]
  constructor
  · intro accepted C member l hl
    rw [← realized_guards F] at member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    exact (accepted.2 i l hl).1
  · intro pos
    refine ⟨by simp [asZeroHoleInput], ?_⟩
    intro i l hl
    have rowMem : guards (asZeroHoleInput F) i ∈ F := by
      have member : guards (asZeroHoleInput F) i ∈
          (List.finRange (asZeroHoleInput F).rows.length).map (guards (asZeroHoleInput F)) :=
        List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
      simpa only [realized_guards F] using member
    exact ⟨pos _ rowMem l hl, visible_below rowMem hl⟩

/-- On this route the supported-input check accepts exactly positive CNFs.
Bounds, empty neighborhoods and the retained dual-Horn check already pass. -/
theorem realized_supported_iff (F : CNF) :
    supportedCheck (asZeroHoleInput F) = true ↔ ∀ C ∈ F, Positive C := by
  have dual : dualHornCheck (asZeroHoleInput F).retained = true := rfl
  simp only [supportedCheck, realized_neighborCheck, dual, Bool.true_and, Bool.and_true,
    realized_inputCheck_iff]

private def mixed : CNF := [[(9,false),(2,true)],[(4,true)],[],[(9,false),(2,true)]]

#guard formula (asZeroHoleInput mixed) == mixed
#guard formula (asZeroHoleInput []) == []
#guard !(supportedCheck (asZeroHoleInput mixed))
#guard !(supportedCheck (asZeroHoleInput [[(2,true),(2,false)]]))
#guard supportedCheck (asZeroHoleInput [[(9,true),(2,true)],[]])

#eval formula (asZeroHoleInput mixed)
#eval [supportedCheck (asZeroHoleInput mixed),
  supportedCheck (asZeroHoleInput [[(9,true),(2,true)],[]])]

#print axioms zero_hole_encode
#print axioms realized_formula
#print axioms realized_supported_iff

end PEqualNP.Outside.ConstructorBoundary
