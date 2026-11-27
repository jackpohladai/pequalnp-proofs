import FreshGuardedCNF

namespace PEqualNP.Outside.GuardedCNFEncoding

open PEqualNP.Search

variable {r h : Nat}

/-- Decode just those variable IDs that name a pair in the finite edge grid. -/
def decodeFreshEdge (r h offset x : Nat) : Option (Edge r h) :=
  if x < offset then none else
    let p := Nat.unpair (x - offset)
    if hi : p.1 < r then
      if hk : p.2 < h then some (⟨p.1, hi⟩, ⟨p.2, hk⟩) else none
    else none

/-- Supply the chosen edge bits at fresh IDs and keep the visible assignment elsewhere. -/
def liftAssignment (offset : Nat) (visible : Assignment)
    (edges : Fin r → Fin h → Bool) : Assignment := fun x =>
  match decodeFreshEdge r h offset x with
  | some p => edges p.1 p.2
  | none => visible x

theorem decodeFreshEdge_at_edge (offset : Nat) (i : Fin r) (k : Fin h) :
    decodeFreshEdge r h offset (freshEdge offset (i, k)) = some (i, k) := by
  have above : ¬ freshEdge offset (i, k) < offset :=
    Nat.not_lt_of_ge (Nat.le_add_right _ _)
  have sub : freshEdge offset (i, k) - offset = Nat.pair i.val k.val :=
    Nat.add_sub_cancel_left _ _
  simp [decodeFreshEdge, above, sub, Nat.unpair_pair, i.isLt, k.isLt]

theorem decodeFreshEdge_sound (offset x : Nat) (p : Edge r h)
    (decoded : decodeFreshEdge r h offset x = some p) :
    freshEdge offset p = x := by
  unfold decodeFreshEdge at decoded
  split at decoded
  next below => simp at decoded
  next above =>
    dsimp only at decoded
    split at decoded
    next hi =>
      split at decoded
      next hk =>
        rw [← Option.some.inj decoded]
        change offset + Nat.pair (Nat.unpair (x - offset)).1
            (Nat.unpair (x - offset)).2 = x
        rw [Nat.pair_unpair, Nat.add_sub_of_le (Nat.le_of_not_lt above)]
      next outside => simp at decoded
    next outside => simp at decoded

theorem liftAssignment_at_edge (offset : Nat) (visible : Assignment)
    (edges : Fin r → Fin h → Bool) (i : Fin r) (k : Fin h) :
    liftAssignment offset visible edges (freshEdge offset (i, k)) = edges i k := by
  simp [liftAssignment, decodeFreshEdge_at_edge]

theorem liftAssignment_below (offset : Nat) (visible : Assignment)
    (edges : Fin r → Fin h → Bool) (x : Nat) (below : x < offset) :
    liftAssignment offset visible edges x = visible x := by
  simp [liftAssignment, decodeFreshEdge, below]

theorem liftAssignment_outside (offset : Nat) (visible : Assignment)
    (edges : Fin r → Fin h → Bool) (x : Nat)
    (outside : ∀ p : Edge r h, freshEdge offset p ≠ x) :
    liftAssignment offset visible edges x = visible x := by
  unfold liftAssignment
  split
  next p decoded => exact False.elim (outside p (decodeFreshEdge_sound offset x p decoded))
  next _ => rfl

theorem liftClause_eval (offset : Nat) (visible : Assignment) (edges : Fin r → Fin h → Bool)
    (C : Clause) (below : ∀ l ∈ C, l.1 < offset) :
    Clause.eval (liftAssignment offset visible edges) C = Clause.eval visible C := by
  induction C with
  | nil => rfl
  | cons l rest ih =>
    have head := liftAssignment_below offset visible edges l.1 (below _ (by simp))
    have tail := ih (fun item member => below item (List.mem_cons_of_mem _ member))
    change (Literal.eval (liftAssignment offset visible edges) l ||
        Clause.eval (liftAssignment offset visible edges) rest) =
      (Literal.eval visible l || Clause.eval visible rest)
    rw [tail]
    simp [Literal.eval, head]

theorem liftCNF_eval (offset : Nat) (visible : Assignment) (edges : Fin r → Fin h → Bool)
    (F : CNF) (below : ∀ C ∈ F, ∀ l ∈ C, l.1 < offset) :
    CNF.eval (liftAssignment offset visible edges) F = CNF.eval visible F := by
  induction F with
  | nil => rfl
  | cons C rest ih =>
    have head := liftClause_eval offset visible edges C (below _ (by simp))
    have tail := ih (fun clause member => below clause (List.mem_cons_of_mem _ member))
    change (Clause.eval (liftAssignment offset visible edges) C &&
        CNF.eval (liftAssignment offset visible edges) rest) =
      (Clause.eval visible C && CNF.eval visible rest)
    rw [head, tail]

/-- Characterize evaluation of the constructed CNF at the computed assignment. -/
theorem liftEncoding_eval (offset : Nat) (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (visible : Assignment) (edges : Fin r → Fin h → Bool)
    (retainedBelow : ∀ C ∈ F, ∀ l ∈ C, l.1 < offset)
    (guardsBelow : ∀ i, ∀ l ∈ guards i, l.1 < offset) :
    CNF.eval (liftAssignment offset visible edges) (encode F N guards (freshEdge offset)) = true ↔
      CNF.eval visible F = true ∧
      (∀ i, Clause.eval visible (guards i) = true ∨ ∃ k ∈ N i, edges i k = true) ∧
      (∀ i j k, k ∈ N i → k ∈ N j → edges i k = true → edges j k = true → i = j) := by
  have guardsEval : ∀ i, Clause.eval (liftAssignment offset visible edges) (guards i) =
      Clause.eval visible (guards i) :=
    fun i => liftClause_eval offset visible edges (guards i) (guardsBelow i)
  rw [encode_eval, liftCNF_eval offset visible edges F retainedBelow]
  simp only [Rows, Columns, guardsEval, liftAssignment_at_edge]

/-- Certify the executable lift from supplied row and column witnesses. -/
theorem lift_witness (offset : Nat) (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (visible : Assignment) (edges : Fin r → Fin h → Bool)
    (retainedBelow : ∀ C ∈ F, ∀ l ∈ C, l.1 < offset)
    (guardsBelow : ∀ i, ∀ l ∈ guards i, l.1 < offset)
    (model : CNF.eval visible F = true)
    (rows : ∀ i, Clause.eval visible (guards i) = true ∨ ∃ k ∈ N i, edges i k = true)
    (columns : ∀ i j k, k ∈ N i → k ∈ N j → edges i k = true → edges j k = true → i = j) :
    CNF.eval (liftAssignment offset visible edges) (encode F N guards (freshEdge offset)) = true :=
  (liftEncoding_eval offset F N guards visible edges retainedBelow guardsBelow).mpr ⟨model, rows, columns⟩

#print axioms decodeFreshEdge
#print axioms liftAssignment
#print axioms decodeFreshEdge_at_edge
#print axioms decodeFreshEdge_sound
#print axioms liftAssignment_at_edge
#print axioms liftAssignment_below
#print axioms liftAssignment_outside
#print axioms liftClause_eval
#print axioms liftCNF_eval
#print axioms liftEncoding_eval
#print axioms lift_witness

end PEqualNP.Outside.GuardedCNFEncoding
