import Init

namespace ParityExtraction

/-- A literal is a variable with its polarity. The positive polarity is `true`. -/
abbrev Clause (Var : Type u) := List (Var × Bool)

def literalValue (assignment : Var → Bool) (literal : Var × Bool) : Bool :=
  if literal.2 then assignment literal.1 else !(assignment literal.1)

def clauseValue (assignment : Var → Bool) (clause : Clause Var) : Bool :=
  clause.any (literalValue assignment)

def cnfValue (assignment : Var → Bool) (clauses : List (Clause Var)) : Bool :=
  clauses.all (clauseValue assignment)

/-- Each bit chooses the literal that is false at that bit of the mask. -/
def exclude (scope : List Var) (mask : List Bool) : Clause Var :=
  List.zipWith (fun var bit => (var, !bit)) scope mask

def parity (bits : List Bool) : Bool :=
  bits.foldr Bool.xor false

/-- For each tail, exactly the indicated leading bit gives the chosen parity. -/
theorem parity_cons_iff (tail : List Bool) (bit target : Bool) :
    parity (bit :: tail) = target ↔ bit = Bool.xor target (parity tail) := by
  change Bool.xor bit (parity tail) = target ↔ bit = Bool.xor target (parity tail)
  cases bit <;> cases target <;> cases parity tail <;> decide

theorem exclude_false_iff (assignment : Var → Bool) (scope : List Var) (mask : List Bool)
    (width : mask.length = scope.length) :
    clauseValue assignment (exclude scope mask) = false ↔ scope.map assignment = mask := by
  induction scope generalizing mask with
  | nil =>
    cases mask with
    | nil => simp [clauseValue, exclude]
    | cons bit rest => simp at width
  | cons var rest ih =>
    cases mask with
    | nil => simp at width
    | cons bit bits =>
      have restWidth : bits.length = rest.length := Nat.succ.inj width
      have first : literalValue assignment (var, !bit) = false ↔ assignment var = bit := by
        cases bit <;> cases h : assignment var <;> simp [literalValue, h]
      simp only [exclude, List.zipWith_cons_cons, clauseValue, List.any_cons,
        Bool.or_eq_false_iff, List.map_cons, List.cons.injEq, first]
      exact and_congr_right fun _ => ih bits restWidth

/-- Masks with the entire blocked parity class falsify the block on exactly that class. -/
theorem block_false_iff (assignment : Var → Bool) (scope : List Var)
    (masks : List (List Bool)) (blocked : Bool)
    (covers : ∀ mask, mask ∈ masks ↔ mask.length = scope.length ∧ parity mask = blocked) :
    cnfValue assignment (masks.map (exclude scope)) = false ↔
      parity (scope.map assignment) = blocked := by
  rw [cnfValue, List.all_eq_false]
  constructor
  · rintro ⟨clause, inClauses, fails⟩
    obtain ⟨mask, inMasks, rfl⟩ := List.mem_map.mp inClauses
    obtain ⟨width, maskParity⟩ := (covers mask).mp inMasks
    have maskEquality := (exclude_false_iff assignment scope mask width).mp
      (Bool.eq_false_iff.mpr fails)
    simpa only [maskEquality] using maskParity
  · intro assignmentParity
    have width : (scope.map assignment).length = scope.length := List.length_map assignment
    have inMasks := (covers (scope.map assignment)).mpr ⟨width, assignmentParity⟩
    refine ⟨exclude scope (scope.map assignment), List.mem_map.mpr ⟨_, inMasks, rfl⟩, ?_⟩
    exact Bool.eq_false_iff.mp ((exclude_false_iff assignment scope _ width).mpr rfl)

theorem block_eq_opposite_parity (assignment : Var → Bool) (scope : List Var)
    (masks : List (List Bool)) (blocked : Bool)
    (covers : ∀ mask, mask ∈ masks ↔ mask.length = scope.length ∧ parity mask = blocked) :
    cnfValue assignment (masks.map (exclude scope)) =
      (parity (scope.map assignment) == !blocked) := by
  have falseIff := block_false_iff assignment scope masks blocked covers
  cases hValue : cnfValue assignment (masks.map (exclude scope)) <;>
    cases hParity : parity (scope.map assignment) <;> cases blocked <;> simp_all

/-- The selected block can be replaced pointwise while arbitrary other clauses are retained. -/
theorem replace_parity_block (assignment : Var → Bool) (scope : List Var)
    (masks : List (List Bool)) (blocked : Bool)
    (covers : ∀ mask, mask ∈ masks ↔ mask.length = scope.length ∧ parity mask = blocked)
    (other : List (Clause Var)) :
    cnfValue assignment (masks.map (exclude scope) ++ other) =
      ((parity (scope.map assignment) == !blocked) && cnfValue assignment other) := by
  rw [cnfValue, List.all_append]
  change (cnfValue assignment (masks.map (exclude scope)) && cnfValue assignment other) = _
  rw [block_eq_opposite_parity assignment scope masks blocked covers]

/-- The selected clauses may occur in any positions in the original CNF. -/
theorem replace_parity_subcollection (assignment : Var → Bool) (scope : List Var)
    (masks : List (List Bool)) (blocked : Bool)
    (covers : ∀ mask, mask ∈ masks ↔ mask.length = scope.length ∧ parity mask = blocked)
    (original other : List (Clause Var))
    (selection : original.Perm (masks.map (exclude scope) ++ other)) :
    cnfValue assignment original =
      ((parity (scope.map assignment) == !blocked) && cnfValue assignment other) := by
  calc
    cnfValue assignment original = cnfValue assignment (masks.map (exclude scope) ++ other) :=
      selection.all_eq
    _ = _ := replace_parity_block assignment scope masks blocked covers other

-- The assignment (true, false) passes odd parity and fails the full three-clause CNF.
example : parity ([1, 2].map (· == (1 : Nat))) = true := rfl
example : cnfValue (· == (1 : Nat))
    [[(1, true), (2, true)], [(1, false), (2, false)], [(1, false), (2, true)]] = false := rfl

#print axioms parity_cons_iff
#print axioms exclude_false_iff
#print axioms block_false_iff
#print axioms replace_parity_subcollection

end ParityExtraction
