import ExplicitConstructorInput

namespace PEqualNP.Outside.ConstructorBoundary

open PEqualNP.Search
open PEqualNP.Outside.DualHorn
open PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Outside.GuardedHall
open PEqualNP.Outside.CertifiedConstructorSolver
open PEqualNP.Outside.SparseDualHornAlgorithm

variable {r h : Nat}

def negativeVars (g : Fin r → Clause) : List Nat :=
  ((List.finRange r).flatMap (fun i => ((g i).filter (fun l => !l.2)).map Prod.fst)).eraseDups

theorem mem_negativeVars (g : Fin r → Clause) (x : Nat) :
    x ∈ negativeVars g ↔ ∃ i, (x, false) ∈ g i := by
  simp only [negativeVars, List.mem_eraseDups, List.mem_flatMap]
  constructor
  · rintro ⟨i, _, member⟩
    obtain ⟨⟨v, sign⟩, filtered, rfl⟩ := List.mem_map.mp member
    have held := List.mem_filter.mp filtered
    cases sign
    · exact ⟨i, held.1⟩
    · simp at held
  · rintro ⟨i, member⟩
    exact ⟨i, List.mem_finRange i, List.mem_map.mpr
      ⟨(x,false), List.mem_filter.mpr ⟨member, rfl⟩, rfl⟩⟩

def writeBit (a : Assignment) (x : Nat) (b : Bool) : Assignment :=
  fun i => if i = x then b else a i

def enumerateBits : List Nat → List Assignment
  | [] => [fun _ => false]
  | x :: xs =>
    let tail := enumerateBits xs
    (tail.map fun a => writeBit a x false) ++ (tail.map fun a => writeBit a x true)

theorem enumerateBits_length (xs : List Nat) :
    (enumerateBits xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [enumerateBits, ih, Nat.pow_succ, Nat.mul_two]

theorem enumerateBits_complete (xs : List Nat) (σ : Assignment) :
    ∃ a ∈ enumerateBits xs, ∀ x ∈ xs, a x = σ x := by
  induction xs with
  | nil => exact ⟨fun _ => false, by simp [enumerateBits], by simp⟩
  | cons x xs ih =>
    obtain ⟨a, member, agree⟩ := ih
    refine ⟨writeBit a x (σ x), ?_, ?_⟩
    · cases σ x
      · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a, member, rfl⟩))
      · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨a, member, rfl⟩))
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | later
      · simp [writeBit]
      · by_cases same : y = x
        · simp [writeBit, same]
        · simp [writeBit, same, agree y later]

/-- Bind branch bits using unit retained clauses. The new positive flag
is the old offset, and edge IDs in the branch start at its successor. -/
def branchRetained (F : CNF) (xs : List Nat) (flag : Nat) (a : Assignment) : CNF :=
  (F ++ xs.map (fun x => [(x, a x)])) ++ [[(flag, true)]]

theorem branchRetained_eval (σ a : Assignment) (F : CNF) (xs : List Nat) (flag : Nat) :
    CNF.eval σ (branchRetained F xs flag a) = true ↔
      CNF.eval σ F = true ∧ (∀ x ∈ xs, σ x = a x) ∧ σ flag = true := by
  simp [branchRetained, CNF.eval, List.all_append, Clause.eval, Literal.eval, List.all_eq_true]

theorem branchRetained_dual (F : CNF) (xs : List Nat) (flag : Nat) (a : Assignment)
    (dual : IsDualHorn F) : IsDualHorn (branchRetained F xs flag a) := by
  intro C hC
  rcases List.mem_append.mp hC with earlier | flagUnit
  · rcases List.mem_append.mp earlier with orig | fixed
    · exact dual C orig
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp fixed
      cases a x <;> simp [IsDualHornClause]
  · have same := List.mem_singleton.mp flagUnit
    subst C
    simp [IsDualHornClause]

def lowerGuard (flag : Nat) (a : Assignment) : Clause → Clause
  | [] => []
  | (x, true) :: rest => (x, true) :: lowerGuard flag a rest
  | (x, false) :: rest =>
    if a x then lowerGuard flag a rest else (flag, true) :: lowerGuard flag a rest

theorem lowerGuard_eval (σ a : Assignment) (flag : Nat) (C : Clause)
    (flagOn : σ flag = true)
    (fixed : ∀ x, (x, false) ∈ C → σ x = a x) :
    Clause.eval σ (lowerGuard flag a C) = Clause.eval σ C := by
  induction C with
  | nil => rfl
  | cons l rest ih =>
    obtain ⟨x, sign⟩ := l
    have tail := ih (fun y hy => fixed y (List.mem_cons_of_mem _ hy))
    cases sign
    · have same := fixed x (by simp)
      cases b : a x <;> simp [lowerGuard, Clause.eval, Literal.eval, flagOn, same, b] at tail ⊢
      exact tail
    · change (Literal.eval σ (x,true) || Clause.eval σ (lowerGuard flag a rest)) = _
      rw [tail]
      rfl

theorem lowerGuard_safe (flag : Nat) (a : Assignment) (C : Clause)
    (below : ∀ l ∈ C, l.1 < flag) :
    ∀ l ∈ lowerGuard flag a C, l.2 = true ∧ l.1 < flag+1 := by
  induction C with
  | nil => simp [lowerGuard]
  | cons l rest ih =>
    obtain ⟨x, sign⟩ := l
    have tail := ih (fun l hl => below l (List.mem_cons_of_mem _ hl))
    cases sign
    · cases b : a x
      · intro l hl
        simp only [lowerGuard, b, Bool.false_eq_true, ite_false, List.mem_cons] at hl
        rcases hl with rfl | old
        · exact ⟨rfl, Nat.lt_succ_self _⟩
        · exact tail l old
      · exact fun l hl => tail l (by simpa [lowerGuard,b] using hl)
    · intro l hl
      rcases List.mem_cons.mp hl with rfl | old
      · exact ⟨rfl, Nat.lt_succ_of_lt (below _ (by simp))⟩
      · exact tail l old

theorem branch_input_conditions (offset : Nat) (F : CNF) (g : Fin r → Clause)
    (a : Assignment) (retainedBelow : VariablesBelow F offset)
    (guardsBelow : ∀ i, ∀ l ∈ g i, l.1 < offset) :
    InputConditions (offset+1) (branchRetained F (negativeVars g) offset a)
      (fun i => lowerGuard offset a (g i)) := by
  refine ⟨?_, fun i => lowerGuard_safe offset a (g i) (guardsBelow i)⟩
  intro C hC l hl
  rcases List.mem_append.mp hC with earlier | flag
  · rcases List.mem_append.mp earlier with orig | fixed
    · exact Nat.lt_succ_of_lt (retainedBelow C orig l hl)
    · obtain ⟨x, member, rfl⟩ := List.mem_map.mp fixed
      obtain ⟨i, negative⟩ := (mem_negativeVars g x).mp member
      have same := List.mem_singleton.mp hl
      subst l
      exact Nat.lt_succ_of_lt (guardsBelow i (x,false) negative)
  · have same := List.mem_singleton.mp flag
    subst C
    have same := List.mem_singleton.mp hl
    subst l
    exact Nat.lt_succ_self _

theorem branch_checks (offset : Nat) (F : CNF) (g : Fin r → Clause)
    (a : Assignment) (retainedBelow : VariablesBelow F offset)
    (guardsBelow : ∀ i, ∀ l ∈ g i, l.1 < offset) (dual : IsDualHorn F) :
    inputCheck (offset+1) (branchRetained F (negativeVars g) offset a)
      (fun i => lowerGuard offset a (g i)) = true ∧
    dualHornCheck (branchRetained F (negativeVars g) offset a) = true :=
  ⟨(inputCheck_iff _ _ _).mpr (branch_input_conditions offset F g a retainedBelow guardsBelow),
    (dualHornCheck_iff _).mpr (branchRetained_dual F _ offset a dual)⟩

theorem clause_bit_outside (σ : Assignment) (flag : Nat) (C : Clause) (value : Bool)
    (outside : ∀ l ∈ C, l.1 ≠ flag) :
    Clause.eval (writeBit σ flag value) C = Clause.eval σ C := by
  induction C with
  | nil => rfl
  | cons l rest ih =>
    have head := outside l (by simp)
    have tail := ih (fun l hl => outside l (List.mem_cons_of_mem _ hl))
    change (Literal.eval (writeBit σ flag value) l || Clause.eval (writeBit σ flag value) rest) =
      (Literal.eval σ l || Clause.eval σ rest)
    rw [tail]
    simp [Literal.eval, writeBit, head]

/-- At most one supported solver call per enumerated branch is sufficient
for the decision reduction. The branch count is exactly 2^k, where k is
the number of distinct variables used negatively in a guard. -/
theorem mixed_sat_iff_branches (offset : Nat) (F : CNF) (N : Fin r → Finset (Fin h))
    (g : Fin r → Clause) (retainedBelow : VariablesBelow F offset)
    (guardsBelow : ∀ i, ∀ l ∈ g i, l.1 < offset) :
    Satisfiable (encode F N g (freshEdge offset)) ↔
      ∃ a ∈ enumerateBits (negativeVars g),
        Satisfiable (encode (branchRetained F (negativeVars g) offset a) N
          (fun i => lowerGuard offset a (g i)) (freshEdge (offset+1))) := by
  rw [fresh_encoded_sat_iff_matching offset F N g retainedBelow guardsBelow]
  have branchSem (a : Assignment) := fresh_encoded_sat_iff_matching _
    (branchRetained F (negativeVars g) offset a) N (fun i => lowerGuard offset a (g i))
    (branch_input_conditions offset F g a retainedBelow guardsBelow).1
    (fun i l member => ((branch_input_conditions offset F g a retainedBelow guardsBelow).2 i l member).2)
  constructor
  · rintro ⟨σ, retained, matching⟩
    obtain ⟨a, enumerated, agrees⟩ := enumerateBits_complete (negativeVars g) σ
    let lifted := writeBit σ offset true
    have fixed : ∀ x ∈ negativeVars g, lifted x = a x := by
      intro x hx
      obtain ⟨i, negative⟩ := (mem_negativeVars g x).mp hx
      have xne : x ≠ offset := Nat.ne_of_lt (guardsBelow i _ negative)
      simpa [lifted, writeBit, xne] using (agrees x hx).symm
    have flagOn : lifted offset = true := by simp [lifted, writeBit]
    have unchanged : CNF.eval lifted F = true := by
      apply List.all_eq_true.mpr
      intro C hC
      rw [clause_bit_outside σ offset C true
        (fun l hl => Nat.ne_of_lt (retainedBelow C hC l hl))]
      exact List.all_eq_true.mp retained C hC
    refine ⟨a, enumerated, (branchSem a).mpr ⟨lifted, ?_, ?_⟩⟩
    · exact (branchRetained_eval lifted a F _ offset).mpr ⟨unchanged, fixed, flagOn⟩
    · have equalGuards : (fun i => Clause.eval lifted (lowerGuard offset a (g i))) =
          (fun i => Clause.eval σ (g i)) := by
        funext i
        rw [lowerGuard_eval lifted a offset (g i) flagOn
          (fun x hx => fixed x ((mem_negativeVars g x).mpr ⟨i,hx⟩))]
        exact clause_bit_outside σ offset (g i) true (fun l hl => Nat.ne_of_lt (guardsBelow i l hl))
      rw [equalGuards]
      exact matching
  · rintro ⟨a, _, accepted⟩
    obtain ⟨σ, branch, matching⟩ := (branchSem a).mp accepted
    obtain ⟨retained, fixed, flagOn⟩ := (branchRetained_eval σ a F _ offset).mp branch
    have equalGuards : (fun i => Clause.eval σ (lowerGuard offset a (g i))) =
        (fun i => Clause.eval σ (g i)) := by
      funext i
      exact lowerGuard_eval σ a offset (g i) flagOn
        (fun x hx => fixed x ((mem_negativeVars g x).mpr ⟨i,hx⟩))
    exact ⟨σ, retained, equalGuards ▸ matching⟩

#print axioms enumerateBits_length
#print axioms branch_checks
#print axioms mixed_sat_iff_branches

end PEqualNP.Outside.ConstructorBoundary
