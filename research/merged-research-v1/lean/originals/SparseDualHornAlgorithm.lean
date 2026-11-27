import DualHorn
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

namespace PEqualNP.Outside.SparseDualHornAlgorithm
open PEqualNP.Search
open PEqualNP.Outside.DualHorn

/-- Variables in the finite support are true exactly when still in T.
Variables outside the declared support stay true. -/
def state (U : Finset Nat) (T : Finset Nat) : Assignment :=
  fun x => if x ∈ U then decide (x ∈ T) else true

def VariablesIn (F : CNF) (U : Finset Nat) : Prop :=
  ∀ C ∈ F, ∀ l ∈ C, l.1 ∈ U

def Dominates (F : CNF) (a : Assignment) : Prop :=
  ∀ σ : Assignment, CNF.eval σ F = true → σ ≤ a

theorem bad_literal_false (C : Clause) (a : Assignment)
    (bad : Clause.eval a C = false) (l : Literal) (member : l ∈ C) :
    Literal.eval a l = false := by
  simpa using List.any_eq_false.mp bad l member

/-- A violated dual-Horn clause forces its unique negative variable false
in every model below the current assignment. -/
theorem negative_forced (C : Clause) (dual : IsDualHornClause C)
    (a σ : Assignment) (below : σ ≤ a)
    (bad : Clause.eval a C = false) (model : Clause.eval σ C = true)
    (l : Literal) (member : l ∈ C) (negative : l.2 = false) :
    σ l.1 = false := by
  obtain ⟨⟨x,p⟩, hx, hv⟩ := List.any_eq_true.mp model
  cases p with
  | true =>
      have ht : σ x = true := by simpa [Literal.eval] using hv
      have ha : a x = true := Bool.le_iff_imp.mp (below x) ht
      have hf := bad_literal_false C a bad (x,true) hx
      simp [Literal.eval, ha] at hf
  | false =>
      have heq := negative_unique C dual hx member rfl negative
      have ht : σ x = false := by simpa [Literal.eval] using hv
      simpa [← heq] using ht

theorem erase_preserves_domination {U : Finset Nat} (F : CNF) (C : Clause)
    (dual : IsDualHornClause C) (inF : C ∈ F) (T : Finset Nat)
    (dom : Dominates F (state U T)) (bad : Clause.eval (state U T) C = false)
    (l : Literal) (member : l ∈ C) (negative : l.2 = false) :
    Dominates F (state U (T.erase l.1)) := by
  intro σ hs x
  have below := dom σ hs
  by_cases hxl : x = l.1
  · subst x
    have forced := negative_forced C dual (state U T) σ below bad
      (List.all_eq_true.mp hs C inF) l member negative
    simp [forced]
  · by_cases hxn : x ∈ U
    · simpa [state, hxn, Finset.mem_erase, hxl] using below x
    · simp [state, hxn]

theorem erase_strict_progress {U : Finset Nat} (C : Clause) (T : Finset Nat)
    (bad : Clause.eval (state U T) C = false)
    (l : Literal) (member : l ∈ C) (negative : l.2 = false) (bounded : l.1 ∈ U) :
    (T.erase l.1).card + 1 = T.card := by
  have hf := bad_literal_false C (state U T) bad l member
  have ht : l.1 ∈ T := by simpa [Literal.eval, state, bounded, negative] using hf
  exact Finset.card_erase_add_one ht

theorem no_negative_unsat (F : CNF) (C : Clause) (a : Assignment)
    (inF : C ∈ F) (dom : Dominates F a) (bad : Clause.eval a C = false)
    (none : C.find? (fun l => !l.2) = none) : ¬ Satisfiable F := by
  have pos : Positive C := by
    intro l hl
    have hn := List.find?_eq_none.mp none l hl
    simpa using hn
  rintro ⟨σ, hs⟩
  have ht := positive_clause_monotone C pos σ a (dom σ hs)
    (List.all_eq_true.mp hs C inF)
  simp [bad] at ht

/-- Fuel bounds variable-flipping steps; each step scans for a violated
clause and turns its negative variable false. This is executable Lean. -/
def run (U : Finset Nat) (F : CNF) : Nat → Finset Nat → Option (Finset Nat)
  | 0, T => if CNF.eval (state U T) F then some T else none
  | fuel + 1, T =>
      match F.find? (fun C => !Clause.eval (state U T) C) with
      | none => some T
      | some C =>
          match C.find? (fun l => !l.2) with
          | none => none
          | some l => run U F fuel (T.erase l.1)

def Correct (U : Finset Nat) (F : CNF) : Option (Finset Nat) → Prop
  | none => ¬ Satisfiable F
  | some T => CNF.eval (state U T) F = true ∧ Dominates F (state U T)

theorem run_correct (U : Finset Nat) (F : CNF) (dual : IsDualHorn F)
    (bounded : VariablesIn F U) (fuel : Nat) (T : Finset Nat)
    (enough : T.card ≤ fuel) (dom : Dominates F (state U T)) :
    Correct U F (run U F fuel T) := by
  induction fuel generalizing T with
  | zero =>
      by_cases good : CNF.eval (state U T) F = true
      · simpa [run, good, Correct] using And.intro good dom
      · have badF : CNF.eval (state U T) F = false := Bool.eq_false_iff.mpr good
        simp only [run, badF, Bool.false_eq_true, ↓reduceIte, Correct]
        rintro ⟨σ, hs⟩
        have em : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero enough)
        have heval : CNF.eval (state U T) F = true := by
          apply List.all_eq_true.mpr
          intro C hC
          obtain ⟨⟨x,p⟩, hx, hv⟩ := List.any_eq_true.mp (List.all_eq_true.mp hs C hC)
          cases p with
          | false =>
              exact List.any_eq_true.mpr ⟨(x,false), hx, by
                simp [Literal.eval, state, bounded C hC (x,false) hx, em]⟩
          | true =>
              have ht : σ x = true := by simpa [Literal.eval] using hv
              have hh := Bool.le_iff_imp.mp (dom σ hs x) ht
              simp [state, bounded C hC (x,true) hx, em] at hh
        exact good heval
  | succ fuel ih =>
      cases badFind : F.find? (fun C => !Clause.eval (state U T) C) with
      | none =>
          have good : CNF.eval (state U T) F = true := by
            apply List.all_eq_true.mpr
            intro C hC
            have hh := List.find?_eq_none.mp badFind C hC
            simpa using hh
          simpa [run, badFind, Correct] using And.intro good dom
      | some C =>
          have hC : C ∈ F := List.mem_of_find?_eq_some badFind
          have bad : Clause.eval (state U T) C = false := by
            simpa using List.find?_some badFind
          cases negFind : C.find? (fun l => !l.2) with
          | none =>
              simpa [run, badFind, negFind, Correct] using
                no_negative_unsat F C (state U T) hC dom bad negFind
          | some l =>
              have hl : l ∈ C := List.mem_of_find?_eq_some negFind
              have neg : l.2 = false := by simpa using List.find?_some negFind
              have drop := erase_strict_progress C T bad l hl neg (bounded C hC l hl)
              have small : (T.erase l.1).card ≤ fuel := by omega
              have inv := erase_preserves_domination F C (dual C hC) hC T dom bad l hl neg
              simpa [run, badFind, negFind] using ih (T.erase l.1) small inv

def solve (U : Finset Nat) (F : CNF) : Option (Finset Nat) := run U F U.card U

/-- With the explicit input-class and variable-range checks, solve returns
UNSAT correctly or a satisfying assignment dominating every model. -/
theorem solve_correct (U : Finset Nat) (F : CNF) (dual : IsDualHorn F)
    (bounded : VariablesIn F U) : Correct U F (solve U F) := by
  apply run_correct U F dual bounded U.card U
  · simp
  · intro σ hs x
    by_cases h : x ∈ U <;> simp [state, h]

def support (F : CNF) : Finset Nat :=
  (F.flatMap (fun C => C.map Prod.fst)).toFinset

theorem support_covers (F : CNF) : VariablesIn F (support F) := by
  intro C hC l hl
  exact List.mem_toFinset.mpr (List.mem_flatMap.mpr
    ⟨C, hC, List.mem_map.mpr ⟨l, hl, rfl⟩⟩)

theorem support_card_le_literal_occurrences (F : CNF) :
    (support F).card ≤ (F.flatMap (fun C => C.map Prod.fst)).length :=
  List.toFinset_card_le _

def solveSparse (F : CNF) : Option (Finset Nat) := solve (support F) F

theorem solveSparse_correct (F : CNF) (dual : IsDualHorn F) :
    Correct (support F) F (solveSparse F) :=
  solve_correct (support F) F dual (support_covers F)

-- Huge numeric IDs use only their distinct occurrence support as flip fuel.
example : solveSparse [[(1000000000,false)],[(1000000000,true),(7,true)]] =
    some {7} := by decide

#print axioms support_card_le_literal_occurrences
#print axioms solveSparse_correct
#print axioms negative_forced
#print axioms erase_preserves_domination
#print axioms erase_strict_progress
#print axioms run_correct
#print axioms solve_correct

end PEqualNP.Outside.SparseDualHornAlgorithm

