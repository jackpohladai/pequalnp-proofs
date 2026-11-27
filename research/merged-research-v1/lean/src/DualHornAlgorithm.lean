import DualHorn
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

namespace PEqualNP.Outside.DualHornAlgorithm
open PEqualNP.Search
open PEqualNP.Outside.DualHorn

/-- Variables in the bounded range are true exactly when still in T.
Variables outside the declared input range stay true. -/
def state (n : Nat) (T : Finset Nat) : Assignment :=
  fun x => if x < n then decide (x ∈ T) else true

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

theorem erase_preserves_domination {n : Nat} (F : CNF) (C : Clause)
    (dual : IsDualHornClause C) (inF : C ∈ F) (T : Finset Nat)
    (dom : Dominates F (state n T)) (bad : Clause.eval (state n T) C = false)
    (l : Literal) (member : l ∈ C) (negative : l.2 = false) :
    Dominates F (state n (T.erase l.1)) := by
  intro σ hs x
  have below := dom σ hs
  by_cases hxl : x = l.1
  · subst x
    have forced := negative_forced C dual (state n T) σ below bad
      (List.all_eq_true.mp hs C inF) l member negative
    simp [forced]
  · by_cases hxn : x < n
    · simpa [state, hxn, Finset.mem_erase, hxl] using below x
    · simp [state, hxn]

theorem erase_strict_progress {n : Nat} (C : Clause) (T : Finset Nat)
    (bad : Clause.eval (state n T) C = false)
    (l : Literal) (member : l ∈ C) (negative : l.2 = false) (bounded : l.1 < n) :
    (T.erase l.1).card + 1 = T.card := by
  have hf := bad_literal_false C (state n T) bad l member
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
def run (n : Nat) (F : CNF) : Nat → Finset Nat → Option (Finset Nat)
  | 0, T => if CNF.eval (state n T) F then some T else none
  | fuel + 1, T =>
      match F.find? (fun C => !Clause.eval (state n T) C) with
      | none => some T
      | some C =>
          match C.find? (fun l => !l.2) with
          | none => none
          | some l => run n F fuel (T.erase l.1)

def Correct (n : Nat) (F : CNF) : Option (Finset Nat) → Prop
  | none => ¬ Satisfiable F
  | some T => CNF.eval (state n T) F = true ∧ Dominates F (state n T)

theorem run_correct (n : Nat) (F : CNF) (dual : IsDualHorn F)
    (bounded : VariablesBelow F n) (fuel : Nat) (T : Finset Nat)
    (enough : T.card ≤ fuel) (dom : Dominates F (state n T)) :
    Correct n F (run n F fuel T) := by
  induction fuel generalizing T with
  | zero =>
      by_cases good : CNF.eval (state n T) F = true
      · simpa [run, good, Correct] using And.intro good dom
      · have badF : CNF.eval (state n T) F = false := Bool.eq_false_iff.mpr good
        simp only [run, badF, Bool.false_eq_true, ↓reduceIte, Correct]
        rintro ⟨σ, hs⟩
        have em : T = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero enough)
        have heval : CNF.eval (state n T) F = true := by
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
      cases badFind : F.find? (fun C => !Clause.eval (state n T) C) with
      | none =>
          have good : CNF.eval (state n T) F = true := by
            apply List.all_eq_true.mpr
            intro C hC
            have hh := List.find?_eq_none.mp badFind C hC
            simpa using hh
          simpa [run, badFind, Correct] using And.intro good dom
      | some C =>
          have hC : C ∈ F := List.mem_of_find?_eq_some badFind
          have bad : Clause.eval (state n T) C = false := by
            simpa using List.find?_some badFind
          cases negFind : C.find? (fun l => !l.2) with
          | none =>
              simpa [run, badFind, negFind, Correct] using
                no_negative_unsat F C (state n T) hC dom bad negFind
          | some l =>
              have hl : l ∈ C := List.mem_of_find?_eq_some negFind
              have neg : l.2 = false := by simpa using List.find?_some negFind
              have drop := erase_strict_progress C T bad l hl neg (bounded C hC l hl)
              have small : (T.erase l.1).card ≤ fuel := by omega
              have inv := erase_preserves_domination F C (dual C hC) hC T dom bad l hl neg
              simpa [run, badFind, negFind] using ih (T.erase l.1) small inv

def solve (n : Nat) (F : CNF) : Option (Finset Nat) := run n F n (Finset.range n)

/-- With the explicit input-class and variable-range checks, solve returns
UNSAT correctly or a satisfying assignment dominating every model. -/
theorem solve_correct (n : Nat) (F : CNF) (dual : IsDualHorn F)
    (bounded : VariablesBelow F n) : Correct n F (solve n F) := by
  apply run_correct n F dual bounded n (Finset.range n)
  · simp
  · intro σ hs x
    by_cases h : x < n <;> simp [state, h]

#print axioms negative_forced
#print axioms erase_preserves_domination
#print axioms erase_strict_progress
#print axioms run_correct
#print axioms solve_correct

end PEqualNP.Outside.DualHornAlgorithm
