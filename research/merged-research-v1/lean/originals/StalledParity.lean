import PEqualNP.Defs.Search
import Mathlib.Tactic.Linarith

/-!
Local synthesis: parity padding defeats the literal-count pivot certificate.
This is a component/obstruction proof, not SAT in P and not an upstream submission.
The original formula is renamed to identifiers divisible by 3. Each padding
gadget uses its own other two residue classes. Padding never removes or solves
the original SAT obligation.
-/

namespace PEqualNP.Outside.StalledParity

open PEqualNP.Search

def parityGadget (x a b : Nat) : CNF :=
  [[(x, true), (a, true), (b, true)],
   [(x, true), (a, false), (b, false)],
   [(x, false), (a, true), (b, false)],
   [(x, false), (a, false), (b, true)]]

theorem parityGadget_eval (σ : Assignment) (x a b : Nat) :
    CNF.eval σ (parityGadget x a b) = ((σ x ^^ σ a) ^^ σ b) := by
  cases hx : σ x <;> cases ha : σ a <;> cases hb : σ b <;>
    simp [parityGadget, CNF.eval, Clause.eval, Literal.eval, hx, ha, hb]

/-- These are exactly the four raw resolvents obtained by eliminating the
middle variable from the gadget. All four are tautologies and may be dropped. -/
def auxiliaryResolvents (x b : Nat) : CNF :=
  [[(x, true), (b, true), (x, true), (b, false)],
   [(x, true), (b, true), (x, false), (b, true)],
   [(x, false), (b, false), (x, true), (b, false)],
   [(x, false), (b, false), (x, false), (b, true)]]

theorem auxiliaryResolvents_tautological (σ : Assignment) (x b : Nat) :
    CNF.eval σ (auxiliaryResolvents x b) = true := by
  cases hx : σ x <;> cases hb : σ b <;>
    simp [auxiliaryResolvents, CNF.eval, Clause.eval, Literal.eval, hx, hb]

def renameFormula (F : CNF) : CNF :=
  F.map (fun C => C.map (fun l => (3 * l.1, l.2)))

def padding (xs : List Nat) : CNF :=
  xs.flatMap (fun x => parityGadget (3*x) (3*x+1) (3*x+2))

def padded (F : CNF) (xs : List Nat) : CNF :=
  renameFormula F ++ padding xs

/-- Original variables and the first auxiliaries share their truth value; the
second auxiliary is true. This satisfies every added odd-parity constraint. -/
def extend (σ : Assignment) (i : Nat) : Bool :=
  if i % 3 = 2 then true else σ (i / 3)

theorem extend_original (σ : Assignment) (x : Nat) : extend σ (3*x) = σ x := by
  simp [extend, Nat.mul_comm]

theorem extend_aux1 (σ : Assignment) (x : Nat) : extend σ (3*x+1) = σ x := by
  simp [extend, Nat.add_div, Nat.add_mod, Nat.mul_comm]

theorem extend_aux2 (σ : Assignment) (x : Nat) : extend σ (3*x+2) = true := by
  simp [extend, Nat.add_mod, Nat.mul_comm]

theorem eval_rename (σ : Assignment) (F : CNF) :
    CNF.eval σ (renameFormula F) = CNF.eval (fun x => σ (3*x)) F := by
  simp only [CNF.eval, renameFormula, List.all_map]
  congr 1
  funext C
  simp [Function.comp_def, Clause.eval, Literal.eval, List.any_map]
  rfl

theorem eval_padding_extend (σ : Assignment) (xs : List Nat) :
    CNF.eval (extend σ) (padding xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [padding, List.flatMap_cons, CNF.eval, List.all_append] at *
    have hg : CNF.eval (extend σ) (parityGadget (3*x) (3*x+1) (3*x+2)) = true := by
      rw [parityGadget_eval, extend_original, extend_aux1, extend_aux2]
      cases σ x <;> rfl
    change CNF.eval (extend σ) (parityGadget (3*x) (3*x+1) (3*x+2)) && _ = true
    rw [hg, ih]
    rfl

/-- The entire original CNF remains exactly the existential projection of the
padded formula. This theorem is uniform in the formula and variable list. -/
theorem padded_satisfiable_iff (F : CNF) (xs : List Nat) :
    Satisfiable (padded F xs) ↔ Satisfiable F := by
  constructor
  · rintro ⟨σ, hσ⟩
    have hp : CNF.eval σ (renameFormula F) = true ∧
        CNF.eval σ (padding xs) = true := by
      simpa only [padded, CNF.eval, List.all_append, Bool.and_eq_true] using hσ
    rw [eval_rename] at hp
    exact ⟨fun x => σ (3*x), hp.1⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨extend σ, ?_⟩
    have hr : CNF.eval (extend σ) (renameFormula F) = true := by
      rw [eval_rename]
      simpa only [extend_original] using hσ
    simp only [padded, CNF.eval, List.all_append]
    change CNF.eval (extend σ) (renameFormula F) && CNF.eval (extend σ) (padding xs) = true
    rw [hr, eval_padding_extend]
    rfl

theorem padding_clause_count (xs : List Nat) : (padding xs).length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [padding, parityGadget] at *; omega

/-- For proper width-three clauses A=2p and B=2q. Two occurrences of each
polarity already force the proposed pivot certificate to fail by at least 4. -/
theorem width_three_pivot_gap (p q : Int) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    4 ≤ q * (2*p) + p * (2*q) - (2*p + 2*q + p + q) := by
  have hprod : 0 ≤ (p-2)*(q-2) := mul_nonneg (by omega) (by omega)
  nlinarith

#print axioms parityGadget_eval
#print axioms auxiliaryResolvents_tautological
#print axioms padded_satisfiable_iff
#print axioms padding_clause_count
#print axioms width_three_pivot_gap

end PEqualNP.Outside.StalledParity
