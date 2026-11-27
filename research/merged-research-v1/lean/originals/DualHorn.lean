import PEqualNP.Defs.Search
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Preorder.Finite

namespace PEqualNP.Outside.DualHorn

open PEqualNP.Search

/-- The literal occurrence syntax has at most one negative literal per clause. -/
def IsDualHornClause (C : Clause) : Prop :=
  (C.filter (fun l => !l.2)).length ≤ 1

def IsDualHorn (F : CNF) : Prop := ∀ C ∈ F, IsDualHornClause C

def Positive (C : Clause) : Prop := ∀ l ∈ C, l.2 = true

def VariablesBelow (F : CNF) (n : Nat) : Prop := ∀ C ∈ F, ∀ l ∈ C, l.1 < n

def join {ι : Type*} (a b : ι → Bool) : ι → Bool := fun i => a i || b i

theorem le_join_left {ι : Type*} (a b : ι → Bool) : a ≤ join a b := by
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  simp [join, hi]

theorem le_join_right {ι : Type*} (a b : ι → Bool) : b ≤ join a b := by
  intro i
  apply Bool.le_iff_imp.mpr
  intro hi
  simp [join, hi]

private theorem short_list_unique {T : Type*} (L : List T) (h : L.length ≤ 1)
    {a b : T} (ha : a ∈ L) (hb : b ∈ L) : a = b := by
  cases L with
  | nil => simp at ha
  | cons c cs =>
      cases cs with
      | nil => simpa using (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm
      | cons d ds => simp at h

theorem negative_unique (C : Clause) (dual : IsDualHornClause C)
    {l k : Literal} (hl : l ∈ C) (hk : k ∈ C) (nl : l.2 = false) (nk : k.2 = false) :
    l = k := by
  apply short_list_unique (T := Literal) (a := l) (b := k)
    (C.filter (fun t : Literal => !t.2)) dual
  · exact List.mem_filter.mpr ⟨hl, by simp [nl]⟩
  · exact List.mem_filter.mpr ⟨hk, by simp [nk]⟩

theorem clause_join_closed (C : Clause) (dual : IsDualHornClause C)
    (σ τ : Assignment) (hs : Clause.eval σ C = true) (ht : Clause.eval τ C = true) :
    Clause.eval (join σ τ) C = true := by
  obtain ⟨⟨x, p⟩, hx, hv⟩ := List.any_eq_true.mp hs
  cases p with
  | true =>
      have hv' : σ x = true := by simpa [Literal.eval] using hv
      exact List.any_eq_true.mpr ⟨(x, true), hx, by simp [Literal.eval, join, hv']⟩
  | false =>
      have hv' : σ x = false := by simpa [Literal.eval] using hv
      obtain ⟨⟨y, q⟩, hy, hw⟩ := List.any_eq_true.mp ht
      cases q with
      | true =>
          have hw' : τ y = true := by simpa [Literal.eval] using hw
          exact List.any_eq_true.mpr ⟨(y, true), hy, by simp [Literal.eval, join, hw']⟩
      | false =>
          have hw' : τ y = false := by simpa [Literal.eval] using hw
          have heq := negative_unique C dual hx hy rfl rfl
          have hxy : x = y := congrArg Prod.fst heq
          subst y
          exact List.any_eq_true.mpr ⟨(x, false), hx, by simp [Literal.eval, join, hv', hw']⟩

theorem cnf_join_closed (F : CNF) (dual : IsDualHorn F)
    (σ τ : Assignment) (hs : CNF.eval σ F = true) (ht : CNF.eval τ F = true) :
    CNF.eval (join σ τ) F = true := by
  apply List.all_eq_true.mpr
  intro C hC
  exact clause_join_closed C (dual C hC) σ τ
    (List.all_eq_true.mp hs C hC) (List.all_eq_true.mp ht C hC)

theorem positive_clause_monotone (C : Clause) (positive : Positive C)
    (σ τ : Assignment) (hle : σ ≤ τ) (hs : Clause.eval σ C = true) :
    Clause.eval τ C = true := by
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.mp hs
  have hp := positive l hl
  have hx : σ l.1 = true := by simpa [Literal.eval, hp] using hv
  have hy : τ l.1 = true := (Bool.le_iff_imp.mp (hle l.1)) hx
  exact List.any_eq_true.mpr ⟨l, hl, by simp [Literal.eval, hp, hy]⟩

def extend {n : Nat} (a : Fin n → Bool) : Assignment :=
  fun v => if h : v < n then a ⟨v, h⟩ else true

theorem extend_join {n : Nat} (a b : Fin n → Bool) :
    extend (join a b) = join (extend a) (extend b) := by
  funext v
  by_cases hv : v < n <;> simp [extend, join, hv]

theorem restricted_model {n : Nat} (F : CNF) (bounded : VariablesBelow F n)
    (σ : Assignment) (model : CNF.eval σ F = true) :
    CNF.eval (extend (fun i : Fin n => σ i.val)) F = true := by
  apply List.all_eq_true.mpr
  intro C hC
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.mp (List.all_eq_true.mp model C hC)
  exact List.any_eq_true.mpr ⟨l, hl, by simpa [Literal.eval, extend, bounded C hC l hl] using hv⟩

/-- A satisfiable dual-Horn CNF on the stated finite variable range has a
greatest model under the actual pointwise Boolean order on assignments.
Unused variables outside the range are set true. This is an existence
proof via a finite maximal model, not an algorithm or time bound. -/
theorem exists_greatest_model {n : Nat} (F : CNF) (dual : IsDualHorn F)
    (bounded : VariablesBelow F n) (satisfiable : Satisfiable F) :
    ∃ star : Assignment, CNF.eval star F = true ∧
      ∀ σ : Assignment, CNF.eval σ F = true → σ ≤ star := by
  classical
  obtain ⟨σ, hs⟩ := satisfiable
  let Models : Set (Fin n → Bool) := {a | CNF.eval (extend a) F = true}
  have nonempty : Models.Nonempty :=
    ⟨fun i => σ i.val, restricted_model F bounded σ hs⟩
  obtain ⟨a, maximal⟩ := Models.toFinite.exists_maximal nonempty
  refine ⟨extend a, maximal.1, ?_⟩
  intro τ ht
  let b : Fin n → Bool := fun i => τ i.val
  have hb : b ∈ Models := restricted_model F bounded τ ht
  have hj : join a b ∈ Models := by
    change CNF.eval (extend (join a b)) F = true
    rw [extend_join]
    exact cnf_join_closed F dual (extend a) (extend b) maximal.1 hb
  have hba : b ≤ a := (le_join_right a b).trans (maximal.2 hj (le_join_left a b))
  intro v
  by_cases hv : v < n
  · simpa [extend, b, hv] using hba ⟨v, hv⟩
  · simp [extend, hv]

theorem positive_guard_family_monotone {R : Type*} (guards : R → Clause)
    (positive : ∀ i, Positive (guards i)) :
    ∀ σ τ : Assignment, σ ≤ τ → ∀ i,
      Clause.eval σ (guards i) = true → Clause.eval τ (guards i) = true := by
  intro σ τ hle i hs
  exact positive_clause_monotone (guards i) (positive i) σ τ hle hs

#print axioms clause_join_closed
#print axioms cnf_join_closed
#print axioms positive_clause_monotone
#print axioms exists_greatest_model
#print axioms positive_guard_family_monotone

end PEqualNP.Outside.DualHorn
