import PEqualNP.Defs.Search
import GuardedHall
import Mathlib.Logic.Function.Basic

namespace PEqualNP.Outside.GuardedCNFEncoding
open PEqualNP.Search
open PEqualNP.Outside.GuardedHall

variable {r h : Nat}
abbrev Edge (r h : Nat) := Fin r × Fin h

def neighborList (N : Fin r → Finset (Fin h)) (i : Fin r) : List (Fin h) :=
  (List.finRange h).filter (fun j => decide (j ∈ N i))

def rowClause (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (edge : Edge r h → Nat) (i : Fin r) : Clause :=
  guards i ++ (neighborList N i).map (fun j => (edge (i,j), true))

def rowCNF (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (edge : Edge r h → Nat) : CNF :=
  (List.finRange r).map (rowClause N guards edge)

def pairCNF (N : Fin r → Finset (Fin h)) (edge : Edge r h → Nat)
    (i j : Fin r) (k : Fin h) : CNF :=
  if i ≠ j ∧ k ∈ N i ∧ k ∈ N j then
    [[(edge (i,k),false), (edge (j,k),false)]] else []

def columnCNF (N : Fin r → Finset (Fin h)) (edge : Edge r h → Nat) : CNF :=
  (List.finRange r).flatMap (fun i => (List.finRange r).flatMap
    (fun j => (List.finRange h).flatMap (fun k => pairCNF N edge i j k)))

def encode (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (edge : Edge r h → Nat) : CNF :=
  F ++ rowCNF N guards edge ++ columnCNF N edge

def Rows (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (edge : Edge r h → Nat) (σ : Assignment) : Prop :=
  ∀ i, Clause.eval σ (guards i) = true ∨ ∃ k ∈ N i, σ (edge (i,k)) = true

def Columns (N : Fin r → Finset (Fin h)) (edge : Edge r h → Nat)
    (σ : Assignment) : Prop :=
  ∀ i j k, k ∈ N i → k ∈ N j →
    σ (edge (i,k)) = true → σ (edge (j,k)) = true → i = j

theorem rowClause_eval (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (edge : Edge r h → Nat) (σ : Assignment) (i : Fin r) :
    Clause.eval σ (rowClause N guards edge i) = true ↔
      Clause.eval σ (guards i) = true ∨ ∃ k ∈ N i, σ (edge (i,k)) = true := by
  simp [rowClause, neighborList, Clause.eval, Literal.eval, List.any_eq_true]

theorem rows_eval (N : Fin r → Finset (Fin h)) (guards : Fin r → Clause)
    (edge : Edge r h → Nat) (σ : Assignment) :
    CNF.eval σ (rowCNF N guards edge) = true ↔ Rows N guards edge σ := by
  simp [rowCNF, CNF.eval, List.all_eq_true, rowClause_eval, Rows]

theorem pair_eval (N : Fin r → Finset (Fin h)) (edge : Edge r h → Nat)
    (σ : Assignment) (i j : Fin r) (k : Fin h) :
    CNF.eval σ (pairCNF N edge i j k) = true ↔
      (i ≠ j ∧ k ∈ N i ∧ k ∈ N j →
       ¬ (σ (edge (i,k)) = true ∧ σ (edge (j,k)) = true)) := by
  by_cases hc : i ≠ j ∧ k ∈ N i ∧ k ∈ N j
  · cases hi : σ (edge (i,k)) <;> cases hj : σ (edge (j,k)) <;>
      simp [pairCNF, hc, CNF.eval, Clause.eval, Literal.eval, hi, hj]
  · simp [pairCNF, hc, CNF.eval]

theorem columns_eval (N : Fin r → Finset (Fin h)) (edge : Edge r h → Nat)
    (σ : Assignment) :
    CNF.eval σ (columnCNF N edge) = true ↔ Columns N edge σ := by
  have expanded : CNF.eval σ (columnCNF N edge) = true ↔
      ∀ i j k, CNF.eval σ (pairCNF N edge i j k) = true := by
    simp [columnCNF, CNF.eval, List.all_flatMap, List.all_eq_true]
  rw [expanded]
  simp only [pair_eval]
  constructor
  · intro noConflict i j k hi hj ei ej
    by_contra ne
    exact noConflict i j k ⟨ne, hi, hj⟩ ⟨ei, ej⟩
  · intro unique i j k hc he
    exact hc.1 (unique i j k hc.2.1 hc.2.2 he.1 he.2)

theorem eval_append (σ : Assignment) (A B : CNF) :
    CNF.eval σ (A ++ B) = true ↔ CNF.eval σ A = true ∧ CNF.eval σ B = true := by
  simp [CNF.eval]

theorem encode_eval (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (edge : Edge r h → Nat) (σ : Assignment) :
    CNF.eval σ (encode F N guards edge) = true ↔
      CNF.eval σ F = true ∧ Rows N guards edge σ ∧ Columns N edge σ := by
  simp only [encode, eval_append, rows_eval, columns_eval, and_assoc]

/-- No edge variable occurs in a retained or guard clause. This is a
syntactic disjointness obligation on the explicit constructor inputs. -/
def PrivateFromClause (edge : Edge r h → Nat) (C : Clause) : Prop :=
  ∀ l ∈ C, ∀ p, edge p ≠ l.1

def PrivateFromCNF (edge : Edge r h → Nat) (F : CNF) : Prop :=
  ∀ C ∈ F, PrivateFromClause edge C

noncomputable def glue (edge : Edge r h → Nat) (σ : Assignment)
    (e : Fin r → Fin h → Bool) : Assignment :=
  Function.extend edge (fun p => e p.1 p.2) σ

theorem glue_edge (edge : Edge r h → Nat) (injective : Function.Injective edge)
    (σ : Assignment) (e : Fin r → Fin h → Bool) (i : Fin r) (k : Fin h) :
    glue edge σ e (edge (i,k)) = e i k :=
  injective.extend_apply (fun p => e p.1 p.2) σ (i,k)

theorem glue_clause (edge : Edge r h → Nat) (σ : Assignment)
    (e : Fin r → Fin h → Bool) (C : Clause) (separate : PrivateFromClause edge C) :
    Clause.eval (glue edge σ e) C = true ↔ Clause.eval σ C = true := by
  have agrees : ∀ l ∈ C, glue edge σ e l.1 = σ l.1 := by
    intro l hl
    exact Function.extend_apply' (f := edge) (fun p : Edge r h => e p.1 p.2) σ l.1
      (by rintro ⟨p, hp⟩; exact separate l hl p hp)
  simp only [Clause.eval, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hv⟩
    exact ⟨l, hl, by simpa only [Literal.eval, agrees l hl] using hv⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨l, hl, by simpa only [Literal.eval, agrees l hl] using hv⟩

theorem extract_private_edges (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (edge : Edge r h → Nat) (σ : Assignment)
    (rows : Rows N guards edge σ) (columns : Columns N edge σ) :
    HasPrivateEdges N (fun i => Clause.eval σ (guards i)) := by
  let e : Fin r → Fin h → Bool := fun i k => if k ∈ N i then σ (edge (i,k)) else false
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i k he
    by_contra hn
    simp [e, hn] at he
  · intro i
    rcases rows i with hg | ⟨k, hk, he⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k, hk, by simp [e, hk, he]⟩
  · intro i j k hi hj
    have ni : k ∈ N i := by by_contra hn; simp [e, hn] at hi
    have nj : k ∈ N j := by by_contra hn; simp [e, hn] at hj
    exact columns i j k ni nj (by simpa [e, ni] using hi) (by simpa [e, nj] using hj)

theorem lift_private_edges (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (edge : Edge r h → Nat)
    (injective : Function.Injective edge) (retainedPrivate : PrivateFromCNF edge F)
    (guardsPrivate : ∀ i, PrivateFromClause edge (guards i))
    (σ : Assignment) (model : CNF.eval σ F = true)
    (witness : HasPrivateEdges N (fun i => Clause.eval σ (guards i))) :
    Satisfiable (encode F N guards edge) := by
  obtain ⟨e, valid, rows, unique⟩ := witness
  refine ⟨glue edge σ e, (encode_eval F N guards edge _).mpr ⟨?_, ?_, ?_⟩⟩
  · apply List.all_eq_true.mpr
    intro C hC
    exact (glue_clause edge σ e C (retainedPrivate C hC)).mpr
      (List.all_eq_true.mp model C hC)
  · intro i
    rcases rows i with hg | ⟨k, hk, he⟩
    · exact Or.inl ((glue_clause edge σ e (guards i) (guardsPrivate i)).mpr hg)
    · exact Or.inr ⟨k, hk, by simpa only [glue_edge edge injective] using he⟩
  · intro i j k hi hj ei ej
    exact unique i j k (by simpa only [glue_edge edge injective] using ei)
      (by simpa only [glue_edge edge injective] using ej)

theorem encoded_sat_iff_private_edges (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (edge : Edge r h → Nat)
    (injective : Function.Injective edge) (retainedPrivate : PrivateFromCNF edge F)
    (guardsPrivate : ∀ i, PrivateFromClause edge (guards i)) :
    Satisfiable (encode F N guards edge) ↔
      ∃ σ, CNF.eval σ F = true ∧ HasPrivateEdges N (fun i => Clause.eval σ (guards i)) := by
  constructor
  · rintro ⟨σ, hs⟩
    obtain ⟨hf, hr, hc⟩ := (encode_eval F N guards edge σ).mp hs
    exact ⟨σ, hf, extract_private_edges N guards edge σ hr hc⟩
  · rintro ⟨σ, hf, he⟩
    exact lift_private_edges F N guards edge injective retainedPrivate guardsPrivate σ hf he

theorem encoded_sat_iff_matching (F : CNF) (N : Fin r → Finset (Fin h))
    (guards : Fin r → Clause) (edge : Edge r h → Nat)
    (injective : Function.Injective edge) (retainedPrivate : PrivateFromCNF edge F)
    (guardsPrivate : ∀ i, PrivateFromClause edge (guards i)) :
    Satisfiable (encode F N guards edge) ↔
      ∃ σ, CNF.eval σ F = true ∧ HasMatching N (fun i => Clause.eval σ (guards i)) := by
  rw [encoded_sat_iff_private_edges F N guards edge injective retainedPrivate guardsPrivate]
  simp only [private_edges_iff_matching]

#print axioms rowClause_eval
#print axioms columns_eval
#print axioms glue_clause
#print axioms encode_eval
#print axioms encoded_sat_iff_private_edges
#print axioms encoded_sat_iff_matching
end PEqualNP.Outside.GuardedCNFEncoding
