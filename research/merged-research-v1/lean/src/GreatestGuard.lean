import GuardedHall

/-! Restricted composition with an assumed feasible greatest retained assignment.
The static neighbor graph and row-private edge semantics are unchanged.
This does not prove existence of a greatest assignment for any CNF class.
-/
namespace PEqualNP.Outside.GreatestGuard

open PEqualNP.Outside.GuardedHall

variable {α R H : Type*} [Preorder α] [Finite R] [DecidableEq R] [DecidableEq H]

def GuardsMonotone (g : α → R → Bool) : Prop :=
  ∀ a b, a ≤ b → ∀ i, g a i = true → g b i = true

def EdgeWitness (N : R → Finset H) (g : R → Bool) (e : R → H → Bool) : Prop :=
  (∀ i h, e i h = true → h ∈ N i) ∧
  (∀ i, g i = true ∨ ∃ h ∈ N i, e i h = true) ∧
  (∀ i j h, e i h = true → e j h = true → i = j)

theorem edgeWitness_monotone (N : R → Finset H) (g : α → R → Bool)
    (monotone : GuardsMonotone g) {a b : α} (hab : a ≤ b)
    {e : R → H → Bool} (witness : EdgeWitness N (g a) e) :
    EdgeWitness N (g b) e := by
  rcases witness with ⟨valid, rows, unique⟩
  refine ⟨valid, ?_, unique⟩
  intro i
  rcases rows i with hg | he
  · exact Or.inl (monotone a b hab i hg)
  · exact Or.inr he

theorem extension_monotone (N : R → Finset H) (g : α → R → Bool)
    (monotone : GuardsMonotone g) {a b : α} (hab : a ≤ b) :
    HasPrivateEdges N (g a) → HasPrivateEdges N (g b) := by
  rintro ⟨e, he⟩
  exact ⟨e, edgeWitness_monotone N g monotone hab he⟩

theorem greatest_active_subset (F : Set α) (g : α → R → Bool)
    (monotone : GuardsMonotone g) (star : α)
    (greatest : ∀ a ∈ F, a ≤ star) {a : α} (feasible : a ∈ F) :
    {i | g star i = false} ⊆ {i | g a i = false} := by
  intro i hi
  change g a i = false
  have hstar : g star i = false := hi
  cases ha : g a i with
  | false => rfl
  | true =>
      have hg := monotone a star (greatest a feasible) i ha
      rw [hg] at hstar
      cases hstar

theorem exists_feasible_iff_at_greatest (F : Set α) (N : R → Finset H)
    (g : α → R → Bool) (monotone : GuardsMonotone g) (star : α)
    (star_feasible : star ∈ F) (greatest : ∀ a ∈ F, a ≤ star) :
    (∃ a ∈ F, HasPrivateEdges N (g a)) ↔ HasPrivateEdges N (g star) := by
  constructor
  · rintro ⟨a, ha, extension⟩
    exact extension_monotone N g monotone (greatest a ha) extension
  · intro extension
    exact ⟨star, star_feasible, extension⟩

theorem greatest_matching_iff_feasible_extension (F : Set α) (N : R → Finset H)
    (g : α → R → Bool) (monotone : GuardsMonotone g) (star : α)
    (star_feasible : star ∈ F) (greatest : ∀ a ∈ F, a ≤ star) :
    HasMatching N (g star) ↔ ∃ a ∈ F, HasPrivateEdges N (g a) :=
  (private_edges_iff_matching N (g star)).symm.trans
    (exists_feasible_iff_at_greatest F N g monotone star star_feasible greatest).symm

theorem greatest_failure_excludes_all (F : Set α) (N : R → Finset H)
    (g : α → R → Bool) (monotone : GuardsMonotone g) (star : α)
    (greatest : ∀ a ∈ F, a ≤ star) (failure : ¬ HasPrivateEdges N (g star)) :
    ∀ a ∈ F, ¬ HasPrivateEdges N (g a) := by
  intro a ha extension
  exact failure (extension_monotone N g monotone (greatest a ha) extension)

/-- The same concrete private-edge witness lifts to the feasible greatest
assignment; no new matching or hidden edge assignment is needed. -/
theorem concrete_witness_lift (F : Set α) (N : R → Finset H)
    (g : α → R → Bool) (monotone : GuardsMonotone g) (star : α)
    (star_feasible : star ∈ F) (greatest : ∀ a ∈ F, a ≤ star)
    {a : α} (ha : a ∈ F) {e : R → H → Bool} (witness : EdgeWitness N (g a) e) :
    star ∈ F ∧ EdgeWitness N (g star) e :=
  ⟨star_feasible, edgeWitness_monotone N g monotone (greatest a ha) witness⟩

#print axioms extension_monotone
#print axioms greatest_active_subset
#print axioms exists_feasible_iff_at_greatest
#print axioms greatest_matching_iff_feasible_extension
#print axioms greatest_failure_excludes_all
#print axioms concrete_witness_lift

end PEqualNP.Outside.GreatestGuard
