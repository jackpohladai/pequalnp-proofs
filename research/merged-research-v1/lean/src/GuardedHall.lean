import Mathlib.Combinatorics.Hall.Finite

/-! Exact matching projection at one fixed retained-variable assignment.
Rows and holes are separate types. Every choice belongs to exactly one row;
only its hole can conflict with a choice of another row. No CNF recognizer,
polynomial cut enumeration, or general SAT algorithm is claimed here.
-/
namespace PEqualNP.Outside.GuardedHall

variable {R H : Type*} [Finite R] [DecidableEq R] [DecidableEq H]

abbrev Active (g : R → Bool) := {i : R // g i = false}

def HasMatching (N : R → Finset H) (g : R → Bool) : Prop :=
  ∃ f : Active g → H, Function.Injective f ∧ ∀ i, f i ∈ N i.val

/-- Every deficient group of rows has at least one row whose guard is true. -/
def GuardedCuts (N : R → Finset H) (g : R → Bool) : Prop :=
  ∀ S : Finset R, (S.biUnion N).card < S.card → ∃ i ∈ S, g i = true

theorem guarded_cuts_iff_matching (N : R → Finset H) (g : R → Bool) :
    GuardedCuts N g ↔ HasMatching N g := by
  classical
  have hall := Finset.all_card_le_biUnion_card_iff_existsInjective'
    (fun i : Active g => N i.val)
  constructor
  · intro cuts
    apply hall.mp
    intro T
    by_contra hn
    let S : Finset R := T.image Subtype.val
    have hc : S.card = T.card := Finset.card_image_of_injective T Subtype.coe_injective
    have hu : S.biUnion N = T.biUnion (fun i : Active g => N i.val) := by
      exact Finset.image_biUnion
    have hd : (S.biUnion N).card < S.card := by
      rw [hc, hu]
      exact Nat.lt_of_not_ge hn
    obtain ⟨i, hi, hg⟩ := cuts S hd
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    have ha : g a.val = false := a.property
    simp [ha] at hg
  · intro matching S deficient
    by_contra hn
    have all_false : ∀ i ∈ S, g i = false := by
      intro i hi
      cases hg : g i with
      | false => rfl
      | true => exact False.elim (hn ⟨i, hi, hg⟩)
    let T : Finset (Active g) := S.subtype (fun i => g i = false)
    have hc : T.card = S.card := by
      change (S.subtype (fun i => g i = false)).card = S.card
      rw [Finset.card_subtype]
      rw [Finset.filter_eq_self.mpr all_false]
    have hu : T.biUnion (fun i : Active g => N i.val) = S.biUnion N := by
      ext h
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨i, hi, hh⟩
        exact ⟨i.val, Finset.mem_subtype.mp hi, hh⟩
      · rintro ⟨i, hi, hh⟩
        exact ⟨⟨i, all_false i hi⟩, Finset.mem_subtype.mpr hi, hh⟩
    have bound := hall.mpr matching T
    rw [hc, hu] at bound
    exact (Nat.not_lt_of_ge bound) deficient

/-- Each edge Boolean has its own row and hole. There are no other constraints
on these private variables; the retained assignment has already fixed g. -/
def HasPrivateEdges (N : R → Finset H) (g : R → Bool) : Prop :=
  ∃ e : R → H → Bool,
    (∀ i h, e i h = true → h ∈ N i) ∧
    (∀ i, g i = true ∨ ∃ h ∈ N i, e i h = true) ∧
    (∀ i j h, e i h = true → e j h = true → i = j)

theorem private_edges_iff_matching (N : R → Finset H) (g : R → Bool) :
    HasPrivateEdges N g ↔ HasMatching N g := by
  classical
  constructor
  · rintro ⟨e, _, rows, unique⟩
    have choices : ∀ i : Active g, ∃ h, h ∈ N i.val ∧ e i.val h = true := by
      intro i
      rcases rows i.val with hg | hs
      · have hf := i.property
        simp [hf] at hg
      · exact hs
    let f : Active g → H := fun i => Classical.choose (choices i)
    have hf : ∀ i, f i ∈ N i.val ∧ e i.val (f i) = true :=
      fun i => Classical.choose_spec (choices i)
    refine ⟨f, ?_, fun i => (hf i).1⟩
    intro i j hij
    apply Subtype.ext
    apply unique i.val j.val (f i) (hf i).2
    rw [hij]
    exact (hf j).2
  · rintro ⟨f, injective, neighbors⟩
    let e : R → H → Bool := fun i h =>
      if hi : g i = false then decide (f ⟨i, hi⟩ = h) else false
    refine ⟨e, ?_, ?_, ?_⟩
    · intro i h eh
      by_cases hi : g i = false
      · have heq : f ⟨i, hi⟩ = h := by simpa [e, hi] using eh
        rw [← heq]
        exact neighbors ⟨i, hi⟩
      · simp [e, hi] at eh
    · intro i
      cases hi : g i with
      | true => exact Or.inl rfl
      | false =>
          exact Or.inr ⟨f ⟨i, hi⟩, neighbors ⟨i, hi⟩, by simp [e, hi]⟩
    · intro i j h ei ej
      by_cases hi : g i = false
      · by_cases hj : g j = false
        · have hfi : f ⟨i, hi⟩ = h := by simpa [e, hi] using ei
          have hfj : f ⟨j, hj⟩ = h := by simpa [e, hj] using ej
          exact congrArg Subtype.val (injective (hfi.trans hfj.symm))
        · simp [e, hj] at ej
      · simp [e, hi] at ei

theorem guarded_hall_projection (N : R → Finset H) (g : R → Bool) :
    HasPrivateEdges N g ↔ GuardedCuts N g :=
  (private_edges_iff_matching N g).trans (guarded_cuts_iff_matching N g).symm

/-- The minimal guarded two-row, one-hole example. -/
theorem two_row_projection (x y : Bool) :
    (∃ p q : Bool, ((p || x) && (q || !y) && !(p && q)) = true) ↔
      (x || !y) = true := by
  cases x <;> cases y <;> decide

#print axioms guarded_cuts_iff_matching
#print axioms private_edges_iff_matching
#print axioms guarded_hall_projection
#print axioms two_row_projection

end PEqualNP.Outside.GuardedHall
