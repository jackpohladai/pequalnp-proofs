import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite paired-event certificates. Counts are exact finite-set counts.
No affine probability implementation, refinement, runtime or general SAT claim.
-/
namespace PEqualNP.Outside.PairedUnion

open scoped BigOperators

variable {Ω I : Type*} [DecidableEq Ω]

def badMass (D : Finset Ω) (P : Finset I) (A B : I → Finset Ω) : Nat :=
  ∑ i ∈ P, (D ∩ (A i ∪ B i)).card

def individualMass (D : Finset Ω) (P : Finset I) (A B : I → Finset Ω) : Nat :=
  ∑ i ∈ P, ((D ∩ A i).card + (D ∩ B i).card)

theorem certificate_exists (D : Finset Ω) (P : Finset I) (A B : I → Finset Ω)
    (certificate : badMass D P A B < D.card) :
    ∃ x ∈ D, ∀ i ∈ P, x ∉ A i ∪ B i := by
  classical
  let U := P.biUnion (fun i => D ∩ (A i ∪ B i))
  have bound : U.card ≤ badMass D P A B := Finset.card_biUnion_le
  obtain ⟨x, hx, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card (bound.trans_lt certificate)
  refine ⟨x, hx, ?_⟩
  intro i hi he
  apply hu
  exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hx, he⟩⟩

theorem badMass_disjoint_union (D₀ D₁ : Finset Ω) (P : Finset I)
    (A B : I → Finset Ω) (disjoint : Disjoint D₀ D₁) :
    badMass (D₀ ∪ D₁) P A B = badMass D₀ P A B + badMass D₁ P A B := by
  unfold badMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.union_inter_distrib_right]
  apply Finset.card_union_of_disjoint
  exact disjoint.mono Finset.inter_subset_left Finset.inter_subset_left

/-- A strict certificate survives in at least one part of any disjoint
partition. The branches need not have equal sizes. -/
theorem certificate_branch (D₀ D₁ : Finset Ω) (P : Finset I)
    (A B : I → Finset Ω) (disjoint : Disjoint D₀ D₁)
    (certificate : badMass (D₀ ∪ D₁) P A B < (D₀ ∪ D₁).card) :
    badMass D₀ P A B < D₀.card ∨ badMass D₁ P A B < D₁.card := by
  rw [badMass_disjoint_union D₀ D₁ P A B disjoint,
    Finset.card_union_of_disjoint disjoint] at certificate
  by_cases h₀ : badMass D₀ P A B < D₀.card
  · exact Or.inl h₀
  by_cases h₁ : badMass D₁ P A B < D₁.card
  · exact Or.inr h₁
  have bound := Nat.add_le_add (Nat.le_of_not_gt h₀) (Nat.le_of_not_gt h₁)
  exact False.elim ((Nat.not_lt_of_ge bound) certificate)

theorem singleton_terminal (x : Ω) (P : Finset I) (A B : I → Finset Ω)
    (certificate : badMass {x} P A B < ({x} : Finset Ω).card) :
    ∀ i ∈ P, x ∉ A i ∪ B i := by
  obtain ⟨y, hy, good⟩ := certificate_exists {x} P A B certificate
  have heq : y = x := Finset.mem_singleton.mp hy
  subst y
  exact good

theorem paired_le_individual (D : Finset Ω) (P : Finset I) (A B : I → Finset Ω) :
    badMass D P A B ≤ individualMass D P A B := by
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.inter_union_distrib_left]
  exact Finset.card_union_le (D ∩ A i) (D ∩ B i)

#print axioms certificate_exists
#print axioms badMass_disjoint_union
#print axioms certificate_branch
#print axioms singleton_terminal
#print axioms paired_le_individual

end PEqualNP.Outside.PairedUnion
