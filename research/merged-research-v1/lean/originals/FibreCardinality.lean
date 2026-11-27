import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul

namespace FibreCardinality

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

-- A right inverse makes all fibres equinumerous with the kernel.
def preimageEquiv (p : X →+ Y) (lift : Y → X)
    (rightInverse : ∀ y, p (lift y) = y) (Q : Set Y) :
    {x : X // p x ∈ Q} ≃ ({y : Y // y ∈ Q} × {k : X // p k = 0}) where
  toFun x := (⟨p x, x.property⟩, ⟨x - lift (p x), by simp [rightInverse]⟩)
  invFun yk := ⟨lift yk.1 + yk.2, by simp [rightInverse, yk.2.property]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv yk := by
    apply Prod.ext <;> apply Subtype.ext
    · simp [rightInverse, yk.2.property]
    · simp [rightInverse, yk.2.property]

theorem preimage_card [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (p : X →+ Y) (lift : Y → X) (rightInverse : ∀ y, p (lift y) = y)
    (Q : Finset Y) :
    (Finset.univ.filter (fun x => p x ∈ Q)).card =
      Q.card * Fintype.card {k : X // p k = 0} := by
  have h := Fintype.card_congr (preimageEquiv p lift rightInverse (Q : Set Y))
  simpa [Fintype.card_subtype, Fintype.card_prod] using h

-- Distinctness is built into Finset. Lists must be deduplicated first.
theorem exact_preimage_of_count [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (p : X →+ Y) (lift : Y → X) (rightInverse : ∀ y, p (lift y) = y)
    (P : Finset X) (Q : Finset Y)
    (membership : ∀ x ∈ P, p x ∈ Q)
    (count : P.card = Q.card * Fintype.card {k : X // p k = 0}) :
    ∀ x, x ∈ P ↔ p x ∈ Q := by
  have subset : P ⊆ Finset.univ.filter (fun x => p x ∈ Q) := by
    intro x hx
    simp [membership x hx]
  have same : P = Finset.univ.filter (fun x => p x ∈ Q) :=
    Finset.eq_of_subset_of_card_le subset (by rw [preimage_card p lift rightInverse, count])
  intro x
  simp [same]

-- Equivalent count certificate that does not have to enumerate the kernel.
theorem exact_preimage_of_cross_count [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (p : X →+ Y) (lift : Y → X) (rightInverse : ∀ y, p (lift y) = y)
    (P : Finset X) (Q : Finset Y)
    (membership : ∀ x ∈ P, p x ∈ Q)
    (count : P.card * Fintype.card Y = Q.card * Fintype.card X) :
    ∀ x, x ∈ P ↔ p x ∈ Q := by
  have whole : Fintype.card X = Fintype.card Y * Fintype.card {k : X // p k = 0} := by
    simpa using preimage_card p lift rightInverse (Finset.univ : Finset Y)
  apply exact_preimage_of_count p lift rightInverse P Q membership
  apply Nat.eq_of_mul_eq_mul_right (Fintype.card_pos : 0 < Fintype.card Y)
  simpa [whole, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using count

abbrev Bits (n : Nat) := Fin n → ZMod 2

theorem bits_card (n : Nat) : Fintype.card (Bits n) = 2 ^ n := by
  simp [Bits, ZMod.card]

-- This is the proposed block certificate for arbitrary width, not a fixed-width example.
theorem binary_block_certificate {c d : Nat} (hd : d ≤ c)
    (p : Bits c →+ Bits d) (lift : Bits d → Bits c)
    (rightInverse : ∀ y, p (lift y) = y)
    (P : Finset (Bits c)) (Q : Finset (Bits d))
    (membership : ∀ x ∈ P, p x ∈ Q)
    (count : P.card = Q.card * 2 ^ (c-d)) :
    ∀ x, x ∈ P ↔ p x ∈ Q := by
  apply exact_preimage_of_cross_count p lift rightInverse P Q membership
  rw [bits_card, bits_card, count, Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hd]

-- Local forbidden sets may use different finite groups and coordinate maps.
-- The only global assumption is a projection with a right inverse.
theorem blocks_equisatisfiable
    {I A B : Type*} (project : A → B) (lift : B → A)
    (rightInverse : ∀ y, project (lift y) = y)
    (localBad : I → A → Prop) (quotientBad : I → B → Prop)
    (blocks : ∀ i x, localBad i x ↔ quotientBad i (project x)) :
    (∃ x, ∀ i, ¬ localBad i x) ↔ (∃ y, ∀ i, ¬ quotientBad i y) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨project x, fun i hi => hx i ((blocks i x).mpr hi)⟩
  · rintro ⟨y, hy⟩
    refine ⟨lift y, fun i hi => hy i ?_⟩
    simpa [rightInverse] using (blocks i (lift y)).mp hi

-- Compose the numeric certificates through checked local/global coordinate maps.
theorem counted_blocks_equisatisfiable
    {I A B : Type*} (c d : I → Nat) (hd : ∀ i, d i ≤ c i)
    (project : A → B) (lift : B → A)
    (globalRightInverse : ∀ y, project (lift y) = y)
    (localMap : ∀ i, Bits (c i) →+ Bits (d i))
    (localLift : ∀ i, Bits (d i) → Bits (c i))
    (localRightInverse : ∀ i y, localMap i (localLift i y) = y)
    (inputCoords : ∀ i, A → Bits (c i)) (outputCoords : ∀ i, B → Bits (d i))
    (compatible : ∀ i x, localMap i (inputCoords i x) = outputCoords i (project x))
    (P : ∀ i, Finset (Bits (c i))) (Q : ∀ i, Finset (Bits (d i)))
    (membership : ∀ i x, x ∈ P i → localMap i x ∈ Q i)
    (count : ∀ i, (P i).card = (Q i).card * 2 ^ (c i - d i)) :
    (∃ x, ∀ i, inputCoords i x ∉ P i) ↔ (∃ y, ∀ i, outputCoords i y ∉ Q i) := by
  apply blocks_equisatisfiable project lift globalRightInverse
  intro i x
  rw [← compatible i x]
  exact binary_block_certificate (hd i) (localMap i) (localLift i)
    (localRightInverse i) (P i) (Q i) (membership i) (count i) (inputCoords i x)

def matrixMap {c d : Nat} (M : Matrix (Fin d) (Fin c) (ZMod 2)) : Bits c →+ Bits d where
  toFun := M.mulVec
  map_zero' := Matrix.mulVec_zero M
  map_add' := Matrix.mulVec_add M

theorem matrix_right_inverse {c d : Nat}
    (M : Matrix (Fin d) (Fin c) (ZMod 2))
    (R : Matrix (Fin c) (Fin d) (ZMod 2)) (checked : M * R = 1) :
    ∀ y, matrixMap M (R.mulVec y) = y := by
  intro y
  change M.mulVec (R.mulVec y) = y
  rw [Matrix.mulVec_mulVec, checked, Matrix.one_mulVec]

-- Entrywise matrix equalities, point membership and finite-set counts suffice.
theorem matrix_block_certificate {c d : Nat} (hd : d ≤ c)
    (M : Matrix (Fin d) (Fin c) (ZMod 2))
    (R : Matrix (Fin c) (Fin d) (ZMod 2)) (checked : M * R = 1)
    (P : Finset (Bits c)) (Q : Finset (Bits d))
    (membership : ∀ x ∈ P, M.mulVec x ∈ Q)
    (count : P.card = Q.card * 2 ^ (c-d)) :
    ∀ x, x ∈ P ↔ M.mulVec x ∈ Q :=
  binary_block_certificate hd (matrixMap M) R.mulVec
    (matrix_right_inverse M R checked) P Q membership count

theorem matrix_compatibility {n r c d : Nat}
    (M : Matrix (Fin r) (Fin n) (ZMod 2))
    (S : Matrix (Fin c) (Fin n) (ZMod 2))
    (A : Matrix (Fin d) (Fin c) (ZMod 2))
    (T : Matrix (Fin d) (Fin r) (ZMod 2))
    (checked : A * S = T * M) (x : Bits n) :
    matrixMap A (S.mulVec x) = T.mulVec (M.mulVec x) := by
  change A.mulVec (S.mulVec x) = T.mulVec (M.mulVec x)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, checked]

#print axioms preimageEquiv
#print axioms preimage_card
#print axioms exact_preimage_of_count
#print axioms exact_preimage_of_cross_count
#print axioms binary_block_certificate
#print axioms blocks_equisatisfiable
#print axioms counted_blocks_equisatisfiable
#print axioms matrix_block_certificate
#print axioms matrix_compatibility

end FibreCardinality
