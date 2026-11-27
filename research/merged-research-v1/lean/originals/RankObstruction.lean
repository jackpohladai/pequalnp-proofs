import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-! A representation lower bound for the fixed all-x / all-y cut.
This does not assert a lower bound for SAT algorithms or the Python program.
-/
namespace PEqualNP.Outside.RankObstruction

open Matrix
open scoped Kronecker

def Bits : Nat → Type
  | 0 => Unit
  | k + 1 => Bool × Bits k

instance bitsFintype : (k : Nat) → Fintype (Bits k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => by
      letI := bitsFintype k
      exact inferInstanceAs (Fintype (Bool × Bits k))

instance bitsDecEq : (k : Nat) → DecidableEq (Bits k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => by
      letI := bitsDecEq k
      exact inferInstanceAs (DecidableEq (Bool × Bits k))

def base : Matrix Bool Bool (ZMod 2) :=
  fun x y => if x || y then 1 else 0

def baseInverse : Matrix Bool Bool (ZMod 2) :=
  fun x y => if x && y then 0 else 1

theorem base_mul_inverse : base * baseInverse = 1 := by decide
theorem inverse_mul_base : baseInverse * base = 1 := by decide

def kernel : (k : Nat) → Matrix (Bits k) (Bits k) (ZMod 2)
  | 0 => 1
  | k + 1 => base ⊗ₖ kernel k

def inverseKernel : (k : Nat) → Matrix (Bits k) (Bits k) (ZMod 2)
  | 0 => 1
  | k + 1 => baseInverse ⊗ₖ inverseKernel k

/-- The Boolean function AND_i (x_i OR y_i), with the two halves separated. -/
def jointIndicator : (k : Nat) → Bits k → Bits k → Bool
  | 0 => fun _ _ => true
  | k + 1 => fun x y => (x.1 || y.1) && jointIndicator k x.2 y.2

theorem kernel_entry (k : Nat) (x y : Bits k) :
    kernel k x y = if jointIndicator k x y then 1 else 0 := by
  induction k with
  | zero => cases x; cases y; rfl
  | succ k ih =>
      rcases x with ⟨x, xs⟩
      rcases y with ⟨y, ys⟩
      change base x y * kernel k xs ys =
        if (x || y) && jointIndicator k xs ys then 1 else 0
      rw [ih]
      cases x <;> cases y <;> cases h : jointIndicator k xs ys <;> simp [base, h]

theorem kernel_mul_inverse (k : Nat) : kernel k * inverseKernel k = 1 := by
  induction k with
  | zero => simp [kernel, inverseKernel]
  | succ k ih =>
      change (base ⊗ₖ kernel k) * (baseInverse ⊗ₖ inverseKernel k) = 1
      rw [← Matrix.mul_kronecker_mul, base_mul_inverse, ih, Matrix.one_kronecker_one]

theorem inverse_mul_kernel (k : Nat) : inverseKernel k * kernel k = 1 := by
  induction k with
  | zero => simp [kernel, inverseKernel]
  | succ k ih =>
      change (baseInverse ⊗ₖ inverseKernel k) * (base ⊗ₖ kernel k) = 1
      rw [← Matrix.mul_kronecker_mul, inverse_mul_base, ih, Matrix.one_kronecker_one]

theorem bits_card (k : Nat) : Fintype.card (Bits k) = 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      change Fintype.card (Bool × Bits k) = 2 ^ (k+1)
      simp [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

theorem kernel_rank (k : Nat) : (kernel k).rank = 2 ^ k := by
  apply le_antisymm
  · simpa only [bits_card] using Matrix.rank_le_card_width (kernel k)
  · have h := Matrix.rank_mul_le_left (kernel k) (inverseKernel k)
    rw [kernel_mul_inverse, Matrix.rank_one, bits_card] at h
    exact h

/-- Any exact cut factorization has at least 2^k intermediate coordinates. -/
theorem factorization_width_bound (k d : Nat)
    (L : Matrix (Bits k) (Fin d) (ZMod 2))
    (R : Matrix (Fin d) (Bits k) (ZMod 2))
    (h : L * R = kernel k) : 2 ^ k ≤ d := by
  have h₁ := Matrix.rank_mul_le_left L R
  have h₂ := Matrix.rank_le_card_width L
  rw [h, kernel_rank] at h₁
  simpa using h₁.trans h₂

#print axioms base_mul_inverse
#print axioms kernel_mul_inverse
#print axioms inverse_mul_kernel
#print axioms kernel_entry
#print axioms kernel_rank
#print axioms factorization_width_bound

end PEqualNP.Outside.RankObstruction
