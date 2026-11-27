import Std.Tactic

namespace CompressionSoundness

-- The certificate rule does not assume that discovery is complete or efficient.
theorem equisat_of_projection {X Y : Type} (f : X → Bool) (g : Y → Bool)
    (project : X → Y) (lift : Y → X)
    (forward : ∀ x, f x = g (project x))
    (rightInverse : ∀ y, project (lift y) = y) :
    (∃ x, f x = true) ↔ (∃ y, g y = true) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨project x, (forward x).symm.trans hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨lift y, ?_⟩
    rw [forward, rightInverse]
    exact hy

def certificateCheck {X Y : Type} [DecidableEq Y] (xs : List X) (ys : List Y)
    (f : X → Bool) (g : Y → Bool) (project : X → Y) (lift : Y → X) : Bool :=
  xs.all (fun x => decide (f x = g (project x))) &&
    ys.all (fun y => decide (project (lift y) = y))

theorem certificateCheck_sound {X Y : Type} [DecidableEq Y]
    (xs : List X) (ys : List Y)
    (completeX : ∀ x, x ∈ xs) (completeY : ∀ y, y ∈ ys)
    (f : X → Bool) (g : Y → Bool) (project : X → Y) (lift : Y → X)
    (checked : certificateCheck xs ys f g project lift = true) :
    (∃ x, f x = true) ↔ (∃ y, g y = true) := by
  have pair := Bool.and_eq_true_iff.mp checked
  apply equisat_of_projection f g project lift
  · intro x
    exact of_decide_eq_true ((List.all_eq_true.mp pair.1) x (completeX x))
  · intro y
    exact of_decide_eq_true ((List.all_eq_true.mp pair.2) y (completeY y))

-- A useful equivalent rule when assignments have irrelevant unused coordinates.
theorem equisat_of_two_maps {X Y : Type} (f : X → Bool) (g : Y → Bool)
    (project : X → Y) (lift : Y → X)
    (forward : ∀ x, f x = g (project x))
    (backward : ∀ y, f (lift y) = g y) :
    (∃ x, f x = true) ↔ (∃ y, g y = true) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨project x, (forward x).symm.trans hx⟩
  · rintro ⟨y, hy⟩
    exact ⟨lift y, (backward y).trans hy⟩

abbrev Assignment := Nat → Bool
abbrev Lit := Bool × Nat
abbrev Clause := List Lit
abbrev CNF := List Clause

def evalLit (l : Lit) (a : Assignment) : Bool := if l.1 then a l.2 else !(a l.2)

def evalClause : Clause → Assignment → Bool
  | [], _ => false
  | l :: ls, a => evalLit l a || evalClause ls a

def evalCNF : CNF → Assignment → Bool
  | [], _ => true
  | c :: cs, a => evalClause c a && evalCNF cs a

theorem evalCNF_append (xs ys : CNF) (a : Assignment) :
    evalCNF (xs ++ ys) a = (evalCNF xs a && evalCNF ys a) := by
  induction xs with
  | nil => simp [evalCNF]
  | cons c cs ih => simp [evalCNF, ih, Bool.and_assoc]

#print axioms equisat_of_projection
#print axioms certificateCheck_sound
#print axioms equisat_of_two_maps

end CompressionSoundness
