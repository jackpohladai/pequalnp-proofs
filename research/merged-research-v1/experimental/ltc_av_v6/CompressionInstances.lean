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

namespace CompressionInstances
local instance : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩
local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
open CompressionSoundness
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem xor_cancel (a b : Bool) : (a ^^ (a ^^ b)) = b := by
  cases a <;> cases b <;> rfl

def case36_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 6) ^^ false))
  | 1 => ((a 1) ^^ ((a 7) ^^ false))
  | 2 => ((a 2) ^^ ((a 8) ^^ false))
  | 3 => ((a 3) ^^ ((a 9) ^^ false))
  | 4 => ((a 4) ^^ ((a 10) ^^ false))
  | 5 => ((a 5) ^^ ((a 11) ^^ false))
  | _ => false

def case36_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => ((a 1) ^^ false)
  | 2 => ((a 2) ^^ false)
  | 3 => ((a 3) ^^ false)
  | 4 => ((a 4) ^^ false)
  | 5 => ((a 5) ^^ false)
  | 6 => false
  | 7 => false
  | 8 => false
  | 9 => false
  | 10 => false
  | 11 => false
  | _ => false

def case36_b0 : CNF := [[(false, 9), (false, 6), (false, 3), (true, 0)], [(false, 9), (false, 3), (false, 0), (true, 6)], [(false, 6), (true, 0), (true, 3), (true, 9)], [(false, 0), (true, 3), (true, 6), (true, 9)]]
def case36_q0 : CNF := [[(false, 0), (true, 3)]]
theorem case36_b0_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b1) || ((!b0) || (b2 || false)))) && (((!b2) || (b0 || (b1 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b2 ^^ false))) || ((b1 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem case36_b0_correct (a : Assignment) : evalCNF case36_b0 a = evalCNF case36_q0 (case36_project a) := by
  exact case36_b0_table (a 0) (a 3) (a 6) (a 9)

def case36_b1 : CNF := [[(false, 10), (false, 6), (true, 0), (true, 4)], [(false, 10), (false, 0), (true, 4), (true, 6)], [(false, 6), (false, 4), (true, 0), (true, 10)], [(false, 4), (false, 0), (true, 6), (true, 10)]]
def case36_q1 : CNF := [[(false, 0), (false, 4)]]
theorem case36_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || (b0 || (b1 || false)))) && (((!b3) || ((!b0) || (b1 || (b2 || false)))) && (((!b2) || ((!b1) || (b0 || (b3 || false)))) && (((!b1) || ((!b0) || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b2 ^^ false))) || ((!(b1 ^^ (b3 ^^ false))) || false)) && true) := by
  decide +revert
theorem case36_b1_correct (a : Assignment) : evalCNF case36_b1 a = evalCNF case36_q1 (case36_project a) := by
  exact case36_b1_table (a 0) (a 4) (a 6) (a 10)

def case36_b2 : CNF := [[(false, 11), (false, 6), (false, 5), (false, 0)], [(false, 11), (false, 5), (true, 0), (true, 6)], [(false, 6), (false, 0), (true, 5), (true, 11)], [(true, 0), (true, 5), (true, 6), (true, 11)]]
def case36_q2 : CNF := [[(true, 0), (true, 5)]]
theorem case36_b2_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || ((!b0) || false)))) && (((!b3) || ((!b1) || (b0 || (b2 || false)))) && (((!b2) || ((!b0) || (b1 || (b3 || false)))) && ((b0 || (b1 || (b2 || (b3 || false)))) && true)))) = (((b0 ^^ (b2 ^^ false)) || ((b1 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem case36_b2_correct (a : Assignment) : evalCNF case36_b2 a = evalCNF case36_q2 (case36_project a) := by
  exact case36_b2_table (a 0) (a 5) (a 6) (a 11)

def case36_b3 : CNF := [[(false, 9), (false, 7), (false, 1), (true, 3)], [(false, 9), (true, 1), (true, 3), (true, 7)], [(false, 7), (false, 3), (false, 1), (true, 9)], [(false, 3), (true, 1), (true, 7), (true, 9)]]
def case36_q3 : CNF := [[(true, 1), (false, 3)]]
theorem case36_b3_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b3) || (b0 || (b1 || (b2 || false)))) && (((!b2) || ((!b1) || ((!b0) || (b3 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && true)))) = (((b0 ^^ (b2 ^^ false)) || ((!(b1 ^^ (b3 ^^ false))) || false)) && true) := by
  decide +revert
theorem case36_b3_correct (a : Assignment) : evalCNF case36_b3 a = evalCNF case36_q3 (case36_project a) := by
  exact case36_b3_table (a 1) (a 3) (a 7) (a 9)

def case36_b4 : CNF := [[(false, 10), (false, 7), (false, 4), (true, 1)], [(false, 10), (false, 4), (false, 1), (true, 7)], [(false, 7), (true, 1), (true, 4), (true, 10)], [(false, 1), (true, 4), (true, 7), (true, 10)]]
def case36_q4 : CNF := [[(false, 1), (true, 4)]]
theorem case36_b4_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b1) || ((!b0) || (b2 || false)))) && (((!b2) || (b0 || (b1 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b2 ^^ false))) || ((b1 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem case36_b4_correct (a : Assignment) : evalCNF case36_b4 a = evalCNF case36_q4 (case36_project a) := by
  exact case36_b4_table (a 1) (a 4) (a 7) (a 10)

def case36_b5 : CNF := [[(false, 11), (false, 7), (true, 1), (true, 5)], [(false, 11), (false, 1), (true, 5), (true, 7)], [(false, 7), (false, 5), (true, 1), (true, 11)], [(false, 5), (false, 1), (true, 7), (true, 11)]]
def case36_q5 : CNF := [[(false, 1), (false, 5)]]
theorem case36_b5_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || (b0 || (b1 || false)))) && (((!b3) || ((!b0) || (b1 || (b2 || false)))) && (((!b2) || ((!b1) || (b0 || (b3 || false)))) && (((!b1) || ((!b0) || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b2 ^^ false))) || ((!(b1 ^^ (b3 ^^ false))) || false)) && true) := by
  decide +revert
theorem case36_b5_correct (a : Assignment) : evalCNF case36_b5 a = evalCNF case36_q5 (case36_project a) := by
  exact case36_b5_table (a 1) (a 5) (a 7) (a 11)

def case36_b6 : CNF := [[(false, 9), (false, 8), (false, 3), (false, 2)], [(false, 9), (false, 3), (true, 2), (true, 8)], [(false, 8), (false, 2), (true, 3), (true, 9)], [(true, 2), (true, 3), (true, 8), (true, 9)]]
def case36_q6 : CNF := [[(true, 2), (true, 3)]]
theorem case36_b6_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || ((!b0) || false)))) && (((!b3) || ((!b1) || (b0 || (b2 || false)))) && (((!b2) || ((!b0) || (b1 || (b3 || false)))) && ((b0 || (b1 || (b2 || (b3 || false)))) && true)))) = (((b0 ^^ (b2 ^^ false)) || ((b1 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem case36_b6_correct (a : Assignment) : evalCNF case36_b6 a = evalCNF case36_q6 (case36_project a) := by
  exact case36_b6_table (a 2) (a 3) (a 8) (a 9)

def case36_b7 : CNF := [[(false, 10), (false, 8), (false, 4), (false, 2)], [(false, 10), (false, 4), (true, 2), (true, 8)], [(false, 8), (false, 2), (true, 4), (true, 10)], [(true, 2), (true, 4), (true, 8), (true, 10)]]
def case36_q7 : CNF := [[(true, 2), (true, 4)]]
theorem case36_b7_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || ((!b0) || false)))) && (((!b3) || ((!b1) || (b0 || (b2 || false)))) && (((!b2) || ((!b0) || (b1 || (b3 || false)))) && ((b0 || (b1 || (b2 || (b3 || false)))) && true)))) = (((b0 ^^ (b2 ^^ false)) || ((b1 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem case36_b7_correct (a : Assignment) : evalCNF case36_b7 a = evalCNF case36_q7 (case36_project a) := by
  exact case36_b7_table (a 2) (a 4) (a 8) (a 10)

def case36_b8 : CNF := [[(false, 11), (false, 8), (true, 2), (true, 5)], [(false, 11), (false, 2), (true, 5), (true, 8)], [(false, 8), (false, 5), (true, 2), (true, 11)], [(false, 5), (false, 2), (true, 8), (true, 11)]]
def case36_q8 : CNF := [[(false, 2), (false, 5)]]
theorem case36_b8_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || (b0 || (b1 || false)))) && (((!b3) || ((!b0) || (b1 || (b2 || false)))) && (((!b2) || ((!b1) || (b0 || (b3 || false)))) && (((!b1) || ((!b0) || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b2 ^^ false))) || ((!(b1 ^^ (b3 ^^ false))) || false)) && true) := by
  decide +revert
theorem case36_b8_correct (a : Assignment) : evalCNF case36_b8 a = evalCNF case36_q8 (case36_project a) := by
  exact case36_b8_table (a 2) (a 5) (a 8) (a 11)

def case36_original : CNF := case36_b0 ++ case36_b1 ++ case36_b2 ++ case36_b3 ++ case36_b4 ++ case36_b5 ++ case36_b6 ++ case36_b7 ++ case36_b8 ++ []
def case36_quotient : CNF := case36_q0 ++ case36_q1 ++ case36_q2 ++ case36_q3 ++ case36_q4 ++ case36_q5 ++ case36_q6 ++ case36_q7 ++ case36_q8 ++ []
theorem case36_forward (a : Assignment) : evalCNF case36_original a = evalCNF case36_quotient (case36_project a) := by
  simp only [case36_original, case36_quotient, evalCNF_append]
  rw [case36_b0_correct, case36_b1_correct, case36_b2_correct, case36_b3_correct, case36_b4_correct, case36_b5_correct, case36_b6_correct, case36_b7_correct, case36_b8_correct]
  rfl

theorem case36_inverse0_table (y0 y1 y2 y3 y4 y5 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case36_inverse0 (a : Assignment) : case36_project (case36_lift a) 0 = a 0 := by
  exact case36_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

theorem case36_inverse1_table (y0 y1 y2 y3 y4 y5 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case36_inverse1 (a : Assignment) : case36_project (case36_lift a) 1 = a 1 := by
  exact case36_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

theorem case36_inverse2_table (y0 y1 y2 y3 y4 y5 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case36_inverse2 (a : Assignment) : case36_project (case36_lift a) 2 = a 2 := by
  exact case36_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

theorem case36_inverse3_table (y0 y1 y2 y3 y4 y5 : Bool) : ((y3 ^^ false) ^^ (false ^^ false)) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ false)) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case36_inverse3 (a : Assignment) : case36_project (case36_lift a) 3 = a 3 := by
  exact case36_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

theorem case36_inverse4_table (y0 y1 y2 y3 y4 y5 : Bool) : ((y4 ^^ false) ^^ (false ^^ false)) = y4 := by
  calc
    ((y4 ^^ false) ^^ (false ^^ false)) = (y4 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case36_inverse4 (a : Assignment) : case36_project (case36_lift a) 4 = a 4 := by
  exact case36_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

theorem case36_inverse5_table (y0 y1 y2 y3 y4 y5 : Bool) : ((y5 ^^ false) ^^ (false ^^ false)) = y5 := by
  calc
    ((y5 ^^ false) ^^ (false ^^ false)) = (y5 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case36_inverse5 (a : Assignment) : case36_project (case36_lift a) 5 = a 5 := by
  exact case36_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

theorem case36_backward (a : Assignment) : evalCNF case36_original (case36_lift a) = evalCNF case36_quotient a := by
  rw [case36_forward]
  simp only [case36_quotient, case36_q0, case36_q1, case36_q2, case36_q3, case36_q4, case36_q5, case36_q6, case36_q7, case36_q8, evalCNF_append, evalCNF, evalClause, evalLit, case36_inverse0, case36_inverse1, case36_inverse2, case36_inverse3, case36_inverse4, case36_inverse5]
theorem case36_equisatisfiable : (∃ a, evalCNF case36_original a = true) ↔ (∃ b, evalCNF case36_quotient b = true) :=
  equisat_of_two_maps (evalCNF case36_original) (evalCNF case36_quotient) case36_project case36_lift case36_forward case36_backward
#print axioms case36_forward
#print axioms case36_backward
#print axioms case36_equisatisfiable

def case96_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ ((a 2) ^^ false)))
  | 1 => ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ false)))
  | 2 => ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ false)))
  | 3 => ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ false)))
  | _ => false

def case96_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => false
  | 3 => ((a 1) ^^ false)
  | 4 => false
  | 5 => false
  | 6 => ((a 2) ^^ false)
  | 7 => false
  | 8 => false
  | 9 => ((a 3) ^^ false)
  | 10 => false
  | 11 => false
  | _ => false

def case96_b0 : CNF := [[(false, 5), (false, 4), (false, 2), (false, 1), (false, 0), (true, 3)], [(false, 5), (false, 4), (false, 2), (true, 0), (true, 1), (true, 3)], [(false, 5), (false, 4), (false, 1), (true, 0), (true, 2), (true, 3)], [(false, 5), (false, 4), (false, 0), (true, 1), (true, 2), (true, 3)], [(false, 5), (false, 3), (false, 2), (false, 1), (false, 0), (true, 4)], [(false, 5), (false, 3), (false, 2), (true, 0), (true, 1), (true, 4)], [(false, 5), (false, 3), (false, 1), (true, 0), (true, 2), (true, 4)], [(false, 5), (false, 3), (false, 0), (true, 1), (true, 2), (true, 4)], [(false, 4), (false, 3), (false, 2), (false, 1), (false, 0), (true, 5)], [(false, 4), (false, 3), (false, 2), (true, 0), (true, 1), (true, 5)], [(false, 4), (false, 3), (false, 1), (true, 0), (true, 2), (true, 5)], [(false, 4), (false, 3), (false, 0), (true, 1), (true, 2), (true, 5)], [(false, 2), (false, 1), (false, 0), (true, 3), (true, 4), (true, 5)], [(false, 2), (true, 0), (true, 1), (true, 3), (true, 4), (true, 5)], [(false, 1), (true, 0), (true, 2), (true, 3), (true, 4), (true, 5)], [(false, 0), (true, 1), (true, 2), (true, 3), (true, 4), (true, 5)]]
def case96_q0 : CNF := [[(false, 0), (true, 1)]]
theorem case96_b0_table (b0 b1 b2 b3 b4 b5 : Bool) : (((!b5) || ((!b4) || ((!b2) || ((!b1) || ((!b0) || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b2) || (b0 || (b1 || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b1) || (b0 || (b2 || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b0) || (b1 || (b2 || (b3 || false)))))) && (((!b5) || ((!b3) || ((!b2) || ((!b1) || ((!b0) || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b2) || (b0 || (b1 || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b1) || (b0 || (b2 || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b0) || (b1 || (b2 || (b4 || false)))))) && (((!b4) || ((!b3) || ((!b2) || ((!b1) || ((!b0) || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b2) || (b0 || (b1 || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b1) || (b0 || (b2 || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b0) || (b1 || (b2 || (b5 || false)))))) && (((!b2) || ((!b1) || ((!b0) || (b3 || (b4 || (b5 || false)))))) && (((!b2) || (b0 || (b1 || (b3 || (b4 || (b5 || false)))))) && (((!b1) || (b0 || (b2 || (b3 || (b4 || (b5 || false)))))) && (((!b0) || (b1 || (b2 || (b3 || (b4 || (b5 || false)))))) && true)))))))))))))))) = (((!(b0 ^^ (b1 ^^ (b2 ^^ false)))) || ((b3 ^^ (b4 ^^ (b5 ^^ false))) || false)) && true) := by
  decide +revert
theorem case96_b0_correct (a : Assignment) : evalCNF case96_b0 a = evalCNF case96_q0 (case96_project a) := by
  exact case96_b0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)

def case96_b1 : CNF := [[(false, 8), (false, 7), (false, 6), (false, 2), (false, 1), (false, 0)], [(false, 8), (false, 7), (false, 6), (false, 2), (true, 0), (true, 1)], [(false, 8), (false, 7), (false, 6), (false, 1), (true, 0), (true, 2)], [(false, 8), (false, 7), (false, 6), (false, 0), (true, 1), (true, 2)], [(false, 8), (false, 2), (false, 1), (false, 0), (true, 6), (true, 7)], [(false, 8), (false, 2), (true, 0), (true, 1), (true, 6), (true, 7)], [(false, 8), (false, 1), (true, 0), (true, 2), (true, 6), (true, 7)], [(false, 8), (false, 0), (true, 1), (true, 2), (true, 6), (true, 7)], [(false, 7), (false, 2), (false, 1), (false, 0), (true, 6), (true, 8)], [(false, 7), (false, 2), (true, 0), (true, 1), (true, 6), (true, 8)], [(false, 7), (false, 1), (true, 0), (true, 2), (true, 6), (true, 8)], [(false, 7), (false, 0), (true, 1), (true, 2), (true, 6), (true, 8)], [(false, 6), (false, 2), (false, 1), (false, 0), (true, 7), (true, 8)], [(false, 6), (false, 2), (true, 0), (true, 1), (true, 7), (true, 8)], [(false, 6), (false, 1), (true, 0), (true, 2), (true, 7), (true, 8)], [(false, 6), (false, 0), (true, 1), (true, 2), (true, 7), (true, 8)]]
def case96_q1 : CNF := [[(false, 0), (false, 2)]]
theorem case96_b1_table (b0 b1 b2 b3 b4 b5 : Bool) : (((!b5) || ((!b4) || ((!b3) || ((!b2) || ((!b1) || ((!b0) || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b2) || (b0 || (b1 || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b1) || (b0 || (b2 || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b0) || (b1 || (b2 || false)))))) && (((!b5) || ((!b2) || ((!b1) || ((!b0) || (b3 || (b4 || false)))))) && (((!b5) || ((!b2) || (b0 || (b1 || (b3 || (b4 || false)))))) && (((!b5) || ((!b1) || (b0 || (b2 || (b3 || (b4 || false)))))) && (((!b5) || ((!b0) || (b1 || (b2 || (b3 || (b4 || false)))))) && (((!b4) || ((!b2) || ((!b1) || ((!b0) || (b3 || (b5 || false)))))) && (((!b4) || ((!b2) || (b0 || (b1 || (b3 || (b5 || false)))))) && (((!b4) || ((!b1) || (b0 || (b2 || (b3 || (b5 || false)))))) && (((!b4) || ((!b0) || (b1 || (b2 || (b3 || (b5 || false)))))) && (((!b3) || ((!b2) || ((!b1) || ((!b0) || (b4 || (b5 || false)))))) && (((!b3) || ((!b2) || (b0 || (b1 || (b4 || (b5 || false)))))) && (((!b3) || ((!b1) || (b0 || (b2 || (b4 || (b5 || false)))))) && (((!b3) || ((!b0) || (b1 || (b2 || (b4 || (b5 || false)))))) && true)))))))))))))))) = (((!(b0 ^^ (b1 ^^ (b2 ^^ false)))) || ((!(b3 ^^ (b4 ^^ (b5 ^^ false)))) || false)) && true) := by
  decide +revert
theorem case96_b1_correct (a : Assignment) : evalCNF case96_b1 a = evalCNF case96_q1 (case96_project a) := by
  exact case96_b1_table (a 0) (a 1) (a 2) (a 6) (a 7) (a 8)

def case96_b2 : CNF := [[(false, 11), (false, 10), (false, 2), (false, 1), (true, 0), (true, 9)], [(false, 11), (false, 10), (false, 2), (false, 0), (true, 1), (true, 9)], [(false, 11), (false, 10), (false, 1), (false, 0), (true, 2), (true, 9)], [(false, 11), (false, 10), (true, 0), (true, 1), (true, 2), (true, 9)], [(false, 11), (false, 9), (false, 2), (false, 1), (true, 0), (true, 10)], [(false, 11), (false, 9), (false, 2), (false, 0), (true, 1), (true, 10)], [(false, 11), (false, 9), (false, 1), (false, 0), (true, 2), (true, 10)], [(false, 11), (false, 9), (true, 0), (true, 1), (true, 2), (true, 10)], [(false, 10), (false, 9), (false, 2), (false, 1), (true, 0), (true, 11)], [(false, 10), (false, 9), (false, 2), (false, 0), (true, 1), (true, 11)], [(false, 10), (false, 9), (false, 1), (false, 0), (true, 2), (true, 11)], [(false, 10), (false, 9), (true, 0), (true, 1), (true, 2), (true, 11)], [(false, 2), (false, 1), (true, 0), (true, 9), (true, 10), (true, 11)], [(false, 2), (false, 0), (true, 1), (true, 9), (true, 10), (true, 11)], [(false, 1), (false, 0), (true, 2), (true, 9), (true, 10), (true, 11)], [(true, 0), (true, 1), (true, 2), (true, 9), (true, 10), (true, 11)]]
def case96_q2 : CNF := [[(true, 0), (true, 3)]]
theorem case96_b2_table (b0 b1 b2 b3 b4 b5 : Bool) : (((!b5) || ((!b4) || ((!b2) || ((!b1) || (b0 || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b2) || ((!b0) || (b1 || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b1) || ((!b0) || (b2 || (b3 || false)))))) && (((!b5) || ((!b4) || (b0 || (b1 || (b2 || (b3 || false)))))) && (((!b5) || ((!b3) || ((!b2) || ((!b1) || (b0 || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b2) || ((!b0) || (b1 || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b1) || ((!b0) || (b2 || (b4 || false)))))) && (((!b5) || ((!b3) || (b0 || (b1 || (b2 || (b4 || false)))))) && (((!b4) || ((!b3) || ((!b2) || ((!b1) || (b0 || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b2) || ((!b0) || (b1 || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b1) || ((!b0) || (b2 || (b5 || false)))))) && (((!b4) || ((!b3) || (b0 || (b1 || (b2 || (b5 || false)))))) && (((!b2) || ((!b1) || (b0 || (b3 || (b4 || (b5 || false)))))) && (((!b2) || ((!b0) || (b1 || (b3 || (b4 || (b5 || false)))))) && (((!b1) || ((!b0) || (b2 || (b3 || (b4 || (b5 || false)))))) && ((b0 || (b1 || (b2 || (b3 || (b4 || (b5 || false)))))) && true)))))))))))))))) = (((b0 ^^ (b1 ^^ (b2 ^^ false))) || ((b3 ^^ (b4 ^^ (b5 ^^ false))) || false)) && true) := by
  decide +revert
theorem case96_b2_correct (a : Assignment) : evalCNF case96_b2 a = evalCNF case96_q2 (case96_project a) := by
  exact case96_b2_table (a 0) (a 1) (a 2) (a 9) (a 10) (a 11)

def case96_b3 : CNF := [[(false, 8), (false, 7), (false, 5), (false, 4), (false, 3), (true, 6)], [(false, 8), (false, 7), (false, 5), (true, 3), (true, 4), (true, 6)], [(false, 8), (false, 7), (false, 4), (true, 3), (true, 5), (true, 6)], [(false, 8), (false, 7), (false, 3), (true, 4), (true, 5), (true, 6)], [(false, 8), (false, 6), (false, 5), (false, 4), (false, 3), (true, 7)], [(false, 8), (false, 6), (false, 5), (true, 3), (true, 4), (true, 7)], [(false, 8), (false, 6), (false, 4), (true, 3), (true, 5), (true, 7)], [(false, 8), (false, 6), (false, 3), (true, 4), (true, 5), (true, 7)], [(false, 7), (false, 6), (false, 5), (false, 4), (false, 3), (true, 8)], [(false, 7), (false, 6), (false, 5), (true, 3), (true, 4), (true, 8)], [(false, 7), (false, 6), (false, 4), (true, 3), (true, 5), (true, 8)], [(false, 7), (false, 6), (false, 3), (true, 4), (true, 5), (true, 8)], [(false, 5), (false, 4), (false, 3), (true, 6), (true, 7), (true, 8)], [(false, 5), (true, 3), (true, 4), (true, 6), (true, 7), (true, 8)], [(false, 4), (true, 3), (true, 5), (true, 6), (true, 7), (true, 8)], [(false, 3), (true, 4), (true, 5), (true, 6), (true, 7), (true, 8)]]
def case96_q3 : CNF := [[(false, 1), (true, 2)]]
theorem case96_b3_table (b0 b1 b2 b3 b4 b5 : Bool) : (((!b5) || ((!b4) || ((!b2) || ((!b1) || ((!b0) || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b2) || (b0 || (b1 || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b1) || (b0 || (b2 || (b3 || false)))))) && (((!b5) || ((!b4) || ((!b0) || (b1 || (b2 || (b3 || false)))))) && (((!b5) || ((!b3) || ((!b2) || ((!b1) || ((!b0) || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b2) || (b0 || (b1 || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b1) || (b0 || (b2 || (b4 || false)))))) && (((!b5) || ((!b3) || ((!b0) || (b1 || (b2 || (b4 || false)))))) && (((!b4) || ((!b3) || ((!b2) || ((!b1) || ((!b0) || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b2) || (b0 || (b1 || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b1) || (b0 || (b2 || (b5 || false)))))) && (((!b4) || ((!b3) || ((!b0) || (b1 || (b2 || (b5 || false)))))) && (((!b2) || ((!b1) || ((!b0) || (b3 || (b4 || (b5 || false)))))) && (((!b2) || (b0 || (b1 || (b3 || (b4 || (b5 || false)))))) && (((!b1) || (b0 || (b2 || (b3 || (b4 || (b5 || false)))))) && (((!b0) || (b1 || (b2 || (b3 || (b4 || (b5 || false)))))) && true)))))))))))))))) = (((!(b0 ^^ (b1 ^^ (b2 ^^ false)))) || ((b3 ^^ (b4 ^^ (b5 ^^ false))) || false)) && true) := by
  decide +revert
theorem case96_b3_correct (a : Assignment) : evalCNF case96_b3 a = evalCNF case96_q3 (case96_project a) := by
  exact case96_b3_table (a 3) (a 4) (a 5) (a 6) (a 7) (a 8)

def case96_b4 : CNF := [[(false, 11), (false, 10), (false, 9), (false, 5), (false, 4), (true, 3)], [(false, 11), (false, 10), (false, 9), (false, 5), (false, 3), (true, 4)], [(false, 11), (false, 10), (false, 9), (false, 4), (false, 3), (true, 5)], [(false, 11), (false, 10), (false, 9), (true, 3), (true, 4), (true, 5)], [(false, 11), (false, 5), (false, 4), (true, 3), (true, 9), (true, 10)], [(false, 11), (false, 5), (false, 3), (true, 4), (true, 9), (true, 10)], [(false, 11), (false, 4), (false, 3), (true, 5), (true, 9), (true, 10)], [(false, 11), (true, 3), (true, 4), (true, 5), (true, 9), (true, 10)], [(false, 10), (false, 5), (false, 4), (true, 3), (true, 9), (true, 11)], [(false, 10), (false, 5), (false, 3), (true, 4), (true, 9), (true, 11)], [(false, 10), (false, 4), (false, 3), (true, 5), (true, 9), (true, 11)], [(false, 10), (true, 3), (true, 4), (true, 5), (true, 9), (true, 11)], [(false, 9), (false, 5), (false, 4), (true, 3), (true, 10), (true, 11)], [(false, 9), (false, 5), (false, 3), (true, 4), (true, 10), (true, 11)], [(false, 9), (false, 4), (false, 3), (true, 5), (true, 10), (true, 11)], [(false, 9), (true, 3), (true, 4), (true, 5), (true, 10), (true, 11)]]
def case96_q4 : CNF := [[(true, 1), (false, 3)]]
theorem case96_b4_table (b0 b1 b2 b3 b4 b5 : Bool) : (((!b5) || ((!b4) || ((!b3) || ((!b2) || ((!b1) || (b0 || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b2) || ((!b0) || (b1 || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b1) || ((!b0) || (b2 || false)))))) && (((!b5) || ((!b4) || ((!b3) || (b0 || (b1 || (b2 || false)))))) && (((!b5) || ((!b2) || ((!b1) || (b0 || (b3 || (b4 || false)))))) && (((!b5) || ((!b2) || ((!b0) || (b1 || (b3 || (b4 || false)))))) && (((!b5) || ((!b1) || ((!b0) || (b2 || (b3 || (b4 || false)))))) && (((!b5) || (b0 || (b1 || (b2 || (b3 || (b4 || false)))))) && (((!b4) || ((!b2) || ((!b1) || (b0 || (b3 || (b5 || false)))))) && (((!b4) || ((!b2) || ((!b0) || (b1 || (b3 || (b5 || false)))))) && (((!b4) || ((!b1) || ((!b0) || (b2 || (b3 || (b5 || false)))))) && (((!b4) || (b0 || (b1 || (b2 || (b3 || (b5 || false)))))) && (((!b3) || ((!b2) || ((!b1) || (b0 || (b4 || (b5 || false)))))) && (((!b3) || ((!b2) || ((!b0) || (b1 || (b4 || (b5 || false)))))) && (((!b3) || ((!b1) || ((!b0) || (b2 || (b4 || (b5 || false)))))) && (((!b3) || (b0 || (b1 || (b2 || (b4 || (b5 || false)))))) && true)))))))))))))))) = (((b0 ^^ (b1 ^^ (b2 ^^ false))) || ((!(b3 ^^ (b4 ^^ (b5 ^^ false)))) || false)) && true) := by
  decide +revert
theorem case96_b4_correct (a : Assignment) : evalCNF case96_b4 a = evalCNF case96_q4 (case96_project a) := by
  exact case96_b4_table (a 3) (a 4) (a 5) (a 9) (a 10) (a 11)

def case96_b5 : CNF := [[(false, 11), (false, 10), (false, 9), (false, 8), (false, 7), (false, 6)], [(false, 11), (false, 10), (false, 9), (false, 8), (true, 6), (true, 7)], [(false, 11), (false, 10), (false, 9), (false, 7), (true, 6), (true, 8)], [(false, 11), (false, 10), (false, 9), (false, 6), (true, 7), (true, 8)], [(false, 11), (false, 8), (false, 7), (false, 6), (true, 9), (true, 10)], [(false, 11), (false, 8), (true, 6), (true, 7), (true, 9), (true, 10)], [(false, 11), (false, 7), (true, 6), (true, 8), (true, 9), (true, 10)], [(false, 11), (false, 6), (true, 7), (true, 8), (true, 9), (true, 10)], [(false, 10), (false, 8), (false, 7), (false, 6), (true, 9), (true, 11)], [(false, 10), (false, 8), (true, 6), (true, 7), (true, 9), (true, 11)], [(false, 10), (false, 7), (true, 6), (true, 8), (true, 9), (true, 11)], [(false, 10), (false, 6), (true, 7), (true, 8), (true, 9), (true, 11)], [(false, 9), (false, 8), (false, 7), (false, 6), (true, 10), (true, 11)], [(false, 9), (false, 8), (true, 6), (true, 7), (true, 10), (true, 11)], [(false, 9), (false, 7), (true, 6), (true, 8), (true, 10), (true, 11)], [(false, 9), (false, 6), (true, 7), (true, 8), (true, 10), (true, 11)]]
def case96_q5 : CNF := [[(false, 2), (false, 3)]]
theorem case96_b5_table (b0 b1 b2 b3 b4 b5 : Bool) : (((!b5) || ((!b4) || ((!b3) || ((!b2) || ((!b1) || ((!b0) || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b2) || (b0 || (b1 || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b1) || (b0 || (b2 || false)))))) && (((!b5) || ((!b4) || ((!b3) || ((!b0) || (b1 || (b2 || false)))))) && (((!b5) || ((!b2) || ((!b1) || ((!b0) || (b3 || (b4 || false)))))) && (((!b5) || ((!b2) || (b0 || (b1 || (b3 || (b4 || false)))))) && (((!b5) || ((!b1) || (b0 || (b2 || (b3 || (b4 || false)))))) && (((!b5) || ((!b0) || (b1 || (b2 || (b3 || (b4 || false)))))) && (((!b4) || ((!b2) || ((!b1) || ((!b0) || (b3 || (b5 || false)))))) && (((!b4) || ((!b2) || (b0 || (b1 || (b3 || (b5 || false)))))) && (((!b4) || ((!b1) || (b0 || (b2 || (b3 || (b5 || false)))))) && (((!b4) || ((!b0) || (b1 || (b2 || (b3 || (b5 || false)))))) && (((!b3) || ((!b2) || ((!b1) || ((!b0) || (b4 || (b5 || false)))))) && (((!b3) || ((!b2) || (b0 || (b1 || (b4 || (b5 || false)))))) && (((!b3) || ((!b1) || (b0 || (b2 || (b4 || (b5 || false)))))) && (((!b3) || ((!b0) || (b1 || (b2 || (b4 || (b5 || false)))))) && true)))))))))))))))) = (((!(b0 ^^ (b1 ^^ (b2 ^^ false)))) || ((!(b3 ^^ (b4 ^^ (b5 ^^ false)))) || false)) && true) := by
  decide +revert
theorem case96_b5_correct (a : Assignment) : evalCNF case96_b5 a = evalCNF case96_q5 (case96_project a) := by
  exact case96_b5_table (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

def case96_original : CNF := case96_b0 ++ case96_b1 ++ case96_b2 ++ case96_b3 ++ case96_b4 ++ case96_b5 ++ []
def case96_quotient : CNF := case96_q0 ++ case96_q1 ++ case96_q2 ++ case96_q3 ++ case96_q4 ++ case96_q5 ++ []
theorem case96_forward (a : Assignment) : evalCNF case96_original a = evalCNF case96_quotient (case96_project a) := by
  simp only [case96_original, case96_quotient, evalCNF_append]
  rw [case96_b0_correct, case96_b1_correct, case96_b2_correct, case96_b3_correct, case96_b4_correct, case96_b5_correct]
  rfl

theorem case96_inverse0_table (y0 y1 y2 y3 : Bool) : ((y0 ^^ false) ^^ (false ^^ (false ^^ false))) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ (false ^^ false))) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case96_inverse0 (a : Assignment) : case96_project (case96_lift a) 0 = a 0 := by
  exact case96_inverse0_table (a 0) (a 1) (a 2) (a 3)

theorem case96_inverse1_table (y0 y1 y2 y3 : Bool) : ((y1 ^^ false) ^^ (false ^^ (false ^^ false))) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ (false ^^ false))) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case96_inverse1 (a : Assignment) : case96_project (case96_lift a) 1 = a 1 := by
  exact case96_inverse1_table (a 0) (a 1) (a 2) (a 3)

theorem case96_inverse2_table (y0 y1 y2 y3 : Bool) : ((y2 ^^ false) ^^ (false ^^ (false ^^ false))) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ (false ^^ false))) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case96_inverse2 (a : Assignment) : case96_project (case96_lift a) 2 = a 2 := by
  exact case96_inverse2_table (a 0) (a 1) (a 2) (a 3)

theorem case96_inverse3_table (y0 y1 y2 y3 : Bool) : ((y3 ^^ false) ^^ (false ^^ (false ^^ false))) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ (false ^^ false))) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem case96_inverse3 (a : Assignment) : case96_project (case96_lift a) 3 = a 3 := by
  exact case96_inverse3_table (a 0) (a 1) (a 2) (a 3)

theorem case96_backward (a : Assignment) : evalCNF case96_original (case96_lift a) = evalCNF case96_quotient a := by
  rw [case96_forward]
  simp only [case96_quotient, case96_q0, case96_q1, case96_q2, case96_q3, case96_q4, case96_q5, evalCNF_append, evalCNF, evalClause, evalLit, case96_inverse0, case96_inverse1, case96_inverse2, case96_inverse3]
theorem case96_equisatisfiable : (∃ a, evalCNF case96_original a = true) ↔ (∃ b, evalCNF case96_quotient b = true) :=
  equisat_of_two_maps (evalCNF case96_original) (evalCNF case96_quotient) case96_project case96_lift case96_forward case96_backward
#print axioms case96_forward
#print axioms case96_backward
#print axioms case96_equisatisfiable

def positive_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 2) ^^ ((a 3) ^^ false))
  | 2 => ((a 4) ^^ ((a 5) ^^ false))
  | _ => false

def positive_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => ((a 1) ^^ false)
  | 3 => false
  | 4 => ((a 2) ^^ false)
  | 5 => false
  | _ => false

def positive_b0 : CNF := [[(false, 3), (false, 2), (false, 1), (false, 0)], [(false, 3), (false, 2), (true, 0), (true, 1)], [(false, 1), (false, 0), (true, 2), (true, 3)], [(true, 0), (true, 1), (true, 2), (true, 3)]]
def positive_q0 : CNF := [[(true, 0), (true, 1)]]
theorem positive_b0_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || ((!b0) || false)))) && (((!b3) || ((!b2) || (b0 || (b1 || false)))) && (((!b1) || ((!b0) || (b2 || (b3 || false)))) && ((b0 || (b1 || (b2 || (b3 || false)))) && true)))) = (((b0 ^^ (b1 ^^ false)) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem positive_b0_correct (a : Assignment) : evalCNF positive_b0 a = evalCNF positive_q0 (positive_project a) := by
  exact positive_b0_table (a 0) (a 1) (a 2) (a 3)

def positive_b1 : CNF := [[(false, 5), (false, 4), (false, 1), (true, 0)], [(false, 5), (false, 4), (false, 0), (true, 1)], [(false, 1), (true, 0), (true, 4), (true, 5)], [(false, 0), (true, 1), (true, 4), (true, 5)]]
def positive_q1 : CNF := [[(false, 0), (true, 2)]]
theorem positive_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem positive_b1_correct (a : Assignment) : evalCNF positive_b1 a = evalCNF positive_q1 (positive_project a) := by
  exact positive_b1_table (a 0) (a 1) (a 4) (a 5)

def positive_original : CNF := positive_b0 ++ positive_b1 ++ []
def positive_quotient : CNF := positive_q0 ++ positive_q1 ++ []
theorem positive_forward (a : Assignment) : evalCNF positive_original a = evalCNF positive_quotient (positive_project a) := by
  simp only [positive_original, positive_quotient, evalCNF_append]
  rw [positive_b0_correct, positive_b1_correct]
  rfl

theorem positive_inverse0_table (y0 y1 y2 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem positive_inverse0 (a : Assignment) : positive_project (positive_lift a) 0 = a 0 := by
  exact positive_inverse0_table (a 0) (a 1) (a 2)

theorem positive_inverse1_table (y0 y1 y2 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem positive_inverse1 (a : Assignment) : positive_project (positive_lift a) 1 = a 1 := by
  exact positive_inverse1_table (a 0) (a 1) (a 2)

theorem positive_inverse2_table (y0 y1 y2 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem positive_inverse2 (a : Assignment) : positive_project (positive_lift a) 2 = a 2 := by
  exact positive_inverse2_table (a 0) (a 1) (a 2)

theorem positive_backward (a : Assignment) : evalCNF positive_original (positive_lift a) = evalCNF positive_quotient a := by
  rw [positive_forward]
  simp only [positive_quotient, positive_q0, positive_q1, evalCNF_append, evalCNF, evalClause, evalLit, positive_inverse0, positive_inverse1, positive_inverse2]
theorem positive_equisatisfiable : (∃ a, evalCNF positive_original a = true) ↔ (∃ b, evalCNF positive_quotient b = true) :=
  equisat_of_two_maps (evalCNF positive_original) (evalCNF positive_quotient) positive_project positive_lift positive_forward positive_backward
#print axioms positive_forward
#print axioms positive_backward
#print axioms positive_equisatisfiable

end CompressionInstances
