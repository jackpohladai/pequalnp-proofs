import Std.Tactic
namespace MergedCertificates.LargerCompressionInstances

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

def pairs16sat_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 2) ^^ ((a 3) ^^ false))
  | 2 => ((a 4) ^^ ((a 5) ^^ false))
  | 3 => ((a 6) ^^ ((a 7) ^^ false))
  | 4 => ((a 8) ^^ ((a 9) ^^ false))
  | 5 => ((a 10) ^^ ((a 11) ^^ false))
  | 6 => ((a 12) ^^ ((a 13) ^^ false))
  | 7 => ((a 14) ^^ ((a 15) ^^ false))
  | _ => false

def pairs16sat_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => ((a 1) ^^ false)
  | 3 => false
  | 4 => ((a 2) ^^ false)
  | 5 => false
  | 6 => ((a 3) ^^ false)
  | 7 => false
  | 8 => ((a 4) ^^ false)
  | 9 => false
  | 10 => ((a 5) ^^ false)
  | 11 => false
  | 12 => ((a 6) ^^ false)
  | 13 => false
  | 14 => ((a 7) ^^ false)
  | 15 => false
  | _ => false

def pairs16sat_b0 : CNF := [[(false, 1), (false, 0)], [(true, 0), (true, 1)]]
def pairs16sat_q0 : CNF := [[(true, 0)]]
theorem pairs16sat_b0_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs16sat_b0_correct (a : Assignment) : evalCNF pairs16sat_b0 a = evalCNF pairs16sat_q0 (pairs16sat_project a) := by
  exact pairs16sat_b0_table (a 0) (a 1)

def pairs16sat_b1 : CNF := [[(false, 3), (false, 2), (false, 1), (true, 0)], [(false, 3), (false, 2), (false, 0), (true, 1)], [(false, 1), (true, 0), (true, 2), (true, 3)], [(false, 0), (true, 1), (true, 2), (true, 3)]]
def pairs16sat_q1 : CNF := [[(false, 0), (true, 1)]]
theorem pairs16sat_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16sat_b1_correct (a : Assignment) : evalCNF pairs16sat_b1 a = evalCNF pairs16sat_q1 (pairs16sat_project a) := by
  exact pairs16sat_b1_table (a 0) (a 1) (a 2) (a 3)

def pairs16sat_b2 : CNF := [[(false, 5), (false, 4), (false, 3), (true, 2)], [(false, 5), (false, 4), (false, 2), (true, 3)], [(false, 3), (true, 2), (true, 4), (true, 5)], [(false, 2), (true, 3), (true, 4), (true, 5)]]
def pairs16sat_q2 : CNF := [[(false, 1), (true, 2)]]
theorem pairs16sat_b2_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16sat_b2_correct (a : Assignment) : evalCNF pairs16sat_b2 a = evalCNF pairs16sat_q2 (pairs16sat_project a) := by
  exact pairs16sat_b2_table (a 2) (a 3) (a 4) (a 5)

def pairs16sat_b3 : CNF := [[(false, 7), (false, 6), (false, 5), (true, 4)], [(false, 7), (false, 6), (false, 4), (true, 5)], [(false, 5), (true, 4), (true, 6), (true, 7)], [(false, 4), (true, 5), (true, 6), (true, 7)]]
def pairs16sat_q3 : CNF := [[(false, 2), (true, 3)]]
theorem pairs16sat_b3_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16sat_b3_correct (a : Assignment) : evalCNF pairs16sat_b3 a = evalCNF pairs16sat_q3 (pairs16sat_project a) := by
  exact pairs16sat_b3_table (a 4) (a 5) (a 6) (a 7)

def pairs16sat_b4 : CNF := [[(false, 9), (false, 8), (false, 7), (true, 6)], [(false, 9), (false, 8), (false, 6), (true, 7)], [(false, 7), (true, 6), (true, 8), (true, 9)], [(false, 6), (true, 7), (true, 8), (true, 9)]]
def pairs16sat_q4 : CNF := [[(false, 3), (true, 4)]]
theorem pairs16sat_b4_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16sat_b4_correct (a : Assignment) : evalCNF pairs16sat_b4 a = evalCNF pairs16sat_q4 (pairs16sat_project a) := by
  exact pairs16sat_b4_table (a 6) (a 7) (a 8) (a 9)

def pairs16sat_b5 : CNF := [[(false, 11), (false, 10), (false, 9), (true, 8)], [(false, 11), (false, 10), (false, 8), (true, 9)], [(false, 9), (true, 8), (true, 10), (true, 11)], [(false, 8), (true, 9), (true, 10), (true, 11)]]
def pairs16sat_q5 : CNF := [[(false, 4), (true, 5)]]
theorem pairs16sat_b5_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16sat_b5_correct (a : Assignment) : evalCNF pairs16sat_b5 a = evalCNF pairs16sat_q5 (pairs16sat_project a) := by
  exact pairs16sat_b5_table (a 8) (a 9) (a 10) (a 11)

def pairs16sat_b6 : CNF := [[(false, 13), (false, 12), (false, 11), (true, 10)], [(false, 13), (false, 12), (false, 10), (true, 11)], [(false, 11), (true, 10), (true, 12), (true, 13)], [(false, 10), (true, 11), (true, 12), (true, 13)]]
def pairs16sat_q6 : CNF := [[(false, 5), (true, 6)]]
theorem pairs16sat_b6_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16sat_b6_correct (a : Assignment) : evalCNF pairs16sat_b6 a = evalCNF pairs16sat_q6 (pairs16sat_project a) := by
  exact pairs16sat_b6_table (a 10) (a 11) (a 12) (a 13)

def pairs16sat_b7 : CNF := [[(false, 15), (false, 14), (false, 13), (true, 12)], [(false, 15), (false, 14), (false, 12), (true, 13)], [(false, 13), (true, 12), (true, 14), (true, 15)], [(false, 12), (true, 13), (true, 14), (true, 15)]]
def pairs16sat_q7 : CNF := [[(false, 6), (true, 7)]]
theorem pairs16sat_b7_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16sat_b7_correct (a : Assignment) : evalCNF pairs16sat_b7 a = evalCNF pairs16sat_q7 (pairs16sat_project a) := by
  exact pairs16sat_b7_table (a 12) (a 13) (a 14) (a 15)

def pairs16sat_b8 : CNF := [[(false, 15), (false, 14)], [(true, 14), (true, 15)]]
def pairs16sat_q8 : CNF := [[(true, 7)]]
theorem pairs16sat_b8_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs16sat_b8_correct (a : Assignment) : evalCNF pairs16sat_b8 a = evalCNF pairs16sat_q8 (pairs16sat_project a) := by
  exact pairs16sat_b8_table (a 14) (a 15)

def pairs16sat_original : CNF := pairs16sat_b0 ++ pairs16sat_b1 ++ pairs16sat_b2 ++ pairs16sat_b3 ++ pairs16sat_b4 ++ pairs16sat_b5 ++ pairs16sat_b6 ++ pairs16sat_b7 ++ pairs16sat_b8 ++ []
def pairs16sat_quotient : CNF := pairs16sat_q0 ++ pairs16sat_q1 ++ pairs16sat_q2 ++ pairs16sat_q3 ++ pairs16sat_q4 ++ pairs16sat_q5 ++ pairs16sat_q6 ++ pairs16sat_q7 ++ pairs16sat_q8 ++ []
theorem pairs16sat_forward (a : Assignment) : evalCNF pairs16sat_original a = evalCNF pairs16sat_quotient (pairs16sat_project a) := by
  simp only [pairs16sat_original, pairs16sat_quotient, evalCNF_append]
  rw [pairs16sat_b0_correct, pairs16sat_b1_correct, pairs16sat_b2_correct, pairs16sat_b3_correct, pairs16sat_b4_correct, pairs16sat_b5_correct, pairs16sat_b6_correct, pairs16sat_b7_correct, pairs16sat_b8_correct]
  rfl

theorem pairs16sat_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse0 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 0 = a 0 := by
  exact pairs16sat_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse1 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 1 = a 1 := by
  exact pairs16sat_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse2 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 2 = a 2 := by
  exact pairs16sat_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y3 ^^ false) ^^ (false ^^ false)) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ false)) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse3 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 3 = a 3 := by
  exact pairs16sat_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y4 ^^ false) ^^ (false ^^ false)) = y4 := by
  calc
    ((y4 ^^ false) ^^ (false ^^ false)) = (y4 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse4 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 4 = a 4 := by
  exact pairs16sat_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y5 ^^ false) ^^ (false ^^ false)) = y5 := by
  calc
    ((y5 ^^ false) ^^ (false ^^ false)) = (y5 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse5 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 5 = a 5 := by
  exact pairs16sat_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y6 ^^ false) ^^ (false ^^ false)) = y6 := by
  calc
    ((y6 ^^ false) ^^ (false ^^ false)) = (y6 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse6 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 6 = a 6 := by
  exact pairs16sat_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y7 ^^ false) ^^ (false ^^ false)) = y7 := by
  calc
    ((y7 ^^ false) ^^ (false ^^ false)) = (y7 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16sat_inverse7 (a : Assignment) : pairs16sat_project (pairs16sat_lift a) 7 = a 7 := by
  exact pairs16sat_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16sat_backward (a : Assignment) : evalCNF pairs16sat_original (pairs16sat_lift a) = evalCNF pairs16sat_quotient a := by
  rw [pairs16sat_forward]
  simp only [pairs16sat_quotient, pairs16sat_q0, pairs16sat_q1, pairs16sat_q2, pairs16sat_q3, pairs16sat_q4, pairs16sat_q5, pairs16sat_q6, pairs16sat_q7, pairs16sat_q8, evalCNF_append, evalCNF, evalClause, evalLit, pairs16sat_inverse0, pairs16sat_inverse1, pairs16sat_inverse2, pairs16sat_inverse3, pairs16sat_inverse4, pairs16sat_inverse5, pairs16sat_inverse6, pairs16sat_inverse7]
theorem pairs16sat_equisatisfiable : (∃ a, evalCNF pairs16sat_original a = true) ↔ (∃ b, evalCNF pairs16sat_quotient b = true) :=
  equisat_of_two_maps (evalCNF pairs16sat_original) (evalCNF pairs16sat_quotient) pairs16sat_project pairs16sat_lift pairs16sat_forward pairs16sat_backward
#print axioms pairs16sat_forward
#print axioms pairs16sat_backward
#print axioms pairs16sat_equisatisfiable

def pairs16unsat_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 2) ^^ ((a 3) ^^ false))
  | 2 => ((a 4) ^^ ((a 5) ^^ false))
  | 3 => ((a 6) ^^ ((a 7) ^^ false))
  | 4 => ((a 8) ^^ ((a 9) ^^ false))
  | 5 => ((a 10) ^^ ((a 11) ^^ false))
  | 6 => ((a 12) ^^ ((a 13) ^^ false))
  | 7 => ((a 14) ^^ ((a 15) ^^ false))
  | _ => false

def pairs16unsat_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => ((a 1) ^^ false)
  | 3 => false
  | 4 => ((a 2) ^^ false)
  | 5 => false
  | 6 => ((a 3) ^^ false)
  | 7 => false
  | 8 => ((a 4) ^^ false)
  | 9 => false
  | 10 => ((a 5) ^^ false)
  | 11 => false
  | 12 => ((a 6) ^^ false)
  | 13 => false
  | 14 => ((a 7) ^^ false)
  | 15 => false
  | _ => false

def pairs16unsat_b0 : CNF := [[(false, 1), (false, 0)], [(true, 0), (true, 1)]]
def pairs16unsat_q0 : CNF := [[(true, 0)]]
theorem pairs16unsat_b0_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs16unsat_b0_correct (a : Assignment) : evalCNF pairs16unsat_b0 a = evalCNF pairs16unsat_q0 (pairs16unsat_project a) := by
  exact pairs16unsat_b0_table (a 0) (a 1)

def pairs16unsat_b1 : CNF := [[(false, 3), (false, 2), (false, 1), (true, 0)], [(false, 3), (false, 2), (false, 0), (true, 1)], [(false, 1), (true, 0), (true, 2), (true, 3)], [(false, 0), (true, 1), (true, 2), (true, 3)]]
def pairs16unsat_q1 : CNF := [[(false, 0), (true, 1)]]
theorem pairs16unsat_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16unsat_b1_correct (a : Assignment) : evalCNF pairs16unsat_b1 a = evalCNF pairs16unsat_q1 (pairs16unsat_project a) := by
  exact pairs16unsat_b1_table (a 0) (a 1) (a 2) (a 3)

def pairs16unsat_b2 : CNF := [[(false, 5), (false, 4), (false, 3), (true, 2)], [(false, 5), (false, 4), (false, 2), (true, 3)], [(false, 3), (true, 2), (true, 4), (true, 5)], [(false, 2), (true, 3), (true, 4), (true, 5)]]
def pairs16unsat_q2 : CNF := [[(false, 1), (true, 2)]]
theorem pairs16unsat_b2_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16unsat_b2_correct (a : Assignment) : evalCNF pairs16unsat_b2 a = evalCNF pairs16unsat_q2 (pairs16unsat_project a) := by
  exact pairs16unsat_b2_table (a 2) (a 3) (a 4) (a 5)

def pairs16unsat_b3 : CNF := [[(false, 7), (false, 6), (false, 5), (true, 4)], [(false, 7), (false, 6), (false, 4), (true, 5)], [(false, 5), (true, 4), (true, 6), (true, 7)], [(false, 4), (true, 5), (true, 6), (true, 7)]]
def pairs16unsat_q3 : CNF := [[(false, 2), (true, 3)]]
theorem pairs16unsat_b3_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16unsat_b3_correct (a : Assignment) : evalCNF pairs16unsat_b3 a = evalCNF pairs16unsat_q3 (pairs16unsat_project a) := by
  exact pairs16unsat_b3_table (a 4) (a 5) (a 6) (a 7)

def pairs16unsat_b4 : CNF := [[(false, 9), (false, 8), (false, 7), (true, 6)], [(false, 9), (false, 8), (false, 6), (true, 7)], [(false, 7), (true, 6), (true, 8), (true, 9)], [(false, 6), (true, 7), (true, 8), (true, 9)]]
def pairs16unsat_q4 : CNF := [[(false, 3), (true, 4)]]
theorem pairs16unsat_b4_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16unsat_b4_correct (a : Assignment) : evalCNF pairs16unsat_b4 a = evalCNF pairs16unsat_q4 (pairs16unsat_project a) := by
  exact pairs16unsat_b4_table (a 6) (a 7) (a 8) (a 9)

def pairs16unsat_b5 : CNF := [[(false, 11), (false, 10), (false, 9), (true, 8)], [(false, 11), (false, 10), (false, 8), (true, 9)], [(false, 9), (true, 8), (true, 10), (true, 11)], [(false, 8), (true, 9), (true, 10), (true, 11)]]
def pairs16unsat_q5 : CNF := [[(false, 4), (true, 5)]]
theorem pairs16unsat_b5_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16unsat_b5_correct (a : Assignment) : evalCNF pairs16unsat_b5 a = evalCNF pairs16unsat_q5 (pairs16unsat_project a) := by
  exact pairs16unsat_b5_table (a 8) (a 9) (a 10) (a 11)

def pairs16unsat_b6 : CNF := [[(false, 13), (false, 12), (false, 11), (true, 10)], [(false, 13), (false, 12), (false, 10), (true, 11)], [(false, 11), (true, 10), (true, 12), (true, 13)], [(false, 10), (true, 11), (true, 12), (true, 13)]]
def pairs16unsat_q6 : CNF := [[(false, 5), (true, 6)]]
theorem pairs16unsat_b6_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16unsat_b6_correct (a : Assignment) : evalCNF pairs16unsat_b6 a = evalCNF pairs16unsat_q6 (pairs16unsat_project a) := by
  exact pairs16unsat_b6_table (a 10) (a 11) (a 12) (a 13)

def pairs16unsat_b7 : CNF := [[(false, 15), (false, 14), (false, 13), (true, 12)], [(false, 15), (false, 14), (false, 12), (true, 13)], [(false, 13), (true, 12), (true, 14), (true, 15)], [(false, 12), (true, 13), (true, 14), (true, 15)]]
def pairs16unsat_q7 : CNF := [[(false, 6), (true, 7)]]
theorem pairs16unsat_b7_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs16unsat_b7_correct (a : Assignment) : evalCNF pairs16unsat_b7 a = evalCNF pairs16unsat_q7 (pairs16unsat_project a) := by
  exact pairs16unsat_b7_table (a 12) (a 13) (a 14) (a 15)

def pairs16unsat_b8 : CNF := [[(false, 15), (true, 14)], [(false, 14), (true, 15)]]
def pairs16unsat_q8 : CNF := [[(false, 7)]]
theorem pairs16unsat_b8_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem pairs16unsat_b8_correct (a : Assignment) : evalCNF pairs16unsat_b8 a = evalCNF pairs16unsat_q8 (pairs16unsat_project a) := by
  exact pairs16unsat_b8_table (a 14) (a 15)

def pairs16unsat_original : CNF := pairs16unsat_b0 ++ pairs16unsat_b1 ++ pairs16unsat_b2 ++ pairs16unsat_b3 ++ pairs16unsat_b4 ++ pairs16unsat_b5 ++ pairs16unsat_b6 ++ pairs16unsat_b7 ++ pairs16unsat_b8 ++ []
def pairs16unsat_quotient : CNF := pairs16unsat_q0 ++ pairs16unsat_q1 ++ pairs16unsat_q2 ++ pairs16unsat_q3 ++ pairs16unsat_q4 ++ pairs16unsat_q5 ++ pairs16unsat_q6 ++ pairs16unsat_q7 ++ pairs16unsat_q8 ++ []
theorem pairs16unsat_forward (a : Assignment) : evalCNF pairs16unsat_original a = evalCNF pairs16unsat_quotient (pairs16unsat_project a) := by
  simp only [pairs16unsat_original, pairs16unsat_quotient, evalCNF_append]
  rw [pairs16unsat_b0_correct, pairs16unsat_b1_correct, pairs16unsat_b2_correct, pairs16unsat_b3_correct, pairs16unsat_b4_correct, pairs16unsat_b5_correct, pairs16unsat_b6_correct, pairs16unsat_b7_correct, pairs16unsat_b8_correct]
  rfl

theorem pairs16unsat_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse0 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 0 = a 0 := by
  exact pairs16unsat_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse1 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 1 = a 1 := by
  exact pairs16unsat_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse2 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 2 = a 2 := by
  exact pairs16unsat_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y3 ^^ false) ^^ (false ^^ false)) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ false)) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse3 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 3 = a 3 := by
  exact pairs16unsat_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y4 ^^ false) ^^ (false ^^ false)) = y4 := by
  calc
    ((y4 ^^ false) ^^ (false ^^ false)) = (y4 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse4 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 4 = a 4 := by
  exact pairs16unsat_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y5 ^^ false) ^^ (false ^^ false)) = y5 := by
  calc
    ((y5 ^^ false) ^^ (false ^^ false)) = (y5 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse5 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 5 = a 5 := by
  exact pairs16unsat_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y6 ^^ false) ^^ (false ^^ false)) = y6 := by
  calc
    ((y6 ^^ false) ^^ (false ^^ false)) = (y6 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse6 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 6 = a 6 := by
  exact pairs16unsat_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 : Bool) : ((y7 ^^ false) ^^ (false ^^ false)) = y7 := by
  calc
    ((y7 ^^ false) ^^ (false ^^ false)) = (y7 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs16unsat_inverse7 (a : Assignment) : pairs16unsat_project (pairs16unsat_lift a) 7 = a 7 := by
  exact pairs16unsat_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7)

theorem pairs16unsat_backward (a : Assignment) : evalCNF pairs16unsat_original (pairs16unsat_lift a) = evalCNF pairs16unsat_quotient a := by
  rw [pairs16unsat_forward]
  simp only [pairs16unsat_quotient, pairs16unsat_q0, pairs16unsat_q1, pairs16unsat_q2, pairs16unsat_q3, pairs16unsat_q4, pairs16unsat_q5, pairs16unsat_q6, pairs16unsat_q7, pairs16unsat_q8, evalCNF_append, evalCNF, evalClause, evalLit, pairs16unsat_inverse0, pairs16unsat_inverse1, pairs16unsat_inverse2, pairs16unsat_inverse3, pairs16unsat_inverse4, pairs16unsat_inverse5, pairs16unsat_inverse6, pairs16unsat_inverse7]
theorem pairs16unsat_equisatisfiable : (∃ a, evalCNF pairs16unsat_original a = true) ↔ (∃ b, evalCNF pairs16unsat_quotient b = true) :=
  equisat_of_two_maps (evalCNF pairs16unsat_original) (evalCNF pairs16unsat_quotient) pairs16unsat_project pairs16unsat_lift pairs16unsat_forward pairs16unsat_backward
#print axioms pairs16unsat_forward
#print axioms pairs16unsat_backward
#print axioms pairs16unsat_equisatisfiable

def pairs24sat_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 2) ^^ ((a 3) ^^ false))
  | 2 => ((a 4) ^^ ((a 5) ^^ false))
  | 3 => ((a 6) ^^ ((a 7) ^^ false))
  | 4 => ((a 8) ^^ ((a 9) ^^ false))
  | 5 => ((a 10) ^^ ((a 11) ^^ false))
  | 6 => ((a 12) ^^ ((a 13) ^^ false))
  | 7 => ((a 14) ^^ ((a 15) ^^ false))
  | 8 => ((a 16) ^^ ((a 17) ^^ false))
  | 9 => ((a 18) ^^ ((a 19) ^^ false))
  | 10 => ((a 20) ^^ ((a 21) ^^ false))
  | 11 => ((a 22) ^^ ((a 23) ^^ false))
  | _ => false

def pairs24sat_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => ((a 1) ^^ false)
  | 3 => false
  | 4 => ((a 2) ^^ false)
  | 5 => false
  | 6 => ((a 3) ^^ false)
  | 7 => false
  | 8 => ((a 4) ^^ false)
  | 9 => false
  | 10 => ((a 5) ^^ false)
  | 11 => false
  | 12 => ((a 6) ^^ false)
  | 13 => false
  | 14 => ((a 7) ^^ false)
  | 15 => false
  | 16 => ((a 8) ^^ false)
  | 17 => false
  | 18 => ((a 9) ^^ false)
  | 19 => false
  | 20 => ((a 10) ^^ false)
  | 21 => false
  | 22 => ((a 11) ^^ false)
  | 23 => false
  | _ => false

def pairs24sat_b0 : CNF := [[(false, 1), (false, 0)], [(true, 0), (true, 1)]]
def pairs24sat_q0 : CNF := [[(true, 0)]]
theorem pairs24sat_b0_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs24sat_b0_correct (a : Assignment) : evalCNF pairs24sat_b0 a = evalCNF pairs24sat_q0 (pairs24sat_project a) := by
  exact pairs24sat_b0_table (a 0) (a 1)

def pairs24sat_b1 : CNF := [[(false, 3), (false, 2), (false, 1), (true, 0)], [(false, 3), (false, 2), (false, 0), (true, 1)], [(false, 1), (true, 0), (true, 2), (true, 3)], [(false, 0), (true, 1), (true, 2), (true, 3)]]
def pairs24sat_q1 : CNF := [[(false, 0), (true, 1)]]
theorem pairs24sat_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b1_correct (a : Assignment) : evalCNF pairs24sat_b1 a = evalCNF pairs24sat_q1 (pairs24sat_project a) := by
  exact pairs24sat_b1_table (a 0) (a 1) (a 2) (a 3)

def pairs24sat_b2 : CNF := [[(false, 5), (false, 4), (false, 3), (true, 2)], [(false, 5), (false, 4), (false, 2), (true, 3)], [(false, 3), (true, 2), (true, 4), (true, 5)], [(false, 2), (true, 3), (true, 4), (true, 5)]]
def pairs24sat_q2 : CNF := [[(false, 1), (true, 2)]]
theorem pairs24sat_b2_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b2_correct (a : Assignment) : evalCNF pairs24sat_b2 a = evalCNF pairs24sat_q2 (pairs24sat_project a) := by
  exact pairs24sat_b2_table (a 2) (a 3) (a 4) (a 5)

def pairs24sat_b3 : CNF := [[(false, 7), (false, 6), (false, 5), (true, 4)], [(false, 7), (false, 6), (false, 4), (true, 5)], [(false, 5), (true, 4), (true, 6), (true, 7)], [(false, 4), (true, 5), (true, 6), (true, 7)]]
def pairs24sat_q3 : CNF := [[(false, 2), (true, 3)]]
theorem pairs24sat_b3_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b3_correct (a : Assignment) : evalCNF pairs24sat_b3 a = evalCNF pairs24sat_q3 (pairs24sat_project a) := by
  exact pairs24sat_b3_table (a 4) (a 5) (a 6) (a 7)

def pairs24sat_b4 : CNF := [[(false, 9), (false, 8), (false, 7), (true, 6)], [(false, 9), (false, 8), (false, 6), (true, 7)], [(false, 7), (true, 6), (true, 8), (true, 9)], [(false, 6), (true, 7), (true, 8), (true, 9)]]
def pairs24sat_q4 : CNF := [[(false, 3), (true, 4)]]
theorem pairs24sat_b4_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b4_correct (a : Assignment) : evalCNF pairs24sat_b4 a = evalCNF pairs24sat_q4 (pairs24sat_project a) := by
  exact pairs24sat_b4_table (a 6) (a 7) (a 8) (a 9)

def pairs24sat_b5 : CNF := [[(false, 11), (false, 10), (false, 9), (true, 8)], [(false, 11), (false, 10), (false, 8), (true, 9)], [(false, 9), (true, 8), (true, 10), (true, 11)], [(false, 8), (true, 9), (true, 10), (true, 11)]]
def pairs24sat_q5 : CNF := [[(false, 4), (true, 5)]]
theorem pairs24sat_b5_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b5_correct (a : Assignment) : evalCNF pairs24sat_b5 a = evalCNF pairs24sat_q5 (pairs24sat_project a) := by
  exact pairs24sat_b5_table (a 8) (a 9) (a 10) (a 11)

def pairs24sat_b6 : CNF := [[(false, 13), (false, 12), (false, 11), (true, 10)], [(false, 13), (false, 12), (false, 10), (true, 11)], [(false, 11), (true, 10), (true, 12), (true, 13)], [(false, 10), (true, 11), (true, 12), (true, 13)]]
def pairs24sat_q6 : CNF := [[(false, 5), (true, 6)]]
theorem pairs24sat_b6_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b6_correct (a : Assignment) : evalCNF pairs24sat_b6 a = evalCNF pairs24sat_q6 (pairs24sat_project a) := by
  exact pairs24sat_b6_table (a 10) (a 11) (a 12) (a 13)

def pairs24sat_b7 : CNF := [[(false, 15), (false, 14), (false, 13), (true, 12)], [(false, 15), (false, 14), (false, 12), (true, 13)], [(false, 13), (true, 12), (true, 14), (true, 15)], [(false, 12), (true, 13), (true, 14), (true, 15)]]
def pairs24sat_q7 : CNF := [[(false, 6), (true, 7)]]
theorem pairs24sat_b7_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b7_correct (a : Assignment) : evalCNF pairs24sat_b7 a = evalCNF pairs24sat_q7 (pairs24sat_project a) := by
  exact pairs24sat_b7_table (a 12) (a 13) (a 14) (a 15)

def pairs24sat_b8 : CNF := [[(false, 17), (false, 16), (false, 15), (true, 14)], [(false, 17), (false, 16), (false, 14), (true, 15)], [(false, 15), (true, 14), (true, 16), (true, 17)], [(false, 14), (true, 15), (true, 16), (true, 17)]]
def pairs24sat_q8 : CNF := [[(false, 7), (true, 8)]]
theorem pairs24sat_b8_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b8_correct (a : Assignment) : evalCNF pairs24sat_b8 a = evalCNF pairs24sat_q8 (pairs24sat_project a) := by
  exact pairs24sat_b8_table (a 14) (a 15) (a 16) (a 17)

def pairs24sat_b9 : CNF := [[(false, 19), (false, 18), (false, 17), (true, 16)], [(false, 19), (false, 18), (false, 16), (true, 17)], [(false, 17), (true, 16), (true, 18), (true, 19)], [(false, 16), (true, 17), (true, 18), (true, 19)]]
def pairs24sat_q9 : CNF := [[(false, 8), (true, 9)]]
theorem pairs24sat_b9_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b9_correct (a : Assignment) : evalCNF pairs24sat_b9 a = evalCNF pairs24sat_q9 (pairs24sat_project a) := by
  exact pairs24sat_b9_table (a 16) (a 17) (a 18) (a 19)

def pairs24sat_b10 : CNF := [[(false, 21), (false, 20), (false, 19), (true, 18)], [(false, 21), (false, 20), (false, 18), (true, 19)], [(false, 19), (true, 18), (true, 20), (true, 21)], [(false, 18), (true, 19), (true, 20), (true, 21)]]
def pairs24sat_q10 : CNF := [[(false, 9), (true, 10)]]
theorem pairs24sat_b10_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b10_correct (a : Assignment) : evalCNF pairs24sat_b10 a = evalCNF pairs24sat_q10 (pairs24sat_project a) := by
  exact pairs24sat_b10_table (a 18) (a 19) (a 20) (a 21)

def pairs24sat_b11 : CNF := [[(false, 23), (false, 22), (false, 21), (true, 20)], [(false, 23), (false, 22), (false, 20), (true, 21)], [(false, 21), (true, 20), (true, 22), (true, 23)], [(false, 20), (true, 21), (true, 22), (true, 23)]]
def pairs24sat_q11 : CNF := [[(false, 10), (true, 11)]]
theorem pairs24sat_b11_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24sat_b11_correct (a : Assignment) : evalCNF pairs24sat_b11 a = evalCNF pairs24sat_q11 (pairs24sat_project a) := by
  exact pairs24sat_b11_table (a 20) (a 21) (a 22) (a 23)

def pairs24sat_b12 : CNF := [[(false, 23), (false, 22)], [(true, 22), (true, 23)]]
def pairs24sat_q12 : CNF := [[(true, 11)]]
theorem pairs24sat_b12_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs24sat_b12_correct (a : Assignment) : evalCNF pairs24sat_b12 a = evalCNF pairs24sat_q12 (pairs24sat_project a) := by
  exact pairs24sat_b12_table (a 22) (a 23)

def pairs24sat_original : CNF := pairs24sat_b0 ++ pairs24sat_b1 ++ pairs24sat_b2 ++ pairs24sat_b3 ++ pairs24sat_b4 ++ pairs24sat_b5 ++ pairs24sat_b6 ++ pairs24sat_b7 ++ pairs24sat_b8 ++ pairs24sat_b9 ++ pairs24sat_b10 ++ pairs24sat_b11 ++ pairs24sat_b12 ++ []
def pairs24sat_quotient : CNF := pairs24sat_q0 ++ pairs24sat_q1 ++ pairs24sat_q2 ++ pairs24sat_q3 ++ pairs24sat_q4 ++ pairs24sat_q5 ++ pairs24sat_q6 ++ pairs24sat_q7 ++ pairs24sat_q8 ++ pairs24sat_q9 ++ pairs24sat_q10 ++ pairs24sat_q11 ++ pairs24sat_q12 ++ []
theorem pairs24sat_forward (a : Assignment) : evalCNF pairs24sat_original a = evalCNF pairs24sat_quotient (pairs24sat_project a) := by
  simp only [pairs24sat_original, pairs24sat_quotient, evalCNF_append]
  rw [pairs24sat_b0_correct, pairs24sat_b1_correct, pairs24sat_b2_correct, pairs24sat_b3_correct, pairs24sat_b4_correct, pairs24sat_b5_correct, pairs24sat_b6_correct, pairs24sat_b7_correct, pairs24sat_b8_correct, pairs24sat_b9_correct, pairs24sat_b10_correct, pairs24sat_b11_correct, pairs24sat_b12_correct]
  rfl

theorem pairs24sat_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse0 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 0 = a 0 := by
  exact pairs24sat_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse1 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 1 = a 1 := by
  exact pairs24sat_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse2 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 2 = a 2 := by
  exact pairs24sat_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y3 ^^ false) ^^ (false ^^ false)) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ false)) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse3 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 3 = a 3 := by
  exact pairs24sat_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y4 ^^ false) ^^ (false ^^ false)) = y4 := by
  calc
    ((y4 ^^ false) ^^ (false ^^ false)) = (y4 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse4 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 4 = a 4 := by
  exact pairs24sat_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y5 ^^ false) ^^ (false ^^ false)) = y5 := by
  calc
    ((y5 ^^ false) ^^ (false ^^ false)) = (y5 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse5 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 5 = a 5 := by
  exact pairs24sat_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y6 ^^ false) ^^ (false ^^ false)) = y6 := by
  calc
    ((y6 ^^ false) ^^ (false ^^ false)) = (y6 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse6 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 6 = a 6 := by
  exact pairs24sat_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y7 ^^ false) ^^ (false ^^ false)) = y7 := by
  calc
    ((y7 ^^ false) ^^ (false ^^ false)) = (y7 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse7 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 7 = a 7 := by
  exact pairs24sat_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse8_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y8 ^^ false) ^^ (false ^^ false)) = y8 := by
  calc
    ((y8 ^^ false) ^^ (false ^^ false)) = (y8 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y8 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse8 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 8 = a 8 := by
  exact pairs24sat_inverse8_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse9_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y9 ^^ false) ^^ (false ^^ false)) = y9 := by
  calc
    ((y9 ^^ false) ^^ (false ^^ false)) = (y9 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y9 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse9 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 9 = a 9 := by
  exact pairs24sat_inverse9_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse10_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y10 ^^ false) ^^ (false ^^ false)) = y10 := by
  calc
    ((y10 ^^ false) ^^ (false ^^ false)) = (y10 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y10 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse10 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 10 = a 10 := by
  exact pairs24sat_inverse10_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_inverse11_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y11 ^^ false) ^^ (false ^^ false)) = y11 := by
  calc
    ((y11 ^^ false) ^^ (false ^^ false)) = (y11 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y11 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24sat_inverse11 (a : Assignment) : pairs24sat_project (pairs24sat_lift a) 11 = a 11 := by
  exact pairs24sat_inverse11_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24sat_backward (a : Assignment) : evalCNF pairs24sat_original (pairs24sat_lift a) = evalCNF pairs24sat_quotient a := by
  rw [pairs24sat_forward]
  simp only [pairs24sat_quotient, pairs24sat_q0, pairs24sat_q1, pairs24sat_q2, pairs24sat_q3, pairs24sat_q4, pairs24sat_q5, pairs24sat_q6, pairs24sat_q7, pairs24sat_q8, pairs24sat_q9, pairs24sat_q10, pairs24sat_q11, pairs24sat_q12, evalCNF_append, evalCNF, evalClause, evalLit, pairs24sat_inverse0, pairs24sat_inverse1, pairs24sat_inverse2, pairs24sat_inverse3, pairs24sat_inverse4, pairs24sat_inverse5, pairs24sat_inverse6, pairs24sat_inverse7, pairs24sat_inverse8, pairs24sat_inverse9, pairs24sat_inverse10, pairs24sat_inverse11]
theorem pairs24sat_equisatisfiable : (∃ a, evalCNF pairs24sat_original a = true) ↔ (∃ b, evalCNF pairs24sat_quotient b = true) :=
  equisat_of_two_maps (evalCNF pairs24sat_original) (evalCNF pairs24sat_quotient) pairs24sat_project pairs24sat_lift pairs24sat_forward pairs24sat_backward
#print axioms pairs24sat_forward
#print axioms pairs24sat_backward
#print axioms pairs24sat_equisatisfiable

def pairs24unsat_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 2) ^^ ((a 3) ^^ false))
  | 2 => ((a 4) ^^ ((a 5) ^^ false))
  | 3 => ((a 6) ^^ ((a 7) ^^ false))
  | 4 => ((a 8) ^^ ((a 9) ^^ false))
  | 5 => ((a 10) ^^ ((a 11) ^^ false))
  | 6 => ((a 12) ^^ ((a 13) ^^ false))
  | 7 => ((a 14) ^^ ((a 15) ^^ false))
  | 8 => ((a 16) ^^ ((a 17) ^^ false))
  | 9 => ((a 18) ^^ ((a 19) ^^ false))
  | 10 => ((a 20) ^^ ((a 21) ^^ false))
  | 11 => ((a 22) ^^ ((a 23) ^^ false))
  | _ => false

def pairs24unsat_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => ((a 1) ^^ false)
  | 3 => false
  | 4 => ((a 2) ^^ false)
  | 5 => false
  | 6 => ((a 3) ^^ false)
  | 7 => false
  | 8 => ((a 4) ^^ false)
  | 9 => false
  | 10 => ((a 5) ^^ false)
  | 11 => false
  | 12 => ((a 6) ^^ false)
  | 13 => false
  | 14 => ((a 7) ^^ false)
  | 15 => false
  | 16 => ((a 8) ^^ false)
  | 17 => false
  | 18 => ((a 9) ^^ false)
  | 19 => false
  | 20 => ((a 10) ^^ false)
  | 21 => false
  | 22 => ((a 11) ^^ false)
  | 23 => false
  | _ => false

def pairs24unsat_b0 : CNF := [[(false, 1), (false, 0)], [(true, 0), (true, 1)]]
def pairs24unsat_q0 : CNF := [[(true, 0)]]
theorem pairs24unsat_b0_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs24unsat_b0_correct (a : Assignment) : evalCNF pairs24unsat_b0 a = evalCNF pairs24unsat_q0 (pairs24unsat_project a) := by
  exact pairs24unsat_b0_table (a 0) (a 1)

def pairs24unsat_b1 : CNF := [[(false, 3), (false, 2), (false, 1), (true, 0)], [(false, 3), (false, 2), (false, 0), (true, 1)], [(false, 1), (true, 0), (true, 2), (true, 3)], [(false, 0), (true, 1), (true, 2), (true, 3)]]
def pairs24unsat_q1 : CNF := [[(false, 0), (true, 1)]]
theorem pairs24unsat_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b1_correct (a : Assignment) : evalCNF pairs24unsat_b1 a = evalCNF pairs24unsat_q1 (pairs24unsat_project a) := by
  exact pairs24unsat_b1_table (a 0) (a 1) (a 2) (a 3)

def pairs24unsat_b2 : CNF := [[(false, 5), (false, 4), (false, 3), (true, 2)], [(false, 5), (false, 4), (false, 2), (true, 3)], [(false, 3), (true, 2), (true, 4), (true, 5)], [(false, 2), (true, 3), (true, 4), (true, 5)]]
def pairs24unsat_q2 : CNF := [[(false, 1), (true, 2)]]
theorem pairs24unsat_b2_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b2_correct (a : Assignment) : evalCNF pairs24unsat_b2 a = evalCNF pairs24unsat_q2 (pairs24unsat_project a) := by
  exact pairs24unsat_b2_table (a 2) (a 3) (a 4) (a 5)

def pairs24unsat_b3 : CNF := [[(false, 7), (false, 6), (false, 5), (true, 4)], [(false, 7), (false, 6), (false, 4), (true, 5)], [(false, 5), (true, 4), (true, 6), (true, 7)], [(false, 4), (true, 5), (true, 6), (true, 7)]]
def pairs24unsat_q3 : CNF := [[(false, 2), (true, 3)]]
theorem pairs24unsat_b3_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b3_correct (a : Assignment) : evalCNF pairs24unsat_b3 a = evalCNF pairs24unsat_q3 (pairs24unsat_project a) := by
  exact pairs24unsat_b3_table (a 4) (a 5) (a 6) (a 7)

def pairs24unsat_b4 : CNF := [[(false, 9), (false, 8), (false, 7), (true, 6)], [(false, 9), (false, 8), (false, 6), (true, 7)], [(false, 7), (true, 6), (true, 8), (true, 9)], [(false, 6), (true, 7), (true, 8), (true, 9)]]
def pairs24unsat_q4 : CNF := [[(false, 3), (true, 4)]]
theorem pairs24unsat_b4_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b4_correct (a : Assignment) : evalCNF pairs24unsat_b4 a = evalCNF pairs24unsat_q4 (pairs24unsat_project a) := by
  exact pairs24unsat_b4_table (a 6) (a 7) (a 8) (a 9)

def pairs24unsat_b5 : CNF := [[(false, 11), (false, 10), (false, 9), (true, 8)], [(false, 11), (false, 10), (false, 8), (true, 9)], [(false, 9), (true, 8), (true, 10), (true, 11)], [(false, 8), (true, 9), (true, 10), (true, 11)]]
def pairs24unsat_q5 : CNF := [[(false, 4), (true, 5)]]
theorem pairs24unsat_b5_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b5_correct (a : Assignment) : evalCNF pairs24unsat_b5 a = evalCNF pairs24unsat_q5 (pairs24unsat_project a) := by
  exact pairs24unsat_b5_table (a 8) (a 9) (a 10) (a 11)

def pairs24unsat_b6 : CNF := [[(false, 13), (false, 12), (false, 11), (true, 10)], [(false, 13), (false, 12), (false, 10), (true, 11)], [(false, 11), (true, 10), (true, 12), (true, 13)], [(false, 10), (true, 11), (true, 12), (true, 13)]]
def pairs24unsat_q6 : CNF := [[(false, 5), (true, 6)]]
theorem pairs24unsat_b6_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b6_correct (a : Assignment) : evalCNF pairs24unsat_b6 a = evalCNF pairs24unsat_q6 (pairs24unsat_project a) := by
  exact pairs24unsat_b6_table (a 10) (a 11) (a 12) (a 13)

def pairs24unsat_b7 : CNF := [[(false, 15), (false, 14), (false, 13), (true, 12)], [(false, 15), (false, 14), (false, 12), (true, 13)], [(false, 13), (true, 12), (true, 14), (true, 15)], [(false, 12), (true, 13), (true, 14), (true, 15)]]
def pairs24unsat_q7 : CNF := [[(false, 6), (true, 7)]]
theorem pairs24unsat_b7_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b7_correct (a : Assignment) : evalCNF pairs24unsat_b7 a = evalCNF pairs24unsat_q7 (pairs24unsat_project a) := by
  exact pairs24unsat_b7_table (a 12) (a 13) (a 14) (a 15)

def pairs24unsat_b8 : CNF := [[(false, 17), (false, 16), (false, 15), (true, 14)], [(false, 17), (false, 16), (false, 14), (true, 15)], [(false, 15), (true, 14), (true, 16), (true, 17)], [(false, 14), (true, 15), (true, 16), (true, 17)]]
def pairs24unsat_q8 : CNF := [[(false, 7), (true, 8)]]
theorem pairs24unsat_b8_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b8_correct (a : Assignment) : evalCNF pairs24unsat_b8 a = evalCNF pairs24unsat_q8 (pairs24unsat_project a) := by
  exact pairs24unsat_b8_table (a 14) (a 15) (a 16) (a 17)

def pairs24unsat_b9 : CNF := [[(false, 19), (false, 18), (false, 17), (true, 16)], [(false, 19), (false, 18), (false, 16), (true, 17)], [(false, 17), (true, 16), (true, 18), (true, 19)], [(false, 16), (true, 17), (true, 18), (true, 19)]]
def pairs24unsat_q9 : CNF := [[(false, 8), (true, 9)]]
theorem pairs24unsat_b9_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b9_correct (a : Assignment) : evalCNF pairs24unsat_b9 a = evalCNF pairs24unsat_q9 (pairs24unsat_project a) := by
  exact pairs24unsat_b9_table (a 16) (a 17) (a 18) (a 19)

def pairs24unsat_b10 : CNF := [[(false, 21), (false, 20), (false, 19), (true, 18)], [(false, 21), (false, 20), (false, 18), (true, 19)], [(false, 19), (true, 18), (true, 20), (true, 21)], [(false, 18), (true, 19), (true, 20), (true, 21)]]
def pairs24unsat_q10 : CNF := [[(false, 9), (true, 10)]]
theorem pairs24unsat_b10_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b10_correct (a : Assignment) : evalCNF pairs24unsat_b10 a = evalCNF pairs24unsat_q10 (pairs24unsat_project a) := by
  exact pairs24unsat_b10_table (a 18) (a 19) (a 20) (a 21)

def pairs24unsat_b11 : CNF := [[(false, 23), (false, 22), (false, 21), (true, 20)], [(false, 23), (false, 22), (false, 20), (true, 21)], [(false, 21), (true, 20), (true, 22), (true, 23)], [(false, 20), (true, 21), (true, 22), (true, 23)]]
def pairs24unsat_q11 : CNF := [[(false, 10), (true, 11)]]
theorem pairs24unsat_b11_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs24unsat_b11_correct (a : Assignment) : evalCNF pairs24unsat_b11 a = evalCNF pairs24unsat_q11 (pairs24unsat_project a) := by
  exact pairs24unsat_b11_table (a 20) (a 21) (a 22) (a 23)

def pairs24unsat_b12 : CNF := [[(false, 23), (true, 22)], [(false, 22), (true, 23)]]
def pairs24unsat_q12 : CNF := [[(false, 11)]]
theorem pairs24unsat_b12_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem pairs24unsat_b12_correct (a : Assignment) : evalCNF pairs24unsat_b12 a = evalCNF pairs24unsat_q12 (pairs24unsat_project a) := by
  exact pairs24unsat_b12_table (a 22) (a 23)

def pairs24unsat_original : CNF := pairs24unsat_b0 ++ pairs24unsat_b1 ++ pairs24unsat_b2 ++ pairs24unsat_b3 ++ pairs24unsat_b4 ++ pairs24unsat_b5 ++ pairs24unsat_b6 ++ pairs24unsat_b7 ++ pairs24unsat_b8 ++ pairs24unsat_b9 ++ pairs24unsat_b10 ++ pairs24unsat_b11 ++ pairs24unsat_b12 ++ []
def pairs24unsat_quotient : CNF := pairs24unsat_q0 ++ pairs24unsat_q1 ++ pairs24unsat_q2 ++ pairs24unsat_q3 ++ pairs24unsat_q4 ++ pairs24unsat_q5 ++ pairs24unsat_q6 ++ pairs24unsat_q7 ++ pairs24unsat_q8 ++ pairs24unsat_q9 ++ pairs24unsat_q10 ++ pairs24unsat_q11 ++ pairs24unsat_q12 ++ []
theorem pairs24unsat_forward (a : Assignment) : evalCNF pairs24unsat_original a = evalCNF pairs24unsat_quotient (pairs24unsat_project a) := by
  simp only [pairs24unsat_original, pairs24unsat_quotient, evalCNF_append]
  rw [pairs24unsat_b0_correct, pairs24unsat_b1_correct, pairs24unsat_b2_correct, pairs24unsat_b3_correct, pairs24unsat_b4_correct, pairs24unsat_b5_correct, pairs24unsat_b6_correct, pairs24unsat_b7_correct, pairs24unsat_b8_correct, pairs24unsat_b9_correct, pairs24unsat_b10_correct, pairs24unsat_b11_correct, pairs24unsat_b12_correct]
  rfl

theorem pairs24unsat_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse0 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 0 = a 0 := by
  exact pairs24unsat_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse1 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 1 = a 1 := by
  exact pairs24unsat_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse2 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 2 = a 2 := by
  exact pairs24unsat_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y3 ^^ false) ^^ (false ^^ false)) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ false)) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse3 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 3 = a 3 := by
  exact pairs24unsat_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y4 ^^ false) ^^ (false ^^ false)) = y4 := by
  calc
    ((y4 ^^ false) ^^ (false ^^ false)) = (y4 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse4 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 4 = a 4 := by
  exact pairs24unsat_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y5 ^^ false) ^^ (false ^^ false)) = y5 := by
  calc
    ((y5 ^^ false) ^^ (false ^^ false)) = (y5 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse5 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 5 = a 5 := by
  exact pairs24unsat_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y6 ^^ false) ^^ (false ^^ false)) = y6 := by
  calc
    ((y6 ^^ false) ^^ (false ^^ false)) = (y6 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse6 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 6 = a 6 := by
  exact pairs24unsat_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y7 ^^ false) ^^ (false ^^ false)) = y7 := by
  calc
    ((y7 ^^ false) ^^ (false ^^ false)) = (y7 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse7 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 7 = a 7 := by
  exact pairs24unsat_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse8_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y8 ^^ false) ^^ (false ^^ false)) = y8 := by
  calc
    ((y8 ^^ false) ^^ (false ^^ false)) = (y8 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y8 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse8 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 8 = a 8 := by
  exact pairs24unsat_inverse8_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse9_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y9 ^^ false) ^^ (false ^^ false)) = y9 := by
  calc
    ((y9 ^^ false) ^^ (false ^^ false)) = (y9 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y9 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse9 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 9 = a 9 := by
  exact pairs24unsat_inverse9_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse10_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y10 ^^ false) ^^ (false ^^ false)) = y10 := by
  calc
    ((y10 ^^ false) ^^ (false ^^ false)) = (y10 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y10 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse10 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 10 = a 10 := by
  exact pairs24unsat_inverse10_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_inverse11_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Bool) : ((y11 ^^ false) ^^ (false ^^ false)) = y11 := by
  calc
    ((y11 ^^ false) ^^ (false ^^ false)) = (y11 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y11 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs24unsat_inverse11 (a : Assignment) : pairs24unsat_project (pairs24unsat_lift a) 11 = a 11 := by
  exact pairs24unsat_inverse11_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11)

theorem pairs24unsat_backward (a : Assignment) : evalCNF pairs24unsat_original (pairs24unsat_lift a) = evalCNF pairs24unsat_quotient a := by
  rw [pairs24unsat_forward]
  simp only [pairs24unsat_quotient, pairs24unsat_q0, pairs24unsat_q1, pairs24unsat_q2, pairs24unsat_q3, pairs24unsat_q4, pairs24unsat_q5, pairs24unsat_q6, pairs24unsat_q7, pairs24unsat_q8, pairs24unsat_q9, pairs24unsat_q10, pairs24unsat_q11, pairs24unsat_q12, evalCNF_append, evalCNF, evalClause, evalLit, pairs24unsat_inverse0, pairs24unsat_inverse1, pairs24unsat_inverse2, pairs24unsat_inverse3, pairs24unsat_inverse4, pairs24unsat_inverse5, pairs24unsat_inverse6, pairs24unsat_inverse7, pairs24unsat_inverse8, pairs24unsat_inverse9, pairs24unsat_inverse10, pairs24unsat_inverse11]
theorem pairs24unsat_equisatisfiable : (∃ a, evalCNF pairs24unsat_original a = true) ↔ (∃ b, evalCNF pairs24unsat_quotient b = true) :=
  equisat_of_two_maps (evalCNF pairs24unsat_original) (evalCNF pairs24unsat_quotient) pairs24unsat_project pairs24unsat_lift pairs24unsat_forward pairs24unsat_backward
#print axioms pairs24unsat_forward
#print axioms pairs24unsat_backward
#print axioms pairs24unsat_equisatisfiable

def pairs32sat_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 2) ^^ ((a 3) ^^ false))
  | 2 => ((a 4) ^^ ((a 5) ^^ false))
  | 3 => ((a 6) ^^ ((a 7) ^^ false))
  | 4 => ((a 8) ^^ ((a 9) ^^ false))
  | 5 => ((a 10) ^^ ((a 11) ^^ false))
  | 6 => ((a 12) ^^ ((a 13) ^^ false))
  | 7 => ((a 14) ^^ ((a 15) ^^ false))
  | 8 => ((a 16) ^^ ((a 17) ^^ false))
  | 9 => ((a 18) ^^ ((a 19) ^^ false))
  | 10 => ((a 20) ^^ ((a 21) ^^ false))
  | 11 => ((a 22) ^^ ((a 23) ^^ false))
  | 12 => ((a 24) ^^ ((a 25) ^^ false))
  | 13 => ((a 26) ^^ ((a 27) ^^ false))
  | 14 => ((a 28) ^^ ((a 29) ^^ false))
  | 15 => ((a 30) ^^ ((a 31) ^^ false))
  | _ => false

def pairs32sat_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => ((a 1) ^^ false)
  | 3 => false
  | 4 => ((a 2) ^^ false)
  | 5 => false
  | 6 => ((a 3) ^^ false)
  | 7 => false
  | 8 => ((a 4) ^^ false)
  | 9 => false
  | 10 => ((a 5) ^^ false)
  | 11 => false
  | 12 => ((a 6) ^^ false)
  | 13 => false
  | 14 => ((a 7) ^^ false)
  | 15 => false
  | 16 => ((a 8) ^^ false)
  | 17 => false
  | 18 => ((a 9) ^^ false)
  | 19 => false
  | 20 => ((a 10) ^^ false)
  | 21 => false
  | 22 => ((a 11) ^^ false)
  | 23 => false
  | 24 => ((a 12) ^^ false)
  | 25 => false
  | 26 => ((a 13) ^^ false)
  | 27 => false
  | 28 => ((a 14) ^^ false)
  | 29 => false
  | 30 => ((a 15) ^^ false)
  | 31 => false
  | _ => false

def pairs32sat_b0 : CNF := [[(false, 1), (false, 0)], [(true, 0), (true, 1)]]
def pairs32sat_q0 : CNF := [[(true, 0)]]
theorem pairs32sat_b0_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs32sat_b0_correct (a : Assignment) : evalCNF pairs32sat_b0 a = evalCNF pairs32sat_q0 (pairs32sat_project a) := by
  exact pairs32sat_b0_table (a 0) (a 1)

def pairs32sat_b1 : CNF := [[(false, 3), (false, 2), (false, 1), (true, 0)], [(false, 3), (false, 2), (false, 0), (true, 1)], [(false, 1), (true, 0), (true, 2), (true, 3)], [(false, 0), (true, 1), (true, 2), (true, 3)]]
def pairs32sat_q1 : CNF := [[(false, 0), (true, 1)]]
theorem pairs32sat_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b1_correct (a : Assignment) : evalCNF pairs32sat_b1 a = evalCNF pairs32sat_q1 (pairs32sat_project a) := by
  exact pairs32sat_b1_table (a 0) (a 1) (a 2) (a 3)

def pairs32sat_b2 : CNF := [[(false, 5), (false, 4), (false, 3), (true, 2)], [(false, 5), (false, 4), (false, 2), (true, 3)], [(false, 3), (true, 2), (true, 4), (true, 5)], [(false, 2), (true, 3), (true, 4), (true, 5)]]
def pairs32sat_q2 : CNF := [[(false, 1), (true, 2)]]
theorem pairs32sat_b2_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b2_correct (a : Assignment) : evalCNF pairs32sat_b2 a = evalCNF pairs32sat_q2 (pairs32sat_project a) := by
  exact pairs32sat_b2_table (a 2) (a 3) (a 4) (a 5)

def pairs32sat_b3 : CNF := [[(false, 7), (false, 6), (false, 5), (true, 4)], [(false, 7), (false, 6), (false, 4), (true, 5)], [(false, 5), (true, 4), (true, 6), (true, 7)], [(false, 4), (true, 5), (true, 6), (true, 7)]]
def pairs32sat_q3 : CNF := [[(false, 2), (true, 3)]]
theorem pairs32sat_b3_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b3_correct (a : Assignment) : evalCNF pairs32sat_b3 a = evalCNF pairs32sat_q3 (pairs32sat_project a) := by
  exact pairs32sat_b3_table (a 4) (a 5) (a 6) (a 7)

def pairs32sat_b4 : CNF := [[(false, 9), (false, 8), (false, 7), (true, 6)], [(false, 9), (false, 8), (false, 6), (true, 7)], [(false, 7), (true, 6), (true, 8), (true, 9)], [(false, 6), (true, 7), (true, 8), (true, 9)]]
def pairs32sat_q4 : CNF := [[(false, 3), (true, 4)]]
theorem pairs32sat_b4_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b4_correct (a : Assignment) : evalCNF pairs32sat_b4 a = evalCNF pairs32sat_q4 (pairs32sat_project a) := by
  exact pairs32sat_b4_table (a 6) (a 7) (a 8) (a 9)

def pairs32sat_b5 : CNF := [[(false, 11), (false, 10), (false, 9), (true, 8)], [(false, 11), (false, 10), (false, 8), (true, 9)], [(false, 9), (true, 8), (true, 10), (true, 11)], [(false, 8), (true, 9), (true, 10), (true, 11)]]
def pairs32sat_q5 : CNF := [[(false, 4), (true, 5)]]
theorem pairs32sat_b5_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b5_correct (a : Assignment) : evalCNF pairs32sat_b5 a = evalCNF pairs32sat_q5 (pairs32sat_project a) := by
  exact pairs32sat_b5_table (a 8) (a 9) (a 10) (a 11)

def pairs32sat_b6 : CNF := [[(false, 13), (false, 12), (false, 11), (true, 10)], [(false, 13), (false, 12), (false, 10), (true, 11)], [(false, 11), (true, 10), (true, 12), (true, 13)], [(false, 10), (true, 11), (true, 12), (true, 13)]]
def pairs32sat_q6 : CNF := [[(false, 5), (true, 6)]]
theorem pairs32sat_b6_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b6_correct (a : Assignment) : evalCNF pairs32sat_b6 a = evalCNF pairs32sat_q6 (pairs32sat_project a) := by
  exact pairs32sat_b6_table (a 10) (a 11) (a 12) (a 13)

def pairs32sat_b7 : CNF := [[(false, 15), (false, 14), (false, 13), (true, 12)], [(false, 15), (false, 14), (false, 12), (true, 13)], [(false, 13), (true, 12), (true, 14), (true, 15)], [(false, 12), (true, 13), (true, 14), (true, 15)]]
def pairs32sat_q7 : CNF := [[(false, 6), (true, 7)]]
theorem pairs32sat_b7_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b7_correct (a : Assignment) : evalCNF pairs32sat_b7 a = evalCNF pairs32sat_q7 (pairs32sat_project a) := by
  exact pairs32sat_b7_table (a 12) (a 13) (a 14) (a 15)

def pairs32sat_b8 : CNF := [[(false, 17), (false, 16), (false, 15), (true, 14)], [(false, 17), (false, 16), (false, 14), (true, 15)], [(false, 15), (true, 14), (true, 16), (true, 17)], [(false, 14), (true, 15), (true, 16), (true, 17)]]
def pairs32sat_q8 : CNF := [[(false, 7), (true, 8)]]
theorem pairs32sat_b8_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b8_correct (a : Assignment) : evalCNF pairs32sat_b8 a = evalCNF pairs32sat_q8 (pairs32sat_project a) := by
  exact pairs32sat_b8_table (a 14) (a 15) (a 16) (a 17)

def pairs32sat_b9 : CNF := [[(false, 19), (false, 18), (false, 17), (true, 16)], [(false, 19), (false, 18), (false, 16), (true, 17)], [(false, 17), (true, 16), (true, 18), (true, 19)], [(false, 16), (true, 17), (true, 18), (true, 19)]]
def pairs32sat_q9 : CNF := [[(false, 8), (true, 9)]]
theorem pairs32sat_b9_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b9_correct (a : Assignment) : evalCNF pairs32sat_b9 a = evalCNF pairs32sat_q9 (pairs32sat_project a) := by
  exact pairs32sat_b9_table (a 16) (a 17) (a 18) (a 19)

def pairs32sat_b10 : CNF := [[(false, 21), (false, 20), (false, 19), (true, 18)], [(false, 21), (false, 20), (false, 18), (true, 19)], [(false, 19), (true, 18), (true, 20), (true, 21)], [(false, 18), (true, 19), (true, 20), (true, 21)]]
def pairs32sat_q10 : CNF := [[(false, 9), (true, 10)]]
theorem pairs32sat_b10_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b10_correct (a : Assignment) : evalCNF pairs32sat_b10 a = evalCNF pairs32sat_q10 (pairs32sat_project a) := by
  exact pairs32sat_b10_table (a 18) (a 19) (a 20) (a 21)

def pairs32sat_b11 : CNF := [[(false, 23), (false, 22), (false, 21), (true, 20)], [(false, 23), (false, 22), (false, 20), (true, 21)], [(false, 21), (true, 20), (true, 22), (true, 23)], [(false, 20), (true, 21), (true, 22), (true, 23)]]
def pairs32sat_q11 : CNF := [[(false, 10), (true, 11)]]
theorem pairs32sat_b11_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b11_correct (a : Assignment) : evalCNF pairs32sat_b11 a = evalCNF pairs32sat_q11 (pairs32sat_project a) := by
  exact pairs32sat_b11_table (a 20) (a 21) (a 22) (a 23)

def pairs32sat_b12 : CNF := [[(false, 25), (false, 24), (false, 23), (true, 22)], [(false, 25), (false, 24), (false, 22), (true, 23)], [(false, 23), (true, 22), (true, 24), (true, 25)], [(false, 22), (true, 23), (true, 24), (true, 25)]]
def pairs32sat_q12 : CNF := [[(false, 11), (true, 12)]]
theorem pairs32sat_b12_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b12_correct (a : Assignment) : evalCNF pairs32sat_b12 a = evalCNF pairs32sat_q12 (pairs32sat_project a) := by
  exact pairs32sat_b12_table (a 22) (a 23) (a 24) (a 25)

def pairs32sat_b13 : CNF := [[(false, 27), (false, 26), (false, 25), (true, 24)], [(false, 27), (false, 26), (false, 24), (true, 25)], [(false, 25), (true, 24), (true, 26), (true, 27)], [(false, 24), (true, 25), (true, 26), (true, 27)]]
def pairs32sat_q13 : CNF := [[(false, 12), (true, 13)]]
theorem pairs32sat_b13_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b13_correct (a : Assignment) : evalCNF pairs32sat_b13 a = evalCNF pairs32sat_q13 (pairs32sat_project a) := by
  exact pairs32sat_b13_table (a 24) (a 25) (a 26) (a 27)

def pairs32sat_b14 : CNF := [[(false, 29), (false, 28), (false, 27), (true, 26)], [(false, 29), (false, 28), (false, 26), (true, 27)], [(false, 27), (true, 26), (true, 28), (true, 29)], [(false, 26), (true, 27), (true, 28), (true, 29)]]
def pairs32sat_q14 : CNF := [[(false, 13), (true, 14)]]
theorem pairs32sat_b14_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b14_correct (a : Assignment) : evalCNF pairs32sat_b14 a = evalCNF pairs32sat_q14 (pairs32sat_project a) := by
  exact pairs32sat_b14_table (a 26) (a 27) (a 28) (a 29)

def pairs32sat_b15 : CNF := [[(false, 31), (false, 30), (false, 29), (true, 28)], [(false, 31), (false, 30), (false, 28), (true, 29)], [(false, 29), (true, 28), (true, 30), (true, 31)], [(false, 28), (true, 29), (true, 30), (true, 31)]]
def pairs32sat_q15 : CNF := [[(false, 14), (true, 15)]]
theorem pairs32sat_b15_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32sat_b15_correct (a : Assignment) : evalCNF pairs32sat_b15 a = evalCNF pairs32sat_q15 (pairs32sat_project a) := by
  exact pairs32sat_b15_table (a 28) (a 29) (a 30) (a 31)

def pairs32sat_b16 : CNF := [[(false, 31), (false, 30)], [(true, 30), (true, 31)]]
def pairs32sat_q16 : CNF := [[(true, 15)]]
theorem pairs32sat_b16_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs32sat_b16_correct (a : Assignment) : evalCNF pairs32sat_b16 a = evalCNF pairs32sat_q16 (pairs32sat_project a) := by
  exact pairs32sat_b16_table (a 30) (a 31)

def pairs32sat_original : CNF := pairs32sat_b0 ++ pairs32sat_b1 ++ pairs32sat_b2 ++ pairs32sat_b3 ++ pairs32sat_b4 ++ pairs32sat_b5 ++ pairs32sat_b6 ++ pairs32sat_b7 ++ pairs32sat_b8 ++ pairs32sat_b9 ++ pairs32sat_b10 ++ pairs32sat_b11 ++ pairs32sat_b12 ++ pairs32sat_b13 ++ pairs32sat_b14 ++ pairs32sat_b15 ++ pairs32sat_b16 ++ []
def pairs32sat_quotient : CNF := pairs32sat_q0 ++ pairs32sat_q1 ++ pairs32sat_q2 ++ pairs32sat_q3 ++ pairs32sat_q4 ++ pairs32sat_q5 ++ pairs32sat_q6 ++ pairs32sat_q7 ++ pairs32sat_q8 ++ pairs32sat_q9 ++ pairs32sat_q10 ++ pairs32sat_q11 ++ pairs32sat_q12 ++ pairs32sat_q13 ++ pairs32sat_q14 ++ pairs32sat_q15 ++ pairs32sat_q16 ++ []
theorem pairs32sat_forward (a : Assignment) : evalCNF pairs32sat_original a = evalCNF pairs32sat_quotient (pairs32sat_project a) := by
  simp only [pairs32sat_original, pairs32sat_quotient, evalCNF_append]
  rw [pairs32sat_b0_correct, pairs32sat_b1_correct, pairs32sat_b2_correct, pairs32sat_b3_correct, pairs32sat_b4_correct, pairs32sat_b5_correct, pairs32sat_b6_correct, pairs32sat_b7_correct, pairs32sat_b8_correct, pairs32sat_b9_correct, pairs32sat_b10_correct, pairs32sat_b11_correct, pairs32sat_b12_correct, pairs32sat_b13_correct, pairs32sat_b14_correct, pairs32sat_b15_correct, pairs32sat_b16_correct]
  rfl

theorem pairs32sat_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse0 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 0 = a 0 := by
  exact pairs32sat_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse1 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 1 = a 1 := by
  exact pairs32sat_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse2 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 2 = a 2 := by
  exact pairs32sat_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y3 ^^ false) ^^ (false ^^ false)) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ false)) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse3 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 3 = a 3 := by
  exact pairs32sat_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y4 ^^ false) ^^ (false ^^ false)) = y4 := by
  calc
    ((y4 ^^ false) ^^ (false ^^ false)) = (y4 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse4 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 4 = a 4 := by
  exact pairs32sat_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y5 ^^ false) ^^ (false ^^ false)) = y5 := by
  calc
    ((y5 ^^ false) ^^ (false ^^ false)) = (y5 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse5 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 5 = a 5 := by
  exact pairs32sat_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y6 ^^ false) ^^ (false ^^ false)) = y6 := by
  calc
    ((y6 ^^ false) ^^ (false ^^ false)) = (y6 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse6 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 6 = a 6 := by
  exact pairs32sat_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y7 ^^ false) ^^ (false ^^ false)) = y7 := by
  calc
    ((y7 ^^ false) ^^ (false ^^ false)) = (y7 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse7 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 7 = a 7 := by
  exact pairs32sat_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse8_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y8 ^^ false) ^^ (false ^^ false)) = y8 := by
  calc
    ((y8 ^^ false) ^^ (false ^^ false)) = (y8 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y8 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse8 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 8 = a 8 := by
  exact pairs32sat_inverse8_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse9_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y9 ^^ false) ^^ (false ^^ false)) = y9 := by
  calc
    ((y9 ^^ false) ^^ (false ^^ false)) = (y9 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y9 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse9 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 9 = a 9 := by
  exact pairs32sat_inverse9_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse10_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y10 ^^ false) ^^ (false ^^ false)) = y10 := by
  calc
    ((y10 ^^ false) ^^ (false ^^ false)) = (y10 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y10 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse10 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 10 = a 10 := by
  exact pairs32sat_inverse10_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse11_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y11 ^^ false) ^^ (false ^^ false)) = y11 := by
  calc
    ((y11 ^^ false) ^^ (false ^^ false)) = (y11 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y11 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse11 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 11 = a 11 := by
  exact pairs32sat_inverse11_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse12_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y12 ^^ false) ^^ (false ^^ false)) = y12 := by
  calc
    ((y12 ^^ false) ^^ (false ^^ false)) = (y12 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y12 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse12 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 12 = a 12 := by
  exact pairs32sat_inverse12_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse13_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y13 ^^ false) ^^ (false ^^ false)) = y13 := by
  calc
    ((y13 ^^ false) ^^ (false ^^ false)) = (y13 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y13 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse13 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 13 = a 13 := by
  exact pairs32sat_inverse13_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse14_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y14 ^^ false) ^^ (false ^^ false)) = y14 := by
  calc
    ((y14 ^^ false) ^^ (false ^^ false)) = (y14 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y14 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse14 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 14 = a 14 := by
  exact pairs32sat_inverse14_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_inverse15_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y15 ^^ false) ^^ (false ^^ false)) = y15 := by
  calc
    ((y15 ^^ false) ^^ (false ^^ false)) = (y15 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y15 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32sat_inverse15 (a : Assignment) : pairs32sat_project (pairs32sat_lift a) 15 = a 15 := by
  exact pairs32sat_inverse15_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32sat_backward (a : Assignment) : evalCNF pairs32sat_original (pairs32sat_lift a) = evalCNF pairs32sat_quotient a := by
  rw [pairs32sat_forward]
  simp only [pairs32sat_quotient, pairs32sat_q0, pairs32sat_q1, pairs32sat_q2, pairs32sat_q3, pairs32sat_q4, pairs32sat_q5, pairs32sat_q6, pairs32sat_q7, pairs32sat_q8, pairs32sat_q9, pairs32sat_q10, pairs32sat_q11, pairs32sat_q12, pairs32sat_q13, pairs32sat_q14, pairs32sat_q15, pairs32sat_q16, evalCNF_append, evalCNF, evalClause, evalLit, pairs32sat_inverse0, pairs32sat_inverse1, pairs32sat_inverse2, pairs32sat_inverse3, pairs32sat_inverse4, pairs32sat_inverse5, pairs32sat_inverse6, pairs32sat_inverse7, pairs32sat_inverse8, pairs32sat_inverse9, pairs32sat_inverse10, pairs32sat_inverse11, pairs32sat_inverse12, pairs32sat_inverse13, pairs32sat_inverse14, pairs32sat_inverse15]
theorem pairs32sat_equisatisfiable : (∃ a, evalCNF pairs32sat_original a = true) ↔ (∃ b, evalCNF pairs32sat_quotient b = true) :=
  equisat_of_two_maps (evalCNF pairs32sat_original) (evalCNF pairs32sat_quotient) pairs32sat_project pairs32sat_lift pairs32sat_forward pairs32sat_backward
#print axioms pairs32sat_forward
#print axioms pairs32sat_backward
#print axioms pairs32sat_equisatisfiable

def pairs32unsat_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 2) ^^ ((a 3) ^^ false))
  | 2 => ((a 4) ^^ ((a 5) ^^ false))
  | 3 => ((a 6) ^^ ((a 7) ^^ false))
  | 4 => ((a 8) ^^ ((a 9) ^^ false))
  | 5 => ((a 10) ^^ ((a 11) ^^ false))
  | 6 => ((a 12) ^^ ((a 13) ^^ false))
  | 7 => ((a 14) ^^ ((a 15) ^^ false))
  | 8 => ((a 16) ^^ ((a 17) ^^ false))
  | 9 => ((a 18) ^^ ((a 19) ^^ false))
  | 10 => ((a 20) ^^ ((a 21) ^^ false))
  | 11 => ((a 22) ^^ ((a 23) ^^ false))
  | 12 => ((a 24) ^^ ((a 25) ^^ false))
  | 13 => ((a 26) ^^ ((a 27) ^^ false))
  | 14 => ((a 28) ^^ ((a 29) ^^ false))
  | 15 => ((a 30) ^^ ((a 31) ^^ false))
  | _ => false

def pairs32unsat_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ false)
  | 1 => false
  | 2 => ((a 1) ^^ false)
  | 3 => false
  | 4 => ((a 2) ^^ false)
  | 5 => false
  | 6 => ((a 3) ^^ false)
  | 7 => false
  | 8 => ((a 4) ^^ false)
  | 9 => false
  | 10 => ((a 5) ^^ false)
  | 11 => false
  | 12 => ((a 6) ^^ false)
  | 13 => false
  | 14 => ((a 7) ^^ false)
  | 15 => false
  | 16 => ((a 8) ^^ false)
  | 17 => false
  | 18 => ((a 9) ^^ false)
  | 19 => false
  | 20 => ((a 10) ^^ false)
  | 21 => false
  | 22 => ((a 11) ^^ false)
  | 23 => false
  | 24 => ((a 12) ^^ false)
  | 25 => false
  | 26 => ((a 13) ^^ false)
  | 27 => false
  | 28 => ((a 14) ^^ false)
  | 29 => false
  | 30 => ((a 15) ^^ false)
  | 31 => false
  | _ => false

def pairs32unsat_b0 : CNF := [[(false, 1), (false, 0)], [(true, 0), (true, 1)]]
def pairs32unsat_q0 : CNF := [[(true, 0)]]
theorem pairs32unsat_b0_table (b0 b1 : Bool) : (((!b1) || ((!b0) || false)) && ((b0 || (b1 || false)) && true)) = (((b0 ^^ (b1 ^^ false)) || false) && true) := by
  decide +revert
theorem pairs32unsat_b0_correct (a : Assignment) : evalCNF pairs32unsat_b0 a = evalCNF pairs32unsat_q0 (pairs32unsat_project a) := by
  exact pairs32unsat_b0_table (a 0) (a 1)

def pairs32unsat_b1 : CNF := [[(false, 3), (false, 2), (false, 1), (true, 0)], [(false, 3), (false, 2), (false, 0), (true, 1)], [(false, 1), (true, 0), (true, 2), (true, 3)], [(false, 0), (true, 1), (true, 2), (true, 3)]]
def pairs32unsat_q1 : CNF := [[(false, 0), (true, 1)]]
theorem pairs32unsat_b1_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b1_correct (a : Assignment) : evalCNF pairs32unsat_b1 a = evalCNF pairs32unsat_q1 (pairs32unsat_project a) := by
  exact pairs32unsat_b1_table (a 0) (a 1) (a 2) (a 3)

def pairs32unsat_b2 : CNF := [[(false, 5), (false, 4), (false, 3), (true, 2)], [(false, 5), (false, 4), (false, 2), (true, 3)], [(false, 3), (true, 2), (true, 4), (true, 5)], [(false, 2), (true, 3), (true, 4), (true, 5)]]
def pairs32unsat_q2 : CNF := [[(false, 1), (true, 2)]]
theorem pairs32unsat_b2_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b2_correct (a : Assignment) : evalCNF pairs32unsat_b2 a = evalCNF pairs32unsat_q2 (pairs32unsat_project a) := by
  exact pairs32unsat_b2_table (a 2) (a 3) (a 4) (a 5)

def pairs32unsat_b3 : CNF := [[(false, 7), (false, 6), (false, 5), (true, 4)], [(false, 7), (false, 6), (false, 4), (true, 5)], [(false, 5), (true, 4), (true, 6), (true, 7)], [(false, 4), (true, 5), (true, 6), (true, 7)]]
def pairs32unsat_q3 : CNF := [[(false, 2), (true, 3)]]
theorem pairs32unsat_b3_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b3_correct (a : Assignment) : evalCNF pairs32unsat_b3 a = evalCNF pairs32unsat_q3 (pairs32unsat_project a) := by
  exact pairs32unsat_b3_table (a 4) (a 5) (a 6) (a 7)

def pairs32unsat_b4 : CNF := [[(false, 9), (false, 8), (false, 7), (true, 6)], [(false, 9), (false, 8), (false, 6), (true, 7)], [(false, 7), (true, 6), (true, 8), (true, 9)], [(false, 6), (true, 7), (true, 8), (true, 9)]]
def pairs32unsat_q4 : CNF := [[(false, 3), (true, 4)]]
theorem pairs32unsat_b4_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b4_correct (a : Assignment) : evalCNF pairs32unsat_b4 a = evalCNF pairs32unsat_q4 (pairs32unsat_project a) := by
  exact pairs32unsat_b4_table (a 6) (a 7) (a 8) (a 9)

def pairs32unsat_b5 : CNF := [[(false, 11), (false, 10), (false, 9), (true, 8)], [(false, 11), (false, 10), (false, 8), (true, 9)], [(false, 9), (true, 8), (true, 10), (true, 11)], [(false, 8), (true, 9), (true, 10), (true, 11)]]
def pairs32unsat_q5 : CNF := [[(false, 4), (true, 5)]]
theorem pairs32unsat_b5_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b5_correct (a : Assignment) : evalCNF pairs32unsat_b5 a = evalCNF pairs32unsat_q5 (pairs32unsat_project a) := by
  exact pairs32unsat_b5_table (a 8) (a 9) (a 10) (a 11)

def pairs32unsat_b6 : CNF := [[(false, 13), (false, 12), (false, 11), (true, 10)], [(false, 13), (false, 12), (false, 10), (true, 11)], [(false, 11), (true, 10), (true, 12), (true, 13)], [(false, 10), (true, 11), (true, 12), (true, 13)]]
def pairs32unsat_q6 : CNF := [[(false, 5), (true, 6)]]
theorem pairs32unsat_b6_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b6_correct (a : Assignment) : evalCNF pairs32unsat_b6 a = evalCNF pairs32unsat_q6 (pairs32unsat_project a) := by
  exact pairs32unsat_b6_table (a 10) (a 11) (a 12) (a 13)

def pairs32unsat_b7 : CNF := [[(false, 15), (false, 14), (false, 13), (true, 12)], [(false, 15), (false, 14), (false, 12), (true, 13)], [(false, 13), (true, 12), (true, 14), (true, 15)], [(false, 12), (true, 13), (true, 14), (true, 15)]]
def pairs32unsat_q7 : CNF := [[(false, 6), (true, 7)]]
theorem pairs32unsat_b7_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b7_correct (a : Assignment) : evalCNF pairs32unsat_b7 a = evalCNF pairs32unsat_q7 (pairs32unsat_project a) := by
  exact pairs32unsat_b7_table (a 12) (a 13) (a 14) (a 15)

def pairs32unsat_b8 : CNF := [[(false, 17), (false, 16), (false, 15), (true, 14)], [(false, 17), (false, 16), (false, 14), (true, 15)], [(false, 15), (true, 14), (true, 16), (true, 17)], [(false, 14), (true, 15), (true, 16), (true, 17)]]
def pairs32unsat_q8 : CNF := [[(false, 7), (true, 8)]]
theorem pairs32unsat_b8_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b8_correct (a : Assignment) : evalCNF pairs32unsat_b8 a = evalCNF pairs32unsat_q8 (pairs32unsat_project a) := by
  exact pairs32unsat_b8_table (a 14) (a 15) (a 16) (a 17)

def pairs32unsat_b9 : CNF := [[(false, 19), (false, 18), (false, 17), (true, 16)], [(false, 19), (false, 18), (false, 16), (true, 17)], [(false, 17), (true, 16), (true, 18), (true, 19)], [(false, 16), (true, 17), (true, 18), (true, 19)]]
def pairs32unsat_q9 : CNF := [[(false, 8), (true, 9)]]
theorem pairs32unsat_b9_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b9_correct (a : Assignment) : evalCNF pairs32unsat_b9 a = evalCNF pairs32unsat_q9 (pairs32unsat_project a) := by
  exact pairs32unsat_b9_table (a 16) (a 17) (a 18) (a 19)

def pairs32unsat_b10 : CNF := [[(false, 21), (false, 20), (false, 19), (true, 18)], [(false, 21), (false, 20), (false, 18), (true, 19)], [(false, 19), (true, 18), (true, 20), (true, 21)], [(false, 18), (true, 19), (true, 20), (true, 21)]]
def pairs32unsat_q10 : CNF := [[(false, 9), (true, 10)]]
theorem pairs32unsat_b10_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b10_correct (a : Assignment) : evalCNF pairs32unsat_b10 a = evalCNF pairs32unsat_q10 (pairs32unsat_project a) := by
  exact pairs32unsat_b10_table (a 18) (a 19) (a 20) (a 21)

def pairs32unsat_b11 : CNF := [[(false, 23), (false, 22), (false, 21), (true, 20)], [(false, 23), (false, 22), (false, 20), (true, 21)], [(false, 21), (true, 20), (true, 22), (true, 23)], [(false, 20), (true, 21), (true, 22), (true, 23)]]
def pairs32unsat_q11 : CNF := [[(false, 10), (true, 11)]]
theorem pairs32unsat_b11_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b11_correct (a : Assignment) : evalCNF pairs32unsat_b11 a = evalCNF pairs32unsat_q11 (pairs32unsat_project a) := by
  exact pairs32unsat_b11_table (a 20) (a 21) (a 22) (a 23)

def pairs32unsat_b12 : CNF := [[(false, 25), (false, 24), (false, 23), (true, 22)], [(false, 25), (false, 24), (false, 22), (true, 23)], [(false, 23), (true, 22), (true, 24), (true, 25)], [(false, 22), (true, 23), (true, 24), (true, 25)]]
def pairs32unsat_q12 : CNF := [[(false, 11), (true, 12)]]
theorem pairs32unsat_b12_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b12_correct (a : Assignment) : evalCNF pairs32unsat_b12 a = evalCNF pairs32unsat_q12 (pairs32unsat_project a) := by
  exact pairs32unsat_b12_table (a 22) (a 23) (a 24) (a 25)

def pairs32unsat_b13 : CNF := [[(false, 27), (false, 26), (false, 25), (true, 24)], [(false, 27), (false, 26), (false, 24), (true, 25)], [(false, 25), (true, 24), (true, 26), (true, 27)], [(false, 24), (true, 25), (true, 26), (true, 27)]]
def pairs32unsat_q13 : CNF := [[(false, 12), (true, 13)]]
theorem pairs32unsat_b13_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b13_correct (a : Assignment) : evalCNF pairs32unsat_b13 a = evalCNF pairs32unsat_q13 (pairs32unsat_project a) := by
  exact pairs32unsat_b13_table (a 24) (a 25) (a 26) (a 27)

def pairs32unsat_b14 : CNF := [[(false, 29), (false, 28), (false, 27), (true, 26)], [(false, 29), (false, 28), (false, 26), (true, 27)], [(false, 27), (true, 26), (true, 28), (true, 29)], [(false, 26), (true, 27), (true, 28), (true, 29)]]
def pairs32unsat_q14 : CNF := [[(false, 13), (true, 14)]]
theorem pairs32unsat_b14_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b14_correct (a : Assignment) : evalCNF pairs32unsat_b14 a = evalCNF pairs32unsat_q14 (pairs32unsat_project a) := by
  exact pairs32unsat_b14_table (a 26) (a 27) (a 28) (a 29)

def pairs32unsat_b15 : CNF := [[(false, 31), (false, 30), (false, 29), (true, 28)], [(false, 31), (false, 30), (false, 28), (true, 29)], [(false, 29), (true, 28), (true, 30), (true, 31)], [(false, 28), (true, 29), (true, 30), (true, 31)]]
def pairs32unsat_q15 : CNF := [[(false, 14), (true, 15)]]
theorem pairs32unsat_b15_table (b0 b1 b2 b3 : Bool) : (((!b3) || ((!b2) || ((!b1) || (b0 || false)))) && (((!b3) || ((!b2) || ((!b0) || (b1 || false)))) && (((!b1) || (b0 || (b2 || (b3 || false)))) && (((!b0) || (b1 || (b2 || (b3 || false)))) && true)))) = (((!(b0 ^^ (b1 ^^ false))) || ((b2 ^^ (b3 ^^ false)) || false)) && true) := by
  decide +revert
theorem pairs32unsat_b15_correct (a : Assignment) : evalCNF pairs32unsat_b15 a = evalCNF pairs32unsat_q15 (pairs32unsat_project a) := by
  exact pairs32unsat_b15_table (a 28) (a 29) (a 30) (a 31)

def pairs32unsat_b16 : CNF := [[(false, 31), (true, 30)], [(false, 30), (true, 31)]]
def pairs32unsat_q16 : CNF := [[(false, 15)]]
theorem pairs32unsat_b16_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem pairs32unsat_b16_correct (a : Assignment) : evalCNF pairs32unsat_b16 a = evalCNF pairs32unsat_q16 (pairs32unsat_project a) := by
  exact pairs32unsat_b16_table (a 30) (a 31)

def pairs32unsat_original : CNF := pairs32unsat_b0 ++ pairs32unsat_b1 ++ pairs32unsat_b2 ++ pairs32unsat_b3 ++ pairs32unsat_b4 ++ pairs32unsat_b5 ++ pairs32unsat_b6 ++ pairs32unsat_b7 ++ pairs32unsat_b8 ++ pairs32unsat_b9 ++ pairs32unsat_b10 ++ pairs32unsat_b11 ++ pairs32unsat_b12 ++ pairs32unsat_b13 ++ pairs32unsat_b14 ++ pairs32unsat_b15 ++ pairs32unsat_b16 ++ []
def pairs32unsat_quotient : CNF := pairs32unsat_q0 ++ pairs32unsat_q1 ++ pairs32unsat_q2 ++ pairs32unsat_q3 ++ pairs32unsat_q4 ++ pairs32unsat_q5 ++ pairs32unsat_q6 ++ pairs32unsat_q7 ++ pairs32unsat_q8 ++ pairs32unsat_q9 ++ pairs32unsat_q10 ++ pairs32unsat_q11 ++ pairs32unsat_q12 ++ pairs32unsat_q13 ++ pairs32unsat_q14 ++ pairs32unsat_q15 ++ pairs32unsat_q16 ++ []
theorem pairs32unsat_forward (a : Assignment) : evalCNF pairs32unsat_original a = evalCNF pairs32unsat_quotient (pairs32unsat_project a) := by
  simp only [pairs32unsat_original, pairs32unsat_quotient, evalCNF_append]
  rw [pairs32unsat_b0_correct, pairs32unsat_b1_correct, pairs32unsat_b2_correct, pairs32unsat_b3_correct, pairs32unsat_b4_correct, pairs32unsat_b5_correct, pairs32unsat_b6_correct, pairs32unsat_b7_correct, pairs32unsat_b8_correct, pairs32unsat_b9_correct, pairs32unsat_b10_correct, pairs32unsat_b11_correct, pairs32unsat_b12_correct, pairs32unsat_b13_correct, pairs32unsat_b14_correct, pairs32unsat_b15_correct, pairs32unsat_b16_correct]
  rfl

theorem pairs32unsat_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y0 ^^ false) ^^ (false ^^ false)) = y0 := by
  calc
    ((y0 ^^ false) ^^ (false ^^ false)) = (y0 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse0 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 0 = a 0 := by
  exact pairs32unsat_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y1 ^^ false) ^^ (false ^^ false)) = y1 := by
  calc
    ((y1 ^^ false) ^^ (false ^^ false)) = (y1 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse1 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 1 = a 1 := by
  exact pairs32unsat_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y2 ^^ false) ^^ (false ^^ false)) = y2 := by
  calc
    ((y2 ^^ false) ^^ (false ^^ false)) = (y2 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse2 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 2 = a 2 := by
  exact pairs32unsat_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y3 ^^ false) ^^ (false ^^ false)) = y3 := by
  calc
    ((y3 ^^ false) ^^ (false ^^ false)) = (y3 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse3 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 3 = a 3 := by
  exact pairs32unsat_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y4 ^^ false) ^^ (false ^^ false)) = y4 := by
  calc
    ((y4 ^^ false) ^^ (false ^^ false)) = (y4 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse4 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 4 = a 4 := by
  exact pairs32unsat_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y5 ^^ false) ^^ (false ^^ false)) = y5 := by
  calc
    ((y5 ^^ false) ^^ (false ^^ false)) = (y5 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse5 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 5 = a 5 := by
  exact pairs32unsat_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y6 ^^ false) ^^ (false ^^ false)) = y6 := by
  calc
    ((y6 ^^ false) ^^ (false ^^ false)) = (y6 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse6 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 6 = a 6 := by
  exact pairs32unsat_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y7 ^^ false) ^^ (false ^^ false)) = y7 := by
  calc
    ((y7 ^^ false) ^^ (false ^^ false)) = (y7 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse7 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 7 = a 7 := by
  exact pairs32unsat_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse8_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y8 ^^ false) ^^ (false ^^ false)) = y8 := by
  calc
    ((y8 ^^ false) ^^ (false ^^ false)) = (y8 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y8 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse8 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 8 = a 8 := by
  exact pairs32unsat_inverse8_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse9_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y9 ^^ false) ^^ (false ^^ false)) = y9 := by
  calc
    ((y9 ^^ false) ^^ (false ^^ false)) = (y9 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y9 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse9 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 9 = a 9 := by
  exact pairs32unsat_inverse9_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse10_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y10 ^^ false) ^^ (false ^^ false)) = y10 := by
  calc
    ((y10 ^^ false) ^^ (false ^^ false)) = (y10 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y10 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse10 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 10 = a 10 := by
  exact pairs32unsat_inverse10_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse11_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y11 ^^ false) ^^ (false ^^ false)) = y11 := by
  calc
    ((y11 ^^ false) ^^ (false ^^ false)) = (y11 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y11 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse11 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 11 = a 11 := by
  exact pairs32unsat_inverse11_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse12_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y12 ^^ false) ^^ (false ^^ false)) = y12 := by
  calc
    ((y12 ^^ false) ^^ (false ^^ false)) = (y12 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y12 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse12 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 12 = a 12 := by
  exact pairs32unsat_inverse12_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse13_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y13 ^^ false) ^^ (false ^^ false)) = y13 := by
  calc
    ((y13 ^^ false) ^^ (false ^^ false)) = (y13 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y13 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse13 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 13 = a 13 := by
  exact pairs32unsat_inverse13_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse14_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y14 ^^ false) ^^ (false ^^ false)) = y14 := by
  calc
    ((y14 ^^ false) ^^ (false ^^ false)) = (y14 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y14 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse14 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 14 = a 14 := by
  exact pairs32unsat_inverse14_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_inverse15_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Bool) : ((y15 ^^ false) ^^ (false ^^ false)) = y15 := by
  calc
    ((y15 ^^ false) ^^ (false ^^ false)) = (y15 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y15 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem pairs32unsat_inverse15 (a : Assignment) : pairs32unsat_project (pairs32unsat_lift a) 15 = a 15 := by
  exact pairs32unsat_inverse15_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15)

theorem pairs32unsat_backward (a : Assignment) : evalCNF pairs32unsat_original (pairs32unsat_lift a) = evalCNF pairs32unsat_quotient a := by
  rw [pairs32unsat_forward]
  simp only [pairs32unsat_quotient, pairs32unsat_q0, pairs32unsat_q1, pairs32unsat_q2, pairs32unsat_q3, pairs32unsat_q4, pairs32unsat_q5, pairs32unsat_q6, pairs32unsat_q7, pairs32unsat_q8, pairs32unsat_q9, pairs32unsat_q10, pairs32unsat_q11, pairs32unsat_q12, pairs32unsat_q13, pairs32unsat_q14, pairs32unsat_q15, pairs32unsat_q16, evalCNF_append, evalCNF, evalClause, evalLit, pairs32unsat_inverse0, pairs32unsat_inverse1, pairs32unsat_inverse2, pairs32unsat_inverse3, pairs32unsat_inverse4, pairs32unsat_inverse5, pairs32unsat_inverse6, pairs32unsat_inverse7, pairs32unsat_inverse8, pairs32unsat_inverse9, pairs32unsat_inverse10, pairs32unsat_inverse11, pairs32unsat_inverse12, pairs32unsat_inverse13, pairs32unsat_inverse14, pairs32unsat_inverse15]
theorem pairs32unsat_equisatisfiable : (∃ a, evalCNF pairs32unsat_original a = true) ↔ (∃ b, evalCNF pairs32unsat_quotient b = true) :=
  equisat_of_two_maps (evalCNF pairs32unsat_original) (evalCNF pairs32unsat_quotient) pairs32unsat_project pairs32unsat_lift pairs32unsat_forward pairs32unsat_backward
#print axioms pairs32unsat_forward
#print axioms pairs32unsat_backward
#print axioms pairs32unsat_equisatisfiable

def overlap16_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 1) ^^ ((a 2) ^^ false))
  | 2 => ((a 2) ^^ ((a 3) ^^ false))
  | 3 => ((a 3) ^^ ((a 4) ^^ false))
  | 4 => ((a 4) ^^ ((a 5) ^^ false))
  | 5 => ((a 5) ^^ ((a 6) ^^ false))
  | 6 => ((a 6) ^^ ((a 7) ^^ false))
  | 7 => ((a 7) ^^ ((a 8) ^^ false))
  | 8 => ((a 8) ^^ ((a 9) ^^ false))
  | 9 => ((a 9) ^^ ((a 10) ^^ false))
  | 10 => ((a 10) ^^ ((a 11) ^^ false))
  | 11 => ((a 11) ^^ ((a 12) ^^ false))
  | 12 => ((a 12) ^^ ((a 13) ^^ false))
  | 13 => ((a 13) ^^ ((a 14) ^^ false))
  | 14 => ((a 14) ^^ ((a 15) ^^ false))
  | _ => false

def overlap16_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ ((a 2) ^^ ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false)))))))))))))))
  | 1 => ((a 1) ^^ ((a 2) ^^ ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false))))))))))))))
  | 2 => ((a 2) ^^ ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false)))))))))))))
  | 3 => ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false))))))))))))
  | 4 => ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false)))))))))))
  | 5 => ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false))))))))))
  | 6 => ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false)))))))))
  | 7 => ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false))))))))
  | 8 => ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false)))))))
  | 9 => ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false))))))
  | 10 => ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false)))))
  | 11 => ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false))))
  | 12 => ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ false)))
  | 13 => ((a 13) ^^ ((a 14) ^^ false))
  | 14 => ((a 14) ^^ false)
  | 15 => false
  | _ => false

def overlap16_b0 : CNF := [[(false, 1), (true, 0)], [(false, 0), (true, 1)]]
def overlap16_q0 : CNF := [[(false, 0)]]
theorem overlap16_b0_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b0_correct (a : Assignment) : evalCNF overlap16_b0 a = evalCNF overlap16_q0 (overlap16_project a) := by
  exact overlap16_b0_table (a 0) (a 1)

def overlap16_b1 : CNF := [[(false, 2), (true, 1)], [(false, 1), (true, 2)]]
def overlap16_q1 : CNF := [[(false, 1)]]
theorem overlap16_b1_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b1_correct (a : Assignment) : evalCNF overlap16_b1 a = evalCNF overlap16_q1 (overlap16_project a) := by
  exact overlap16_b1_table (a 1) (a 2)

def overlap16_b2 : CNF := [[(false, 3), (true, 2)], [(false, 2), (true, 3)]]
def overlap16_q2 : CNF := [[(false, 2)]]
theorem overlap16_b2_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b2_correct (a : Assignment) : evalCNF overlap16_b2 a = evalCNF overlap16_q2 (overlap16_project a) := by
  exact overlap16_b2_table (a 2) (a 3)

def overlap16_b3 : CNF := [[(false, 4), (true, 3)], [(false, 3), (true, 4)]]
def overlap16_q3 : CNF := [[(false, 3)]]
theorem overlap16_b3_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b3_correct (a : Assignment) : evalCNF overlap16_b3 a = evalCNF overlap16_q3 (overlap16_project a) := by
  exact overlap16_b3_table (a 3) (a 4)

def overlap16_b4 : CNF := [[(false, 5), (true, 4)], [(false, 4), (true, 5)]]
def overlap16_q4 : CNF := [[(false, 4)]]
theorem overlap16_b4_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b4_correct (a : Assignment) : evalCNF overlap16_b4 a = evalCNF overlap16_q4 (overlap16_project a) := by
  exact overlap16_b4_table (a 4) (a 5)

def overlap16_b5 : CNF := [[(false, 6), (true, 5)], [(false, 5), (true, 6)]]
def overlap16_q5 : CNF := [[(false, 5)]]
theorem overlap16_b5_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b5_correct (a : Assignment) : evalCNF overlap16_b5 a = evalCNF overlap16_q5 (overlap16_project a) := by
  exact overlap16_b5_table (a 5) (a 6)

def overlap16_b6 : CNF := [[(false, 7), (true, 6)], [(false, 6), (true, 7)]]
def overlap16_q6 : CNF := [[(false, 6)]]
theorem overlap16_b6_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b6_correct (a : Assignment) : evalCNF overlap16_b6 a = evalCNF overlap16_q6 (overlap16_project a) := by
  exact overlap16_b6_table (a 6) (a 7)

def overlap16_b7 : CNF := [[(false, 8), (true, 7)], [(false, 7), (true, 8)]]
def overlap16_q7 : CNF := [[(false, 7)]]
theorem overlap16_b7_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b7_correct (a : Assignment) : evalCNF overlap16_b7 a = evalCNF overlap16_q7 (overlap16_project a) := by
  exact overlap16_b7_table (a 7) (a 8)

def overlap16_b8 : CNF := [[(false, 9), (true, 8)], [(false, 8), (true, 9)]]
def overlap16_q8 : CNF := [[(false, 8)]]
theorem overlap16_b8_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b8_correct (a : Assignment) : evalCNF overlap16_b8 a = evalCNF overlap16_q8 (overlap16_project a) := by
  exact overlap16_b8_table (a 8) (a 9)

def overlap16_b9 : CNF := [[(false, 10), (true, 9)], [(false, 9), (true, 10)]]
def overlap16_q9 : CNF := [[(false, 9)]]
theorem overlap16_b9_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b9_correct (a : Assignment) : evalCNF overlap16_b9 a = evalCNF overlap16_q9 (overlap16_project a) := by
  exact overlap16_b9_table (a 9) (a 10)

def overlap16_b10 : CNF := [[(false, 11), (true, 10)], [(false, 10), (true, 11)]]
def overlap16_q10 : CNF := [[(false, 10)]]
theorem overlap16_b10_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b10_correct (a : Assignment) : evalCNF overlap16_b10 a = evalCNF overlap16_q10 (overlap16_project a) := by
  exact overlap16_b10_table (a 10) (a 11)

def overlap16_b11 : CNF := [[(false, 12), (true, 11)], [(false, 11), (true, 12)]]
def overlap16_q11 : CNF := [[(false, 11)]]
theorem overlap16_b11_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b11_correct (a : Assignment) : evalCNF overlap16_b11 a = evalCNF overlap16_q11 (overlap16_project a) := by
  exact overlap16_b11_table (a 11) (a 12)

def overlap16_b12 : CNF := [[(false, 13), (true, 12)], [(false, 12), (true, 13)]]
def overlap16_q12 : CNF := [[(false, 12)]]
theorem overlap16_b12_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b12_correct (a : Assignment) : evalCNF overlap16_b12 a = evalCNF overlap16_q12 (overlap16_project a) := by
  exact overlap16_b12_table (a 12) (a 13)

def overlap16_b13 : CNF := [[(false, 14), (true, 13)], [(false, 13), (true, 14)]]
def overlap16_q13 : CNF := [[(false, 13)]]
theorem overlap16_b13_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b13_correct (a : Assignment) : evalCNF overlap16_b13 a = evalCNF overlap16_q13 (overlap16_project a) := by
  exact overlap16_b13_table (a 13) (a 14)

def overlap16_b14 : CNF := [[(false, 15), (true, 14)], [(false, 14), (true, 15)]]
def overlap16_q14 : CNF := [[(false, 14)]]
theorem overlap16_b14_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap16_b14_correct (a : Assignment) : evalCNF overlap16_b14 a = evalCNF overlap16_q14 (overlap16_project a) := by
  exact overlap16_b14_table (a 14) (a 15)

def overlap16_original : CNF := overlap16_b0 ++ overlap16_b1 ++ overlap16_b2 ++ overlap16_b3 ++ overlap16_b4 ++ overlap16_b5 ++ overlap16_b6 ++ overlap16_b7 ++ overlap16_b8 ++ overlap16_b9 ++ overlap16_b10 ++ overlap16_b11 ++ overlap16_b12 ++ overlap16_b13 ++ overlap16_b14 ++ []
def overlap16_quotient : CNF := overlap16_q0 ++ overlap16_q1 ++ overlap16_q2 ++ overlap16_q3 ++ overlap16_q4 ++ overlap16_q5 ++ overlap16_q6 ++ overlap16_q7 ++ overlap16_q8 ++ overlap16_q9 ++ overlap16_q10 ++ overlap16_q11 ++ overlap16_q12 ++ overlap16_q13 ++ overlap16_q14 ++ []
theorem overlap16_forward (a : Assignment) : evalCNF overlap16_original a = evalCNF overlap16_quotient (overlap16_project a) := by
  simp only [overlap16_original, overlap16_quotient, evalCNF_append]
  rw [overlap16_b0_correct, overlap16_b1_correct, overlap16_b2_correct, overlap16_b3_correct, overlap16_b4_correct, overlap16_b5_correct, overlap16_b6_correct, overlap16_b7_correct, overlap16_b8_correct, overlap16_b9_correct, overlap16_b10_correct, overlap16_b11_correct, overlap16_b12_correct, overlap16_b13_correct, overlap16_b14_correct]
  rfl

theorem overlap16_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y0 ^^ (y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))))))) ^^ ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))))) ^^ false)) = y0 := by
  calc
    ((y0 ^^ (y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))))))) ^^ ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))))) ^^ false)) = (y0 ^^ (y1 ^^ (y1 ^^ (y2 ^^ (y2 ^^ (y3 ^^ (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse0 (a : Assignment) : overlap16_project (overlap16_lift a) 0 = a 0 := by
  exact overlap16_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))))) ^^ ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))))) ^^ false)) = y1 := by
  calc
    ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))))) ^^ ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))))) ^^ false)) = (y1 ^^ (y2 ^^ (y2 ^^ (y3 ^^ (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse1 (a : Assignment) : overlap16_project (overlap16_lift a) 1 = a 1 := by
  exact overlap16_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))))) ^^ ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))) ^^ false)) = y2 := by
  calc
    ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))))) ^^ ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))) ^^ false)) = (y2 ^^ (y3 ^^ (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse2 (a : Assignment) : overlap16_project (overlap16_lift a) 2 = a 2 := by
  exact overlap16_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))) ^^ ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))) ^^ false)) = y3 := by
  calc
    ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))))) ^^ ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))) ^^ false)) = (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse3 (a : Assignment) : overlap16_project (overlap16_lift a) 3 = a 3 := by
  exact overlap16_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))) ^^ ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))) ^^ false)) = y4 := by
  calc
    ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))))) ^^ ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))) ^^ false)) = (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse4 (a : Assignment) : overlap16_project (overlap16_lift a) 4 = a 4 := by
  exact overlap16_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))) ^^ ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))) ^^ false)) = y5 := by
  calc
    ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))))) ^^ ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))) ^^ false)) = (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse5 (a : Assignment) : overlap16_project (overlap16_lift a) 5 = a 5 := by
  exact overlap16_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))) ^^ ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))) ^^ false)) = y6 := by
  calc
    ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))))) ^^ ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))) ^^ false)) = (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse6 (a : Assignment) : overlap16_project (overlap16_lift a) 6 = a 6 := by
  exact overlap16_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))) ^^ ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))) ^^ false)) = y7 := by
  calc
    ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))))) ^^ ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))) ^^ false)) = (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse7 (a : Assignment) : overlap16_project (overlap16_lift a) 7 = a 7 := by
  exact overlap16_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse8_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))) ^^ ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))) ^^ false)) = y8 := by
  calc
    ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))))) ^^ ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))) ^^ false)) = (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y8 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse8 (a : Assignment) : overlap16_project (overlap16_lift a) 8 = a 8 := by
  exact overlap16_inverse8_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse9_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))) ^^ ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))) ^^ false)) = y9 := by
  calc
    ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))))) ^^ ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))) ^^ false)) = (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y9 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse9 (a : Assignment) : overlap16_project (overlap16_lift a) 9 = a 9 := by
  exact overlap16_inverse9_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse10_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))) ^^ ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))) ^^ false)) = y10 := by
  calc
    ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false))))) ^^ ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))) ^^ false)) = (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y10 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse10 (a : Assignment) : overlap16_project (overlap16_lift a) 10 = a 10 := by
  exact overlap16_inverse10_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse11_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))) ^^ ((y12 ^^ (y13 ^^ (y14 ^^ false))) ^^ false)) = y11 := by
  calc
    ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ false)))) ^^ ((y12 ^^ (y13 ^^ (y14 ^^ false))) ^^ false)) = (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y11 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse11 (a : Assignment) : overlap16_project (overlap16_lift a) 11 = a 11 := by
  exact overlap16_inverse11_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse12_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y12 ^^ (y13 ^^ (y14 ^^ false))) ^^ ((y13 ^^ (y14 ^^ false)) ^^ false)) = y12 := by
  calc
    ((y12 ^^ (y13 ^^ (y14 ^^ false))) ^^ ((y13 ^^ (y14 ^^ false)) ^^ false)) = (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ false))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y12 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse12 (a : Assignment) : overlap16_project (overlap16_lift a) 12 = a 12 := by
  exact overlap16_inverse12_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse13_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y13 ^^ (y14 ^^ false)) ^^ ((y14 ^^ false) ^^ false)) = y13 := by
  calc
    ((y13 ^^ (y14 ^^ false)) ^^ ((y14 ^^ false) ^^ false)) = (y13 ^^ (y14 ^^ (y14 ^^ false))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y13 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse13 (a : Assignment) : overlap16_project (overlap16_lift a) 13 = a 13 := by
  exact overlap16_inverse13_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_inverse14_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 : Bool) : ((y14 ^^ false) ^^ (false ^^ false)) = y14 := by
  calc
    ((y14 ^^ false) ^^ (false ^^ false)) = (y14 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y14 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap16_inverse14 (a : Assignment) : overlap16_project (overlap16_lift a) 14 = a 14 := by
  exact overlap16_inverse14_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14)

theorem overlap16_backward (a : Assignment) : evalCNF overlap16_original (overlap16_lift a) = evalCNF overlap16_quotient a := by
  rw [overlap16_forward]
  simp only [overlap16_quotient, overlap16_q0, overlap16_q1, overlap16_q2, overlap16_q3, overlap16_q4, overlap16_q5, overlap16_q6, overlap16_q7, overlap16_q8, overlap16_q9, overlap16_q10, overlap16_q11, overlap16_q12, overlap16_q13, overlap16_q14, evalCNF_append, evalCNF, evalClause, evalLit, overlap16_inverse0, overlap16_inverse1, overlap16_inverse2, overlap16_inverse3, overlap16_inverse4, overlap16_inverse5, overlap16_inverse6, overlap16_inverse7, overlap16_inverse8, overlap16_inverse9, overlap16_inverse10, overlap16_inverse11, overlap16_inverse12, overlap16_inverse13, overlap16_inverse14]
theorem overlap16_equisatisfiable : (∃ a, evalCNF overlap16_original a = true) ↔ (∃ b, evalCNF overlap16_quotient b = true) :=
  equisat_of_two_maps (evalCNF overlap16_original) (evalCNF overlap16_quotient) overlap16_project overlap16_lift overlap16_forward overlap16_backward
#print axioms overlap16_forward
#print axioms overlap16_backward
#print axioms overlap16_equisatisfiable

def overlap32_project (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ false))
  | 1 => ((a 1) ^^ ((a 2) ^^ false))
  | 2 => ((a 2) ^^ ((a 3) ^^ false))
  | 3 => ((a 3) ^^ ((a 4) ^^ false))
  | 4 => ((a 4) ^^ ((a 5) ^^ false))
  | 5 => ((a 5) ^^ ((a 6) ^^ false))
  | 6 => ((a 6) ^^ ((a 7) ^^ false))
  | 7 => ((a 7) ^^ ((a 8) ^^ false))
  | 8 => ((a 8) ^^ ((a 9) ^^ false))
  | 9 => ((a 9) ^^ ((a 10) ^^ false))
  | 10 => ((a 10) ^^ ((a 11) ^^ false))
  | 11 => ((a 11) ^^ ((a 12) ^^ false))
  | 12 => ((a 12) ^^ ((a 13) ^^ false))
  | 13 => ((a 13) ^^ ((a 14) ^^ false))
  | 14 => ((a 14) ^^ ((a 15) ^^ false))
  | 15 => ((a 15) ^^ ((a 16) ^^ false))
  | 16 => ((a 16) ^^ ((a 17) ^^ false))
  | 17 => ((a 17) ^^ ((a 18) ^^ false))
  | 18 => ((a 18) ^^ ((a 19) ^^ false))
  | 19 => ((a 19) ^^ ((a 20) ^^ false))
  | 20 => ((a 20) ^^ ((a 21) ^^ false))
  | 21 => ((a 21) ^^ ((a 22) ^^ false))
  | 22 => ((a 22) ^^ ((a 23) ^^ false))
  | 23 => ((a 23) ^^ ((a 24) ^^ false))
  | 24 => ((a 24) ^^ ((a 25) ^^ false))
  | 25 => ((a 25) ^^ ((a 26) ^^ false))
  | 26 => ((a 26) ^^ ((a 27) ^^ false))
  | 27 => ((a 27) ^^ ((a 28) ^^ false))
  | 28 => ((a 28) ^^ ((a 29) ^^ false))
  | 29 => ((a 29) ^^ ((a 30) ^^ false))
  | 30 => ((a 30) ^^ ((a 31) ^^ false))
  | _ => false

def overlap32_lift (a : Assignment) : Assignment := fun i => match i with
  | 0 => ((a 0) ^^ ((a 1) ^^ ((a 2) ^^ ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))))))))))))))))
  | 1 => ((a 1) ^^ ((a 2) ^^ ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))))))))))))))))
  | 2 => ((a 2) ^^ ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))))))))))))))
  | 3 => ((a 3) ^^ ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))))))))))))))
  | 4 => ((a 4) ^^ ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))))))))))))
  | 5 => ((a 5) ^^ ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))))))))))))
  | 6 => ((a 6) ^^ ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))))))))))
  | 7 => ((a 7) ^^ ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))))))))))
  | 8 => ((a 8) ^^ ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))))))))
  | 9 => ((a 9) ^^ ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))))))))
  | 10 => ((a 10) ^^ ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))))))
  | 11 => ((a 11) ^^ ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))))))
  | 12 => ((a 12) ^^ ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))))
  | 13 => ((a 13) ^^ ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))))
  | 14 => ((a 14) ^^ ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))))
  | 15 => ((a 15) ^^ ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))))
  | 16 => ((a 16) ^^ ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))))
  | 17 => ((a 17) ^^ ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))))
  | 18 => ((a 18) ^^ ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))))
  | 19 => ((a 19) ^^ ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))))
  | 20 => ((a 20) ^^ ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))))
  | 21 => ((a 21) ^^ ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))))
  | 22 => ((a 22) ^^ ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))))
  | 23 => ((a 23) ^^ ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))))
  | 24 => ((a 24) ^^ ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))))
  | 25 => ((a 25) ^^ ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))))
  | 26 => ((a 26) ^^ ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))))
  | 27 => ((a 27) ^^ ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false))))
  | 28 => ((a 28) ^^ ((a 29) ^^ ((a 30) ^^ false)))
  | 29 => ((a 29) ^^ ((a 30) ^^ false))
  | 30 => ((a 30) ^^ false)
  | 31 => false
  | _ => false

def overlap32_b0 : CNF := [[(false, 1), (true, 0)], [(false, 0), (true, 1)]]
def overlap32_q0 : CNF := [[(false, 0)]]
theorem overlap32_b0_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b0_correct (a : Assignment) : evalCNF overlap32_b0 a = evalCNF overlap32_q0 (overlap32_project a) := by
  exact overlap32_b0_table (a 0) (a 1)

def overlap32_b1 : CNF := [[(false, 2), (true, 1)], [(false, 1), (true, 2)]]
def overlap32_q1 : CNF := [[(false, 1)]]
theorem overlap32_b1_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b1_correct (a : Assignment) : evalCNF overlap32_b1 a = evalCNF overlap32_q1 (overlap32_project a) := by
  exact overlap32_b1_table (a 1) (a 2)

def overlap32_b2 : CNF := [[(false, 3), (true, 2)], [(false, 2), (true, 3)]]
def overlap32_q2 : CNF := [[(false, 2)]]
theorem overlap32_b2_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b2_correct (a : Assignment) : evalCNF overlap32_b2 a = evalCNF overlap32_q2 (overlap32_project a) := by
  exact overlap32_b2_table (a 2) (a 3)

def overlap32_b3 : CNF := [[(false, 4), (true, 3)], [(false, 3), (true, 4)]]
def overlap32_q3 : CNF := [[(false, 3)]]
theorem overlap32_b3_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b3_correct (a : Assignment) : evalCNF overlap32_b3 a = evalCNF overlap32_q3 (overlap32_project a) := by
  exact overlap32_b3_table (a 3) (a 4)

def overlap32_b4 : CNF := [[(false, 5), (true, 4)], [(false, 4), (true, 5)]]
def overlap32_q4 : CNF := [[(false, 4)]]
theorem overlap32_b4_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b4_correct (a : Assignment) : evalCNF overlap32_b4 a = evalCNF overlap32_q4 (overlap32_project a) := by
  exact overlap32_b4_table (a 4) (a 5)

def overlap32_b5 : CNF := [[(false, 6), (true, 5)], [(false, 5), (true, 6)]]
def overlap32_q5 : CNF := [[(false, 5)]]
theorem overlap32_b5_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b5_correct (a : Assignment) : evalCNF overlap32_b5 a = evalCNF overlap32_q5 (overlap32_project a) := by
  exact overlap32_b5_table (a 5) (a 6)

def overlap32_b6 : CNF := [[(false, 7), (true, 6)], [(false, 6), (true, 7)]]
def overlap32_q6 : CNF := [[(false, 6)]]
theorem overlap32_b6_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b6_correct (a : Assignment) : evalCNF overlap32_b6 a = evalCNF overlap32_q6 (overlap32_project a) := by
  exact overlap32_b6_table (a 6) (a 7)

def overlap32_b7 : CNF := [[(false, 8), (true, 7)], [(false, 7), (true, 8)]]
def overlap32_q7 : CNF := [[(false, 7)]]
theorem overlap32_b7_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b7_correct (a : Assignment) : evalCNF overlap32_b7 a = evalCNF overlap32_q7 (overlap32_project a) := by
  exact overlap32_b7_table (a 7) (a 8)

def overlap32_b8 : CNF := [[(false, 9), (true, 8)], [(false, 8), (true, 9)]]
def overlap32_q8 : CNF := [[(false, 8)]]
theorem overlap32_b8_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b8_correct (a : Assignment) : evalCNF overlap32_b8 a = evalCNF overlap32_q8 (overlap32_project a) := by
  exact overlap32_b8_table (a 8) (a 9)

def overlap32_b9 : CNF := [[(false, 10), (true, 9)], [(false, 9), (true, 10)]]
def overlap32_q9 : CNF := [[(false, 9)]]
theorem overlap32_b9_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b9_correct (a : Assignment) : evalCNF overlap32_b9 a = evalCNF overlap32_q9 (overlap32_project a) := by
  exact overlap32_b9_table (a 9) (a 10)

def overlap32_b10 : CNF := [[(false, 11), (true, 10)], [(false, 10), (true, 11)]]
def overlap32_q10 : CNF := [[(false, 10)]]
theorem overlap32_b10_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b10_correct (a : Assignment) : evalCNF overlap32_b10 a = evalCNF overlap32_q10 (overlap32_project a) := by
  exact overlap32_b10_table (a 10) (a 11)

def overlap32_b11 : CNF := [[(false, 12), (true, 11)], [(false, 11), (true, 12)]]
def overlap32_q11 : CNF := [[(false, 11)]]
theorem overlap32_b11_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b11_correct (a : Assignment) : evalCNF overlap32_b11 a = evalCNF overlap32_q11 (overlap32_project a) := by
  exact overlap32_b11_table (a 11) (a 12)

def overlap32_b12 : CNF := [[(false, 13), (true, 12)], [(false, 12), (true, 13)]]
def overlap32_q12 : CNF := [[(false, 12)]]
theorem overlap32_b12_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b12_correct (a : Assignment) : evalCNF overlap32_b12 a = evalCNF overlap32_q12 (overlap32_project a) := by
  exact overlap32_b12_table (a 12) (a 13)

def overlap32_b13 : CNF := [[(false, 14), (true, 13)], [(false, 13), (true, 14)]]
def overlap32_q13 : CNF := [[(false, 13)]]
theorem overlap32_b13_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b13_correct (a : Assignment) : evalCNF overlap32_b13 a = evalCNF overlap32_q13 (overlap32_project a) := by
  exact overlap32_b13_table (a 13) (a 14)

def overlap32_b14 : CNF := [[(false, 15), (true, 14)], [(false, 14), (true, 15)]]
def overlap32_q14 : CNF := [[(false, 14)]]
theorem overlap32_b14_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b14_correct (a : Assignment) : evalCNF overlap32_b14 a = evalCNF overlap32_q14 (overlap32_project a) := by
  exact overlap32_b14_table (a 14) (a 15)

def overlap32_b15 : CNF := [[(false, 16), (true, 15)], [(false, 15), (true, 16)]]
def overlap32_q15 : CNF := [[(false, 15)]]
theorem overlap32_b15_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b15_correct (a : Assignment) : evalCNF overlap32_b15 a = evalCNF overlap32_q15 (overlap32_project a) := by
  exact overlap32_b15_table (a 15) (a 16)

def overlap32_b16 : CNF := [[(false, 17), (true, 16)], [(false, 16), (true, 17)]]
def overlap32_q16 : CNF := [[(false, 16)]]
theorem overlap32_b16_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b16_correct (a : Assignment) : evalCNF overlap32_b16 a = evalCNF overlap32_q16 (overlap32_project a) := by
  exact overlap32_b16_table (a 16) (a 17)

def overlap32_b17 : CNF := [[(false, 18), (true, 17)], [(false, 17), (true, 18)]]
def overlap32_q17 : CNF := [[(false, 17)]]
theorem overlap32_b17_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b17_correct (a : Assignment) : evalCNF overlap32_b17 a = evalCNF overlap32_q17 (overlap32_project a) := by
  exact overlap32_b17_table (a 17) (a 18)

def overlap32_b18 : CNF := [[(false, 19), (true, 18)], [(false, 18), (true, 19)]]
def overlap32_q18 : CNF := [[(false, 18)]]
theorem overlap32_b18_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b18_correct (a : Assignment) : evalCNF overlap32_b18 a = evalCNF overlap32_q18 (overlap32_project a) := by
  exact overlap32_b18_table (a 18) (a 19)

def overlap32_b19 : CNF := [[(false, 20), (true, 19)], [(false, 19), (true, 20)]]
def overlap32_q19 : CNF := [[(false, 19)]]
theorem overlap32_b19_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b19_correct (a : Assignment) : evalCNF overlap32_b19 a = evalCNF overlap32_q19 (overlap32_project a) := by
  exact overlap32_b19_table (a 19) (a 20)

def overlap32_b20 : CNF := [[(false, 21), (true, 20)], [(false, 20), (true, 21)]]
def overlap32_q20 : CNF := [[(false, 20)]]
theorem overlap32_b20_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b20_correct (a : Assignment) : evalCNF overlap32_b20 a = evalCNF overlap32_q20 (overlap32_project a) := by
  exact overlap32_b20_table (a 20) (a 21)

def overlap32_b21 : CNF := [[(false, 22), (true, 21)], [(false, 21), (true, 22)]]
def overlap32_q21 : CNF := [[(false, 21)]]
theorem overlap32_b21_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b21_correct (a : Assignment) : evalCNF overlap32_b21 a = evalCNF overlap32_q21 (overlap32_project a) := by
  exact overlap32_b21_table (a 21) (a 22)

def overlap32_b22 : CNF := [[(false, 23), (true, 22)], [(false, 22), (true, 23)]]
def overlap32_q22 : CNF := [[(false, 22)]]
theorem overlap32_b22_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b22_correct (a : Assignment) : evalCNF overlap32_b22 a = evalCNF overlap32_q22 (overlap32_project a) := by
  exact overlap32_b22_table (a 22) (a 23)

def overlap32_b23 : CNF := [[(false, 24), (true, 23)], [(false, 23), (true, 24)]]
def overlap32_q23 : CNF := [[(false, 23)]]
theorem overlap32_b23_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b23_correct (a : Assignment) : evalCNF overlap32_b23 a = evalCNF overlap32_q23 (overlap32_project a) := by
  exact overlap32_b23_table (a 23) (a 24)

def overlap32_b24 : CNF := [[(false, 25), (true, 24)], [(false, 24), (true, 25)]]
def overlap32_q24 : CNF := [[(false, 24)]]
theorem overlap32_b24_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b24_correct (a : Assignment) : evalCNF overlap32_b24 a = evalCNF overlap32_q24 (overlap32_project a) := by
  exact overlap32_b24_table (a 24) (a 25)

def overlap32_b25 : CNF := [[(false, 26), (true, 25)], [(false, 25), (true, 26)]]
def overlap32_q25 : CNF := [[(false, 25)]]
theorem overlap32_b25_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b25_correct (a : Assignment) : evalCNF overlap32_b25 a = evalCNF overlap32_q25 (overlap32_project a) := by
  exact overlap32_b25_table (a 25) (a 26)

def overlap32_b26 : CNF := [[(false, 27), (true, 26)], [(false, 26), (true, 27)]]
def overlap32_q26 : CNF := [[(false, 26)]]
theorem overlap32_b26_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b26_correct (a : Assignment) : evalCNF overlap32_b26 a = evalCNF overlap32_q26 (overlap32_project a) := by
  exact overlap32_b26_table (a 26) (a 27)

def overlap32_b27 : CNF := [[(false, 28), (true, 27)], [(false, 27), (true, 28)]]
def overlap32_q27 : CNF := [[(false, 27)]]
theorem overlap32_b27_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b27_correct (a : Assignment) : evalCNF overlap32_b27 a = evalCNF overlap32_q27 (overlap32_project a) := by
  exact overlap32_b27_table (a 27) (a 28)

def overlap32_b28 : CNF := [[(false, 29), (true, 28)], [(false, 28), (true, 29)]]
def overlap32_q28 : CNF := [[(false, 28)]]
theorem overlap32_b28_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b28_correct (a : Assignment) : evalCNF overlap32_b28 a = evalCNF overlap32_q28 (overlap32_project a) := by
  exact overlap32_b28_table (a 28) (a 29)

def overlap32_b29 : CNF := [[(false, 30), (true, 29)], [(false, 29), (true, 30)]]
def overlap32_q29 : CNF := [[(false, 29)]]
theorem overlap32_b29_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b29_correct (a : Assignment) : evalCNF overlap32_b29 a = evalCNF overlap32_q29 (overlap32_project a) := by
  exact overlap32_b29_table (a 29) (a 30)

def overlap32_b30 : CNF := [[(false, 31), (true, 30)], [(false, 30), (true, 31)]]
def overlap32_q30 : CNF := [[(false, 30)]]
theorem overlap32_b30_table (b0 b1 : Bool) : (((!b1) || (b0 || false)) && (((!b0) || (b1 || false)) && true)) = (((!(b0 ^^ (b1 ^^ false))) || false) && true) := by
  decide +revert
theorem overlap32_b30_correct (a : Assignment) : evalCNF overlap32_b30 a = evalCNF overlap32_q30 (overlap32_project a) := by
  exact overlap32_b30_table (a 30) (a 31)

def overlap32_original : CNF := overlap32_b0 ++ overlap32_b1 ++ overlap32_b2 ++ overlap32_b3 ++ overlap32_b4 ++ overlap32_b5 ++ overlap32_b6 ++ overlap32_b7 ++ overlap32_b8 ++ overlap32_b9 ++ overlap32_b10 ++ overlap32_b11 ++ overlap32_b12 ++ overlap32_b13 ++ overlap32_b14 ++ overlap32_b15 ++ overlap32_b16 ++ overlap32_b17 ++ overlap32_b18 ++ overlap32_b19 ++ overlap32_b20 ++ overlap32_b21 ++ overlap32_b22 ++ overlap32_b23 ++ overlap32_b24 ++ overlap32_b25 ++ overlap32_b26 ++ overlap32_b27 ++ overlap32_b28 ++ overlap32_b29 ++ overlap32_b30 ++ []
def overlap32_quotient : CNF := overlap32_q0 ++ overlap32_q1 ++ overlap32_q2 ++ overlap32_q3 ++ overlap32_q4 ++ overlap32_q5 ++ overlap32_q6 ++ overlap32_q7 ++ overlap32_q8 ++ overlap32_q9 ++ overlap32_q10 ++ overlap32_q11 ++ overlap32_q12 ++ overlap32_q13 ++ overlap32_q14 ++ overlap32_q15 ++ overlap32_q16 ++ overlap32_q17 ++ overlap32_q18 ++ overlap32_q19 ++ overlap32_q20 ++ overlap32_q21 ++ overlap32_q22 ++ overlap32_q23 ++ overlap32_q24 ++ overlap32_q25 ++ overlap32_q26 ++ overlap32_q27 ++ overlap32_q28 ++ overlap32_q29 ++ overlap32_q30 ++ []
theorem overlap32_forward (a : Assignment) : evalCNF overlap32_original a = evalCNF overlap32_quotient (overlap32_project a) := by
  simp only [overlap32_original, overlap32_quotient, evalCNF_append]
  rw [overlap32_b0_correct, overlap32_b1_correct, overlap32_b2_correct, overlap32_b3_correct, overlap32_b4_correct, overlap32_b5_correct, overlap32_b6_correct, overlap32_b7_correct, overlap32_b8_correct, overlap32_b9_correct, overlap32_b10_correct, overlap32_b11_correct, overlap32_b12_correct, overlap32_b13_correct, overlap32_b14_correct, overlap32_b15_correct, overlap32_b16_correct, overlap32_b17_correct, overlap32_b18_correct, overlap32_b19_correct, overlap32_b20_correct, overlap32_b21_correct, overlap32_b22_correct, overlap32_b23_correct, overlap32_b24_correct, overlap32_b25_correct, overlap32_b26_correct, overlap32_b27_correct, overlap32_b28_correct, overlap32_b29_correct, overlap32_b30_correct]
  rfl

theorem overlap32_inverse0_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y0 ^^ (y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))))))) ^^ ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))))) ^^ false)) = y0 := by
  calc
    ((y0 ^^ (y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))))))) ^^ ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))))) ^^ false)) = (y0 ^^ (y1 ^^ (y1 ^^ (y2 ^^ (y2 ^^ (y3 ^^ (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y0 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse0 (a : Assignment) : overlap32_project (overlap32_lift a) 0 = a 0 := by
  exact overlap32_inverse0_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse1_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))))) ^^ ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))))) ^^ false)) = y1 := by
  calc
    ((y1 ^^ (y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))))) ^^ ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))))) ^^ false)) = (y1 ^^ (y2 ^^ (y2 ^^ (y3 ^^ (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y1 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse1 (a : Assignment) : overlap32_project (overlap32_lift a) 1 = a 1 := by
  exact overlap32_inverse1_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse2_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))))) ^^ ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))) ^^ false)) = y2 := by
  calc
    ((y2 ^^ (y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))))) ^^ ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))) ^^ false)) = (y2 ^^ (y3 ^^ (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y2 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse2 (a : Assignment) : overlap32_project (overlap32_lift a) 2 = a 2 := by
  exact overlap32_inverse2_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse3_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))) ^^ ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))) ^^ false)) = y3 := by
  calc
    ((y3 ^^ (y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))))) ^^ ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))) ^^ false)) = (y3 ^^ (y4 ^^ (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y3 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse3 (a : Assignment) : overlap32_project (overlap32_lift a) 3 = a 3 := by
  exact overlap32_inverse3_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse4_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))) ^^ ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))) ^^ false)) = y4 := by
  calc
    ((y4 ^^ (y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))))) ^^ ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))) ^^ false)) = (y4 ^^ (y5 ^^ (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y4 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse4 (a : Assignment) : overlap32_project (overlap32_lift a) 4 = a 4 := by
  exact overlap32_inverse4_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse5_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))) ^^ ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))) ^^ false)) = y5 := by
  calc
    ((y5 ^^ (y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))))) ^^ ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))) ^^ false)) = (y5 ^^ (y6 ^^ (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y5 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse5 (a : Assignment) : overlap32_project (overlap32_lift a) 5 = a 5 := by
  exact overlap32_inverse5_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse6_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))) ^^ ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))) ^^ false)) = y6 := by
  calc
    ((y6 ^^ (y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))))) ^^ ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))) ^^ false)) = (y6 ^^ (y7 ^^ (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y6 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse6 (a : Assignment) : overlap32_project (overlap32_lift a) 6 = a 6 := by
  exact overlap32_inverse6_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse7_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))) ^^ ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))) ^^ false)) = y7 := by
  calc
    ((y7 ^^ (y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))))) ^^ ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))) ^^ false)) = (y7 ^^ (y8 ^^ (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y7 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse7 (a : Assignment) : overlap32_project (overlap32_lift a) 7 = a 7 := by
  exact overlap32_inverse7_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse8_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))) ^^ ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))) ^^ false)) = y8 := by
  calc
    ((y8 ^^ (y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))))) ^^ ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))) ^^ false)) = (y8 ^^ (y9 ^^ (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y8 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse8 (a : Assignment) : overlap32_project (overlap32_lift a) 8 = a 8 := by
  exact overlap32_inverse8_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse9_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))) ^^ ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))) ^^ false)) = y9 := by
  calc
    ((y9 ^^ (y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))))) ^^ ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))) ^^ false)) = (y9 ^^ (y10 ^^ (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y9 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse9 (a : Assignment) : overlap32_project (overlap32_lift a) 9 = a 9 := by
  exact overlap32_inverse9_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse10_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))) ^^ ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))) ^^ false)) = y10 := by
  calc
    ((y10 ^^ (y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))))) ^^ ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))) ^^ false)) = (y10 ^^ (y11 ^^ (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y10 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse10 (a : Assignment) : overlap32_project (overlap32_lift a) 10 = a 10 := by
  exact overlap32_inverse10_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse11_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))) ^^ ((y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))) ^^ false)) = y11 := by
  calc
    ((y11 ^^ (y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))))) ^^ ((y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))) ^^ false)) = (y11 ^^ (y12 ^^ (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y11 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse11 (a : Assignment) : overlap32_project (overlap32_lift a) 11 = a 11 := by
  exact overlap32_inverse11_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse12_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))) ^^ ((y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))) ^^ false)) = y12 := by
  calc
    ((y12 ^^ (y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))))) ^^ ((y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))) ^^ false)) = (y12 ^^ (y13 ^^ (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y12 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse12 (a : Assignment) : overlap32_project (overlap32_lift a) 12 = a 12 := by
  exact overlap32_inverse12_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse13_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))) ^^ ((y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))) ^^ false)) = y13 := by
  calc
    ((y13 ^^ (y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))))) ^^ ((y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))) ^^ false)) = (y13 ^^ (y14 ^^ (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y13 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse13 (a : Assignment) : overlap32_project (overlap32_lift a) 13 = a 13 := by
  exact overlap32_inverse13_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse14_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))) ^^ ((y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))) ^^ false)) = y14 := by
  calc
    ((y14 ^^ (y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))))) ^^ ((y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))) ^^ false)) = (y14 ^^ (y15 ^^ (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y14 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse14 (a : Assignment) : overlap32_project (overlap32_lift a) 14 = a 14 := by
  exact overlap32_inverse14_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse15_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))) ^^ ((y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))) ^^ false)) = y15 := by
  calc
    ((y15 ^^ (y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))))) ^^ ((y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))) ^^ false)) = (y15 ^^ (y16 ^^ (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y15 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse15 (a : Assignment) : overlap32_project (overlap32_lift a) 15 = a 15 := by
  exact overlap32_inverse15_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse16_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))) ^^ ((y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))) ^^ false)) = y16 := by
  calc
    ((y16 ^^ (y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))))) ^^ ((y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))) ^^ false)) = (y16 ^^ (y17 ^^ (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y16 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse16 (a : Assignment) : overlap32_project (overlap32_lift a) 16 = a 16 := by
  exact overlap32_inverse16_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse17_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))) ^^ ((y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))) ^^ false)) = y17 := by
  calc
    ((y17 ^^ (y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))))) ^^ ((y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))) ^^ false)) = (y17 ^^ (y18 ^^ (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y17 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse17 (a : Assignment) : overlap32_project (overlap32_lift a) 17 = a 17 := by
  exact overlap32_inverse17_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse18_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))) ^^ ((y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))) ^^ false)) = y18 := by
  calc
    ((y18 ^^ (y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))))) ^^ ((y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))) ^^ false)) = (y18 ^^ (y19 ^^ (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y18 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse18 (a : Assignment) : overlap32_project (overlap32_lift a) 18 = a 18 := by
  exact overlap32_inverse18_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse19_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))) ^^ ((y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))) ^^ false)) = y19 := by
  calc
    ((y19 ^^ (y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))))) ^^ ((y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))) ^^ false)) = (y19 ^^ (y20 ^^ (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y19 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse19 (a : Assignment) : overlap32_project (overlap32_lift a) 19 = a 19 := by
  exact overlap32_inverse19_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse20_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))) ^^ ((y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))) ^^ false)) = y20 := by
  calc
    ((y20 ^^ (y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))))) ^^ ((y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))) ^^ false)) = (y20 ^^ (y21 ^^ (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y20 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse20 (a : Assignment) : overlap32_project (overlap32_lift a) 20 = a 20 := by
  exact overlap32_inverse20_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse21_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))) ^^ ((y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))) ^^ false)) = y21 := by
  calc
    ((y21 ^^ (y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))))) ^^ ((y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))) ^^ false)) = (y21 ^^ (y22 ^^ (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y21 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse21 (a : Assignment) : overlap32_project (overlap32_lift a) 21 = a 21 := by
  exact overlap32_inverse21_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse22_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))) ^^ ((y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))) ^^ false)) = y22 := by
  calc
    ((y22 ^^ (y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))))) ^^ ((y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))) ^^ false)) = (y22 ^^ (y23 ^^ (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y22 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse22 (a : Assignment) : overlap32_project (overlap32_lift a) 22 = a 22 := by
  exact overlap32_inverse22_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse23_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))) ^^ ((y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))) ^^ false)) = y23 := by
  calc
    ((y23 ^^ (y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))))) ^^ ((y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))) ^^ false)) = (y23 ^^ (y24 ^^ (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y23 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse23 (a : Assignment) : overlap32_project (overlap32_lift a) 23 = a 23 := by
  exact overlap32_inverse23_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse24_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))) ^^ ((y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))) ^^ false)) = y24 := by
  calc
    ((y24 ^^ (y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))))) ^^ ((y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))) ^^ false)) = (y24 ^^ (y25 ^^ (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y24 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse24 (a : Assignment) : overlap32_project (overlap32_lift a) 24 = a 24 := by
  exact overlap32_inverse24_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse25_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))) ^^ ((y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))) ^^ false)) = y25 := by
  calc
    ((y25 ^^ (y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))))) ^^ ((y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))) ^^ false)) = (y25 ^^ (y26 ^^ (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y25 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse25 (a : Assignment) : overlap32_project (overlap32_lift a) 25 = a 25 := by
  exact overlap32_inverse25_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse26_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))) ^^ ((y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))) ^^ false)) = y26 := by
  calc
    ((y26 ^^ (y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false))))) ^^ ((y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))) ^^ false)) = (y26 ^^ (y27 ^^ (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y26 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse26 (a : Assignment) : overlap32_project (overlap32_lift a) 26 = a 26 := by
  exact overlap32_inverse26_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse27_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))) ^^ ((y28 ^^ (y29 ^^ (y30 ^^ false))) ^^ false)) = y27 := by
  calc
    ((y27 ^^ (y28 ^^ (y29 ^^ (y30 ^^ false)))) ^^ ((y28 ^^ (y29 ^^ (y30 ^^ false))) ^^ false)) = (y27 ^^ (y28 ^^ (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y27 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse27 (a : Assignment) : overlap32_project (overlap32_lift a) 27 = a 27 := by
  exact overlap32_inverse27_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse28_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y28 ^^ (y29 ^^ (y30 ^^ false))) ^^ ((y29 ^^ (y30 ^^ false)) ^^ false)) = y28 := by
  calc
    ((y28 ^^ (y29 ^^ (y30 ^^ false))) ^^ ((y29 ^^ (y30 ^^ false)) ^^ false)) = (y28 ^^ (y29 ^^ (y29 ^^ (y30 ^^ (y30 ^^ false))))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y28 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse28 (a : Assignment) : overlap32_project (overlap32_lift a) 28 = a 28 := by
  exact overlap32_inverse28_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse29_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y29 ^^ (y30 ^^ false)) ^^ ((y30 ^^ false) ^^ false)) = y29 := by
  calc
    ((y29 ^^ (y30 ^^ false)) ^^ ((y30 ^^ false) ^^ false)) = (y29 ^^ (y30 ^^ (y30 ^^ false))) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y29 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse29 (a : Assignment) : overlap32_project (overlap32_lift a) 29 = a 29 := by
  exact overlap32_inverse29_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_inverse30_table (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : Bool) : ((y30 ^^ false) ^^ (false ^^ false)) = y30 := by
  calc
    ((y30 ^^ false) ^^ (false ^^ false)) = (y30 ^^ false) := by
      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl
    _ = y30 := by
      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]
theorem overlap32_inverse30 (a : Assignment) : overlap32_project (overlap32_lift a) 30 = a 30 := by
  exact overlap32_inverse30_table (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) (a 15) (a 16) (a 17) (a 18) (a 19) (a 20) (a 21) (a 22) (a 23) (a 24) (a 25) (a 26) (a 27) (a 28) (a 29) (a 30)

theorem overlap32_backward (a : Assignment) : evalCNF overlap32_original (overlap32_lift a) = evalCNF overlap32_quotient a := by
  rw [overlap32_forward]
  simp only [overlap32_quotient, overlap32_q0, overlap32_q1, overlap32_q2, overlap32_q3, overlap32_q4, overlap32_q5, overlap32_q6, overlap32_q7, overlap32_q8, overlap32_q9, overlap32_q10, overlap32_q11, overlap32_q12, overlap32_q13, overlap32_q14, overlap32_q15, overlap32_q16, overlap32_q17, overlap32_q18, overlap32_q19, overlap32_q20, overlap32_q21, overlap32_q22, overlap32_q23, overlap32_q24, overlap32_q25, overlap32_q26, overlap32_q27, overlap32_q28, overlap32_q29, overlap32_q30, evalCNF_append, evalCNF, evalClause, evalLit, overlap32_inverse0, overlap32_inverse1, overlap32_inverse2, overlap32_inverse3, overlap32_inverse4, overlap32_inverse5, overlap32_inverse6, overlap32_inverse7, overlap32_inverse8, overlap32_inverse9, overlap32_inverse10, overlap32_inverse11, overlap32_inverse12, overlap32_inverse13, overlap32_inverse14, overlap32_inverse15, overlap32_inverse16, overlap32_inverse17, overlap32_inverse18, overlap32_inverse19, overlap32_inverse20, overlap32_inverse21, overlap32_inverse22, overlap32_inverse23, overlap32_inverse24, overlap32_inverse25, overlap32_inverse26, overlap32_inverse27, overlap32_inverse28, overlap32_inverse29, overlap32_inverse30]
theorem overlap32_equisatisfiable : (∃ a, evalCNF overlap32_original a = true) ↔ (∃ b, evalCNF overlap32_quotient b = true) :=
  equisat_of_two_maps (evalCNF overlap32_original) (evalCNF overlap32_quotient) overlap32_project overlap32_lift overlap32_forward overlap32_backward
#print axioms overlap32_forward
#print axioms overlap32_backward
#print axioms overlap32_equisatisfiable

end CompressionInstances
end MergedCertificates.LargerCompressionInstances
