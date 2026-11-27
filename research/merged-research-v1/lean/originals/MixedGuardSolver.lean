import MixedGuardBranches

namespace PEqualNP.Outside.ConstructorBoundary

open PEqualNP.Search
open PEqualNP.Outside.DualHorn
open PEqualNP.Outside.SparseDualHornAlgorithm

variable {r h : Nat}

def mixedInputCheck (offset : Nat) (F : CNF) (g : Fin r → Clause) : Bool :=
  F.all (fun C => C.all (fun l => decide (l.1 < offset))) &&
    (List.finRange r).all (fun i => (g i).all (fun l => decide (l.1 < offset))) &&
    dualHornCheck F

theorem mixedInputCheck_iff (offset : Nat) (F : CNF) (g : Fin r → Clause) :
    mixedInputCheck offset F g = true ↔
      VariablesBelow F offset ∧ (∀ i, ∀ l ∈ g i, l.1 < offset) ∧ IsDualHorn F := by
  simp [mixedInputCheck, VariablesBelow, List.all_eq_true, dualHornCheck_iff, and_assoc]

def branchSolve (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) (a : Assignment) : AutomaticConstructor.Outcome :=
  AutomaticConstructor.solve (offset+1) (branchRetained F (negativeVars g) offset a)
    adj (fun i => lowerGuard offset a (g i))

def branchFormula (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) (a : Assignment) : CNF :=
  AutomaticConstructor.encoded (offset+1) (branchRetained F (negativeVars g) offset a)
    adj (fun i => lowerGuard offset a (g i))

theorem branchSolve_sat_iff (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) (a : Assignment) (below : VariablesBelow F offset)
    (guardBounds : ∀ i, ∀ l ∈ g i, l.1 < offset) (dual : IsDualHorn F) :
    (∃ w, branchSolve offset F adj g a = .sat w) ↔
      Satisfiable (branchFormula offset F adj g a) := by
  have supported := branch_checks offset F g a below guardBounds dual
  constructor
  · rintro ⟨w, returned⟩
    exact ⟨w, AutomaticConstructor.returned_sat_is_model _ _ _ _ _ returned⟩
  · intro sat
    have decisive : AutomaticConstructor.Decisive (branchSolve offset F adj g a) :=
      AutomaticConstructor.supported_solve_decisive _ _ _ _ supported.1 supported.2
    rcases decisive with unsat | accepted
    · exact ((AutomaticConstructor.returned_unsat_excludes_models _ _ _ _ unsat) sat).elim
    · exact accepted

private def isSat : AutomaticConstructor.Outcome → Bool
  | .sat _ => true
  | _ => false

private theorem isSat_iff (result : AutomaticConstructor.Outcome) :
    isSat result = true ↔ ∃ w, result = .sat w := by
  cases result <;> simp [isSat]

private def anySatBranch (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) : Bool :=
  (enumerateBits (negativeVars g)).any fun a => isSat (branchSolve offset F adj g a)

/-- Branch only after the retained syntax and visible identifier bounds
pass. Each enumerated branch then has a supported, decisive solver call. -/
def solveMixed (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) : Option Bool :=
  if mixedInputCheck offset F g then some (anySatBranch offset F adj g) else none

theorem solveMixed_sat (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) (checks : mixedInputCheck offset F g = true) :
    solveMixed offset F adj g = some true ↔
      Satisfiable (AutomaticConstructor.encoded offset F adj g) := by
  obtain ⟨below, guardBounds, dual⟩ := (mixedInputCheck_iff offset F g).mp checks
  have reduction : Satisfiable (AutomaticConstructor.encoded offset F adj g) ↔
      ∃ a ∈ enumerateBits (negativeVars g), Satisfiable (branchFormula offset F adj g a) :=
    mixed_sat_iff_branches offset F (fun i => (adj i).toFinset) g below guardBounds
  rw [reduction]
  simp only [solveMixed, checks, ↓reduceIte, Option.some.injEq, anySatBranch,
    List.any_eq_true, isSat_iff]
  constructor
  · rintro ⟨a, listed, sat⟩
    exact ⟨a, listed, (branchSolve_sat_iff offset F adj g a below guardBounds dual).mp sat⟩
  · rintro ⟨a, listed, sat⟩
    exact ⟨a, listed, (branchSolve_sat_iff offset F adj g a below guardBounds dual).mpr sat⟩

theorem solveMixed_unsat (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) (checks : mixedInputCheck offset F g = true) :
    solveMixed offset F adj g = some false ↔
      ¬ Satisfiable (AutomaticConstructor.encoded offset F adj g) := by
  have exactSat := solveMixed_sat offset F adj g checks
  cases value : anySatBranch offset F adj g <;> simp [solveMixed, checks, value] at exactSat ⊢
  all_goals tauto

theorem solveMixed_rejects (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) (bad : mixedInputCheck offset F g = false) :
    solveMixed offset F adj g = none := by
  simp [solveMixed, bad]

private theorem eraseDups_nodup (xs : List Nat) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons x xs =>
    rw [List.eraseDups_cons]
    refine List.nodup_cons.mpr ⟨?_, eraseDups_nodup _⟩
    intro member
    have filtered := List.mem_eraseDups.mp member
    have different := (List.mem_filter.mp filtered).2
    simp at different
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem negativeVars_nodup (g : Fin r → Clause) : (negativeVars g).Nodup :=
  eraseDups_nodup _

/-- Count branch solver invocations only, excluding preprocessing and the
operations inside each call. This uses the same short-circuit rule as List.any. -/
private def anyCounted (test : α → Bool) : List α → Bool × Nat
  | [] => (false, 0)
  | a :: rest =>
    if test a then (true, 1)
    else
      let after := anyCounted test rest
      (after.1, after.2 + 1)

private theorem anyCounted_erases (test : α → Bool) (items : List α) :
    (anyCounted test items).1 = items.any test := by
  induction items with
  | nil => rfl
  | cons a rest ih =>
    cases tested : test a <;> simp [anyCounted, tested, ih]

private theorem anyCounted_calls (test : α → Bool) (items : List α) :
    (anyCounted test items).2 ≤ items.length := by
  induction items with
  | nil => simp [anyCounted]
  | cons a rest ih =>
    cases tested : test a with
    | false => simpa [anyCounted, tested] using Nat.add_le_add_right ih 1
    | true => simp [anyCounted, tested]

def solveMixedCounted (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) : Option (Bool × Nat) :=
  if mixedInputCheck offset F g then
    some (anyCounted (fun a => isSat (branchSolve offset F adj g a))
      (enumerateBits (negativeVars g)))
  else none

theorem solveMixedCounted_erases (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) :
    (solveMixedCounted offset F adj g).map Prod.fst = solveMixed offset F adj g := by
  cases checked : mixedInputCheck offset F g <;>
    simp [solveMixedCounted, solveMixed, checked, anySatBranch, anyCounted_erases]

theorem solveMixedCounted_calls (offset : Nat) (F : CNF) (adj : Fin r → List (Fin h))
    (g : Fin r → Clause) (verdict : Bool) (calls : Nat)
    (returned : solveMixedCounted offset F adj g = some (verdict, calls)) :
    calls ≤ 2 ^ (negativeVars g).length := by
  cases checked : mixedInputCheck offset F g with
  | false => simp [solveMixedCounted, checked] at returned
  | true =>
    have actual := congrArg Prod.snd (Option.some.inj (by
      simpa [solveMixedCounted, checked] using returned))
    change _ = calls at actual
    rw [← actual, ← enumerateBits_length]
    exact anyCounted_calls _ _

private def noHoles (_ : Fin 1) : List (Fin 0) := []
private def sharedHole (_ : Fin 2) : List (Fin 1) := [0]
private def mixedGuards (i : Fin 2) : Clause := if i = 0 then [(0,false),(1,true)] else []

private def fixtures : List (Option Bool) :=
  [solveMixed 2 [] noHoles (fun _ => [(0,false)]),
   solveMixed 2 [[(0,true)]] noHoles (fun _ => [(0,false)]),
   solveMixed 2 [[(1,false)]] sharedHole mixedGuards,
   solveMixed 2 [[(0,true)],[(1,false)]] sharedHole mixedGuards,
   solveMixed 2 [] noHoles (fun _ => [(1,true)]),
   solveMixed 2 [] noHoles (fun _ => [(2,false)]),
   solveMixed 2 [[(0,false),(1,false)]] noHoles (fun _ => [(0,false)])]

#eval fixtures
#guard fixtures == [some true, some false, some true, some false, some true, none, none]
#guard (enumerateBits (negativeVars (fun (_ : Fin 1) => [(0,false),(1,false),(0,false)]))).length == 4
private def exhaustedBranches : Option (Bool × Nat) :=
  solveMixedCounted 2 [[(0,true)],[(1,true)]] noHoles
    (fun _ => [(0,false),(1,false),(0,false)])

#eval exhaustedBranches
#guard exhaustedBranches == some (false, 4)

#print axioms mixedInputCheck_iff
#print axioms branchSolve_sat_iff
#print axioms solveMixed_sat
#print axioms solveMixed_unsat
#print axioms negativeVars_nodup
#print axioms solveMixedCounted_erases
#print axioms solveMixedCounted_calls

end PEqualNP.Outside.ConstructorBoundary
