import Std.Tactic

-- BEGIN_SHARED_PREAMBLE
namespace CompressionSoundness

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

end CompressionSoundness
-- END_SHARED_PREAMBLE

namespace LTCSoundness
open CompressionSoundness

def negLit (l : Lit) : Lit := (!l.1, l.2)

def clauseHasVar (v : Nat) (c : Clause) : Bool :=
  c.any (fun l => l.2 == v)

def cnfNoVar (v : Nat) (f : CNF) : Bool :=
  f.all (fun c => !clauseHasVar v c)

def sameClause (c d : Clause) : Bool :=
  c.all (fun l => d.any (fun l' => l == l')) &&
    d.all (fun l' => c.any (fun l => l' == l))

def cnfEquiv (A B : CNF) : Bool :=
  A.all (fun c => B.any (fun d => sameClause c d)) &&
    B.all (fun d => A.any (fun c => sameClause c d))

def ltcProject (l1 l2 : Lit) (a : Assignment) : Assignment :=
  fun u => if u == l1.2 then (evalLit l1 a || evalLit l2 a) else a u

def ltcLift (l1 l2 : Lit) (b : Assignment) : Assignment :=
  fun u =>
    if u == l1.2 then (if l1.1 then b l1.2 else !(b l1.2))
    else if u == l2.2 then (!l2.1)
    else b u

def ltcSrc (l1 l2 : Lit) (co neg rest : CNF) : CNF :=
  co.map (fun r => l1 :: l2 :: r) ++
    neg.map (fun s => negLit l1 :: s) ++
    neg.map (fun s => negLit l2 :: s) ++
    rest

def ltcDst (v1 : Nat) (co neg rest : CNF) : CNF :=
  co.map (fun r => (true, v1) :: r) ++
    neg.map (fun s => (false, v1) :: s) ++
    rest

def checkLTCStep (l1 l2 : Lit) (co neg rest F G : CNF) : Bool :=
  (l1.2 != l2.2) &&
    cnfNoVar l1.2 co && cnfNoVar l2.2 co &&
    cnfNoVar l1.2 neg && cnfNoVar l2.2 neg &&
    cnfNoVar l1.2 rest && cnfNoVar l2.2 rest &&
    cnfEquiv F (ltcSrc l1 l2 co neg rest) &&
    cnfEquiv (ltcDst l1.2 co neg rest) G

theorem evalLit_negLit (l : Lit) (a : Assignment) :
    evalLit (negLit l) a = !(evalLit l a) := by
  cases l with
  | mk b v => cases b <;> simp [negLit, evalLit]

theorem evalClause_eq_true_iff (c : Clause) (a : Assignment) :
    evalClause c a = true ↔ ∃ l ∈ c, evalLit l a = true := by
  induction c with
  | nil => simp [evalClause]
  | cons l ls ih =>
    simp [evalClause, Bool.or_eq_true, ih]

theorem evalCNF_eq_true_iff (F : CNF) (a : Assignment) :
    evalCNF F a = true ↔ ∀ c ∈ F, evalClause c a = true := by
  induction F with
  | nil => simp [evalCNF]
  | cons c cs ih =>
    simp [evalCNF, Bool.and_eq_true, ih]

theorem evalClause_of_sameClause {c d : Clause} {a : Assignment}
    (h : sameClause c d = true) :
    evalClause c a = evalClause d a := by
  have pair := Bool.and_eq_true_iff.mp h
  rw [Bool.eq_iff_iff, evalClause_eq_true_iff, evalClause_eq_true_iff]
  constructor
  · rintro ⟨l, hl, hval⟩
    have hany := (List.all_eq_true.mp pair.1) l hl
    rcases List.any_eq_true.mp hany with ⟨l', hl', heq⟩
    have hll' : l = l' := of_decide_eq_true heq
    exact ⟨l', hl', hll' ▸ hval⟩
  · rintro ⟨l', hl', hval⟩
    have hany := (List.all_eq_true.mp pair.2) l' hl'
    rcases List.any_eq_true.mp hany with ⟨l, hl, heq⟩
    have hl'l : l' = l := of_decide_eq_true heq
    exact ⟨l, hl, hl'l ▸ hval⟩

theorem evalCNF_of_cnfEquiv {A B : CNF} {a : Assignment}
    (h : cnfEquiv A B = true) :
    evalCNF A a = evalCNF B a := by
  have pair := Bool.and_eq_true_iff.mp h
  rw [Bool.eq_iff_iff, evalCNF_eq_true_iff, evalCNF_eq_true_iff]
  constructor
  · intro hA d hd
    have hany := (List.all_eq_true.mp pair.2) d hd
    rcases List.any_eq_true.mp hany with ⟨c, hc, hsc⟩
    rw [← evalClause_of_sameClause hsc]
    exact hA c hc
  · intro hB c hc
    have hany := (List.all_eq_true.mp pair.1) c hc
    rcases List.any_eq_true.mp hany with ⟨d, hd, hsc⟩
    rw [evalClause_of_sameClause hsc]
    exact hB d hd

theorem evalClause_agrees {c : Clause} {a b : Assignment}
    (h : ∀ l ∈ c, a l.2 = b l.2) :
    evalClause c a = evalClause c b := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    simp only [evalClause]
    have hl : a l.2 = b l.2 := h l (by simp)
    have hls : evalClause ls a = evalClause ls b := ih (fun x hx => h x (by simp [hx]))
    simp [evalLit, hl, hls]

theorem evalClause_noVar_eq {v : Nat} {c : Clause} {a b : Assignment}
    (hno : clauseHasVar v c = false)
    (hag : ∀ u, u ≠ v → a u = b u) :
    evalClause c a = evalClause c b := by
  apply evalClause_agrees
  intro l hl
  apply hag
  intro heq
  have : clauseHasVar v c = true := List.any_eq_true.mpr ⟨l, hl, by simp [heq]⟩
  rw [hno] at this
  contradiction

theorem evalCNF_noVar_eq {v : Nat} {f : CNF} {a b : Assignment}
    (hno : cnfNoVar v f = true)
    (hag : ∀ u, u ≠ v → a u = b u) :
    evalCNF f a = evalCNF f b := by
  induction f with
  | nil => rfl
  | cons c cs ih =>
    have hc : clauseHasVar v c = false := by
      have := (List.all_eq_true.mp hno) c (by simp)
      simpa using this
    have hcs : cnfNoVar v cs = true := by
      apply List.all_eq_true.mpr
      intro x hx
      exact (List.all_eq_true.mp hno) x (by simp [hx])
    simp [evalCNF, evalClause_noVar_eq hc hag, ih hcs]

theorem evalCNF_ltcProject_co (l1 l2 : Lit) (co : CNF) (a : Assignment)
    (hno : cnfNoVar l1.2 co = true) :
    evalCNF (co.map (fun r => l1 :: l2 :: r)) a =
      evalCNF (co.map (fun r => (true, l1.2) :: r)) (ltcProject l1 l2 a) := by
  induction co with
  | nil => rfl
  | cons r rs ih =>
    have hr : clauseHasVar l1.2 r = false := by
      simpa using (List.all_eq_true.mp hno) r (by simp)
    have hrs : cnfNoVar l1.2 rs = true := by
      apply List.all_eq_true.mpr
      intro x hx
      exact (List.all_eq_true.mp hno) x (by simp [hx])
    have heqR : evalClause r a = evalClause r (ltcProject l1 l2 a) := by
      apply evalClause_noVar_eq hr
      intro u hu
      simp [ltcProject, hu]
    have hproj : evalLit (true, l1.2) (ltcProject l1 l2 a) = (evalLit l1 a || evalLit l2 a) := by
      simp [evalLit, ltcProject]
    simp [List.map, evalCNF, evalClause, heqR, hproj, Bool.or_assoc, ih hrs]

theorem evalCNF_ltcProject_neg (l1 l2 : Lit) (neg : CNF) (a : Assignment)
    (hno : cnfNoVar l1.2 neg = true) :
    (evalCNF (neg.map (fun s => negLit l1 :: s)) a &&
      evalCNF (neg.map (fun s => negLit l2 :: s)) a) =
      evalCNF (neg.map (fun s => (false, l1.2) :: s)) (ltcProject l1 l2 a) := by
  induction neg with
  | nil => rfl
  | cons s ss ih =>
    have hs : clauseHasVar l1.2 s = false := by
      simpa using (List.all_eq_true.mp hno) s (by simp)
    have hss : cnfNoVar l1.2 ss = true := by
      apply List.all_eq_true.mpr
      intro x hx
      exact (List.all_eq_true.mp hno) x (by simp [hx])
    have heqS : evalClause s a = evalClause s (ltcProject l1 l2 a) := by
      apply evalClause_noVar_eq hs
      intro u hu
      simp [ltcProject, hu]
    have hproj : evalLit (false, l1.2) (ltcProject l1 l2 a) = !(evalLit l1 a || evalLit l2 a) := by
      simp [evalLit, ltcProject]
    simp only [List.map, evalCNF, evalClause, evalLit_negLit, hproj, ← heqS]
    rw [← ih hss]
    cases evalLit l1 a <;> cases evalLit l2 a <;> cases evalClause s a <;>
      cases evalCNF (ss.map (fun s => negLit l1 :: s)) a <;>
      cases evalCNF (ss.map (fun s => negLit l2 :: s)) a <;> rfl

theorem evalCNF_ltcSrc_eq_dst (l1 l2 : Lit) (co neg rest : CNF) (a : Assignment)
    (hco : cnfNoVar l1.2 co = true)
    (hneg : cnfNoVar l1.2 neg = true)
    (hrest : cnfNoVar l1.2 rest = true) :
    evalCNF (ltcSrc l1 l2 co neg rest) a =
      evalCNF (ltcDst l1.2 co neg rest) (ltcProject l1 l2 a) := by
  simp only [ltcSrc, ltcDst, evalCNF_append]
  rw [evalCNF_ltcProject_co l1 l2 co a hco]
  have hnegEq := evalCNF_ltcProject_neg l1 l2 neg a hneg
  have hrestEq : evalCNF rest a = evalCNF rest (ltcProject l1 l2 a) := by
    apply evalCNF_noVar_eq hrest
    intro u hu
    simp [ltcProject, hu]
  rw [← hrestEq, ← hnegEq]
  simp [Bool.and_assoc]

theorem ltcProject_ltcLift_agrees (l1 l2 : Lit) (b : Assignment)
    (hne : (l1.2 != l2.2) = true) :
    ∀ u, u ≠ l2.2 → ltcProject l1 l2 (ltcLift l1 l2 b) u = b u := by
  have hne' : l1.2 ≠ l2.2 := bne_iff_ne.mp hne
  intro u hu
  by_cases h1 : u = l1.2
  · subst h1
    have h12 : (l2.2 == l1.2) = false := beq_false_of_ne (Ne.symm hne')
    have hl1 : evalLit l1 (ltcLift l1 l2 b) = b l1.2 := by
      cases l1 with
      | mk s v =>
        cases s <;> simp [evalLit, ltcLift]
    have hl2 : evalLit l2 (ltcLift l1 l2 b) = false := by
      cases l2 with
      | mk s v =>
        cases s <;> simp [evalLit, ltcLift, h12]
    simp [ltcProject, hl1, hl2]
  · simp [ltcProject, ltcLift, h1, hu]

theorem cnfNoVar_ltcDst (v1 v2 : Nat) (co neg rest : CNF)
    (hne : (v1 != v2) = true)
    (hco : cnfNoVar v2 co = true)
    (hneg : cnfNoVar v2 neg = true)
    (hrest : cnfNoVar v2 rest = true) :
    cnfNoVar v2 (ltcDst v1 co neg rest) = true := by
  have hne' : v1 ≠ v2 := bne_iff_ne.mp hne
  have h12 : (v1 == v2) = false := beq_false_of_ne hne'
  simp only [ltcDst, cnfNoVar, List.all_append, Bool.and_eq_true, List.all_map]
  refine ⟨⟨?_, ?_⟩, hrest⟩
  · apply List.all_eq_true.mpr
    intro r hr
    have hvr := (List.all_eq_true.mp hco) r hr
    simp [Function.comp, clauseHasVar, h12]
    simpa [clauseHasVar] using hvr
  · apply List.all_eq_true.mpr
    intro s hs
    have hvs := (List.all_eq_true.mp hneg) s hs
    simp [Function.comp, clauseHasVar, h12]
    simpa [clauseHasVar] using hvs

theorem checkLTCStep_sound (l1 l2 : Lit) (co neg rest F G : CNF)
    (h : checkLTCStep l1 l2 co neg rest F G = true) :
    (∃ a, evalCNF F a = true) ↔ (∃ b, evalCNF G b = true) := by
  simp only [checkLTCStep, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hne, hco1⟩, hco2⟩, hneg1⟩, hneg2⟩, hrest1⟩, hrest2⟩, hFG1⟩, hFG2⟩
  apply equisat_of_two_maps (evalCNF F) (evalCNF G) (ltcProject l1 l2) (ltcLift l1 l2)
  · intro a
    rw [evalCNF_of_cnfEquiv hFG1, evalCNF_ltcSrc_eq_dst l1 l2 co neg rest a hco1 hneg1 hrest1,
      evalCNF_of_cnfEquiv hFG2]
  · intro b
    rw [evalCNF_of_cnfEquiv hFG1, evalCNF_ltcSrc_eq_dst l1 l2 co neg rest _ hco1 hneg1 hrest1]
    have hnoDst := cnfNoVar_ltcDst l1.2 l2.2 co neg rest hne hco2 hneg2 hrest2
    rw [evalCNF_noVar_eq hnoDst (ltcProject_ltcLift_agrees l1 l2 b hne)]
    exact evalCNF_of_cnfEquiv hFG2

#print axioms checkLTCStep_sound

end LTCSoundness
