import AugmentationBfsBridge

namespace PEqualNP.Outside.MatchingLoop

open PEqualNP.Outside.GuardedHall
open PEqualNP.Outside.MatchingCertificates
open PEqualNP.Outside.MatchingAugmentation
open PEqualNP.Outside.MatchingSearch

variable {r h : Nat}

inductive Proposal (r h : Nat)
  | path (hole : Fin h) (reverseRows : List (Fin r))
  | cut (rows : Finset (Fin r))
  | inconclusive

inductive Result (r h : Nat)
  | success (certificate : SuccessCertificate r h)
  | failure (rows : Finset (Fin r))
  | inconclusive

def Result.Accepted (N : Fin r → Finset (Fin h)) (g : Fin r → Bool) :
    Result r h → Prop
  | .success c => successCheck N g c = true
  | .failure rows => failureCheck N g rows = true
  | .inconclusive => True

def Result.Correct (N : Fin r → Finset (Fin h)) (g : Fin r → Bool) :
    Result r h → Prop
  | .success _ => HasMatching N g
  | .failure _ => ¬ HasMatching N g
  | .inconclusive => True

theorem Result.accepted_correct {N : Fin r → Finset (Fin h)} {g : Fin r → Bool}
    {result : Result r h} (accepted : result.Accepted N g) : result.Correct N g := by
  cases result with
  | success certificate => exact accepted_success_has_matching N g certificate accepted
  | failure rows => exact accepted_failure_no_matching N g rows accepted
  | inconclusive => exact True.intro

/-- Replay the proposal only on active rows, and require that the requested
root is actually covered by the new partial matching. -/
def tryPath (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (s : State r h) (root : Fin r) (free : Fin h) (reverseRows : List (Fin r)) :
    Option (State r h) :=
  if reverseRows.all (fun i => !g i) then
    match augmentRows N reverseRows s free with
    | none => none
    | some next => if (next.rowMatch root).isSome then some next else none
  else none

theorem tryPath_sound {N : Fin r → Finset (Fin h)} {g : Fin r → Bool}
    {s next : State r h} {root : Fin r} {free : Fin h} {rows : List (Fin r)}
    (valid : Valid N s) (active : ActiveOnly g s)
    (replayed : tryPath N g s root free rows = some next) :
    Valid N next ∧ ActiveOnly g next ∧ matchedRows s ⊆ matchedRows next ∧
      root ∈ matchedRows next := by
  by_cases pathActive : rows.all (fun i => !g i) = true
  · cases replay : augmentRows N rows s free with
    | none => simp [tryPath, pathActive, replay] at replayed
    | some out =>
      by_cases covered : (out.rowMatch root).isSome = true
      · simp [tryPath, pathActive, replay, covered] at replayed
        subst next
        obtain ⟨outValid, coverage, _⟩ := augmentRows_sound N rows s free out valid replay
        have activeRows : ∀ i ∈ rows, g i = false := by
          intro i hi
          have fact := (List.all_eq_true.mp pathActive) i hi
          simpa using fact
        exact ⟨outValid, augmentRows_active_only N g rows s free out active activeRows replay,
          coverage, by simpa [matchedRows] using covered⟩
      · simp [tryPath, pathActive, replay, covered] at replayed
  · simp [tryPath, pathActive] at replayed

/-- Every active row outside the pending list is already covered. No order
or uniqueness premise is needed for the loop inductive invariant. -/
def CoversPast (g : Fin r → Bool) (todo : List (Fin r)) (s : State r h) : Prop :=
  ∀ i, g i = false → i ∉ todo → i ∈ matchedRows s

theorem covers_cons {g : Fin r → Bool} {root : Fin r} {todo : List (Fin r)}
    {s next : State r h} (old : CoversPast g (root :: todo) s)
    (preserved : matchedRows s ⊆ matchedRows next)
    (rootCovered : g root = false → root ∈ matchedRows next) :
    CoversPast g todo next := by
  intro i hi notTodo
  by_cases same : i = root
  · subst i
    exact rootCovered hi
  · exact preserved (old i hi (fun mem => (List.mem_cons.mp mem).elim same notTodo))

/-- The fold visits the supplied roots in order. A failed proposal, invalid
path, or rejected cut is represented by `inconclusive`. -/
def visit (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (propose : State r h → Fin r → Proposal r h) :
    List (Fin r) → State r h → Result r h
  | [], s => .success s.rowMatch
  | root :: todo, s =>
    if g root = false ∧ s.rowMatch root = none then
      match propose s root with
      | .path k rows =>
        match tryPath N g s root k rows with
        | some next => visit N g propose todo next
        | none => .inconclusive
      | .cut rows => if failureCheck N g rows then .failure rows else .inconclusive
      | .inconclusive => .inconclusive
    else
      visit N g propose todo s

/-- This is the exact additional obligation needed to rule out an
inconclusive run. The soundness proof applies even to an arbitrary proposer. -/
def ProposesProgress (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (propose : State r h → Fin r → Proposal r h) : Prop :=
  ∀ s root, Valid N s → ActiveOnly g s → g root = false → s.rowMatch root = none →
    match propose s root with
    | .path hole rows => (tryPath N g s root hole rows).isSome = true
    | .cut rows => failureCheck N g rows = true
    | .inconclusive => False

theorem visit_checked (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (propose : State r h → Fin r → Proposal r h) (todo : List (Fin r)) (s : State r h)
    (valid : Valid N s) (active : ActiveOnly g s) (past : CoversPast g todo s) :
    (visit N g propose todo s).Accepted N g ∧
      (ProposesProgress N g propose → visit N g propose todo s ≠ .inconclusive) := by
  induction todo generalizing s with
  | nil =>
    refine ⟨full_coverage_accepted N g s valid (fun i hi => past i hi (by simp)), ?_⟩
    simp [visit]
  | cons root todo ih =>
    by_cases need : g root = false ∧ s.rowMatch root = none
    · cases p : propose s root with
      | inconclusive =>
        refine ⟨by simp [visit, need, p, Result.Accepted], ?_⟩
        intro progress
        have impossible := progress s root valid active need.1 need.2
        simp [p] at impossible
      | cut rows =>
        by_cases accepted : failureCheck N g rows = true
        · simp [visit, need, p, accepted, Result.Accepted]
        · refine ⟨by simp [visit, need, p, accepted, Result.Accepted], ?_⟩
          intro progress
          have goodCut := progress s root valid active need.1 need.2
          exact (accepted (by simpa [p] using goodCut)).elim
      | path hole rows =>
        cases replay : tryPath N g s root hole rows with
        | none =>
          refine ⟨by simp [visit, need, p, replay, Result.Accepted], ?_⟩
          intro progress
          have goodPath := progress s root valid active need.1 need.2
          simp [p, replay] at goodPath
        | some next =>
          obtain ⟨nextValid, nextActive, retained, rootCovered⟩ :=
            tryPath_sound valid active replay
          have nextPast := covers_cons past retained (fun _ => rootCovered)
          simpa only [visit, ite_eq_left need, p, replay] using ih next nextValid nextActive nextPast
    · have covered : g root = false → root ∈ matchedRows s := by
        intro rootActive
        cases assigned : s.rowMatch root with
        | none => exact (need ⟨rootActive, assigned⟩).elim
        | some k => simp [matchedRows, assigned]
      have nextPast := covers_cons past (fun _ hi => hi) covered
      simpa only [visit, ite_eq_right need] using ih s valid active nextPast

def solveWith (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (propose : State r h → Fin r → Proposal r h) : Result r h :=
  visit N g propose (List.finRange r) empty

theorem solveWith_checked (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (propose : State r h → Fin r → Proposal r h) :
    (solveWith N g propose).Accepted N g ∧
      (ProposesProgress N g propose → solveWith N g propose ≠ .inconclusive) :=
  visit_checked N g propose _ empty (empty_valid N) (empty_active_only g)
    (fun i _ notListed => (notListed (List.mem_finRange i)).elim)

/-- Use the verified BFS cut when the queue drains. A free result delegates
path reconstruction through an explicit checked proposal boundary. -/
def proposeFromBfs (adj : Fin r → List (Fin h))
    (path : State r h → Fin r → Option (Fin h × List (Fin r)))
    (s : State r h) (root : Fin r) : Proposal r h :=
  match explore adj s.owner r (Frontier.start root) with
  | .exhausted final => .cut final.reached
  | .free _ =>
    match path s root with
    | some (hole, rows) => .path hole rows
    | none => .inconclusive
  | .budget => .inconclusive

def solveFromBfs (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (path : State r h → Fin r → Option (Fin h × List (Fin r))) : Result r h :=
  solveWith (fun i => (adj i).toFinset) g (proposeFromBfs adj path)

theorem solveFromBfs_checked (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (path : State r h → Fin r → Option (Fin h × List (Fin r))) :
    (solveFromBfs adj g path).Accepted (fun i => (adj i).toFinset) g :=
  (solveWith_checked _ g (proposeFromBfs adj path)).1

/-- Only the free-hole branch needs an additional premise to rule out
inconclusiveness: it must supply rows that replay and cover the root. -/
theorem solveFromBfs_no_inconclusive (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (path : State r h → Fin r → Option (Fin h × List (Fin r)))
    (freePath : ∀ s root hole,
      Valid (fun i => (adj i).toFinset) s → ActiveOnly g s →
      g root = false → s.rowMatch root = none →
      explore adj s.owner r (Frontier.start root) = .free hole →
      ∃ free rows, path s root = some (free, rows) ∧
        (tryPath (fun i => (adj i).toFinset) g s root free rows).isSome = true) :
    solveFromBfs adj g path ≠ .inconclusive := by
  apply (solveWith_checked _ g (proposeFromBfs adj path)).2
  intro s root valid active rootActive unmatched
  cases found : explore adj s.owner r (Frontier.start root) with
  | exhausted final =>
    simpa [proposeFromBfs, found] using
      (typed_bfs_failure adj g s valid active root rootActive unmatched final found).1
  | budget =>
    exact (typed_bfs_full_budget adj g s valid active root rootActive found).elim
  | free hole =>
    obtain ⟨free, rows, proposed, replay⟩ := freePath s root hole valid active rootActive unmatched found
    simpa [proposeFromBfs, found, proposed] using replay

#print axioms tryPath_sound
#print axioms visit_checked
#print axioms solveWith_checked
#print axioms solveFromBfs_checked
#print axioms solveFromBfs_no_inconclusive
#print axioms Result.accepted_correct

section Examples

private def describe : Result r h → String × List (Option Nat)
  | .success certificate =>
    ("success", (List.finRange r).map (fun i => (certificate i).map Fin.val))
  | .failure cut =>
    ("failure", ((List.finRange r).filter (fun i => i ∈ cut)).map (fun i => some i.val))
  | .inconclusive => ("inconclusive", [])

private def twoRows (row : Fin 2) : List (Fin 2) :=
  if row = 0 then [0, 1] else [0]

private def suppliedPath (_ : State 2 2) (root : Fin 2) :
    Option (Fin 2 × List (Fin 2)) :=
  if root = 0 then some (0, [0]) else some (1, [0, 1])

private def fourRows (row : Fin 4) : List (Fin 4) :=
  if row = 0 then [0, 1] else if row = 1 then [0] else if row = 2 then [1] else [2, 3]

private def suppliedCutPrefix (_ : State 4 4) (root : Fin 4) :
    Option (Fin 4 × List (Fin 4)) :=
  if root = 0 then some (0, [0]) else if root = 1 then some (1, [0, 1]) else none

-- The second root needs a fresh search and a reversal of the first assignment.
example : describe (solveFromBfs twoRows (fun _ => false) suppliedPath) =
    ("success", [some 1, some 0]) := by decide

-- The actual BFS, rather than the supplied path callback, returns the cut.
example : describe (solveFromBfs fourRows (fun _ => false) suppliedCutPrefix) =
    ("failure", [some 0, some 1, some 2]) := by decide

-- An omitted or wrong-root path is inconclusive even when another row can move.
example : describe (solveFromBfs twoRows (fun _ => false) (fun _ _ => none)) =
    ("inconclusive", []) := by decide

example : describe (solveFromBfs twoRows (fun _ => false) (fun _ _ => some (0, [1]))) =
    ("inconclusive", []) := by decide

-- A bogus empty cut cannot yield a failure certificate.
example : describe (solveWith (fun i => (twoRows i).toFinset) (fun _ => false)
    (fun _ _ => .cut ∅)) = ("inconclusive", []) := by decide

example : describe (solveFromBfs (fun (_ : Fin 1) => ([] : List (Fin 0)))
    (fun _ => true) (fun _ _ => none)) = ("success", [none]) := by decide

example : describe (solveFromBfs (fun (_ : Fin 1) => ([] : List (Fin 0)))
    (fun _ => false) (fun _ _ => none)) = ("failure", [some 0]) := by decide

#eval describe (solveFromBfs twoRows (fun _ => false) suppliedPath)
#eval describe (solveFromBfs fourRows (fun _ => false) suppliedCutPrefix)
#eval describe (solveFromBfs twoRows (fun _ => false) (fun _ _ => none))
#eval describe (solveFromBfs twoRows (fun _ => false) (fun _ _ => some (0, [1])))
#eval describe (solveWith (fun i => (twoRows i).toFinset) (fun _ => false) (fun _ _ => .cut ∅))
#eval describe (solveFromBfs (fun (_ : Fin 1) => ([] : List (Fin 0)))
  (fun _ => true) (fun _ _ => none))
#eval describe (solveFromBfs (fun (_ : Fin 1) => ([] : List (Fin 0)))
  (fun _ => false) (fun _ _ => none))

end Examples

end PEqualNP.Outside.MatchingLoop
