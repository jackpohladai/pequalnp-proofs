import ExhaustedSearchCut
import Mathlib.Data.List.Nodup

namespace PEqualNP.Outside.MatchingSearch
open PEqualNP.Outside.GuardedHall PEqualNP.Outside.MatchingCertificates

variable {r h : Nat}

/-- Seen holes are the domain of the parent-hole table. Only this domain is
needed on a failed search, so this state omits the parent values. -/
structure Frontier (r h : Nat) where
  reached : Finset (Fin r)
  seen : Finset (Fin h)
  queue : List (Fin r)

def Frontier.start (root : Fin r) : Frontier r h :=
  ⟨{root}, ∅, [root]⟩

def scanHole (owner : Fin h → Option (Fin r)) (s : Frontier r h) (k : Fin h) :
    Except (Fin h) (Frontier r h) :=
  if k ∈ s.seen then .ok s
  else
    match owner k with
    | none => .error k
    | some i =>
      if i ∈ s.reached then .ok {s with seen := insert k s.seen}
      else .ok ⟨insert i s.reached, insert k s.seen, s.queue ++ [i]⟩

def scanHoles (owner : Fin h → Option (Fin r)) (s : Frontier r h) :
    List (Fin h) → Except (Fin h) (Frontier r h)
  | [] => .ok s
  | k :: ks =>
    match scanHole owner s k with
    | .error free => .error free
    | .ok next => scanHoles owner next ks

structure FrontierGood (g : Fin r → Bool) (owner : Fin h → Option (Fin r))
    (s : Frontier r h) : Prop where
  active : ∀ i ∈ s.reached, g i = false
  owned : ∀ k ∈ s.seen, ∃ i ∈ s.reached, owner k = some i
  queued : ∀ i ∈ s.queue, i ∈ s.reached
  distinct : s.queue.Nodup

structure ScanProgress (s t : Frontier r h) : Prop where
  reached : s.reached ⊆ t.reached
  seen : s.seen ⊆ t.seen
  queue : ∀ i ∈ s.queue, i ∈ t.queue
  newRows : ∀ i ∈ t.reached, i ∉ s.reached → i ∈ t.queue
  oldRows : ∀ i ∈ s.reached, i ∈ t.queue → i ∈ s.queue

theorem ScanProgress.refl (s : Frontier r h) : ScanProgress s s :=
  ⟨fun _ hi => hi, fun _ hk => hk, fun _ hi => hi,
    fun _ hi hn => (hn hi).elim, fun _ _ hi => hi⟩

theorem ScanProgress.trans {s t u : Frontier r h} (st : ScanProgress s t)
    (tu : ScanProgress t u) : ScanProgress s u := by
  refine ⟨st.reached.trans tu.reached, st.seen.trans tu.seen,
    fun i hi => tu.queue i (st.queue i hi), ?_,
    fun i hi hq => st.oldRows i hi (tu.oldRows i (st.reached hi) hq)⟩
  intro i hu hs
  by_cases ht : i ∈ t.reached
  · exact tu.queue i (st.newRows i ht hs)
  · exact tu.newRows i hu ht

/-- A completed hole visit either leaves the frontier alone or records a
matched owner. Discoveries are appended only for previously unreached rows. -/
theorem scanHole_ok {g : Fin r → Bool} {owner : Fin h → Option (Fin r)}
    (ownerActive : ∀ k i, owner k = some i → g i = false)
    {s t : Frontier r h} {k : Fin h} (good : FrontierGood g owner s)
    (step : scanHole owner s k = .ok t) :
    FrontierGood g owner t ∧ ScanProgress s t ∧ k ∈ t.seen := by
  by_cases seen : k ∈ s.seen
  · simp [scanHole, seen] at step
    subst t
    exact ⟨good, ScanProgress.refl _, seen⟩
  cases own : owner k with
  | none => simp [scanHole, seen, own] at step
  | some i =>
    by_cases known : i ∈ s.reached
    · simp [scanHole, seen, own, known] at step
      subst t
      refine ⟨⟨good.active, ?_, good.queued, good.distinct⟩,
        ⟨fun _ hj => hj, Finset.subset_insert _ _, fun _ hj => hj,
          fun _ hj hn => (hn hj).elim, fun _ _ hj => hj⟩, Finset.mem_insert_self _ _⟩
      intro l hl
      rcases Finset.mem_insert.mp hl with rfl | old
      · exact ⟨i, known, own⟩
      · exact good.owned l old
    · simp [scanHole, seen, own, known] at step
      subst t
      have notQueued : i ∉ s.queue := fun hi => known (good.queued i hi)
      have distinct : (s.queue ++ [i]).Nodup := by
        simpa only [List.concat_eq_append] using (List.nodup_concat _ _).mpr
          ⟨notQueued, good.distinct⟩
      refine ⟨⟨?_, ?_, ?_, distinct⟩,
        ⟨Finset.subset_insert _ _, Finset.subset_insert _ _, ?_, ?_, ?_⟩,
        Finset.mem_insert_self _ _⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | old
        · exact ownerActive k j own
        · exact good.active j old
      · intro l hl
        rcases Finset.mem_insert.mp hl with rfl | old
        · exact ⟨i, Finset.mem_insert_self _ _, own⟩
        · obtain ⟨j, hj, owned⟩ := good.owned l old
          exact ⟨j, Finset.mem_insert_of_mem hj, owned⟩
      · intro j hj
        simp only [List.mem_append, List.mem_singleton] at hj
        rcases hj with old | rfl
        · exact Finset.mem_insert_of_mem (good.queued j old)
        · exact Finset.mem_insert_self _ _
      · intro j hj
        simp only [List.mem_append, List.mem_singleton]
        exact Or.inl hj
      · intro j hj old
        simp only [List.mem_append, List.mem_singleton]
        exact Or.inr ((Finset.mem_insert.mp hj).resolve_right old)
      · intro j hj queued
        simp only [List.mem_append, List.mem_singleton] at queued
        exact queued.resolve_right (fun same => known (same ▸ hj))

theorem scanHoles_ok {g : Fin r → Bool} {owner : Fin h → Option (Fin r)}
    (ownerActive : ∀ k i, owner k = some i → g i = false)
    (ks : List (Fin h)) {s t : Frontier r h} (good : FrontierGood g owner s)
    (step : scanHoles owner s ks = .ok t) :
    FrontierGood g owner t ∧ ScanProgress s t ∧ ∀ k ∈ ks, k ∈ t.seen := by
  induction ks generalizing s with
  | nil =>
    simp [scanHoles] at step
    subst t
    exact ⟨good, ScanProgress.refl _, by simp⟩
  | cons k ks ih =>
    cases hstep : scanHole owner s k with
    | error free => simp [scanHoles, hstep] at step
    | ok next =>
      obtain ⟨goodNext, st, seen⟩ := scanHole_ok ownerActive good hstep
      obtain ⟨goodEnd, tu, seenTail⟩ := ih goodNext (by simpa [scanHoles, hstep] using step)
      refine ⟨goodEnd, st.trans tu, ?_⟩
      intro l hl
      rcases List.mem_cons.mp hl with rfl | tail
      · exact tu.seen seen
      · exact seenTail l tail

theorem scanHole_error {owner : Fin h → Option (Fin r)} {s : Frontier r h}
    {k free : Fin h} (out : scanHole owner s k = .error free) :
    k = free ∧ owner free = none := by
  by_cases seen : k ∈ s.seen
  · simp [scanHole, seen] at out
  cases own : owner k with
  | none =>
    simp [scanHole, seen, own] at out
    subst free
    exact ⟨rfl, own⟩
  | some i =>
    by_cases known : i ∈ s.reached <;> simp [scanHole, seen, own, known] at out

theorem scanHoles_error {owner : Fin h → Option (Fin r)} (ks : List (Fin h))
    {s : Frontier r h} {free : Fin h} (out : scanHoles owner s ks = .error free) :
    free ∈ ks ∧ owner free = none := by
  induction ks generalizing s with
  | nil => simp [scanHoles] at out
  | cons k ks ih =>
    cases step : scanHole owner s k with
    | error hole =>
      simp [scanHoles, step] at out
      subst hole
      obtain ⟨same, unowned⟩ := scanHole_error step
      exact ⟨List.mem_cons.mpr (Or.inl same.symm), unowned⟩
    | ok next =>
      obtain ⟨member, unowned⟩ := ih (by simpa [scanHoles, step] using out)
      exact ⟨List.mem_cons_of_mem _ member, unowned⟩

structure SearchGood (adj : Fin r → List (Fin h)) (g : Fin r → Bool)
    (owner : Fin h → Option (Fin r)) (root : Fin r) (s : Frontier r h) : Prop where
  frontier : FrontierGood g owner s
  rootMem : root ∈ s.reached
  processed : ∀ i ∈ s.reached, i ∉ s.queue → ∀ k ∈ adj i, k ∈ s.seen

theorem start_good (adj : Fin r → List (Fin h)) {g : Fin r → Bool}
    (owner : Fin h → Option (Fin r)) {root : Fin r} (active : g root = false) :
    SearchGood adj g owner root (Frontier.start (h := h) root) := by
  refine ⟨⟨?_, by simp [Frontier.start], by simp [Frontier.start],
    by simp [Frontier.start]⟩, by simp [Frontier.start], ?_⟩
  · simpa [Frontier.start] using active
  · simp [Frontier.start]

theorem pop_good {g : Fin r → Bool} {owner : Fin h → Option (Fin r)}
    {s : Frontier r h} {row : Fin r} {todo : List (Fin r)}
    (good : FrontierGood g owner s) (pop : s.queue = row :: todo) :
    FrontierGood g owner {s with queue := todo} := by
  refine ⟨good.active, good.owned, ?_, ?_⟩
  · intro i hi
    exact good.queued i (pop ▸ List.mem_cons_of_mem _ hi)
  · exact (List.nodup_cons.mp (pop ▸ good.distinct)).2

/-- One queue pop followed by a full adjacency scan is the outer BFS step.
If it succeeds, every reached row outside the queue has been covered. -/
theorem expand_good {adj : Fin r → List (Fin h)} {g : Fin r → Bool}
    {owner : Fin h → Option (Fin r)} {root row : Fin r} {todo : List (Fin r)}
    {s t : Frontier r h} (ownerActive : ∀ k i, owner k = some i → g i = false)
    (good : SearchGood adj g owner root s) (pop : s.queue = row :: todo)
    (scanned : scanHoles owner {s with queue := todo} (adj row) = .ok t) :
    SearchGood adj g owner root t := by
  have popped := pop_good good.frontier pop
  obtain ⟨frontier, progress, rowCovered⟩ := scanHoles_ok ownerActive (adj row) popped scanned
  refine ⟨frontier, progress.reached good.rootMem, ?_⟩
  intro i hi noQueue
  by_cases processing : i = row
  · subst i
    exact rowCovered
  have old : i ∈ s.reached := by
    by_contra hn
    exact noQueue (progress.newRows i hi hn)
  have unqueued : i ∉ s.queue := by
    intro member
    rw [pop, List.mem_cons] at member
    exact noQueue (progress.queue i (member.resolve_left processing))
  exact fun k hk => progress.seen (good.processed i old unqueued k hk)

def Frontier.done (s : Frontier r h) : Finset (Fin r) :=
  s.reached \ s.queue.toFinset

/-- A successful pop processes a fresh row and cannot requeue an old
processed row. This gives a finite expansion measure. -/
theorem expand_done_lt {adj : Fin r → List (Fin h)} {g : Fin r → Bool}
    {owner : Fin h → Option (Fin r)} {row : Fin r} {todo : List (Fin r)}
    {s t : Frontier r h} (ownerActive : ∀ k i, owner k = some i → g i = false)
    (good : FrontierGood g owner s) (pop : s.queue = row :: todo)
    (scanned : scanHoles owner {s with queue := todo} (adj row) = .ok t) :
    s.done.card < t.done.card := by
  obtain ⟨_, progress, _⟩ := scanHoles_ok ownerActive (adj row) (pop_good good pop) scanned
  have prior : s.done ⊆ t.done := by
    intro i hi
    obtain ⟨reached, notQueued⟩ := Finset.mem_sdiff.mp hi
    refine Finset.mem_sdiff.mpr ⟨progress.reached reached, ?_⟩
    intro queued
    have before := progress.oldRows i reached (List.mem_toFinset.mp queued)
    exact notQueued (List.mem_toFinset.mpr (pop ▸ List.mem_cons_of_mem _ before))
  have front : row ∈ s.queue := pop ▸ List.mem_cons_self
  have reached := good.queued row front
  have rowDone : row ∈ t.done := by
    refine Finset.mem_sdiff.mpr ⟨progress.reached reached, ?_⟩
    intro queued
    have before := progress.oldRows row reached (List.mem_toFinset.mp queued)
    exact (List.nodup_cons.mp (pop ▸ good.distinct)).1 before
  have rowNew : row ∉ s.done := fun hi =>
    (Finset.mem_sdiff.mp hi).2 (List.mem_toFinset.mpr front)
  exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset prior).mpr ⟨row, rowDone, rowNew⟩)

inductive BfsOutcome (r h : Nat)
  | exhausted (s : Frontier r h)
  | free (hole : Fin h)
  | budget

/-- Executable, row-level BFS with an explicit budget. The queue is checked
before fuel so spending the last allowed pop can still report exhaustion. -/
def explore (adj : Fin r → List (Fin h)) (owner : Fin h → Option (Fin r)) :
    Nat → Frontier r h → BfsOutcome r h
  | 0, s =>
    match s.queue with
    | [] => .exhausted s
    | _ :: _ => .budget
  | n + 1, s =>
    match s.queue with
    | [] => .exhausted s
    | row :: todo =>
      match scanHoles owner {s with queue := todo} (adj row) with
      | .error hole => .free hole
      | .ok next => explore adj owner n next

theorem explore_step {adj : Fin r → List (Fin h)} {owner : Fin h → Option (Fin r)}
    (fuel : Nat) {row : Fin r} {todo : List (Fin r)} {s t : Frontier r h}
    (pop : s.queue = row :: todo)
    (scan : scanHoles owner {s with queue := todo} (adj row) = .ok t) :
    explore adj owner (fuel + 1) s = explore adj owner fuel t := by
  simp only [explore, pop, scan]

theorem explore_exhaustion {adj : Fin r → List (Fin h)} {g : Fin r → Bool}
    {owner : Fin h → Option (Fin r)} {root : Fin r}
    (ownerActive : ∀ k i, owner k = some i → g i = false) (fuel : Nat)
    {s t : Frontier r h} (good : SearchGood adj g owner root s)
    (out : explore adj owner fuel s = .exhausted t) :
    SearchGood adj g owner root t ∧ t.queue = [] := by
  induction fuel generalizing s with
  | zero =>
    cases pop : s.queue with
    | nil =>
      simp [explore, pop] at out
      subst t
      exact ⟨good, pop⟩
    | cons row todo => simp [explore, pop] at out
  | succ fuel ih =>
    cases pop : s.queue with
    | nil =>
      simp [explore, pop] at out
      subst t
      exact ⟨good, pop⟩
    | cons row todo =>
      cases scan : scanHoles owner {s with queue := todo} (adj row) with
      | error hole => simp [explore, pop, scan] at out
      | ok next =>
        rw [explore_step fuel pop scan] at out
        exact ih (expand_good ownerActive good pop scan) out

/-- The number of rows bounds the available queue pops. A budget result
cannot occur if the fuel covers the rows still outside the processed set. -/
theorem explore_budget_sufficient {adj : Fin r → List (Fin h)} {g : Fin r → Bool}
    {owner : Fin h → Option (Fin r)}
    (ownerActive : ∀ k i, owner k = some i → g i = false) (fuel : Nat)
    {s : Frontier r h} (good : FrontierGood g owner s) (enough : r ≤ s.done.card + fuel) :
    explore adj owner fuel s ≠ .budget := by
  induction fuel generalizing s with
  | zero =>
    cases pop : s.queue with
    | nil => simp [explore, pop]
    | cons row todo =>
      have front : row ∈ s.queue := pop ▸ List.mem_cons_self
      have rowNotDone : row ∉ s.done := fun hi =>
        (Finset.mem_sdiff.mp hi).2 (List.mem_toFinset.mpr front)
      have strict : s.done ⊂ (Finset.univ : Finset (Fin r)) :=
        (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr
          ⟨row, Finset.mem_univ _, rowNotDone⟩
      have less : s.done.card < r := by simpa using Finset.card_lt_card strict
      omega
  | succ fuel ih =>
    cases pop : s.queue with
    | nil => simp [explore, pop]
    | cons row todo =>
      cases scan : scanHoles owner {s with queue := todo} (adj row) with
      | error hole => simp [explore, pop, scan]
      | ok next =>
        have more := expand_done_lt ownerActive good pop scan
        obtain ⟨goodNext, _, _⟩ := scanHoles_ok ownerActive (adj row) (pop_good good pop) scan
        rw [explore_step fuel pop scan]
        exact ih goodNext (by omega)

/-- Fuel equal to the number of rows suffices for a fresh search. -/
theorem start_full_budget {adj : Fin r → List (Fin h)} {g : Fin r → Bool}
    {owner : Fin h → Option (Fin r)} {root : Fin r}
    (ownerActive : ∀ k i, owner k = some i → g i = false) (active : g root = false) :
    explore adj owner r (Frontier.start root) ≠ .budget :=
  explore_budget_sufficient ownerActive r (start_good adj owner active).frontier (by omega)

theorem explore_free_hole {adj : Fin r → List (Fin h)} {owner : Fin h → Option (Fin r)}
    (fuel : Nat) {s : Frontier r h} {hole : Fin h}
    (out : explore adj owner fuel s = .free hole) :
    (∃ row, hole ∈ adj row) ∧ owner hole = none := by
  induction fuel generalizing s with
  | zero => cases pop : s.queue <;> simp [explore, pop] at out
  | succ fuel ih =>
    cases pop : s.queue with
    | nil => simp [explore, pop] at out
    | cons row todo =>
      cases scan : scanHoles owner {s with queue := todo} (adj row) with
      | error free =>
        simp [explore, pop, scan] at out
        subst free
        obtain ⟨member, unowned⟩ := scanHoles_error (adj row) scan
        exact ⟨⟨row, member⟩, unowned⟩
      | ok next =>
        rw [explore_step fuel pop scan] at out
        exact ih out

/-- Mutable-table consistency transports activity of matched rows to owners.
It also makes any row that was discovered through a hole have at most one
such ownership edge, independently of queue duplicate prevention. -/
theorem ownerFacts {g : Fin r → Bool} {rowMatch : Fin r → Option (Fin h)}
    {owner : Fin h → Option (Fin r)} (consistent : InverseConsistent rowMatch owner)
    (matchedActive : ∀ i k, rowMatch i = some k → g i = false) :
    (∀ k i, owner k = some i → g i = false) ∧
      ∀ k l i, owner k = some i → owner l = some i → k = l :=
  ⟨fun k i own => matchedActive i k (consistent k i own),
    fun k l i first second =>
      Option.some.inj ((consistent k i first).symm.trans (consistent l i second))⟩

/-- An exhausted run from the active unmatched root yields an accepted Hall
failure certificate. Its owner closure is derived from the executed scans. -/
theorem drained_bfs_certificate {adj : Fin r → List (Fin h)} {g : Fin r → Bool}
    {rowMatch : Fin r → Option (Fin h)} {owner : Fin h → Option (Fin r)}
    {root : Fin r} {t : Frontier r h} (fuel : Nat) (active : g root = false)
    (unmatched : rowMatch root = none) (consistent : InverseConsistent rowMatch owner)
    (matchedActive : ∀ i k, rowMatch i = some k → g i = false)
    (out : explore adj owner fuel (Frontier.start root) = .exhausted t) :
    failureCheck (fun i => (adj i).toFinset) g t.reached = true ∧
      ¬ HasMatching (fun i => (adj i).toFinset) g := by
  obtain ⟨good, empty⟩ := explore_exhaustion (ownerFacts consistent matchedActive).1 fuel
    (start_good adj owner active) out
  have closed : ∀ k ∈ t.reached.biUnion (fun i => (adj i).toFinset),
      ∃ i ∈ t.reached, owner k = some i := by
    intro k hk
    obtain ⟨i, hi, edge⟩ := Finset.mem_biUnion.mp hk
    have noQueue : i ∉ t.queue := by simp [empty]
    exact good.frontier.owned k (good.processed i hi noQueue k (List.mem_toFinset.mp edge))
  have accepted := exhausted_cut_accepted (fun i => (adj i).toFinset) g rowMatch owner
    t.reached root good.rootMem unmatched consistent closed good.frontier.active
  exact ⟨accepted, accepted_failure_no_matching _ g t.reached accepted⟩

#print axioms scanHole_ok
#print axioms scanHoles_ok
#print axioms expand_good
#print axioms expand_done_lt
#print axioms explore_exhaustion
#print axioms start_full_budget
#print axioms explore_free_hole
#print axioms ownerFacts
#print axioms drained_bfs_certificate

section Examples

private def ladderAdj (row : Fin 3) : List (Fin 3) :=
  if row = 0 then [0] else if row = 1 then [0, 1] else [1, 2]

private def ladderOwner (hole : Fin 3) : Option (Fin 3) :=
  if hole = 0 then some 1 else if hole = 1 then some 2 else none

private def properCutAdj (row : Fin 4) : List (Fin 4) :=
  if row = 0 then [0, 1] else if row = 1 then [0] else if row = 2 then [1] else [2, 3]

private def properCutOwner (hole : Fin 4) : Option (Fin 4) :=
  if hole = 0 then some 1 else if hole = 1 then some 2 else none

private def exactCut (outcome : BfsOutcome 4 4) : Bool :=
  match outcome with
  | .exhausted s =>
    decide (s.reached = {0, 1, 2} ∧ s.seen = {0, 1} ∧ s.queue = [])
  | _ => false

private def outcomeView : BfsOutcome r h → Nat × Nat
  | .exhausted s => (0, s.reached.card)
  | .free k => (1, k.val)
  | .budget => (2, 0)

-- The fourth row is isolated from this forest but has its own two neighbors.
example : exactCut (explore properCutAdj properCutOwner 4 (Frontier.start 0)) = true :=
  by decide

-- The free hole is reached only after three row expansions.
example : outcomeView (explore ladderAdj ladderOwner 3 (Frontier.start 0)) = (1, 2) :=
  by decide

example : outcomeView (explore ladderAdj ladderOwner 2 (Frontier.start 0)) = (2, 0) :=
  by decide

example : outcomeView (explore (fun (_ : Fin 1) => ([] : List (Fin 0)))
    (fun _ => none) 1 (Frontier.start 0)) = (0, 1) :=
  by decide

end Examples

end PEqualNP.Outside.MatchingSearch
