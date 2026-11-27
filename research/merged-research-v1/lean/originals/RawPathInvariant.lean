import PathCarryingSearch

namespace PEqualNP.Outside.MatchingPaths
open PEqualNP.Outside.MatchingAugmentation
variable {r h : Nat}

def QueueGood (N : Fin r → Finset (Fin h)) (s : State r h) (root : Fin r)
    (work : PathWork r) : Prop :=
  ∀ path ∈ work.queue, GoodPath N s root work.seen path

theorem scan_preserves (N : Fin r → Finset (Fin h)) (s : State r h)
    (valid : Valid N s) (root i : Fin r) (rest : List (Fin r))
    (holes : List (Fin h)) (work : PathWork r)
    (good : GoodPath N s root work.seen (i :: rest)) (queued : QueueGood N s root work)
    (neighbors : ∀ k ∈ holes, k ∈ N i) :
    match scanPaths s (i :: rest) holes work with
    | .inl (k, path) => ReturnOK N s root k path
    | .inr next => GoodPath N s root next.seen (i :: rest) ∧ QueueGood N s root next := by
  induction holes generalizing work with
  | nil => exact ⟨good, queued⟩
  | cons k ks ih =>
      simp only [scanPaths]
      cases owner : s.owner k with
      | none =>
          simp only [owner]
          exact ⟨good.follows, good.distinct, owner, neighbors k (by simp)⟩
      | some row =>
          simp only [owner]
          by_cases seen : row ∈ work.seen
          · simp only [if_pos seen]
            exact ih work good queued (fun t ht => neighbors t (by simp [ht]))
          · simp only [if_neg seen]
            have subset : work.seen ⊆ insert row work.seen := Finset.subset_insert _ _
            have nextGood := good.mono subset
            have extended := good.extend seen k ((valid.1 row k).mpr owner)
              (neighbors k (by simp))
            have nextQueue : QueueGood N s root
                ⟨insert row work.seen, work.queue ++ [row :: i :: rest]⟩ := by
              intro path member
              rcases List.mem_append.mp member with old | added
              · exact (queued path old).mono subset
              · have same := List.mem_singleton.mp added
                subst path
                exact extended
            exact ih _ nextGood nextQueue (fun t ht => neighbors t (by simp [ht]))

theorem explore_preserves (adj : Fin r → List (Fin h)) (s : State r h)
    (valid : Valid (fun i => (adj i).toFinset) s) (root : Fin r)
    (fuel : Nat) (work : PathWork r)
    (queued : QueueGood (fun i => (adj i).toFinset) s root work)
    (hole : Fin h) (path : List (Fin r))
    (returned : explorePaths adj s fuel work = some (hole, path)) :
    ReturnOK (fun i => (adj i).toFinset) s root hole path := by
  induction fuel generalizing work with
  | zero => simp [explorePaths] at returned
  | succ fuel ih =>
      cases queue : work.queue with
      | nil => simp [explorePaths, queue] at returned
      | cons current tail =>
          have currentGood := queued current (by simp [queue])
          cases current with
          | nil => exact False.elim currentGood.follows
          | cons i rest =>
              have tailGood : QueueGood (fun i => (adj i).toFinset) s root
                  ⟨work.seen, tail⟩ := by
                intro p hp
                exact queued p (by simp [queue, hp])
              have scanGood := scan_preserves (fun i => (adj i).toFinset) s valid root i rest
                (adj i) ⟨work.seen, tail⟩ currentGood tailGood
                (fun _ hk => List.mem_toFinset.mpr hk)
              cases scanned : scanPaths s (i :: rest) (adj i) ⟨work.seen, tail⟩ with
              | inl found =>
                  have same : found = (hole, path) := Option.some.inj (by
                    simpa [explorePaths, queue, scanned] using returned)
                  have good : ReturnOK (fun i => (adj i).toFinset) s root found.1 found.2 := by
                    simpa only [scanned] using scanGood
                  cases same
                  exact good
              | inr next =>
                  have result : explorePaths adj s fuel next = some (hole, path) := by
                    simpa [explorePaths, queue, scanned] using returned
                  have nextGood : GoodPath (fun i => (adj i).toFinset) s root next.seen
                      (i :: rest) ∧ QueueGood (fun i => (adj i).toFinset) s root next := by
                    simpa only [scanned] using scanGood
                  exact ih next nextGood.2 result

theorem rawSearchPath_certificate (adj : Fin r → List (Fin h)) (s : State r h)
    (valid : Valid (fun i => (adj i).toFinset) s) (root : Fin r)
    (unmatched : s.rowMatch root = none) (fuel : Nat) (hole : Fin h)
    (path : List (Fin r))
    (returned : rawSearchPath adj s root fuel = some (hole, path)) :
    ReturnOK (fun i => (adj i).toFinset) s root hole path := by
  apply explore_preserves adj s valid root fuel ⟨{root}, [[root]]⟩ _ hole path returned
  intro p hp
  have same : p = [root] := List.mem_singleton.mp hp
  subst p
  exact ⟨⟨rfl, unmatched⟩, by simp, by simp⟩

theorem searchPath_eq_raw (adj : Fin r → List (Fin h)) (s : State r h)
    (valid : Valid (fun i => (adj i).toFinset) s) (root : Fin r)
    (unmatched : s.rowMatch root = none) (fuel : Nat) :
    searchPath adj s root fuel = rawSearchPath adj s root fuel := by
  cases found : rawSearchPath adj s root fuel with
  | none => simp [searchPath, found]
  | some pair =>
      rcases pair with ⟨hole, path⟩
      have good := rawSearchPath_certificate adj s valid root unmatched fuel hole path found
      simp [searchPath, found, good]

#print axioms rawSearchPath_certificate
#print axioms searchPath_eq_raw
end PEqualNP.Outside.MatchingPaths
