import RawPathInvariant
import MatchingPathComposition

namespace PEqualNP.Outside.MatchingCorrespondence
open PEqualNP.Outside.MatchingAugmentation
open PEqualNP.Outside.MatchingSearch
open PEqualNP.Outside.MatchingPaths
variable {r h : Nat}

structure Related (owner : Fin h → Option (Fin r)) (root : Fin r)
    (plain : Frontier r h) (paths : PathWork r) : Prop where
  reached : plain.reached = paths.seen
  queue : plain.queue = paths.queue.map (fun p => p.headD root)
  nonempty : ∀ p ∈ paths.queue, p ≠ []
  owned : ∀ k ∈ plain.seen, ∃ i ∈ plain.reached, owner k = some i

theorem Related.record {owner : Fin h → Option (Fin r)} {root : Fin r}
    {plain : Frontier r h} {paths : PathWork r} (rel : Related owner root plain paths)
    (k : Fin h) (i : Fin r) (known : i ∈ plain.reached) (owned : owner k = some i) :
    Related owner root {plain with seen := insert k plain.seen} paths := by
  refine ⟨rel.reached, rel.queue, rel.nonempty, ?_⟩
  intro l hl
  rcases Finset.mem_insert.mp hl with rfl | prior
  · exact ⟨i, known, owned⟩
  · exact rel.owned l prior

theorem Related.discover {owner : Fin h → Option (Fin r)} {root : Fin r}
    {plain : Frontier r h} {paths : PathWork r} (rel : Related owner root plain paths)
    (k : Fin h) (i : Fin r) (path : List (Fin r)) (owned : owner k = some i) :
    Related owner root ⟨insert i plain.reached, insert k plain.seen, plain.queue ++ [i]⟩
      ⟨insert i paths.seen, paths.queue ++ [i :: path]⟩ := by
  refine ⟨by simp [rel.reached], by simp [rel.queue], ?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with prior | added
    · exact rel.nonempty p prior
    · have same := List.mem_singleton.mp added
      simp [same]
  · intro l hl
    rcases Finset.mem_insert.mp hl with rfl | prior
    · exact ⟨i, Finset.mem_insert_self _ _, owned⟩
    · obtain ⟨j, known, own⟩ := rel.owned l prior
      exact ⟨j, Finset.mem_insert_of_mem known, own⟩

theorem scan_correspondence (s : State r h) (root : Fin r) (path : List (Fin r))
    (holes : List (Fin h)) (plain : Frontier r h) (paths : PathWork r)
    (rel : Related s.owner root plain paths) :
    match scanHoles s.owner plain holes with
    | .error k => scanPaths s path holes paths = .inl (k, path)
    | .ok next => ∃ after, scanPaths s path holes paths = .inr after ∧
        Related s.owner root next after := by
  induction holes generalizing plain paths with
  | nil => exact ⟨paths, rfl, rel⟩
  | cons k ks ih =>
      by_cases seen : k ∈ plain.seen
      · obtain ⟨i, known, own⟩ := rel.owned k seen
        have knownPath : i ∈ paths.seen := rel.reached ▸ known
        simpa [scanHoles, scanHole, seen, scanPaths, own, knownPath] using
          ih plain paths rel
      · cases own : s.owner k with
        | none => simp [scanHoles, scanHole, seen, own, scanPaths]
        | some i =>
            by_cases known : i ∈ plain.reached
            · have knownPath : i ∈ paths.seen := rel.reached ▸ known
              simpa [scanHoles, scanHole, seen, own, known, scanPaths, knownPath] using
                ih {plain with seen := insert k plain.seen} paths (rel.record k i known own)
            · have freshPath : i ∉ paths.seen := by simpa [← rel.reached] using known
              simpa [scanHoles, scanHole, seen, own, known, scanPaths, freshPath] using
                ih ⟨insert i plain.reached, insert k plain.seen, plain.queue ++ [i]⟩
                  ⟨insert i paths.seen, paths.queue ++ [i :: path]⟩ (rel.discover k i path own)

theorem explore_correspondence (adj : Fin r → List (Fin h)) (s : State r h)
    (root : Fin r) (fuel : Nat) (plain : Frontier r h) (paths : PathWork r)
    (rel : Related s.owner root plain paths) (hole : Fin h)
    (free : explore adj s.owner fuel plain = .free hole) :
    ∃ rows, explorePaths adj s fuel paths = some (hole, rows) := by
  induction fuel generalizing plain paths with
  | zero => cases q : plain.queue <;> simp [explore, q] at free
  | succ fuel ih =>
      cases q : paths.queue with
      | nil =>
          have pq : plain.queue = [] := by simpa [q] using rel.queue
          simp [explore, pq] at free
      | cons current tail =>
          have nonempty := rel.nonempty current (by simp [q])
          cases current with
          | nil => exact False.elim (nonempty rfl)
          | cons row rest =>
              have pq : plain.queue = row :: tail.map (fun p => p.headD root) := by
                simpa [q] using rel.queue
              have popped : Related s.owner root
                  {plain with queue := tail.map (fun p => p.headD root)} ⟨paths.seen, tail⟩ := by
                refine ⟨rel.reached, rfl, ?_, rel.owned⟩
                intro p hp
                exact rel.nonempty p (by simp [q, hp])
              have scans := scan_correspondence s root (row :: rest) (adj row)
                {plain with queue := tail.map (fun p => p.headD root)} ⟨paths.seen, tail⟩ popped
              cases scanned : scanHoles s.owner
                  {plain with queue := tail.map (fun p => p.headD root)} (adj row) with
              | error k =>
                  have same : k = hole := by
                    simpa only [explore, pq, scanned, BfsOutcome.free.injEq] using free
                  subst k
                  have pathScan : scanPaths s (row :: rest) (adj row) ⟨paths.seen, tail⟩ =
                      .inl (hole, row :: rest) := by simpa only [scanned] using scans
                  exact ⟨row :: rest, by simp [explorePaths, q, pathScan]⟩
              | ok next =>
                  have nextFree : explore adj s.owner fuel next = .free hole := by
                    simpa only [explore, pq, scanned] using free
                  have continuation : ∃ after,
                      scanPaths s (row :: rest) (adj row) ⟨paths.seen, tail⟩ = .inr after ∧
                      Related s.owner root next after := by simpa only [scanned] using scans
                  obtain ⟨after, pathScan, related⟩ := continuation
                  obtain ⟨rows, found⟩ := ih next after related nextFree
                  exact ⟨rows, by simpa [explorePaths, q, pathScan] using found⟩

theorem free_implies_rawPath (adj : Fin r → List (Fin h)) (s : State r h)
    (root : Fin r) (fuel : Nat) (hole : Fin h)
    (free : explore adj s.owner fuel (Frontier.start root) = .free hole) :
    ∃ rows, rawSearchPath adj s root fuel = some (hole, rows) := by
  apply explore_correspondence adj s root fuel (Frontier.start root)
    ⟨{root}, [[root]]⟩ _ hole free
  exact ⟨rfl, rfl, by simp, by simp [Frontier.start]⟩

theorem solve_definite (adj : Fin r → List (Fin h)) (g : Fin r → Bool) :
    MatchingPathComposition.solve adj g ≠ .inconclusive := by
  apply MatchingPathComposition.solve_definite_if_path_found adj g
  intro s root hole valid active rootActive unmatched free
  obtain ⟨rows, found⟩ := free_implies_rawPath adj s root r hole free
  exact ⟨(hole, rows), (searchPath_eq_raw adj s valid root unmatched r).trans found⟩

#print axioms scan_correspondence
#print axioms explore_correspondence
#print axioms free_implies_rawPath
#print axioms solve_definite
end PEqualNP.Outside.MatchingCorrespondence
