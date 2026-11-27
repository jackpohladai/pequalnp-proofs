import ActiveAugmentation

namespace PEqualNP.Outside.MatchingPaths
open PEqualNP.Outside.MatchingAugmentation
variable {r h : Nat}

/-- A reverse alternating row path in the original partial matching. -/
def Follows (N : Fin r → Finset (Fin h)) (rows : Fin r → Option (Fin h))
    (root : Fin r) : List (Fin r) → Prop
  | [] => False
  | [i] => i = root ∧ rows i = none
  | i :: j :: rest => ∃ k, rows i = some k ∧ k ∈ N j ∧ Follows N rows root (j :: rest)

theorem follows_congr (N : Fin r → Finset (Fin h)) (a b : Fin r → Option (Fin h))
    (root : Fin r) (path : List (Fin r)) (same : ∀ i ∈ path, a i = b i)
    (follows : Follows N a root path) : Follows N b root path := by
  induction path with
  | nil => exact follows
  | cons i rest ih =>
      cases rest with
      | nil => simpa only [Follows, same i (by simp)] using follows
      | cons j tail =>
          obtain ⟨k, matched, neighbor, next⟩ := follows
          exact ⟨k, (same i (by simp)).symm.trans matched, neighbor,
            ih (fun t ht => same t (List.mem_cons_of_mem i ht)) next⟩

theorem follows_rows (N : Fin r → Finset (Fin h)) (s : State r h)
    (root : Fin r) (path : List (Fin r)) (follows : Follows N s.rowMatch root path) :
    ∀ i ∈ path, i = root ∨ (s.rowMatch i).isSome = true := by
  induction path with
  | nil => simp
  | cons i rest ih =>
      cases rest with
      | nil =>
          intro t member
          have same : t = i := List.mem_singleton.mp member
          subst t
          exact Or.inl follows.1
      | cons j tail =>
          obtain ⟨k, matched, _, next⟩ := follows
          intro t member
          rcases List.mem_cons.mp member with rfl | ht
          · exact Or.inr (by simp [matched])
          · exact ih next t ht

/-- Structural path data suffices for actual executable replay, at the exact
unmatched root. Replay acceptance is a conclusion rather than a premise. -/
theorem follows_replay (N : Fin r → Finset (Fin h)) (s : State r h)
    (valid : Valid N s) (root : Fin r) (i : Fin r) (rest : List (Fin r))
    (follows : Follows N s.rowMatch root (i :: rest)) (distinct : (i :: rest).Nodup)
    (hole : Fin h) (free : s.owner hole = none) (neighbor : hole ∈ N i) :
    ∃ out, augmentRows N (i :: rest) s hole = some out ∧ root ∈ matchedRows out := by
  induction rest generalizing s i hole with
  | nil =>
      obtain ⟨same, unmatched⟩ := follows
      refine ⟨move s i hole, ?_, ?_⟩
      · simp [augmentRows, free, neighbor, unmatched]
      · rw [matchedRows_move, ← same]
        exact Finset.mem_insert_self _ _
  | cons j tail ih =>
      obtain ⟨previous, old, adjacency, next⟩ := follows
      have nextValid := move_valid N s valid i hole free neighbor
      have nextFree := move_frees_previous s valid.1 i hole previous free old
      have different : ∀ t ∈ j :: tail, t ≠ i := by
        intro t ht same
        exact (List.nodup_cons.mp distinct).1 (same ▸ ht)
      have nextFollows : Follows N (move s i hole).rowMatch root (j :: tail) :=
        follows_congr N s.rowMatch (move s i hole).rowMatch root (j :: tail)
          (fun t ht => by simp [move, different t ht]) next
      obtain ⟨out, returned, covered⟩ := ih (move s i hole) nextValid j nextFollows
        (List.nodup_cons.mp distinct).2 previous nextFree adjacency
      refine ⟨out, ?_, covered⟩
      simpa [augmentRows, free, neighbor, old] using returned

structure GoodPath (N : Fin r → Finset (Fin h)) (s : State r h) (root : Fin r)
    (seen : Finset (Fin r)) (path : List (Fin r)) : Prop where
  follows : Follows N s.rowMatch root path
  distinct : path.Nodup
  inside : ∀ i ∈ path, i ∈ seen

theorem GoodPath.mono {N : Fin r → Finset (Fin h)} {s : State r h} {root : Fin r}
    {seen more : Finset (Fin r)} {path : List (Fin r)}
    (good : GoodPath N s root seen path) (subset : seen ⊆ more) :
    GoodPath N s root more path :=
  ⟨good.follows, good.distinct, fun i hi => subset (good.inside i hi)⟩

theorem GoodPath.extend {N : Fin r → Finset (Fin h)} {s : State r h} {root i j : Fin r}
    {seen : Finset (Fin r)} {rest : List (Fin r)} (good : GoodPath N s root seen (i :: rest))
    (fresh : j ∉ seen) (hole : Fin h) (matched : s.rowMatch j = some hole)
    (neighbor : hole ∈ N i) : GoodPath N s root (insert j seen) (j :: i :: rest) := by
  refine ⟨⟨hole,matched,neighbor,good.follows⟩, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨fun member => fresh (good.inside j member),good.distinct⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | prior
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (good.inside t prior)

#print axioms follows_replay
#print axioms follows_rows
#print axioms GoodPath.extend
end PEqualNP.Outside.MatchingPaths
