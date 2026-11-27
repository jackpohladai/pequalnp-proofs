import ReversePaths

namespace PEqualNP.Outside.MatchingPaths
open PEqualNP.Outside.MatchingAugmentation
variable {r h : Nat}

instance followsDecidable (N : Fin r → Finset (Fin h)) (rows : Fin r → Option (Fin h))
    (root : Fin r) (path : List (Fin r)) : Decidable (Follows N rows root path) := by
  induction path with
  | nil => exact inferInstanceAs (Decidable False)
  | cons i rest ih =>
      cases rest with
      | nil => exact inferInstanceAs (Decidable (i = root ∧ rows i = none))
      | cons j tail =>
          letI := ih
          exact inferInstanceAs (Decidable (∃ k, rows i = some k ∧ k ∈ N j ∧
            Follows N rows root (j :: tail)))

structure PathWork (r : Nat) where
  seen : Finset (Fin r)
  queue : List (List (Fin r))

/-- Each newly discovered owner is enqueued with its reverse path. -/
def scanPaths (s : State r h) (path : List (Fin r)) :
    List (Fin h) → PathWork r → Sum (Fin h × List (Fin r)) (PathWork r)
  | [], work => .inr work
  | hole :: rest, work =>
      match s.owner hole with
      | none => .inl (hole, path)
      | some row =>
          if row ∈ work.seen then scanPaths s path rest work
          else scanPaths s path rest
            ⟨insert row work.seen, work.queue ++ [row :: path]⟩

def explorePaths (adj : Fin r → List (Fin h)) (s : State r h) :
    Nat → PathWork r → Option (Fin h × List (Fin r))
  | 0, _ => none
  | fuel + 1, work =>
      match work.queue with
      | [] => none
      | [] :: _ => none
      | (row :: rest) :: queue =>
          match scanPaths s (row :: rest) (adj row) ⟨work.seen, queue⟩ with
          | .inl found => some found
          | .inr next => explorePaths adj s fuel next

def rawSearchPath (adj : Fin r → List (Fin h)) (s : State r h)
    (root : Fin r) (fuel : Nat) : Option (Fin h × List (Fin r)) :=
  explorePaths adj s fuel ⟨{root}, [[root]]⟩

/-- Structural certificate checked on the returned path, not assumed by callers. -/
def ReturnOK (N : Fin r → Finset (Fin h)) (s : State r h) (root : Fin r)
    (hole : Fin h) (path : List (Fin r)) : Prop :=
  match path with
  | [] => False
  | row :: rest => Follows N s.rowMatch root (row :: rest) ∧
      (row :: rest).Nodup ∧ s.owner hole = none ∧ hole ∈ N row

instance returnOKDecidable (N : Fin r → Finset (Fin h)) (s : State r h)
    (root : Fin r) (hole : Fin h) (path : List (Fin r)) :
    Decidable (ReturnOK N s root hole path) := by
  cases path <;> unfold ReturnOK <;> infer_instance

/-- `none` means inconclusive, including fuel exhaustion or rejected path. -/
def searchPath (adj : Fin r → List (Fin h)) (s : State r h)
    (root : Fin r) (fuel : Nat) : Option (Fin h × List (Fin r)) :=
  match rawSearchPath adj s root fuel with
  | none => none
  | some (hole, path) =>
      if ReturnOK (fun i => (adj i).toFinset) s root hole path then some (hole, path)
      else none

theorem searchPath_certificate (adj : Fin r → List (Fin h)) (s : State r h)
    (root : Fin r) (fuel : Nat) (hole : Fin h) (path : List (Fin r))
    (returned : searchPath adj s root fuel = some (hole, path)) :
    ReturnOK (fun i => (adj i).toFinset) s root hole path := by
  unfold searchPath at returned
  cases found : rawSearchPath adj s root fuel with
  | none => simp [found] at returned
  | some pair =>
      rcases pair with ⟨k, rows⟩
      simp only [found] at returned
      split at returned
      next good =>
        have same := Option.some.inj returned
        cases same
        exact good
      next => contradiction

theorem searchPath_sound (adj : Fin r → List (Fin h)) (s : State r h)
    (root : Fin r) (fuel : Nat) (hole : Fin h) (path : List (Fin r))
    (valid : Valid (fun i => (adj i).toFinset) s)
    (returned : searchPath adj s root fuel = some (hole, path)) :
    ∃ out, augmentRows (fun i => (adj i).toFinset) path s hole = some out ∧
      root ∈ matchedRows out := by
  have good := searchPath_certificate adj s root fuel hole path returned
  cases path with
  | nil => exact False.elim good
  | cons i rest =>
      exact follows_replay _ s valid root i rest good.1 good.2.1 hole
        good.2.2.1 good.2.2.2

theorem searchPath_active (adj : Fin r → List (Fin h)) (s : State r h)
    (g : Fin r → Bool) (root : Fin r) (fuel : Nat) (hole : Fin h)
    (path : List (Fin r)) (active : ActiveOnly g s) (rootActive : g root = false)
    (returned : searchPath adj s root fuel = some (hole, path)) :
    ∀ i ∈ path, g i = false := by
  have good := searchPath_certificate adj s root fuel hole path returned
  cases path with
  | nil => simp
  | cons i rest =>
      intro j member
      rcases follows_rows _ s root (i :: rest) good.1 j member with same | matched
      · simpa [same] using rootActive
      · cases eq : s.rowMatch j with
        | none => simp [eq] at matched
        | some k => exact active j k eq

#print axioms searchPath_sound
#print axioms searchPath_active
#print axioms searchPath_certificate
end PEqualNP.Outside.MatchingPaths
