import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace PEqualNP.Outside.MatchingAugmentation
variable {r h : Nat}

structure State (r h : Nat) where
  rowMatch : Fin r → Option (Fin h)
  owner : Fin h → Option (Fin r)

def Consistent (s : State r h) : Prop :=
  ∀ i k, s.rowMatch i = some k ↔ s.owner k = some i

def Valid (N : Fin r → Finset (Fin h)) (s : State r h) : Prop :=
  Consistent s ∧ ∀ i k, s.rowMatch i = some k → k ∈ N i

def empty : State r h := ⟨fun _ => none, fun _ => none⟩

theorem empty_valid (N : Fin r → Finset (Fin h)) : Valid N empty := by
  constructor
  · intro i k; simp [empty]
  · intro i k assigned; simp [empty] at assigned

theorem assigned_rows_injective (s : State r h) (consistent : Consistent s)
    (i j : Fin r) (k : Fin h) (hi : s.rowMatch i = some k)
    (hj : s.rowMatch j = some k) : i = j :=
  Option.some.inj (((consistent i k).mp hi).symm.trans ((consistent j k).mp hj))

/-- Atomic reverse-path step: assign a row to the free hole and clear its old
hole immediately. This differs from a Python loop's transient stale owners. -/
def move (s : State r h) (i : Fin r) (k : Fin h) : State r h where
  rowMatch := fun j => if j = i then some k else s.rowMatch j
  owner := fun l => if l = k then some i else
    if s.rowMatch i = some l then none else s.owner l

theorem move_consistent (s : State r h) (consistent : Consistent s)
    (i : Fin r) (k : Fin h) (free : s.owner k = none) : Consistent (move s i k) := by
  intro j l
  by_cases ji : j = i
  · subst j
    by_cases lk : l = k
    · subst l; simp [move]
    · have kl : k ≠ l := Ne.symm lk
      by_cases old : s.rowMatch i = some l
      · simp [move, lk, kl, old]
      · have noOwner : s.owner l ≠ some i := fun owned => old ((consistent i l).mpr owned)
        simp [move, lk, kl, old, noOwner]
  · have ij : i ≠ j := Ne.symm ji
    by_cases lk : l = k
    · subst l
      have noRow : s.rowMatch j ≠ some k := by
        intro assigned
        have owned := (consistent j k).mp assigned
        simp [free] at owned
      simp [move, ji, ij, noRow]
    · by_cases old : s.rowMatch i = some l
      · have noRow : s.rowMatch j ≠ some l := fun assigned =>
          ji (assigned_rows_injective s consistent j i l assigned old)
        simp [move, ji, lk, old, noRow]
      · simpa [move, ji, lk, old] using consistent j l

theorem move_valid (N : Fin r → Finset (Fin h)) (s : State r h) (valid : Valid N s)
    (i : Fin r) (k : Fin h) (free : s.owner k = none) (neighbor : k ∈ N i) :
    Valid N (move s i k) := by
  refine ⟨move_consistent s valid.1 i k free, ?_⟩
  intro j l assigned
  by_cases ji : j = i
  · subst j
    have same : k = l := by simpa [move] using assigned
    simpa [← same] using neighbor
  · exact valid.2 j l (by simpa [move, ji] using assigned)

theorem move_frees_previous (s : State r h) (consistent : Consistent s)
    (i : Fin r) (k previous : Fin h) (free : s.owner k = none)
    (old : s.rowMatch i = some previous) : (move s i k).owner previous = none := by
  have different : previous ≠ k := by
    intro same
    subst previous
    have owned := (consistent i k).mp old
    simp [free] at owned
  simp [move, different, old]

def matchedRows (s : State r h) : Finset (Fin r) :=
  Finset.univ.filter (fun i => (s.rowMatch i).isSome)

theorem matchedRows_move (s : State r h) (i : Fin r) (k : Fin h) :
    matchedRows (move s i k) = insert i (matchedRows s) := by
  ext j
  simp only [matchedRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases ji : j = i <;> simp [move, ji]

theorem move_preserves_coverage (s : State r h) (i : Fin r) (k : Fin h) :
    matchedRows s ⊆ matchedRows (move s i k) := by
  rw [matchedRows_move]
  exact Finset.subset_insert _ _

theorem move_unmatched_card (s : State r h) (i : Fin r) (k : Fin h)
    (unmatched : s.rowMatch i = none) :
    (matchedRows (move s i k)).card = (matchedRows s).card + 1 := by
  rw [matchedRows_move, Finset.card_insert_of_notMem]
  simp [matchedRows, unmatched]

theorem move_matched_card (s : State r h) (i : Fin r) (k previous : Fin h)
    (matched : s.rowMatch i = some previous) :
    (matchedRows (move s i k)).card = (matchedRows s).card := by
  rw [matchedRows_move, Finset.card_insert_of_mem]
  simp [matchedRows, matched]

/-- Replay a reverse alternating path, starting with its free end hole.
Each move checks freeness and adjacency. A successful path must end at an
unmatched row; a truncated or malformed path is rejected with none. -/
def augmentRows (N : Fin r → Finset (Fin h)) :
    List (Fin r) → State r h → Fin h → Option (State r h)
  | [], _, _ => none
  | i :: rest, s, k =>
      if s.owner k = none ∧ k ∈ N i then
        let next := move s i k
        match s.rowMatch i with
        | none => if rest = [] then some next else none
        | some previous => augmentRows N rest next previous
      else none

theorem augmentRows_sound (N : Fin r → Finset (Fin h)) (path : List (Fin r))
    (s : State r h) (k : Fin h) (out : State r h) (valid : Valid N s)
    (returned : augmentRows N path s k = some out) :
    Valid N out ∧ matchedRows s ⊆ matchedRows out ∧
      (matchedRows out).card = (matchedRows s).card + 1 := by
  induction path generalizing s k out with
  | nil => simp [augmentRows] at returned
  | cons i rest ih =>
      by_cases permitted : s.owner k = none ∧ k ∈ N i
      · simp only [augmentRows, ite_eq_left permitted] at returned
        have nextValid := move_valid N s valid i k permitted.1 permitted.2
        have coverage := move_preserves_coverage s i k
        cases old : s.rowMatch i with
        | none =>
            by_cases final : rest = []
            · have same : move s i k = out := by simpa [old, final] using returned
              subst out
              exact ⟨nextValid, coverage, move_unmatched_card s i k old⟩
            · simp [old, final] at returned
        | some previous =>
            have nextReturned : augmentRows N rest (move s i k) previous = some out := by
              simpa [old] using returned
            obtain ⟨outValid, outCoverage, outCard⟩ :=
              ih (move s i k) previous out nextValid nextReturned
            refine ⟨outValid, coverage.trans outCoverage, ?_⟩
            rw [outCard, move_matched_card s i k previous old]
      · simp [augmentRows, permitted] at returned

#print axioms move
#print axioms augmentRows
#print axioms empty_valid
#print axioms move_consistent
#print axioms move_valid
#print axioms move_frees_previous
#print axioms matchedRows_move
#print axioms augmentRows_sound
end PEqualNP.Outside.MatchingAugmentation
