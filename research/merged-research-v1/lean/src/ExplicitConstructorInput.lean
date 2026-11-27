import AutomaticConstructorTotal

namespace PEqualNP.Outside.ExplicitConstructorInput
open PEqualNP.Search
open PEqualNP.Outside.AutomaticConstructor
open PEqualNP.Outside.CertifiedConstructorSolver
open PEqualNP.Outside.SparseDualHornAlgorithm

/-- Explicit data, rather than a caller-supplied function on a potentially
enormous `Fin r`. The numeric hole bound is not enumerated by `solve`. -/
structure Row where
  neighbors : List Nat
  guard : Clause

structure Input where
  offset : Nat
  holeBound : Nat
  retained : CNF
  rows : List Row

def boundedNeighbors (bound : Nat) (neighbors : List Nat) : Bool :=
  neighbors.all (fun j => decide (j < bound))

def neighborCheck (input : Input) : Bool :=
  input.rows.all (fun row => boundedNeighbors input.holeBound row.neighbors)

def toHole (bound j : Nat) : Option (Fin bound) :=
  if h : j < bound then some ⟨j, h⟩ else none

def toNeighbors (bound : Nat) (neighbors : List Nat) : List (Fin bound) :=
  neighbors.filterMap (toHole bound)

theorem toNeighbors_values (bound : Nat) (neighbors : List Nat)
    (checked : boundedNeighbors bound neighbors = true) :
    (toNeighbors bound neighbors).map Fin.val = neighbors := by
  induction neighbors with
  | nil => rfl
  | cons j rest ih =>
      have bounds : j < bound ∧ boundedNeighbors bound rest = true := by
        simpa [boundedNeighbors] using checked
      simpa [toNeighbors, toHole, bounds.1] using congrArg (List.cons j) (ih bounds.2)

def adjacency (input : Input) (i : Fin input.rows.length) : List (Fin input.holeBound) :=
  toNeighbors input.holeBound (input.rows.get i).neighbors

def guards (input : Input) (i : Fin input.rows.length) : Clause :=
  (input.rows.get i).guard

theorem checked_adjacency_preserves_values (input : Input)
    (checked : neighborCheck input = true) (i : Fin input.rows.length) :
    (adjacency input i).map Fin.val = (input.rows.get i).neighbors := by
  apply toNeighbors_values
  exact List.all_eq_true.mp checked _ (List.get_mem _ _)

/-- A logical reference formula. The actual solver does not materialize it;
in particular this reference constructor may enumerate the hole bound. -/
def formula (input : Input) : CNF :=
  encoded input.offset input.retained (adjacency input) (guards input)

def solve (input : Input) : Outcome :=
  if neighborCheck input then
    AutomaticConstructor.solve input.offset input.retained (adjacency input) (guards input)
  else .unsupported

def supportedCheck (input : Input) : Bool :=
  neighborCheck input && inputCheck input.offset input.retained (guards input) &&
    dualHornCheck input.retained

theorem solve_correct (input : Input) :
    AutomaticConstructor.Correct (formula input) (solve input) := by
  by_cases checked : neighborCheck input = true
  · simpa [solve, checked, formula] using AutomaticConstructor.solve_correct
      input.offset input.retained (adjacency input) (guards input)
  · simp [solve, checked, AutomaticConstructor.Correct]

theorem solve_ne_inconclusive (input : Input) : solve input ≠ .inconclusive := by
  by_cases checked : neighborCheck input = true
  · simpa [solve, checked] using AutomaticConstructor.solve_ne_inconclusive
      input.offset input.retained (adjacency input) (guards input)
  · simp [solve, checked]

theorem supported_solve_decisive (input : Input)
    (supported : supportedCheck input = true) : Decisive (solve input) := by
  have checks : (neighborCheck input = true ∧
      inputCheck input.offset input.retained (guards input) = true) ∧
      dualHornCheck input.retained = true := by
    simpa only [supportedCheck, Bool.and_eq_true] using supported
  simpa [solve, checks.1.1] using AutomaticConstructor.supported_solve_decisive
    input.offset input.retained (adjacency input) (guards input) checks.1.2 checks.2

/-- A count of explicit list cells, not a bit-time bound. Numeric identifiers
can require many bits and all list/closure costs remain to be accounted for. -/
def structuralSize (input : Input) : Nat :=
  1 + input.rows.length + input.retained.length +
    (input.retained.map List.length).sum +
    (input.rows.map (fun row => row.neighbors.length + row.guard.length)).sum

theorem rows_le_structuralSize (input : Input) : input.rows.length ≤ structuralSize input := by
  unfold structuralSize
  omega

theorem rejected_neighbor_is_unsupported (input : Input)
    (invalid : neighborCheck input = false) : solve input = .unsupported := by
  simp [solve, invalid]

#print axioms checked_adjacency_preserves_values
#print axioms solve_correct
#print axioms solve_ne_inconclusive
#print axioms supported_solve_decisive
#print axioms rows_le_structuralSize
end PEqualNP.Outside.ExplicitConstructorInput
