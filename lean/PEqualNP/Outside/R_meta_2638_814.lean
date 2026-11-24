import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2638_814
 (classify : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (A : Finset (Fin n)) (z : Fin n) (C : Circuit),
     let B := Aᶜ.erase z
     let cnt := (C.output :: C.gates.flatMap Gate.inputs).count
     let excess := (∑ v ∈ B, (cnt v.val - 2)) +
       (∑ i ∈ Finset.range C.size, (cnt (n+i) - 1)) + (2*C.size - (C.gates.flatMap Gate.inputs).length)
     H = G.deleteEdges (G.incidenceSet z) →
     (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
     (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
     (∀ u v, G.Adj u v → u ∉ A) → z ∉ A →
     (∀ T : Finset (Fin n), CoverPromise.IsVertexCover H T → k ≤ T.card) →
     IsMinimalCircuit n C → circuitFun n C = graphFun H A →
     ¬ (A.card + H.edgeSet.ncard + k ≤ C.size + 1) → (∃ v ∈ B, cnt v.val = 1) ∨ ((∀ v ∈ B, 2 ≤ cnt v.val) ∧ 6*excess + 9 < B.card))
 (single : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (A : Finset (Fin n)) (z : Fin n) (C : Circuit),
     let B := Aᶜ.erase z
     let cnt := (C.output :: C.gates.flatMap Gate.inputs).count
     H = G.deleteEdges (G.incidenceSet z) →
     (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
     (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
     (∀ u v, G.Adj u v → u ∉ A) → z ∉ A →
     (∀ T : Finset (Fin n), CoverPromise.IsVertexCover H T → k ≤ T.card) →
     IsMinimalCircuit n C → circuitFun n C = graphFun H A →
     (∃ v ∈ B, cnt v.val = 1) → A.card + H.edgeSet.ncard + k ≤ C.size + 1)
 (sparse : ∀ (n k : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (A : Finset (Fin n)) (z : Fin n) (C : Circuit),
     let B := Aᶜ.erase z
     let cnt := (C.output :: C.gates.flatMap Gate.inputs).count
     let excess := (∑ v ∈ B, (cnt v.val - 2)) +
       (∑ i ∈ Finset.range C.size, (cnt (n+i) - 1)) + (2*C.size - (C.gates.flatMap Gate.inputs).length)
     H = G.deleteEdges (G.incidenceSet z) →
     (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
     (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
     (∀ u v, G.Adj u v → u ∉ A) → z ∉ A →
     (∀ T : Finset (Fin n), CoverPromise.IsVertexCover H T → k ≤ T.card) →
     IsMinimalCircuit n C → circuitFun n C = graphFun H A →
     ((∀ v ∈ B, 2 ≤ cnt v.val) ∧ 6*excess + 9 < B.card) → A.card + H.edgeSet.ncard + k ≤ C.size + 1) :
 ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  classical
  intro n k s G A z f deg girth ends _ hz spec demand size
  let H := G.deleteEdges (G.incidenceSet z)
  letI : DecidableRel H.Adj := fun _ _ => Classical.propDecidable _
  have eqf : f = graphFun H A := by
    funext x
    rw [Bool.eq_iff_iff, spec]
    simp [graphFun,H]
  have ex : ∃ t, HasCircuitSize n f t := ⟨s,size⟩
  obtain ⟨C,fan,cs,ev⟩ := Nat.find_spec ex
  have hi := cs.trans (Nat.find_min' ex size)
  have hfun : circuitFun n C = f := funext ev
  have minimal : IsMinimalCircuit n C := by
    refine ⟨fan,fun D ok same => cs.trans (Nat.find_min' ex ?_)⟩
    exact ⟨D,ok,le_rfl,fun x => congrFun (same.trans hfun) x⟩
  have value := hfun.trans eqf
  change A.card + H.edgeSet.ncard + k ≤ s + 1
  by_cases small : A.card + H.edgeSet.ncard + k ≤ C.size + 1
  · exact small.trans (Nat.succ_le_succ hi)
  · rcases classify n k G H A z C rfl deg girth ends hz demand minimal value small with h | h
    · exact (single n k G H A z C rfl deg girth ends hz demand minimal value h).trans (Nat.succ_le_succ hi)
    · exact (sparse n k G H A z C rfl deg girth ends hz demand minimal value h).trans (Nat.succ_le_succ hi)
