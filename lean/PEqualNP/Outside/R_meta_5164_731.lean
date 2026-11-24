import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5164_731
    (operand : let S := singerLines3
      let N (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
      let ok (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (N Q) = false
      ∀ C, ok C → (∀ D, ok D → C.size ≤ D.size) → ∀ (j : ℕ), j < C.size → (gateAt C j).op = .and → ∀ w ∈ (gateAt C j).inputs,
        ∃ Q, IsQuadrangle S Q ∧
          (⟨C.gates.set j ⟨.and, []⟩, C.output⟩ : Circuit).eval (N Q) = true ∧
          (C.wires (N Q)).getD w false = true ∧ (C.wires (N Q)).getD (26+j) false = false)
    (replacement : let S := singerLines3
      let N (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
      let ok (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (N Q) = false
      let free (C : Circuit) (w : ℕ) := 26 ≤ w → ∀ i, (gateAt C i).op = .and →
        i ≠ w-26 ∧ ¬ InCone 26 C i (w-26)
      let nested (C : Circuit) (i j : ℕ) := (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j
      ∀ C, ok C → (∀ D, ok D → D.size = C.size → andPairs 26 C ≤ andPairs 26 D) → ∀ i j, nested C i j → ∀ a b, a < 26+j → b < 26+j → free C a → free C b →
        ¬ok ⟨C.gates.set j ⟨.and, [a,b]⟩, C.output⟩)
    (count : let S := singerLines3
      let N (Q : Finset (Fin 13)) := incidenceInput Q (missLines S Q)
      let ok (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs S C ∧
        ∀ Q, IsQuadrangle S Q → C.eval (N Q) = false
      ∀ C, ok C → 2 ≤ andPairs 26 C →
      let gate := gateAt C
      let isAnd (k : ℕ) := (gate k).op = .and
      let cone := InCone 26 C
      let free (w : ℕ) := 26 ≤ w → ∀ k, isAnd k → k ≠ w-26 ∧ ¬cone k (w-26)
      let edited (k : ℕ) (ws : List ℕ) : Circuit := ⟨C.gates.set k ⟨.and,ws⟩, C.output⟩
      let rows := (quadrangles S).image N
      let val (x : List Bool) (w : ℕ) := (C.wires x).getD w false
      (∀ i j, isAnd i → isAnd j → cone i j →
        (∃ x ∈ rows, val x (26+i) = true) ∧
        (∀ w ∈ (gate i).inputs, ∃ x ∈ rows, (edited i []).eval x = true ∧ val x w = true) ∧
        ∀ a b, a < 26+j → b < 26+j → free a → free b → ¬ok (edited j [a,b])) → 64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → (∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 → x6.size = x3.size → PEqualNP.TopForm.andPairs (26 : ℕ) x3 ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x6) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ (x8 x9 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x8 x9 → ∃ (x13 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x13 ∧ (x3.wires (x1 x13)).getD ((26 : ℕ) + x8) Bool.false = Bool.true) → (64 : ℕ) ≤ x3.size := by
  intro neg good C hC hsize hpairs hn hdirty
  let ok (D : Circuit) := Monotone2 D ∧ ReadsBack 26 D ∧ RightOnIncidentPairs singerLines3 D ∧
    ∀ Q, IsQuadrangle singerLines3 Q → D.eval (neg Q) = false
  have pos (p l : Fin 13) : incidenceInput {p} {l} =
      (List.ofFn fun q : Fin 13 => decide (q = p)) ++
      List.ofFn (fun m : Fin 13 => decide (m = l)) := by
    unfold incidenceInput
    simp only [Finset.mem_singleton]
  have spec (D : Circuit) : ok D ↔ good D := by
    constructor
    · rintro ⟨hm,hr,ha,hq⟩
      exact ⟨hm,hr,fun p l h => (pos p l) ▸ ha l p h,hq⟩
    · rintro ⟨hm,hr,ha,hq⟩
      exact ⟨hm,hr,fun l p h => (pos p l).symm ▸ ha p l h,hq⟩
  have okC := (spec C).2 hC
  apply count C okC hn
  intro i j hi hj hc
  have hlen : i < C.size := by
    by_contra h
    have hgate : (gateAt C i).op = .or := by
      change (C.gates.getD i _).op = .or
      rw [List.getD_eq_default _ _ (show C.gates.length ≤ i by exact Nat.le_of_not_gt h)]
    exact GateOp.noConfusion (hi.symm.trans hgate)
  have hrow (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
      neg Q ∈ (quadrangles singerLines3).image neg := by
    apply Finset.mem_image_of_mem
    change Q ∈ (Finset.univ.powersetCard 4).filter (fun P => ∀ l : Fin 13, (P ∩ singerLines3 l).card ≤ 2)
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
      true_and]
    exact hQ
  refine ⟨?_,?_,?_⟩
  · obtain ⟨Q,hQ,hv⟩ := hdirty i j hi hj hc
    exact ⟨neg Q,hrow Q hQ,hv⟩
  · intro w hw
    obtain ⟨Q,hQ,ht,hwv,hiv⟩ := operand C okC (fun D hD => hsize D ((spec D).1 hD)) i hlen hi w hw
    exact ⟨neg Q,hrow Q hQ,ht,hwv⟩
  · exact replacement C okC (fun D hD => hpairs D ((spec D).1 hD)) i j ⟨hi,hj,hc⟩
