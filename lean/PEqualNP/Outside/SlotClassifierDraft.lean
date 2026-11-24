import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.SlotClassifierDraft_aux

-- Gate deletion and raw input-slot counting are adapted from L-meta-1975 (Apache-2.0).

-- Gate deletion and evaluation agreement adapted from the upstream L-meta-522 proof.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))


private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega


private lemma deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
    (x : List Bool) (hx : x.length = m) :
    ∀ i < m + C.gates.length, i ≠ m + j →
      ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length, i ≠ m + j →
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
          (substWire (m + j) 0 i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop]
    exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
  have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
      w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
      (∀ g ∈ gs, (m + j) ∉ g.inputs) →
      (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
      ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
        (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
          (wiresFrom gs w₁').getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁' w₂' _ _ _ hag i hi hne
      exact hag i hi hne
    | cons g rest ih =>
      intro w₁' w₂' hlen' hk' hnod hag'
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
          (g.inputs.map fun i => w₁'.getD i false) := by
        simp only [substGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply]
        have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
        by_cases hlt : i < w₁'.length
        · exact hag' i hlt hne
        · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
            unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
      rw [hmap]
      apply ih _ _ (by simp [hlen']) (by simp; omega)
        (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
      intro i hi hne
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w₁'.length
      · have hsublt : substWire (m + j) 0 i < w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
        exact hag' i hlt hne
      · have hieq : i = w₁'.length := by omega
        have hsubeq : substWire (m + j) 0 i = w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
        rfl
  intro i hi hne
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
  intro u hu hune
  have hlt : u < m + j := by omega
  simp only [substWire, hlt, ↓reduceIte]
  rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

private lemma deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ m + j)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
    by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
  intro x
  show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
  · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
      rw [deleteGate_len m C j 0 hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
        m + (deleteGate m C j 0).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
private def slots (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

private lemma gateSlotBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g tail ih =>
    have hg := h g List.mem_cons_self
    have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private lemma countBound (xs : List ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, xs.count i ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

private lemma essentialSlot {n : ℕ} (C : Circuit) (a : Fin n)
    (dep : ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
    (a : ℕ) ∈ slots C := by
  obtain ⟨x, y, hagree, hne⟩ := dep
  by_contra hn
  have hout : C.output ≠ (a : ℕ) := by
    intro he
    exact hn (by simp [slots, he])
  have noRead : ∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ ({↑a} : Set ℕ) := by
    intro g hg i hi hia
    have hi' : i = (a : ℕ) := hia
    exact hn (by apply List.mem_cons_of_mem; exact List.mem_flatMap.mpr ⟨g,hg,hi' ▸ hi⟩)
  apply hne
  apply (wiresFrom_agree C.gates ({↑a} : Set ℕ) (List.ofFn x) (List.ofFn y)
    (by simp) (by simp) ?_ noRead).2 C.output hout
  intro i hi
  by_cases h : i < n
  · rw [ofFn_getD_lt _ _ _ h, ofFn_getD_lt _ _ _ h]
    exact hagree _ (fun he => hi (congrArg Fin.val he))
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma internalSlot {n : ℕ} (C : Circuit) (hC : FanInTwo C)
    (hmin : ∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s)
    (i : ℕ) (hi : i < C.gates.length) : n+i ∈ slots C := by
  by_contra hn
  have hout : C.output ≠ n+i := fun e => hn (by simp [slots,e])
  have hno : ∀ j, (hj : j < C.gates.length) → i < j → n+i ∉ C.gates[j].inputs := by
    intro j hj _ hm
    exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_,List.getElem_mem hj,hm⟩))
  have bad := hmin _ (deleteDeadGate C hC i hi hout hno)
  change C.gates.length ≤ C.gates.length - 1 at bad
  omega



theorem smallTriangleCover {n : ℕ} (H : SimpleGraph (Fin n)) (B : Finset (Fin n))
    (triangle : ∀ a b c, H.Adj a b → H.Adj b c → ¬H.Adj c a)
    (ends : ∀ u v, H.Adj u v → u ∈ B)
    (deg : ∀ v ∈ B, (H.neighborSet v).ncard ≤ 3) :
    ∃ T : Finset (Fin n), (∀ u v, H.Adj u v → u ∈ T ∨ v ∈ T) ∧ 3*T.card ≤ 2*B.card := by
  classical
  let independent (I : Finset (Fin n)) := ∀ u ∈ I, ∀ v ∈ I, ¬ H.Adj u v
  let family := B.powerset.filter independent
  have h0 : ∅ ∈ family := by simp [family, independent]
  obtain ⟨I, hi, hbest⟩ := family.exists_max_image Finset.card ⟨_,h0⟩
  have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hi).1
  have hfree := (Finset.mem_filter.mp hi).2
  have dominates : B ⊆ I.biUnion (fun v => insert v (H.neighborFinset v)) := by
    intro u hu
    by_cases hui : u ∈ I
    · exact Finset.mem_biUnion.mpr ⟨u,hui,Finset.mem_insert_self ..⟩
    · by_contra hn
      have hnbr (v : Fin n) (hv : v ∈ I) : ¬H.Adj v u := by
        intro h
        exact hn <| Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_insert_of_mem (by simpa using h)⟩
      have hf' : independent (insert u I) := by
        intro a ha b hb e
        rcases Finset.mem_insert.mp ha with ea | ha <;> rcases Finset.mem_insert.mp hb with eb | hb
        · exact e.ne (ea.trans eb.symm)
        · exact hnbr b hb (ea ▸ e.symm)
        · exact hnbr a ha (eb ▸ e)
        · exact hfree a ha b hb e
      have h' : insert u I ∈ family := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.insert_subset hu hsub), hf'⟩
      have h := hbest (insert u I) h'
      rw [Finset.card_insert_of_notMem hui] at h
      omega
  let D := B \ I
  let neigh (d : Fin n) := I.filter (fun i => H.Adj i d)
  let P := D.filter fun d => (neigh d).card = 1
  have hasN (d : Fin n) (hd : d ∈ D) : (neigh d).Nonempty := by
    obtain ⟨i,hi,h⟩ := Finset.mem_biUnion.mp (dominates (Finset.mem_sdiff.mp hd).1)
    rcases Finset.mem_insert.mp h with he | he
    · exact False.elim ((Finset.mem_sdiff.mp hd).2 (he ▸ hi))
    · exact ⟨i,Finset.mem_filter.mpr ⟨hi,by simpa using he⟩⟩
  have privateN (d : ↥P) : ∃ i ∈ I, H.Adj i d ∧ ∀ j ∈ I, H.Adj j d → j = i := by
    have one := (Finset.mem_filter.mp d.property).2
    obtain ⟨i,hi,unique⟩ := Finset.card_eq_one_iff_existsUnique.mp one
    obtain ⟨hi',hadj⟩ := Finset.mem_filter.mp hi
    exact ⟨i,hi',hadj,fun j hji hj => unique j (Finset.mem_filter.mpr ⟨hji,hj⟩)⟩
  choose lab inI touches onlyI using privateN
  let charge (d : ↥P) : ↥I := ⟨lab d,inI d⟩
  have inj : Function.Injective charge := by
    intro d e hs
    by_contra hne
    have de : (d : Fin n) ≠ e := fun eq => hne (Subtype.ext eq)
    have shared : lab d = lab e := congrArg Subtype.val hs
    have nd := Finset.mem_sdiff.mp (Finset.mem_filter.mp d.property).1
    have ne := Finset.mem_sdiff.mp (Finset.mem_filter.mp e.property).1
    have dNe : ¬ H.Adj d e := fun de' => triangle (lab d) d e (touches d) de' (shared ▸ (touches e).symm)
    let J := I.erase (lab d)
    have dJ (i : Fin n) (hi : i ∈ J) : ¬ H.Adj i d := by
      obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hi
      exact fun h => hne (onlyI d i hin h)
    have eJ (i : Fin n) (hi : i ∈ J) : ¬ H.Adj i e := by
      obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hi
      exact fun h => hne ((onlyI e i hin h).trans shared.symm)
    have insertFree (S : Finset (Fin n)) (w : Fin n) (hf : independent S)
        (away : ∀ i ∈ S, ¬ H.Adj i w) : independent (insert w S) := by
      intro a ha b hb edge
      rcases Finset.mem_insert.mp ha with ea | ha <;> rcases Finset.mem_insert.mp hb with eb | hb
      · exact edge.ne (ea.trans eb.symm)
      · exact away b hb (ea ▸ edge.symm)
      · exact away a ha (eb ▸ edge)
      · exact hf a ha b hb edge
    have freeJ : independent J := fun u hu v hv => hfree u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv)
    have good := insertFree (insert (d:Fin n) J) (e:Fin n) (insertFree J d freeJ dJ) (by
      intro i hi
      rcases Finset.mem_insert.mp hi with eq | hj
      · exact eq ▸ dNe
      · exact eJ i hj)
    have subJ : J ⊆ B := (Finset.erase_subset ..).trans hsub
    have member : insert (e:Fin n) (insert (d:Fin n) J) ∈ family := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.insert_subset ne.1 (Finset.insert_subset nd.1 subJ)),good⟩
    have h := hbest _ member
    have dn : (d : Fin n) ∉ J := fun hd => nd.2 (Finset.mem_of_mem_erase hd)
    have en : (e : Fin n) ∉ J := fun he => ne.2 (Finset.mem_of_mem_erase he)
    rw [Finset.card_insert_of_notMem (by simp [de.symm,en]),Finset.card_insert_of_notMem dn] at h
    have hj : J.card + 1 = I.card := Finset.card_erase_add_one (inI d)
    omega
  have smallP : P.card ≤ I.card := by simpa using Fintype.card_le_of_injective charge inj
  let score (i d : Fin n) : ℕ := if H.Adj i d then 1 else 0
  have dscore (d : Fin n) : (neigh d).card = ∑ i ∈ I, score i d := by simp [neigh,score,Finset.sum_boole]
  have iscore (i : Fin n) (hi : i ∈ I) : (∑ d ∈ D, score i d) ≤ 3 := by
    have sub : D.filter (fun d => H.Adj i d) ⊆ H.neighborFinset i := by
      intro d hd
      exact (H.mem_neighborFinset i d).mpr ((Finset.mem_filter.mp hd).2)
    have hd := deg i (hsub hi)
    simpa [score,Finset.sum_boole,SimpleGraph.ncard_neighborSet] using
      (Finset.card_le_card sub).trans (show (H.neighborFinset i).card ≤ 3 by simpa using hd)
  have upper : (∑ d ∈ D, (neigh d).card) ≤ 3 * I.card := by
    simp_rw [dscore]
    rw [Finset.sum_comm]
    have h := Finset.sum_le_sum iscore
    simpa [Nat.mul_comm] using h
  have atLeast (d : Fin n) (hd : d ∈ D) : 2 ≤ (neigh d).card + (if d ∈ P then 1 else 0) := by
    have pos := Finset.card_pos.mpr (hasN d hd)
    by_cases hp : d ∈ P
    · simp only [hp,↓reduceIte]; omega
    · have hn : (neigh d).card ≠ 1 := fun h => hp (Finset.mem_filter.mpr ⟨hd,h⟩)
      simp only [hp,↓reduceIte]; omega
  have aggregate := Finset.sum_le_sum atLeast
  have psub : P ⊆ D := Finset.filter_subset ..
  have peq : D.filter (fun d => d ∈ P) = P := by ext d; simp only [Finset.mem_filter]; exact ⟨And.right,fun h => ⟨psub h,h⟩⟩
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Finset.sum_boole,peq] at aggregate
  change D.card * 2 ≤ (∑ d ∈ D, (neigh d).card) + P.card at aggregate
  refine ⟨B \ I, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ I
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨ends v u huv.symm,fun hv => hfree u hu v hv huv⟩)
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨ends u v huv,hu⟩)
  · have h := Finset.card_sdiff_add_card_eq_card hsub
    change D.card + I.card = B.card at h
    change 3 * D.card ≤ 2 * B.card
    omega




theorem girth_no_tri {n : ℕ} (G : SimpleGraph (Fin n))
     (girth : ∀ v (q : G.Walk v v), q.IsCycle → 7 ≤ q.length) :
    ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a := by
  intro a b c ab bc ca
  let p : G.Walk a a := .cons ab (.cons bc (.cons ca .nil))
  have cyc : p.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [p,SimpleGraph.Walk.isPath_def, bc.ne,ca.ne,ab.ne.symm]
    · exact le_rfl
  have seven := girth a p cyc
  change 7 ≤ 3 at seven
  omega


end PEqualNP.Outside.SlotClassifierDraft_aux

open PEqualNP.Outside.SlotClassifierDraft_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Structural classification of an undersized minimum circuit on a punctured cubic graph.
theorem PEqualNP.Outside.SlotClassifierDraft :
∀ (x1 x2 : ℕ) (x3 x4 : SimpleGraph (Fin x1)) [x5 : DecidableRel x4.Adj] (x6 : Finset (Fin x1)) (x7 : Fin x1) (x8 : PEqualNP.CircuitLowerBounds.Circuit),   have x9 : Finset (Fin x1) := x6ᶜ.erase x7;   have x10 : ℕ → ℕ := fun (x10 : ℕ) => List.count x10 (x8.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x8.gates);   have x11 : ℕ := ∑ x11 ∈ x9, (x10 ↑x11 - (2 : ℕ)) + ∑ x11 ∈ Finset.range x8.size, (x10 (x1 + x11) - (1 : ℕ)) + ((2 : ℕ) * x8.size - (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x8.gates).length);   x4 = x3.deleteEdges (x3.incidenceSet x7) → (∀ x13 ∉ x6, (x3.neighborSet x13).ncard = (3 : ℕ)) → (∀ (x14 : Fin x1) (x15 : x3.Walk x14 x14), x15.IsCycle → (7 : ℕ) ≤ x15.length) → (∀ (x15 x16 : Fin x1), x3.Adj x15 x16 → x15 ∉ x6) → x7 ∉ x6 → (∀ (x17 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x4 x17 → x2 ≤ x17.card) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 x6 → ¬x6.card + x4.edgeSet.ncard + x2 ≤ x8.size + (1 : ℕ) → (∃ x21 ∈ x9, x10 ↑x21 = (1 : ℕ)) ∨ (∀ x21 ∈ x9, (2 : ℕ) ≤ x10 ↑x21) ∧ (6 : ℕ) * x11 + (9 : ℕ) < x9.card := by
  classical
  intro n k G H _ A z C B cnt' excess' hH deg girth ends hz demand minC hvalue under
  subst H
  let H := G.deleteEdges (G.incidenceSet z)
  let f := circuitFun n C
  have hfun : circuitFun n C = f := rfl
  have fan := minC.1
  have hmin (s) (h : HasCircuitSize n f s) : C.size ≤ s := by
    obtain ⟨D,hD,hd,ev⟩ := h
    exact (minC.2 D hD (funext ev)).trans hd
  have spec (x : Fin n → Bool) : f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ u v, H.Adj u v ∧ x u = true ∧ x v = true := by
    change circuitFun n C x = true ↔ _
    rw [hvalue]
    simp [graphFun,H]
  have memB (v : Fin n) : v ∈ B ↔ v ∉ A ∧ v ≠ z := by simp [B,and_comm]
  have endsH (u v : Fin n) (h : H.Adj u v) : u ∈ B :=
    (memB u).mpr ⟨ends u v (SimpleGraph.deleteIncidenceSet_adj.mp h).1,
      (SimpleGraph.deleteIncidenceSet_adj.mp h).2.1⟩
  have degH (v : Fin n) (hv : v ∈ B) : (H.neighborSet v).ncard ≤ 3 := by
    rw [← deg v ((memB v).mp hv).1]
    exact Set.ncard_le_ncard (fun u h => (SimpleGraph.deleteIncidenceSet_adj.mp h).1) (Set.toFinite _)
  obtain ⟨T, cover, hT⟩ := smallTriangleCover H B (fun a b c ab bc ca => girth_no_tri G girth a b c
    (SimpleGraph.deleteIncidenceSet_adj.mp ab).1 (SimpleGraph.deleteIncidenceSet_adj.mp bc).1
    (SimpleGraph.deleteIncidenceSet_adj.mp ca).1) endsH degH
  have kBound := demand T cover
  have dA : ∀ v ∈ A, G.degree v = 0 := fun v hv => (G.degree_eq_zero v).mpr (fun u h => ends v u h hv)
  have dB : ∀ v ∈ Aᶜ, G.degree v = 3 := by
    intro v hv
    rw [← G.ncard_neighborSet]
    exact deg v (Finset.mem_compl.mp hv)
  have degreeSum := G.sum_degrees_eq_twice_card_edges
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dB] at degreeSum
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at degreeSum
  have cards : B.card + 1 = Aᶜ.card := Finset.card_erase_add_one (Finset.mem_compl.mpr hz)
  have delE : H.edgeSet.ncard + 3 = G.edgeFinset.card := by
    have hinc : (G.incidenceSet z).ncard = 3 := by
      rw [← SimpleGraph.coe_incidenceFinset, Set.ncard_coe_finset,
        SimpleGraph.card_incidenceFinset_eq_degree, ← SimpleGraph.ncard_neighborSet]
      exact deg z hz
    have h := Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset z) (Set.toFinite _)
    have eqE : G.edgeSet.ncard = G.edgeFinset.card := by rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    change (G.deleteEdges (G.incidenceSet z)).edgeSet.ncard + 3 = G.edgeFinset.card
    rw [SimpleGraph.edgeSet_deleteEdges, ← hinc, h, eqE]
  let cnt (v : Fin n) := (slots C).count v.val
  have marked (a : Fin n) (ha : a ∈ A) : 1 ≤ cnt a := by
    apply List.count_pos_iff.mpr
    apply essentialSlot
    let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = a)
    refine ⟨x,y,fun i hi => by simp [x,y,hi],?_⟩
    rw [hfun]
    have hx : f x ≠ true := by simp [spec,x]
    have hy : f y = true := (spec y).mpr (Or.inl ⟨a,ha,by simp [y]⟩)
    exact fun he => hx (he.trans hy)
  have active (a : Fin n) (ha : a ∈ B) : 1 ≤ cnt a := by
    obtain ⟨han, haz⟩ := (memB a).mp ha
    have hasN : ∃ b, H.Adj a b := by
      by_contra none
      have sub : G.neighborSet a ⊆ ({z} : Set (Fin n)) := by
        intro b hb
        by_contra hn
        exact none ⟨b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hb,haz,by simpa using hn⟩⟩
      have small := Set.ncard_le_ncard sub
      simp [deg a han] at small
    obtain ⟨b, ab⟩ := hasN
    have hb := ((memB b).mp (endsH b a ab.symm)).1
    apply List.count_pos_iff.mpr
    apply essentialSlot
    let x : Fin n → Bool := fun i => decide (i = b)
    let y : Fin n → Bool := fun i => decide (i = b ∨ i = a)
    refine ⟨x,y,fun i hi => by simp [x,y,hi],?_⟩
    rw [hfun]
    have hx : f x ≠ true := by
      intro e
      rcases (spec x).mp e with ⟨i,hi,hit⟩ | ⟨u,v,uv,ut,vt⟩
      · have h : i = b := by simpa [x] using hit
        exact hb (h ▸ hi)
      · have hu : u = b := by simpa [x] using ut
        have hv : v = b := by simpa [x] using vt
        exact uv.ne (hu.trans hv.symm)
    have hy : f y = true := (spec y).mpr (Or.inr ⟨a,b,ab,by simp [y],by simp [y]⟩)
    exact fun he => hx (he.trans hy)
  by_cases h1 : ∃ v ∈ B, cnt v = 1
  · exact Or.inl h1
  have two (v : Fin n) (hv : v ∈ B) : 2 ≤ cnt v := by
    have hp := active v hv
    have hn : cnt v ≠ 1 := fun e => h1 ⟨v,hv,e⟩
    omega
  refine Or.inr ⟨two,?_⟩
  by_contra rare
  have totals (v : Fin n) (hv : v ∈ B) : cnt v = 2 + (cnt v - 2) := by have := two v hv; omega
  have lowerA := Finset.sum_le_sum marked
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at lowerA
  have splitB := Finset.sum_congr rfl totals
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at splitB
  change B.sum cnt = B.card * 2 + (∑ v ∈ B, (cnt v - 2)) at splitB
  have lowerB : ∑ v ∈ B, cnt v ≤ ∑ v ∈ Aᶜ, cnt v := Finset.sum_le_sum_of_subset (Finset.erase_subset ..)
  change B.sum cnt ≤ Aᶜ.sum cnt at lowerB
  have inputSum := A.sum_add_sum_compl cnt
  let allCount := fun i => (slots C).count i
  change _ = ∑ v : Fin n, allCount v.val at inputSum
  rw [Fin.sum_univ_eq_sum_range] at inputSum
  change A.sum cnt + Aᶜ.sum cnt = _ at inputSum
  change A.card ≤ A.sum cnt at lowerA
  have internal (i : ℕ) (hi : i ∈ Finset.range C.gates.length) : 1 ≤ allCount (n+i) :=
    List.count_pos_iff.mpr (internalSlot C fan (by simpa [hfun] using hmin) i (Finset.mem_range.mp hi))
  have decomp (i : ℕ) (hi : i ∈ Finset.range C.gates.length) : allCount (n+i) = 1 + (allCount (n+i)-1) := by
    have := internal i hi
    omega
  have lowerI := Finset.sum_congr rfl decomp
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,mul_one,Finset.card_range] at lowerI
  have cap := countBound (slots C) (Finset.range (n+C.gates.length))
  change ∑ i ∈ Finset.range (n+C.gates.length), allCount i ≤ (slots C).length at cap
  rw [Finset.sum_range_add] at cap
  have len := gateSlotBound C.gates (fun g hg => (fan g hg).2)
  simp only [slots,List.length_cons] at cap
  change ¬ A.card + H.edgeSet.ncard + k ≤ C.gates.length + 1 at under
  change ¬ 6 * ((∑ v ∈ B, (cnt v - 2)) + (∑ i ∈ Finset.range C.gates.length, (allCount (n+i)-1)) +
    (2*C.gates.length - (C.gates.flatMap Gate.inputs).length)) + 9 < B.card at rare
  omega
