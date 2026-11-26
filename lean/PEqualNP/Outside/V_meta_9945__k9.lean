import Mathlib.Tactic.Push
import PEqualNP.Defs

-- Generic live-wire argument adapted from the saved L_meta_7280 proof.
-- This certificate excludes circuits with at most 8 gates on selected rows.
namespace PEqualNP.Outside.V_meta_9945__k9

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem split_at {α : Type} (gs : List α) (p : ℕ) (g : α) (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  have hlt : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
  have hget : gs[p] = g := (List.getElem?_eq_some_iff.1 hp).2
  refine ⟨gs.take p, gs.drop (p + 1), ?_, by simp; omega⟩
  have h1 : gs = gs.take p ++ gs.drop p := (List.take_append_drop p gs).symm
  have h2 : gs.drop p = gs[p] :: gs.drop (p + 1) := List.drop_eq_getElem_cons hlt
  exact h1.trans (by rw [h2, hget])

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def initId (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr (i : ℕ)

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initId n, []) := by
  refine ⟨by simp [initId], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [initId, hlt, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem exists_clean (n : ℕ) (f : BFn n) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) :
    ∃ gs o, CleanL n gs ∧ gs.length ≤ s ∧ o < n + gs.length ∧ ∀ x, val gs n o x = f x := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set acc := elim n C.gates (initId n, []) with hacc
  have hinv : ∀ y : Fin n → Bool, Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ ok (inv_initId n y)
  have hcl : CleanL n acc.2 := by
    apply elim_clean n C.gates (initId n, []) ok
    · intro i
      by_cases hlt : i < n
      · simp [initId, hlt, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initId]; omega)]; trivial
    · intro p g hp; simp at hp
  have hlen : acc.2.length ≤ s := by
    have := elim_len n C.gates (initId n, [])
    rw [← hacc] at this
    simp only [List.length_nil, zero_add] at this
    omega
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    have e1 := ((hinv y).2 C.output).2
    have e2 := ((hinv y').2 C.output).2
    rw [hst] at e1 e2
    have h1 : (wiresFrom C.gates (List.ofFn y)).getD C.output false = f y := hev y
    have h2 : (wiresFrom C.gates (List.ofFn y')).getD C.output false = f y' := hev y'
    rw [← h1, ← h2, ← e1, ← e2]; rfl
  | inr j =>
    have hj : j < n + acc.2.length := by
      obtain ⟨y, _, _⟩ := hnc
      have := ((hinv y).2 C.output).1
      rw [hst] at this
      exact this
    refine ⟨acc.2, j, hcl, hlen, hj, ?_⟩
    intro x
    have e1 := ((hinv x).2 C.output).2
    rw [hst] at e1
    exact e1.trans (hev x)

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

def Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) (t : ℕ) (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 [y] →
    (∀ {s xs zs}, List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a r} (neg save : Bool), P s ((if neg then inv a else a) :: kept save a r) →
      P (s+1) (a :: r)) →
    (∀ {s a b r} (c ka kb : Bool),
      P s ((if c then meet a b else join a b) :: kept ka a (kept kb b r)) →
      P (s+1) (a :: b :: r)) → P t ws

theorem Run.done {α inv meet join y} : @Run α inv meet join y 0 [y] := fun _ d _ _ _ => d

theorem Run.perm {α inv meet join y s xs zs} (p : List.Perm xs zs)
    (h : @Run α inv meet join y s xs) : Run inv meet join y s zs :=
  fun P d q u b => q p (h P d q u b)

theorem Run.one {α inv meet join y s a r} (neg save : Bool)
    (h : @Run α inv meet join y s ((if neg then inv a else a) :: kept save a r)) :
    Run inv meet join y (s+1) (a :: r) := fun P d q u b => u neg save (h P d q u b)

theorem Run.two {α inv meet join y s a b r} (c ka kb : Bool)
    (h : @Run α inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))) :
    Run inv meet join y (s+1) (a :: b :: r) := fun P d q u v => v c ka kb (h P d q u v)

theorem Run.fold {α inv meet join y} {P : ∀ t ws, @Run α inv meet join y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : Run inv meet join y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (one : ∀ {s a r} (neg save : Bool)
      (h : Run inv meet join y s ((if neg then inv a else a) :: kept save a r)),
      P _ _ h → P _ _ (Run.one neg save h))
    (two : ∀ {s a b r} (c ka kb : Bool)
      (h : Run inv meet join y s ((if c then meet a b else join a b) :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two c ka kb h))
    {t ws} (h : Run inv meet join y t ws) : P t ws h := by
  have hex := h (fun s xs => ∃ h' : Run inv meet join y s xs, P s xs h')
    ⟨Run.done, done⟩
    (fun hp ⟨h', ih⟩ => ⟨Run.perm hp h', perm hp h' ih⟩)
    (fun n k ⟨h', ih⟩ => ⟨Run.one n k h', one n k h' ih⟩)
    (fun c a b ⟨h', ih⟩ => ⟨Run.two c a b h', two c a b h' ih⟩)
  exact hex.elim fun _ hp => hp

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h using Run.fold with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

def Reach (n : ℕ) (gs : List Gate) (o a : ℕ) : Prop :=
  ∀ P : ℕ → Prop, P o →
    (∀ q g, gs[q]? = some g → P (n + q) → ∀ u ∈ g.inputs, P u) → P a

theorem reach_self (n : ℕ) (gs : List Gate) (o : ℕ) : Reach n gs o o :=
  fun _ ho _ => ho

theorem reach_step {n : ℕ} {gs : List Gate} {o q u : ℕ} {g : Gate}
    (hq : gs[q]? = some g) (hr : Reach n gs o (n + q)) (hu : u ∈ g.inputs) :
    Reach n gs o u :=
  fun P ho hs => hs q g hq (hr P ho hs) u hu

theorem reach_cases {n : ℕ} {gs : List Gate} {o a : ℕ} (h : Reach n gs o a) :
    a = o ∨ ∃ q g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q) := by
  apply h (fun x => x = o ∨ ∃ q g, gs[q]? = some g ∧ x ∈ g.inputs ∧ Reach n gs o (n + q))
  · exact Or.inl rfl
  · intro q g hq hP u hu
    refine Or.inr ⟨q, g, hq, hu, ?_⟩
    rcases hP with rfl | ⟨q', g', hq', hin', hr'⟩
    · exact reach_self n gs (n + q)
    · exact reach_step hq' hr' hin'

def Live (n : ℕ) (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs ∧ Reach n gs o (n + q)

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live n gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live n gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ_reach (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (hr : Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live n gs o (p + 1) a)) := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases reach_cases hr with h | ⟨q, g', hg', hin, hrq⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin, hrq⟩
        have := cleanG_lt (hcl q g' hg') _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

theorem live_succ_dead (n : ℕ) (gs : List Gate) (o : ℕ)
    (p : ℕ) (hnr : ¬ Reach n gs o (n + p)) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔ a ∈ liveList gs n o p := by
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    have hne : a ≠ n + p := by
      rintro rfl
      rcases hl with rfl | ⟨q, _, g', hg', hin, hrq⟩
      · exact hnr (reach_self n gs _)
      · exact hnr (reach_step hg' hrq hin)
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩
  · rintro ⟨hlt, hl⟩
    refine ⟨by omega, ?_⟩
    rcases hl with h | ⟨q, hq, g', hg', hin, hrq⟩
    · exact Or.inl h
    · by_cases hqp : q = p
      · subst hqp; exact absurd hrq hnr
      · exact Or.inr ⟨q, by omega, g', hg', hin, hrq⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length) :
    ∀ d p, p + d = gs.length →
      ∃ d', d' ≤ d ∧
        Run (invF (n := n)) meetF joinF (val gs n o) d' ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _, _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1; omega
    exact ⟨0, le_rfl, Run.perm (hperm.map (val gs n)) Run.done⟩
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    obtain ⟨d', hd', IH⟩ := ih (p + 1) (by omega)
    by_cases hr : Reach n gs o (n + p)
    · have hstep := live_succ_reach n gs o hcl p g hg hr
      have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
        (mem_liveList _ _ _ _ _).2 ⟨cleanG_lt (hcl p g hg) a ha, Or.inr ⟨p, le_rfl, g, hg, ha, hr⟩⟩
      have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
        Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
      have hvg := val_gate n gs p g hg (cleanG_lt (hcl p g hg))
      have hnd0 := nodup_liveList gs n o p
      have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
          val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
          Run (invF (n := n)) meetF joinF (val gs n o) (d' + 1)
            ((liveList gs n o p).map (val gs n)) := by
        intro j neg hmem hval
        have hj := hin j ((hmem j).2 rfl)
        have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
          List.perm_cons_erase hj
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
            rw [mem_kept]
            rintro (⟨_, h⟩ | h)
            · exact hnew j hj h.symm
            · exact hnew _ (List.mem_of_mem_erase h) rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
            simp only [decide_eq_true_eq]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
                · exact Or.inr (Or.inr ⟨haj, h1⟩)
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hj, fun _ => h1⟩
              · exact Or.inr ⟨h2, fun h => absurd h h1⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        rw [List.map_cons, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
      refine ⟨d' + 1, by omega, ?_⟩
      rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
      · apply single j true
        · intro a; simp [hinp]
        · funext x; rw [hvg x, hop, hinp]; simp [GateOp.eval]
      · by_cases hjk : j = k
        · subst hjk
          apply single j false
          · intro a; simp [hinp]
          · funext x; rw [hvg x, hinp]; rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        · have hjm := hin j (by simp [hinp])
          have hkm := hin k (by simp [hinp])
          have hke : k ∈ (liveList gs n o p).erase j :=
            (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
          have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
          have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
          have hp1 : (liveList gs n o p).Perm
              (j :: k :: ((liveList gs n o p).erase j).erase k) :=
            (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
          have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
              a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
            intro a; rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
          have hp2 : (liveList gs n o (p + 1)).Perm
              ((n + p) :: kept (decide (Live n gs o (p + 1) j)) j
                (kept (decide (Live n gs o (p + 1) k)) k
                  (((liveList gs n o p).erase j).erase k))) := by
            refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
            · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
              · rw [mem_kept, mem_kept]
                rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
                · exact hnew j hjm h.symm
                · exact hnew k hkm h.symm
                · exact hnew _ ((hmr _).1 h).2.2 rfl
              · rw [hmr]; simp
              · rw [mem_kept, hmr]
                rintro (⟨_, h⟩ | h)
                · exact hjk h
                · exact h.2.1 rfl
            · intro a
              rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
              simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
              constructor
              · rintro (h | ⟨h1, h2⟩)
                · exact Or.inl h
                · by_cases haj : a = j
                  · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                  · by_cases hak : a = k
                    · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                    · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
              · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
                · exact Or.inl h
                · exact Or.inr ⟨hjm, fun _ => h1⟩
                · exact Or.inr ⟨hkm, fun _ => h1⟩
                · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
          have IH' := Run.perm (hp2.map (val gs n)) IH
          have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
              then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
            funext x; rw [hvg x, hinp]
            rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
          rw [List.map_cons, kept_map, kept_map, hval] at IH'
          exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')
    · have hp : (liveList gs n o (p + 1)).Perm (liveList gs n o p) :=
        (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) (nodup_liveList _ _ _ _)).2
          (live_succ_dead n gs o p hr)
      exact ⟨d', by omega, Run.perm (hp.map (val gs n)) IH⟩

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  obtain ⟨gs, o, hcl, hlen, ho, hev⟩ := exists_clean n f s hnc h
  obtain ⟨d', hd', hrun⟩ := run_live n gs o hcl ho gs.length 0 (by omega)
  refine ⟨d', by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact hrun

theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h using Run.fold with
  | done => simp
  | perm hp _ ih => rwa [← hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha, hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha, hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask, lo, Nat.testBit_two_pow_sub_one, show i < k+k by omega, show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

theorem keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl, ?_⟩
  apply List.any_eq_true.2 ⟨neg, by cases neg <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht, hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a, ha, ?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b, hb, ?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab, ?_⟩
  apply List.any_eq_true.2 ⟨conj, by cases conj <;> simp, ?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj := conj) (ka := kb) (kb := ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h using Run.fold with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or, Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih => simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal, lo, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hi, show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo, Nat.testBit_two_pow_sub_one, hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers, he, required_up h he]
  · simp [covers, he, required h]

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h using Run.fold with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;>
      first | (grw [← Nat.add_assoc, ← hand]; exact ih')
            | (grw [← Nat.add_assoc, ← hor]; exact ih')

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6, Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6, Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl, Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def bsr (T w h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if fld T w ((lo + hi) / 2) ≤ h then bsr T w h f ((lo + hi) / 2) hi
       else bsr T w h f lo ((lo + hi) / 2))
    else lo

def hw (w : Nat) : Nat := (w % 11400714819323198549 + 317) ^ 3 % 11400714819323198549 + 1

def hz : List Nat → Nat
  | [] => 0
  | w :: t => hw w + hz t

def hk (zs : List Nat) : Nat := hz zs % 4294967291

def found (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (s : Nat) (zs : List Nat) : Bool :=
  decide (idx s zs < N s) && zs.isPerm (S s (idx s zs))

def scr (k s : Nat) (pool : List Nat) (zs : List Nat) : Bool :=
  zs.length == s + 1 && pool.any (scoreCheck k s zs)

theorem scr_no {k s : Nat} (pool : List Nat) {zs : List Nat}
    (h : NatRun (mask k) (goal k) s zs) : scr k s pool zs = false := by
  unfold scr
  rw [Bool.and_eq_false_iff]
  right
  rw [List.any_eq_false]
  intro x _
  rw [scoreCheck_no h x]
  simp

def bar (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat) (idx : Nat → List Nat → Nat)
    (ori : List Nat → List Nat) (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s + 1, i =>
    let ws := S (s + 1) i
    !(next (mask k) (s + 2 - ws.length) ws fun _ zs =>
        covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs)))

theorem bar_sound {k S N idx ori pool} {s i : Nat} (hb : bar k S N idx ori pool s i = true)
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [bar, zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (_ : Nat) (zs : List Nat) :=
      covers k s zs && !(scr k s pool zs) && !(found S N idx s (ori zs))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F, covers_ok hz, scr_no pool hz, Bool.not_false, Bool.true_and, found]
      simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq]
      intro hj
      by_contra! hp
      have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
      exact hn s (by omega) _ hj (Run.perm p (hr hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem bar_all {k S N idx ori pool} {cap : Nat}
    (hr : ∀ {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (ori ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, bar k S N idx ori pool s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q, hq, j, hj, h⟩ := bar_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h

def mv (m c : Nat) (ws : List Nat) : List Nat :=
  let a := ws.getD (c % 16) 0
  let b := ws.getD (c / 16 % 16) 0
  let op := c / 256 % 4
  let r := if op < 2 then ws.erase a else (ws.erase a).erase b
  (if op = 0 then a else if op = 1 then a ^^^ m else if op = 2 then a &&& b else a ||| b) ::
    kept (decide (c / 1024 % 2 = 1)) a (kept (decide (2 ≤ op ∧ c / 2048 % 2 = 1)) b r)

def StGen (k : Nat) (xs : List Nat) (PT : Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fld (PT s) 32 j
    mv (mask k) (e % 4096) (StGen k xs PT d (s + 1) (e / 4096))

def Sgen (k cap : Nat) (xs : List Nat) (PT : Nat → Nat) (s j : Nat) : List Nat :=
  StGen k xs PT (cap - s) s j

def idxGen (NN HT : Nat → Nat) (s : Nat) (zs : List Nat) : Nat :=
  bsr (HT s) 32 (hk zs) 24 0 (NN s)

theorem prove_base (n k cap : ℕ) (f : BFn n) (rows xs pool : List ℕ)
    (NN HT PT : ℕ → ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hlen : rows.length = k + k)
    (hxs : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun a => encL a rows) = xs)
    (hgoal : encL f rows = goal k)
    (hprop : ∀ zs ∈ xs.sublists, zs ≠ xs → (cov k zs &&& lo k) ≠ lo k)
    (hNcap : 0 < NN cap)
    (hchk : ∀ s ≤ cap, ∀ i < NN s,
      bar k (Sgen k cap xs PT) NN (idxGen NN HT) id pool s i = true) :
    ∀ s : ℕ, HasCircuitSize n f s → cap + 1 ≤ s := by
  intro s h
  by_contra hlt
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run f hnc s h
  have hmask : mask k = 2 ^ rows.length - 1 := by rw [hlen]; rfl
  have hr : NatRun (mask k) (encL f rows) s' (ws.map fun a => encL a rows) :=
    Run.map (fun a : BFn n => encL a rows)
      (fun a => by rw [hmask]; exact encL_inv a rows)
      (fun a b => encL_and a b rows) (fun a b => encL_or a b rows) hrun
  rw [hgoal] at hr
  have hsub' : (ws.map fun a => encL a rows).Sublist xs := by
    rw [← hxs]; exact hsub.map _
  by_cases he : (ws.map fun a => encL a rows) = xs
  · rw [he] at hr
    cases hxs_nil : xs with
    | nil =>
      rw [hxs_nil] at hr
      have hc := required hr
      have hne : cov k [] = 0 := rfl
      rw [hne] at hc
      have hlo : lo k ≠ 0 := by
        cases k with
        | zero =>
          simp [goal, lo] at hgoal
          obtain ⟨y, y', hne'⟩ := hnc
          have h0 : rows.length = 0 := hlen
          have hnil : rows = [] := List.eq_nil_of_length_eq_zero h0
          rw [hnil] at hxs
          have hxs0 : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)).map (fun _ => 0) = [] := by
            simpa [encL, hxs_nil] using hxs
          have hn0 : n = 0 := by simpa using congrArg List.length hxs0
          subst hn0
          exact absurd (Subsingleton.elim y y') (fun e => hne' (e ▸ rfl))
        | succ k' =>
          simp only [lo]
          have : 1 ≤ 2 ^ k' := Nat.one_le_two_pow
          rw [pow_succ]; omega
      simp at hc
      exact hlo hc.symm
    | cons a r =>
      rw [hxs_nil] at hr
      have hcap : NatRun (mask k) (goal k) cap (a :: r) := extend_run hr (by omega)
      rw [← hxs_nil] at hcap
      have hS0 : Sgen k cap xs PT cap 0 = xs := by simp [Sgen, StGen]
      rw [← hS0] at hcap
      exact bar_all (fun h => h) hchk cap le_rfl 0 hNcap hcap
  · exact hprop _ (List.mem_sublists.2 hsub') he (required hr)



open PEqualNP.MetaComplexity

def targetFn (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4278124270 * 2 ^ 32 + 4277862024)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def packWords (words : List ℕ) : ℕ := words.foldr (fun word rest => word ||| (rest <<< 32)) 0

def inputMasks : List ℕ := [(packWords [4278190335, 0, 1392508928, 1397969747, 1397969747, 21331]), (packWords [65280, 4278190335, 2231369728, 2240120197, 2240120197, 34181]), (packWords [4294901760, 255, 671153920, 673720360, 673720360, 10280]), (packWords [0, 65280, 251592704, 235802126, 235802126, 3598]), (packWords [0, 4294901760, 822018048, 808464432, 808464432, 12336]), (packWords [0, 0, 3238002687, 3233857728, 3233857728, 49344])]
def sampleRows : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 8, 8, 8, 8, 8, 8, 8, 8, 16, 16, 16, 16, 16, 16, 16, 16, 18, 18, 18, 18, 18, 18, 18, 18, 32, 32, 32, 32, 32, 32, 32, 32, 36, 36, 36, 36, 36, 36, 36, 36, 56, 56, 56, 56, 56, 56, 56, 56, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34, 3, 9, 10, 12, 17, 20, 33, 34]
def stateCount : ℕ → ℕ
  | 8 => 1
  | 7 => 61
  | 6 => 805
  | 5 => 761
  | 4 => 289
  | 3 => 53
  | 2 => 9
  | _ => 0
def stateHash : ℕ → ℕ
  | 8 => packWords [3903145210]
  | 7 => packWords [27872872, 53933119, 86419942, 320348705, 389789393, 431957181, 633013938, 643605771, 711904085, 777581724, 796457437, 855923253, 883232604, 893335544, 998205784, 1029948234, 1129404320, 1147905614, 1197065295, 1201081719, 1304865202, 1405186400, 1467656313, 1476447807, 1619959392, 1651314939, 1699748926, 1804166605, 1818634827, 1870178058, 2193911765, 2241519871, 2650623426, 2694893067, 2759688328, 2774156550, 2803475092, 2863670764, 2945111733, 3205698071, 3326376230, 3345016774, 3345246037, 3406754828, 3473330287, 3499652111, 3551322614, 3570198327, 3623198306, 3626517377, 3652926544, 3681853305, 3808663970, 3823132192, 3888676988, 3903145210, 3914722820, 3922442173, 4055996876, 4058882636, 4196048744]
  | 6 => packWords [6406924, 9493576, 14456946, 16446484, 25496105, 27872872, 36240284, 36689771, 40172307, 40401801, 41426577, 50708506, 52343418, 53933119, 56818879, 71914757, 76119409, 80134585, 86419942, 99010298, 116971593, 125665177, 125753808, 127155133, 140133399, 146345049, 152664616, 153979454, 157009488, 158476114, 159430362, 166994444, 171370843, 175876542, 179706298, 185785465, 185851353, 189872137, 195888405, 197821014, 197843193, 201521765, 202333846, 208552719, 215134529, 223926023, 239031818, 240112672, 240335687, 240483137, 242157368, 243048242, 248723654, 265390756, 266665150, 277209566, 279368689, 282396545, 285448188, 286908437, 291783175, 296049978, 300067055, 300758645, 302524826, 315203239, 320348705, 331569980, 332501095, 349336347, 351472991, 356221032, 359398534, 361316172, 363658867, 367437608, 370689254, 379323476, 387386556, 389789393, 391426836, 392593151, 407536995, 419577499, 421252808, 431957181, 441445411, 447152923, 448901644, 450458475, 455144386, 456579110, 463369866, 466547810, 469442420, 471232385, 490554353, 495449305, 497634820, 499618156, 501280322, 503634580, 507422814, 507858057, 509622836, 514167838, 515609422, 518414330, 519044057, 522326279, 527428232, 528014674, 531135504, 531410008, 535351107, 540888254, 546725195, 547119500, 550285721, 551644821, 557655776, 561587722, 563592753, 566113043, 570760266, 586470473, 591145241, 599555013, 603285700, 607358825, 607418063, 607996052, 615343428, 617656274, 633013938, 643605771, 648300971, 655174696, 660274480, 661742498, 661925915, 683158448, 691092684, 693281462, 696868924, 697626670, 700216275, 701573934, 703924113, 707739261, 709392719, 711904085, 723366512, 729517747, 732705265, 737834734, 741189398, 741715449, 746346817, 757879684, 760815039, 769262723, 770209174, 777581724, 779000668, 788751364, 790210134, 791106920, 795274094, 796457437, 799343197, 805169113, 808026362, 808474820, 841247110, 843944350, 846133128, 849450121, 852567233, 853334766, 855923253, 856775779, 858764968, 860601350, 860602009, 867958710, 868770789, 874758558, 880264328, 883232604, 893335544, 896637662, 898765622, 921871544, 922512253, 928812006, 941389981, 944069712, 953042606, 953867800, 954910003, 957559114, 971918319, 975189652, 982923931, 988998087, 994631181, 995570834, 998205784, 1002301787, 1006186432, 1010453746, 1019819883, 1021622455, 1021671376, 1024918298, 1029948234, 1042188877, 1051287937, 1062497459, 1081663672, 1093476611, 1103147951, 1104783654, 1106719466, 1112531211, 1113052426, 1121187688, 1121847794, 1123569010, 1125027921, 1129404320, 1143792807, 1147905614, 1151888971, 1154924557, 1163459727, 1172671549, 1172730919, 1176136138, 1179120272, 1197065295, 1201081719, 1203358544, 1212798175, 1213950377, 1216865800, 1224852184, 1230996121, 1235878288, 1243604019, 1247821840, 1255102915, 1262290062, 1264917561, 1267735601, 1269348943, 1271879266, 1277517986, 1283486394, 1286271024, 1299492343, 1304865202, 1322244445, 1323665471, 1325605355, 1340024989, 1344209303, 1345066038, 1347926330, 1359429574, 1361474627, 1364006088, 1366094441, 1366802043, 1371368035, 1373787676, 1375246587, 1375334906, 1394011473, 1405186400, 1416360265, 1426391123, 1439302159, 1442371283, 1450342798, 1463124700, 1466812231, 1467656313, 1468163073, 1476447807, 1477870496, 1485687944, 1495998934, 1496464626, 1507166544, 1510177731, 1518355462, 1521634766, 1530719977, 1537231175, 1538687923, 1539946374, 1544072732, 1550953308, 1558474870, 1562853359, 1566217928, 1566661478, 1574958551, 1577321581, 1590231154, 1597768736, 1610280376, 1611148980, 1619735908, 1619959392, 1634553983, 1639585033, 1650771280, 1651314939, 1659205790, 1662911566, 1668454487, 1675476053, 1682388671, 1692589949, 1693017973, 1699748926, 1709833161, 1711326536, 1719069594, 1724153587, 1728417581, 1734617443, 1736859590, 1741821677, 1743518088, 1745129489, 1785104213, 1785517140, 1790165040, 1791972514, 1800595090, 1801654851, 1801732455, 1804166605, 1807052365, 1812298433, 1813009576, 1815416000, 1816123073, 1816380007, 1818634827, 1825344072, 1829884222, 1832792035, 1845441615, 1855486352, 1869177826, 1870178058, 1872699392, 1876567411, 1883646048, 1889697275, 1889803699, 1892451053, 1894809001, 1894944212, 1901819488, 1905637287, 1908572988, 1918660456, 1928763396, 1953176287, 1965150099, 1977805511, 1978636247, 1992652460, 1997445928, 2024291206, 2037491618, 2038722690, 2047795878, 2052636409, 2053926770, 2062241189, 2073854446, 2076709411, 2079757952, 2085478114, 2092494990, 2092724253, 2101315417, 2106027953, 2111538361, 2120356588, 2124726622, 2129556962, 2132857724, 2142669719, 2145504126, 2150985439, 2154233044, 2161506853, 2163081592, 2166223625, 2168726819, 2174899277, 2177990949, 2189326008, 2193911765, 2194295321, 2206595894, 2206778436, 2210951385, 2212820727, 2213978600, 2220808503, 2224844782, 2239313004, 2241519871, 2247130327, 2247664594, 2247934214, 2251314104, 2264390027, 2277766168, 2289414200, 2296876850, 2298800830, 2309974451, 2317676543, 2337754665, 2340261879, 2340293054, 2348420081, 2368342753, 2370676522, 2373995593, 2377953947, 2386983297, 2387212560, 2387779967, 2392723881, 2393574857, 2396597369, 2397257297, 2400404760, 2411065591, 2422333954, 2425117943, 2425761258, 2429331521, 2441209667, 2441315802, 2454020326, 2456441664, 2456814560, 2459337593, 2472115384, 2488807163, 2494209646, 2494811519, 2515296810, 2521666858, 2523528188, 2524401050, 2524985929, 2534423405, 2541618634, 2556142186, 2559547578, 2563415278, 2564151663, 2570610408, 2571180262, 2578612924, 2581172910, 2583723860, 2590022827, 2593289137, 2612164850, 2612189259, 2628929091, 2636155204, 2643793523, 2647569635, 2647798898, 2650623426, 2659376808, 2662201036, 2665164829, 2668483900, 2669920389, 2673115372, 2675792840, 2679797091, 2694893067, 2699855154, 2709408143, 2719761894, 2723819828, 2734024576, 2735176778, 2752222522, 2759688328, 2760681278, 2766637732, 2774156550, 2775883148, 2802204972, 2802776505, 2803475092, 2803971153, 2806360852, 2814142691, 2832054885, 2839594457, 2840241493, 2848070468, 2850630493, 2854062679, 2863670764, 2866292439, 2883583379, 2889243306, 2890712483, 2900205596, 2905605910, 2915425754, 2921385910, 2926369624, 2929070238, 2929893976, 2930643511, 2933953414, 2936472564, 2945111733, 2947277555, 2949173656, 2950940786, 2955479405, 2956436021, 2956689343, 2959626809, 2964408696, 2970067401, 2974803611, 2975732984, 2984406166, 2993429347, 2994658124, 3000308241, 3011589143, 3013155510, 3022464544, 3028004602, 3029692854, 3031619687, 3041761507, 3063069410, 3067060084, 3070318379, 3074494938, 3087553476, 3088944129, 3093689512, 3096378626, 3097963399, 3101847486, 3111216831, 3125685053, 3128865449, 3135784636, 3137399757, 3139030970, 3139801060, 3140718828, 3147987668, 3160122456, 3165167726, 3189191975, 3189680888, 3191229849, 3200942618, 3205071387, 3205698071, 3207464252, 3208214482, 3210662253, 3217275681, 3224995034, 3233399468, 3238015267, 3240288700, 3252398573, 3263374176, 3264744489, 3268007928, 3268627401, 3271375710, 3276947723, 3279133016, 3288636302, 3290251423, 3293570494, 3302636581, 3308428482, 3313288076, 3316646675, 3322958856, 3324523221, 3326376230, 3326741810, 3333121293, 3345016774, 3345246037, 3346384837, 3348002222, 3353380298, 3355040270, 3358549737, 3361435497, 3362429919, 3362794212, 3364806686, 3366097408, 3377092478, 3384483577, 3386935381, 3390866933, 3396436209, 3406754828, 3410844718, 3412053803, 3422622140, 3423353756, 3428750555, 3432234900, 3437090362, 3447336396, 3457425472, 3458433148, 3471309596, 3473330287, 3474402688, 3477374887, 3490185309, 3498601605, 3499652111, 3504962517, 3515322110, 3516574556, 3525261555, 3541013304, 3543185288, 3545517607, 3550452435, 3551322614, 3558647148, 3564920657, 3566681924, 3566865341, 3570198327, 3578910003, 3607040737, 3613429487, 3623198306, 3625393024, 3626517377, 3629186895, 3641699600, 3642814146, 3651453271, 3652926544, 3654005218, 3654084125, 3655389537, 3657282519, 3668551104, 3675459445, 3678113221, 3680235960, 3681853305, 3683940094, 3689953220, 3690746478, 3692521447, 3699658362, 3707060040, 3725935753, 3726723207, 3729993896, 3754349592, 3762876371, 3768890995, 3775150772, 3775644728, 3777711598, 3777807832, 3778935732, 3784784407, 3785996674, 3800325191, 3806685105, 3808663970, 3809584402, 3814805017, 3820027231, 3821153327, 3823132192, 3838902944, 3839675171, 3844226148, 3858645751, 3863101861, 3869110590, 3879405561, 3882265412, 3882845562, 3884996851, 3888676988, 3890845843, 3898368760, 3900633844, 3903145210, 3908328745, 3909171619, 3910205834, 3913315078, 3914722820, 3915728037, 3916101840, 3917868857, 3922442173, 3922643484, 3925678111, 3930454626, 3933625061, 3935000224, 3935781051, 3938207154, 3940171886, 3961749065, 3969947752, 3970294973, 3973946778, 3980539585, 3987309545, 3992526837, 3997556659, 4008659437, 4012024881, 4015953527, 4023127659, 4025369438, 4028026498, 4029477333, 4029564637, 4040651291, 4048440350, 4048837899, 4049211235, 4055996876, 4056799170, 4058882636, 4060162187, 4070460246, 4072393741, 4080634966, 4084928468, 4095656614, 4095967906, 4098384290, 4101440329, 4114515538, 4116035726, 4133391251, 4135345853, 4155929447, 4156322693, 4171849827, 4178221104, 4180878164, 4190351121, 4191983241, 4192804370, 4192857067, 4196048744, 4201023492, 4202409656, 4203073727, 4218235034, 4222589185, 4230269358, 4230534090, 4235841622, 4239510802, 4241125923, 4243527226, 4250872726, 4258878103, 4284656891, 4288460674]
  | 5 => packWords [179531, 3252206, 4827349, 6476974, 11836271, 17720428, 40387595, 44268310, 61786406, 76501852, 84961717, 92544254, 93254460, 93659781, 93770907, 100214298, 100566610, 104463982, 117118423, 117487151, 124054042, 124608829, 128149969, 140133399, 140745821, 141489689, 146750177, 149408216, 189210379, 198726080, 204001627, 211070375, 212370523, 214932312, 215563357, 220985607, 222364974, 225843831, 228492169, 235662518, 240483137, 251463104, 255916900, 261483819, 272681141, 272962644, 281640818, 285476792, 291321685, 291550948, 300142112, 305908905, 310722380, 312447730, 314838224, 322372744, 323553317, 327731498, 333051815, 343607204, 351472991, 353840798, 354812815, 359398534, 361316172, 361346801, 370689254, 377776626, 387032561, 388152703, 393122016, 394204275, 396583743, 399626882, 405037827, 407336515, 408313289, 415932703, 419635198, 440910222, 441414881, 445306764, 445957022, 450219943, 455144386, 458271163, 463059510, 468863039, 481622762, 483993543, 488540550, 490996304, 491822518, 505152190, 507422814, 510044489, 515135960, 515609422, 522485950, 527428232, 532995356, 534464533, 539119749, 549210671, 550530618, 552144254, 559214077, 561587722, 572822288, 577362438, 577705464, 578490501, 586046601, 588411222, 591550576, 599231455, 599555013, 600441393, 602088675, 602879444, 609892286, 622006059, 627376418, 628158216, 637281915, 638100941, 648456990, 652246899, 652847021, 655174696, 658164288, 664112774, 678063705, 680184464, 691092684, 696564334, 697626670, 702443322, 702977027, 703924113, 710421010, 726114463, 737834734, 739872979, 750208639, 754968881, 755370856, 756004718, 758374273, 762241973, 769437103, 770679891, 771836771, 779999605, 785484611, 786144362, 787795987, 789504185, 791106920, 791739718, 802033114, 810912122, 831961637, 834981899, 843698978, 846830110, 849369228, 849450121, 861027731, 868747084, 871850745, 872546792, 880335940, 884112267, 893789037, 912379451, 922669664, 931071674, 932851271, 934448428, 942812869, 952180532, 955633981, 965464427, 970102203, 970856344, 976873343, 978680468, 979350042, 982923931, 985235492, 995142810, 997274162, 1000567976, 1001603200, 1002301787, 1005187547, 1008602752, 1019819883, 1026012127, 1034618983, 1047837130, 1051287937, 1053296506, 1059383712, 1062497459, 1066374190, 1075151900, 1080842412, 1081044005, 1082642306, 1090727282, 1094030882, 1095893293, 1100578575, 1104432605, 1104783654, 1113984326, 1114064569, 1129351338, 1132437083, 1133937359, 1134203264, 1148714567, 1151423943, 1162391086, 1168894096, 1171626976, 1174824247, 1189269657, 1192356560, 1196976812, 1198445017, 1202399198, 1207523594, 1207896462, 1210433974, 1211445034, 1213950377, 1220017446, 1230996121, 1233694078, 1239630386, 1261332201, 1269145074, 1279097097, 1281189108, 1289069583, 1293774658, 1295205321, 1299535814, 1316478487, 1327692144, 1331966438, 1332174618, 1341855696, 1345066038, 1347371643, 1355250864, 1356479631, 1363285640, 1369687803, 1391271739, 1394011473, 1394826386, 1412643045, 1418027488, 1446521480, 1451247864, 1477774446, 1489165330, 1517247554, 1518177834, 1526072268, 1526597612, 1531947988, 1545211532, 1558474870, 1561110277, 1561620907, 1566837860, 1579238244, 1583310272, 1584801201, 1587719709, 1595934904, 1598524187, 1610342997, 1610880498, 1625532869, 1631061595, 1634839173, 1636526539, 1642128842, 1646163091, 1655776931, 1659705577, 1663271795, 1666802876, 1668454487, 1673229383, 1686107941, 1692192400, 1692589949, 1694721301, 1703914237, 1709428708, 1714212296, 1717463484, 1719129712, 1728680518, 1729211828, 1734144546, 1743518088, 1754839648, 1768396500, 1769942760, 1778591478, 1779097903, 1801732455, 1802247745, 1803052402, 1818024297, 1826670274, 1829884222, 1838367408, 1840189193, 1846825777, 1848078726, 1849000180, 1856109214, 1862405103, 1863301339, 1870195317, 1874286140, 1874527843, 1876873325, 1879898202, 1882168826, 1889573173, 1889803699, 1899255514, 1900249309, 1921248166, 1938020616, 1946346384, 1953176287, 1954942468, 1962337508, 1973229686, 1973977467, 1978636247, 1992652460, 1998402544, 1999151886, 2002683307, 2007943407, 2008411097, 2016734228, 2018351783, 2018853926, 2025682921, 2037729639, 2038501866, 2043284287, 2053926770, 2064431067, 2067937285, 2073586210, 2075755355, 2092698795, 2093863053, 2097195455, 2114429753, 2117740791, 2124570694, 2125068576, 2132857724, 2134607746, 2140736688, 2142794354, 2147149726, 2151009549, 2165557071, 2165929939, 2175191448, 2177751159, 2179366280, 2183094659, 2183414046, 2184568578, 2190465293, 2200529848, 2204110097, 2218088030, 2223096434, 2223519407, 2224196133, 2239477986, 2247664594, 2249430775, 2258988882, 2271220436, 2275891265, 2289999915, 2306125364, 2313342233, 2314160140, 2314343557, 2334172548, 2340433694, 2340629775, 2354442944, 2354756142, 2358948512, 2364943605, 2370676522, 2372578331, 2376239618, 2377047799, 2388351360, 2389177816, 2394565895, 2395298451, 2400091256, 2401483434, 2402535554, 2408161761, 2416148605, 2417003776, 2419059001, 2421415880, 2424148760, 2429439325, 2432594034, 2438337497, 2439999663, 2442353921, 2454328763, 2455495482, 2458161352, 2466119779, 2466196037, 2479056885, 2481039045, 2487218412, 2490606440, 2493285360, 2494738703, 2496375117, 2503596717, 2510017113, 2520496125, 2525189814, 2546078166, 2546137404, 2565564839, 2567661164, 2569000271, 2581104837, 2582317734, 2588696389, 2600162319, 2600461839, 2607180429, 2607890963, 2608648447, 2610941465, 2626883777, 2643793523, 2646458602, 2647122224, 2647773440, 2648112060, 2648698922, 2648937698, 2650623426, 2668237088, 2676180150, 2679645339, 2681835950, 2683666123, 2690648372, 2691615000, 2695971741, 2696127832, 2696265036, 2705714148, 2708928515, 2717720009, 2723314019, 2726429977, 2734129673, 2739643223, 2757903238, 2759184742, 2760723329, 2779966451, 2791286574, 2793109549, 2799321350, 2804842894, 2814142691, 2819678121, 2835357003, 2840241493, 2848456688, 2857887934, 2858565814, 2860590885, 2861200009, 2861231594, 2865312074, 2867802311, 2869234785, 2869418202, 2872122666, 2879281643, 2881180542, 2885995977, 2886387137, 2910637660, 2911473733, 2924413171, 2926960698, 2931389270, 2933220882, 2934290175, 2935239397, 2936800476, 2940963940, 2945111733, 2949173087, 2951853854, 2953273260, 2954652596, 2956034135, 2956436021, 2957359695, 2960341796, 2960716784, 2984348339, 2989243291, 2995074308, 3001317764, 3004162931, 3008904680, 3009403408, 3015544254, 3022464544, 3026060951, 3028831383, 3029108987, 3031619687, 3040529173, 3040913486, 3041867292, 3045438807, 3055381708, 3056395651, 3057386739, 3065429232, 3066063674, 3066437933, 3070474959, 3080264459, 3084939227, 3097244845, 3104143479, 3104942737, 3111450260, 3111564505, 3117839613, 3118947359, 3121267069, 3135784636, 3137399757, 3142094957, 3149063399, 3151517516, 3181129911, 3181958422, 3182578906, 3193110404, 3203186705, 3205698071, 3207464252, 3209494213, 3215759140, 3222183862, 3225770818, 3226499251, 3262384812, 3263056709, 3271375710, 3282928644, 3283785379, 3289068080, 3291413059, 3293137183, 3298963099, 3327922299, 3330427197, 3330579359, 3332345540, 3346384837, 3352558954, 3363201678, 3367398472, 3377092478, 3386114666, 3393918498, 3401844041, 3406304858, 3413134761, 3424407285, 3433330585, 3435183967, 3435935830, 3436637045, 3437090362, 3444159860, 3444764715, 3448709621, 3448897072, 3475950516, 3476717917, 3477067213, 3482907016, 3483563909, 3486852323, 3488391501, 3488425167, 3505380819, 3513613869, 3536320200, 3540282137, 3540935441, 3546458678, 3547597697, 3554420024, 3558054929, 3558647148, 3566681924, 3566865341, 3569873739, 3577416951, 3591013535, 3601454449, 3604033229, 3615641780, 3622382002, 3637586793, 3641699600, 3642000520, 3654005218, 3654768805, 3666465535, 3680541018, 3688406805, 3693226029, 3696332348, 3698249986, 3707623068, 3708017266, 3712991393, 3718717821, 3723823554, 3737653551, 3740072177, 3745422534, 3746295396, 3753572287, 3753971949, 3762407942, 3762876371, 3765673252, 3777711598, 3780280241, 3784757940, 3786655108, 3790814889, 3792078200, 3796117450, 3801123330, 3815286752, 3821815902, 3830156143, 3830241494, 3833552427, 3838003289, 3839357002, 3844356628, 3848263272, 3858584900, 3875669345, 3875686334, 3878755925, 3879405561, 3882446648, 3884994175, 3887805459, 3898521536, 3903145210, 3903679513, 3903869440, 3909869204, 3910154251, 3923156258, 3932940719, 3936165269, 3941714857, 3947408941, 3953820435, 3956918686, 3958235932, 3958684867, 3958836324, 3962196408, 3963010547, 3965224391, 3968209406, 3977286191, 3992108510, 4000960530, 4015428752, 4024513963, 4025369438, 4028026498, 4034560484, 4040857927, 4044747294, 4049410832, 4052664538, 4071632571, 4074768548, 4093733444, 4095742013, 4104942966, 4113129574, 4124948384, 4128045349, 4130777724, 4138873464, 4139603813, 4147229161, 4159107874, 4186383935, 4197075165, 4203109368, 4203335434, 4208590681, 4226858981, 4242892104, 4252694848, 4273441628, 4276474006, 4287167828, 4288460674, 4288612836, 4290379017]
  | 4 => packWords [1879097, 2700562, 16330381, 69022012, 72127657, 73354538, 116125430, 122808935, 130970462, 131592574, 142545098, 146676018, 153769163, 172056381, 187958191, 198531354, 217178478, 224509616, 234109682, 252400497, 272947993, 292689748, 301492171, 327092183, 340532321, 345976421, 346068588, 362862885, 363564100, 364756634, 367066069, 382240741, 383395273, 384550977, 409841896, 414489256, 504952059, 512986835, 513170252, 519740969, 550540027, 560242912, 562513536, 587178055, 593392590, 597025310, 598404646, 601111745, 614975300, 622975455, 628266020, 645644876, 654322177, 659296304, 668714930, 679865740, 680770041, 698696493, 702423412, 709815724, 738502348, 746183406, 747895529, 756881395, 761766573, 767826966, 825710472, 849450121, 865935912, 878857237, 888956578, 904540843, 923160315, 958632028, 970666031, 1004304031, 1056714629, 1057392509, 1070949361, 1072715542, 1074910605, 1077082635, 1077941133, 1080842412, 1125787393, 1125839629, 1139790635, 1145991668, 1148985110, 1180072250, 1202399198, 1210433974, 1223694789, 1224887646, 1269041099, 1317774054, 1320093764, 1356743443, 1362027745, 1381405601, 1382400217, 1391937099, 1392285038, 1474560557, 1502336950, 1537135058, 1545211532, 1547431563, 1550878177, 1611961456, 1613565592, 1621038241, 1621308650, 1642986555, 1646309837, 1649924962, 1663526260, 1670507686, 1681733711, 1706405661, 1718701466, 1720873883, 1737129761, 1756881624, 1768396500, 1768700434, 1774529774, 1802859924, 1840827215, 1880826798, 1894721153, 1906843961, 1915563490, 1938898872, 1945122091, 1962337508, 1969635276, 1979106936, 2008267009, 2028982838, 2029068189, 2030749019, 2032379122, 2047743182, 2070022733, 2083820870, 2093705252, 2096314165, 2097348231, 2102506208, 2136201701, 2157062627, 2182251375, 2200203160, 2221020661, 2224196133, 2248237527, 2270459266, 2271771156, 2277017469, 2292560139, 2294568708, 2325751902, 2335303084, 2340433694, 2346055856, 2390150108, 2395970055, 2402162129, 2416148605, 2425767244, 2432594034, 2454328763, 2455588424, 2496171120, 2498621335, 2524765942, 2555580392, 2570295838, 2572741202, 2585006890, 2585179986, 2587176331, 2610912409, 2635283675, 2641800661, 2670846803, 2692520066, 2705714148, 2722286155, 2724848843, 2724882282, 2726429977, 2728223526, 2812976098, 2838860275, 2877082962, 2882167403, 2886853067, 2901309815, 2902107275, 2934704208, 2939287317, 2944013929, 2947322093, 2956853496, 3009403408, 3018996532, 3043714498, 3044324604, 3055381708, 3056243427, 3068070679, 3071156424, 3115800045, 3131075901, 3174038081, 3178349727, 3190875358, 3196237308, 3219908449, 3227788924, 3242860887, 3260788793, 3281589973, 3283785379, 3286090984, 3288761645, 3296972458, 3325755623, 3343163214, 3352471812, 3366340778, 3377906253, 3416463650, 3444175040, 3456934763, 3458943243, 3464791609, 3476717917, 3513613869, 3522042785, 3526144193, 3547090492, 3564252210, 3568945886, 3571043496, 3575245880, 3602688419, 3605522217, 3620833493, 3633861480, 3635256308, 3645680290, 3650930255, 3665420962, 3677466135, 3678289028, 3688699512, 3701690448, 3715179706, 3787719521, 3810272473, 3875704052, 3885065725, 3887805459, 3945041850, 3955453569, 3956860756, 3958235932, 3982959316, 4005648744, 4061335702, 4081513695, 4089728890, 4092318173, 4101175989, 4120386640, 4129604746, 4152724498, 4161854214, 4162238748, 4178330367, 4186383935, 4200894364, 4244358890, 4263840008, 4266140296, 4270944541]
  | 3 => packWords [93547848, 261307725, 419847356, 599230643, 614975300, 687466548, 745198625, 861001447, 904540843, 975959153, 983286816, 984881362, 1135933134, 1173981443, 1197464733, 1372864776, 1419486610, 1557427672, 1834083003, 1914696591, 2157062627, 2220879549, 2297629799, 2395524416, 2440875081, 2609919416, 2625386560, 2781520699, 2809949456, 2856656871, 2878344963, 3044334013, 3049310558, 3058976293, 3072820776, 3126365422, 3192490479, 3239977392, 3338876101, 3416954301, 3444972576, 3473401333, 3568704591, 3593298411, 3737078574, 3855821731, 4026951421, 4076849751, 4115102636, 4143718948, 4144923816, 4200199647, 4230923747]
  | 2 => packWords [637328891, 1121219791, 1325192117, 1784671668, 2288566035, 2757194461, 2825268526, 3420646338, 3478675348]
  | _ => 0
def parentSteps : ℕ → ℕ
  | 7 => packWords [3921, 1284, 256, 3889, 3666, 3923, 3922, 2900, 1027, 1285, 3924, 3616, 2898, 3904, 1024, 3617, 1029, 3634, 3633, 3906, 2848, 3600, 3856, 1280, 1282, 1857, 2883, 3905, 2881, 258, 3651, 259, 1859, 3872, 1281, 257, 3907, 3888, 1824, 1875, 3665, 3632, 1283, 1874, 3664, 3650, 261, 1876, 2899, 3920, 1026, 3649, 3873, 2849, 1025, 0, 3890, 3648, 1028, 1825, 260]
  | 6 => packWords [11041, 190032, 34656, 135424, 137776, 0, 125760, 2880, 59184, 15202, 169792, 123712, 83779, 4096, 241924, 64306, 47952, 20738, 8192, 23394, 27488, 236336, 215600, 165728, 234288, 183136, 87892, 215616, 114948, 46948, 235312, 159520, 67394, 82178, 169776, 21330, 183120, 72497, 55141, 134976, 148320, 43600, 27216, 119043, 91988, 96084, 75587, 43601, 15169, 86848, 10017, 80689, 236384, 138049, 155904, 236352, 160000, 194384, 181025, 832, 28929, 102656, 27490, 59236, 187184, 47968, 12288, 2864, 63332, 170816, 90720, 183088, 185168, 37472, 30545, 100180, 181040, 8452, 16640, 16384, 39744, 154176, 54114, 180480, 15168, 20480, 72496, 87857, 110848, 71522, 168784, 209760, 114944, 134992, 2640, 128592, 13121, 13136, 38737, 75618, 47936, 79717, 133921, 103681, 91953, 39520, 152385, 96049, 101216, 102657, 234304, 165680, 174656, 37697, 86272, 96816, 235328, 72512, 41810, 113490, 163632, 70464, 31555, 117569, 106755, 166736, 71472, 168768, 51009, 92736, 83795, 170832, 41824, 120643, 24576, 28672, 15184, 139856, 150321, 76592, 101153, 100912, 135760, 104242, 196864, 98864, 6688, 6720, 164704, 87908, 64320, 14880, 170800, 53504, 150096, 168752, 119042, 108354, 140848, 150080, 144928, 121680, 92004, 36864, 96100, 27457, 27200, 94768, 132352, 40960, 30531, 39760, 141904, 83793, 6944, 137808, 112451, 131921, 75584, 62288, 45056, 166752, 39728, 116530, 75568, 23121, 161616, 159552, 72544, 25360, 53248, 232000, 71520, 154160, 100196, 248608, 124705, 106752, 82181, 104276, 78689, 203328, 83796, 43568, 148048, 131329, 72273, 163360, 47888, 148321, 64336, 78080, 70480, 163664, 80448, 84819, 61440, 190000, 98848, 152418, 6960, 97088, 161024, 164656, 112485, 127234, 100944, 116564, 11092, 100193, 92976, 2592, 39488, 35392, 62304, 104275, 14896, 72528, 120659, 49413, 163376, 35376, 77824, 108372, 192768, 107345, 159568, 83745, 86880, 124755, 169824, 113218, 2896, 117297, 87888, 141920, 9760, 134688, 73984, 128817, 198480, 102661, 81920, 116563, 100928, 109105, 186208, 88896, 74592, 106757, 61696, 11090, 12544, 27232, 108369, 105300, 99169, 90928, 166450, 37440, 59936, 14912, 186176, 27184, 134978, 80720, 187216, 114949, 60192, 80432, 9472, 174880, 116561, 141856, 22049, 132355, 209712, 119045, 131331, 38496, 120660, 117588, 100145, 160001, 132096, 133953, 142128, 21344, 84785, 173664, 146208, 121683, 82180, 123696, 134945, 109379, 98304, 142176, 141872, 30544, 102400, 6928, 209744, 98912, 182049, 39472, 132930, 23088, 106496, 2656, 150353, 23392, 113473, 88880, 233728, 136992, 159536, 185184, 128851, 209152, 17232, 99121, 113200, 20736, 141106, 168800, 110592, 104241, 248640, 29953, 187200, 145185, 45312, 111376, 199457, 185152, 56128, 149331, 108355, 80704, 118784, 92768, 23104, 78656, 127237, 139824, 101152, 184576, 131328, 2865, 153409, 128852, 30529, 43825, 132945, 6992, 211808, 86832, 4945, 137060, 162624, 87872, 11040, 147712, 38721, 74576, 141156, 134739, 145235, 174896, 865, 134689, 132353, 71488, 149345, 4913, 154192, 101184, 10049, 4704, 121616, 5969, 62256, 132948, 129842, 119044, 153442, 176384, 27440, 11075, 96832, 23136, 15153, 211776, 76624, 91744, 113216, 182080, 134738, 1569, 545, 126976, 150098, 157523, 164096, 129856, 5937, 145234, 108368, 11073, 131333, 159312, 148322, 6976, 101200, 31554, 8450, 159314, 21345, 134994, 13137, 159281, 156931, 83520, 200960, 183104, 19264, 128818, 132100, 17216, 143621, 52000, 247376, 150082, 145236, 100896, 159280, 39456, 209728, 17248, 15154, 229632, 146259, 166704, 159313, 850, 23393, 150064, 2866, 127236, 137810, 134979, 71504, 38464, 80480, 133955, 163616, 5728, 28928, 23345, 56129, 155909, 157524, 19296, 23106, 132099, 181056, 163361, 161025, 33616, 95792, 134977, 158547, 159569, 150066, 64352, 2608, 190016, 60208, 138048, 99888, 8451, 159298, 41216, 41825, 88928, 139264, 43584, 211792, 143360, 23090, 163412, 17200, 35664, 186160, 132931, 13154, 54098, 43841, 54081, 163648, 138034, 41793, 35616, 76640, 17234, 19280, 78688, 211760, 28932, 141105, 82176, 51027, 23346, 140081, 156674, 75616, 56114, 58160, 182096, 97056, 54066, 160772, 234320, 138050, 120352, 159297, 134944, 52052, 235344, 163411, 43586, 128576, 125744, 92720, 101168, 234336, 87904, 55872, 4688, 235360, 99872, 143620, 1893, 108096, 62289, 45920, 52051, 6993, 156676, 96848, 163651, 162627, 10051, 74578, 29521, 55904, 78674, 31521, 78641, 43824, 191280, 203312, 100960, 160771, 165712, 90368, 21280, 185136, 125776, 55888, 163649, 163410, 142112, 155908, 132944, 8449, 121632, 187232, 137824, 23344, 37713, 28933, 87841, 76626, 41826, 43826, 165696, 76608, 120336, 83201, 170848, 247360, 68144, 177969, 92993, 35360, 33024, 70448, 83778, 156928, 174928, 160773, 161603, 159264, 14162, 1859, 186930, 181072, 141888, 2624, 5954, 84803, 25376, 69888, 137792, 6704, 95025, 97072, 18277, 4656, 15152, 215648, 123728, 191282, 60000, 22369, 5712, 195395, 160005, 184320, 163392, 84802, 49412, 90962, 64304, 199491, 23376, 47920, 188416, 74560, 45872, 74544, 82177, 41760, 191296, 56112, 215632, 21264, 2898, 60256, 166720, 70498, 75600, 5989, 19216, 70496, 6752, 187201, 14147, 179009, 26469, 93010, 99936, 208896, 10067, 24832, 134960, 45888, 176389, 190258, 194371, 19249, 247328, 34640, 86864, 22355, 134720, 87856, 164688, 136784, 198467, 96864, 92752, 134704, 140880, 207664, 28931, 96800, 38757, 144960, 205616, 43873, 864, 188677, 182112, 4961, 39712, 164672, 97104, 5680, 10066, 2576, 168192, 46932, 62272, 528, 55856, 174624, 108337, 102659, 35648, 88912, 196869, 14178, 59984, 151808, 51028, 120400, 174912, 6672, 56146, 82179, 49408, 106756, 27441, 231984, 97120, 30530, 19282, 2912, 142160, 213248, 146240, 5985, 217344, 132672, 157248, 22304, 8453, 59220, 10068, 34626, 49411, 4352, 123136, 213792, 236368, 215874, 63316, 114947, 219953, 14944, 93025, 173648, 11091, 38722, 217348, 42835, 6736, 256, 174640, 67429, 149072, 159296, 71506, 169808, 19248, 46881, 225540, 38480, 23120, 142144, 45904, 56144, 55105, 23378, 182064, 75602, 21346, 80722, 186192, 241920, 102660, 181088]
  | 5 => packWords [595795, 915233, 516929, 609106, 303361, 914209, 636754, 857939, 152402, 631632, 508754, 1099602, 573985, 672338, 725249, 1041233, 1086272, 898882, 1868624, 303953, 437042, 3212096, 1815360, 86800, 1261824, 1144660, 1790784, 2798416, 238401, 3098432, 942656, 590673, 1082192, 728864, 2352704, 598848, 1549905, 297522, 1819200, 437074, 200704, 402257, 643923, 611104, 1585986, 357218, 498514, 837457, 1534513, 1532161, 1610595, 2574160, 2384736, 787281, 296784, 365410, 795425, 2032449, 529248, 420672, 286720, 795202, 1814786, 294912, 4353, 2048818, 291600, 2061153, 189282, 672289, 664385, 832320, 848704, 3023680, 1401696, 916290, 498241, 307810, 1712962, 111440, 1790768, 430912, 858706, 1868369, 368640, 807761, 516945, 1753681, 3098400, 643889, 1872704, 1383250, 728896, 631648, 417792, 2147171, 297793, 217906, 1938001, 209440, 2155361, 996144, 881489, 1414994, 2814544, 2057024, 3212128, 111392, 1796914, 1456962, 2196323, 95073, 791392, 721729, 1450240, 726020, 41744, 1164098, 848736, 750385, 1839938, 1338145, 3098448, 858690, 1208912, 2032480, 664096, 1020705, 1735201, 422432, 1880914, 2384704, 422721, 95057, 225840, 70224, 442944, 844608, 838481, 94992, 574050, 107346, 140048, 758624, 1636160, 728899, 836432, 2929473, 1934179, 1938258, 727875, 787297, 916306, 1958737, 1383217, 967488, 837424, 1483569, 438816, 2364210, 983858, 562993, 148320, 726019, 1414977, 584498, 838194, 724992, 1534801, 858674, 1456945, 1053520, 688736, 3179040, 202576, 420688, 688976, 357169, 2061154, 1065218, 1479488, 2353985, 1028928, 2081633, 1037104, 1401664, 181041, 709425, 455505, 631312, 2032448, 1337171, 983904, 729953, 2097986, 856064, 726851, 754529, 172896, 2446145, 643331, 1090369, 442928, 838448, 123713, 258849, 1550897, 2601808, 1548849, 455489, 717632, 1041249, 1340224, 189266, 238417, 1274705, 455440, 288544, 402002, 111456, 1455956, 1006403, 1155905, 728640, 1324880, 1401680, 728865, 2241104, 1636162, 1252176, 1496915, 2888528, 300848, 2351937, 3102512, 1336864, 2351921, 2908992, 1003520, 864864, 1015808, 1643074, 529216, 1954401, 1796930, 1139536, 611154, 2713392, 938817, 856322, 1340256, 1337888, 725250, 1868640, 2717264, 2470738, 385840, 791360, 2474834, 406370, 2474818, 1005379, 1712992, 320016, 193376, 1338195, 1028913, 41809, 837440, 238369, 1145632, 717664, 2868048, 983888, 1549873, 664369, 2532178, 1249280, 1810992, 1534785, 1430353, 1327954, 1581601, 140113, 1463105, 381536, 435776, 452128, 1552929, 189216, 1796690, 705376, 2761248, 3102544, 664353, 508704, 1122561, 2315073, 1954369, 320032, 726016, 288560, 1003778, 1164064, 1483616, 420384, 729937, 1252161, 754513, 1324864, 1250113, 41793, 296464, 168752, 2310960, 3101504, 2024288, 1196289, 1549840, 1024784, 832352, 557648, 967504, 1139538, 1155856, 1041217, 1409568, 1209136, 288528, 795168, 1735489, 578384, 1561441, 2814545, 1796946, 437057, 594752, 837456, 419394, 728881, 647696, 1383233, 2864976, 3212112, 915248, 1993538, 9057, 1729344, 287552, 1610577, 728641, 17200, 54097, 2225985, 728625, 127568, 2226000, 1893201, 492065, 838482, 70498, 512864, 78641, 1127201, 1008224, 385888, 2237280, 2464545, 2291522, 2249569, 111441, 2533186, 119649, 202529, 1708881, 148321, 1913680, 53856, 156481, 2048561, 156515, 1225297, 873056, 583472, 1163824, 1569616, 189268, 2016081, 791376, 1053504, 2327106, 1139552, 95041, 217937, 230225, 2540368, 1483600, 726593, 258913, 258898, 262945, 2425664, 279393, 1401633, 2601824, 2705218, 2015489, 2713410, 49411, 70176, 561984, 967520, 336706, 1904897, 848720, 2577248, 349025, 1680224, 2400816, 857681, 152353, 365409, 837408, 373586, 2226754, 2770770, 297794, 385889, 1335840, 295746, 1901392, 156449, 3252816, 1144657, 1323840, 406369, 410449, 414529, 418625, 2855744, 127569, 2280002, 1053536, 2585154, 152144, 2623280, 1327970, 705360, 1090401, 492387, 1208864, 2093904, 2773840, 512865, 180769, 50001, 2650689, 291377, 1462816, 1155921, 1550160, 1005121, 583504, 570195, 437058, 484162, 189217, 1561409, 1586016, 1159968, 107361, 598849, 111457, 615249, 1024865, 365378, 107314, 627538, 1717072, 148273, 563024, 152419, 1721152, 160611, 152418, 172849, 832336, 3097392, 181089, 185185, 1082208, 582464, 197475, 2623316, 2048609, 217953, 2982720, 713554, 729939, 41825, 754515, 357202, 37648, 1790800, 783187, 779073, 1356384, 2577232, 3208000, 420400, 406354, 308065, 193360, 313121, 406338, 532739, 3103552, 717648, 320338, 1266273, 332643, 828241, 1479520, 127584, 1868608, 140129, 1251873, 728608, 353123, 647761, 381537, 33552, 865106, 595776, 2605888, 2280272, 1688369, 565792, 865073, 381746, 942672, 394066, 398162, 119585, 1671776, 3102528, 1512241, 435026, 1950272, 213776, 488016, 2032464, 1708897, 53840, 504384, 480099, 726272, 488289, 496466, 1340240, 500563, 611170, 289600, 758592, 708865, 512817, 516963, 516961, 2623313, 1017633, 545617, 2298465, 728624, 2855760, 107296, 987986, 303888, 557923, 2384720, 1000273, 13136, 1983312, 101186, 844610, 279329, 8976, 262928, 959313, 435744, 729921, 529232, 631650, 307745, 660289, 70433, 107297, 1098578, 688994, 2401120, 697171, 70432, 1533522, 1901408, 1734226, 3102496, 217632, 746322, 2411313, 1549888, 148240, 2388832, 180834, 296736, 1708865, 313172, 1123137, 983872, 803681, 1913664, 1100626, 53808, 564032, 2257760, 1139489, 1086256, 1003780, 836433, 100145, 3195456, 1479504, 1011969, 123729, 844643, 49969, 869202, 1325888, 563008, 127552, 2257744, 2855776, 123745, 436034, 111408, 529184, 574224, 453442, 202545, 2089824, 2282305, 497474, 934737, 1327937, 951122, 365328, 522050, 172848, 288592, 971619, 1337136, 288561, 2626144, 297777, 300866, 313137, 631616, 2458176, 1913696, 1085696, 100180, 307794, 1795664, 1053265, 202560, 2397009, 2208609, 1041168, 728609, 37408, 636738, 1225313, 1028960, 2196321, 370497, 1497888, 1037136, 1483618, 1700688, 584512, 3098416, 184914, 611105, 574241, 419649, 1114704, 1172320, 1528657, 475985, 100914, 676384, 942688, 2601792, 1143617, 152386, 17168, 111424, 688928, 1200944, 1151843, 2127392, 422464, 728898, 476001, 447024, 2388816, 1172321, 836400, 2106193, 70240, 583488, 727872, 1090385, 314178, 864832, 562994, 726275, 725251, 1225570, 837409, 583457, 574002, 608067, 726017, 1680208, 370514, 1626930, 636721, 307778, 3099440, 1287009, 436050, 452436, 184865, 1483584, 2233152, 2208577, 915284, 365394, 726850, 522066, 1643329, 2904608, 1647425, 288576, 193344, 563028, 107362, 1551169, 1778482, 103184, 583508, 583440]
  | 4 => packWords [1315667, 1696595, 1708881, 1364819, 1966929, 29489, 312128, 819776, 853808, 639809, 1827650, 1427264, 336704, 205650, 1292096, 1293105, 566065, 13089, 1569569, 1581874, 1754913, 1520465, 434994, 946753, 1893201, 610898, 889633, 1593921, 140114, 1573715, 2007889, 1594195, 1020480, 340785, 266834, 639777, 1659729, 1667921, 1672018, 2102065, 1364800, 639825, 1385264, 525104, 1729362, 844608, 693024, 651522, 1753922, 1765968, 16976, 1811025, 1434432, 135744, 1893153, 1819475, 234305, 1471298, 1844050, 2302801, 152384, 2930208, 987986, 185138, 356610, 29232, 181073, 45857, 2040642, 74546, 303905, 1626928, 340801, 1292064, 2687825, 1427249, 1155920, 1717056, 2114385, 2233137, 639793, 2343744, 1098529, 844304, 525120, 746289, 1628961, 2012992, 656193, 316192, 742160, 762400, 1098577, 2253649, 1286978, 1434448, 1925921, 717376, 680768, 693056, 1681202, 1133122, 1291792, 574272, 222001, 1802817, 1130496, 1516353, 733776, 320321, 1798962, 2179649, 1997633, 2544465, 922401, 2573104, 1405746, 853825, 1692224, 2253632, 782914, 2270000, 1754928, 783153, 963376, 693072, 2806593, 1725266, 197456, 959313, 1819458, 2421569, 918353, 849, 1628721, 246592, 963378, 25425, 1996610, 2814801, 1627952, 2941729, 54098, 1286402, 1779520, 1180480, 1037106, 111410, 1971011, 1934145, 1086018, 2564913, 1996576, 176977, 1754896, 193329, 283472, 230194, 238417, 2155328, 250706, 1628976, 279380, 295763, 529216, 181057, 90370, 1681216, 733712, 74256, 1997634, 229904, 385857, 853553, 660290, 9043, 459603, 33619, 37714, 394033, 234321, 140098, 516945, 74578, 103217, 1323857, 713553, 119635, 496160, 156482, 889665, 1233745, 152352, 643922, 598850, 1569617, 361296, 676674, 1344337, 1581584, 312147, 324433, 451410, 340818, 451394, 353107, 70416, 1323825, 643889, 426835, 189200, 656177, 897873, 336720, 496467, 508755, 119617, 992065, 140096, 562003, 578386, 968496, 959297, 193346, 639826, 45840, 1053507, 725826, 1233729, 209713, 680787, 1004321, 701267, 709442, 721746, 357168, 361265, 1344321, 1119059, 193296, 226081, 111169, 1151810, 832338, 957232, 848721, 959281, 1020432, 500545, 148033, 152400, 1172272, 33296, 1176384, 1754944, 926288, 1200977, 566082, 2147122, 963411, 1680944, 1348433, 1028947, 111153, 320337, 168480, 1098578, 1467218, 1090385, 561952, 1106754, 1200945, 725810, 29505, 1168178, 1172307, 2012704, 119601, 221729, 140064, 86834, 1622866, 680752, 29507, 1569601, 680784, 1602337, 119633, 1467184]
  | 3 => packWords [226115, 500545, 198433, 709408, 196608, 516914, 631617, 905760, 290816, 78369, 742160, 250672, 586288, 140080, 61984, 574273, 250688, 574257, 226097, 332577, 21008, 766752, 418608, 1065776, 356913, 25411, 37698, 250656, 144192, 111427, 136002, 13121, 664096, 1065760, 188994, 500513, 66354, 250690, 115521, 295746, 1131312, 336704, 181042, 58161, 262961, 402243, 57889, 684609, 293665, 471858, 262720, 381761, 198449]
  | 2 => packWords [4912, 8993, 9009, 99120, 13105, 95025, 49970, 135985, 45874]
  | _ => 0
def stateCheck (s : ℕ) := bar 88 (Sgen 88 8 inputMasks parentSteps) stateCount (idxGen stateCount stateHash) id [] s
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_0 : span (stateCheck 0) 0 0 = true := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_1 : span (stateCheck 1) 0 0 = true := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_2_0 : span (stateCheck 2) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_2_8 : span (stateCheck 2) 1 8 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_2 : span (stateCheck 2) 9 0 = true := by
  apply span_join (b := 1) c_2_0
  exact c_2_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_3_0 : span (stateCheck 3) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_3_8 : span (stateCheck 3) 8 8 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_3_16 : span (stateCheck 3) 8 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_3_24 : span (stateCheck 3) 8 24 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_3_32 : span (stateCheck 3) 8 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_3_40 : span (stateCheck 3) 8 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_3_48 : span (stateCheck 3) 5 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_3 : span (stateCheck 3) 53 0 = true := by
  apply span_join (b := 45) c_3_0
  apply span_join (b := 37) c_3_8
  apply span_join (b := 29) c_3_16
  apply span_join (b := 21) c_3_24
  apply span_join (b := 13) c_3_32
  apply span_join (b := 5) c_3_40
  exact c_3_48
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_0 : span (stateCheck 4) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_8 : span (stateCheck 4) 8 8 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_16 : span (stateCheck 4) 8 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_24 : span (stateCheck 4) 8 24 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_32 : span (stateCheck 4) 8 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_40 : span (stateCheck 4) 8 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_48 : span (stateCheck 4) 8 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_56 : span (stateCheck 4) 8 56 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_64 : span (stateCheck 4) 8 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_72 : span (stateCheck 4) 8 72 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_80 : span (stateCheck 4) 8 80 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_88 : span (stateCheck 4) 8 88 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_96 : span (stateCheck 4) 8 96 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_104 : span (stateCheck 4) 8 104 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_112 : span (stateCheck 4) 8 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_120 : span (stateCheck 4) 8 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_128 : span (stateCheck 4) 8 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_136 : span (stateCheck 4) 8 136 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_144 : span (stateCheck 4) 8 144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_152 : span (stateCheck 4) 8 152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_160 : span (stateCheck 4) 8 160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_168 : span (stateCheck 4) 8 168 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_176 : span (stateCheck 4) 8 176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_184 : span (stateCheck 4) 8 184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_192 : span (stateCheck 4) 8 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_200 : span (stateCheck 4) 8 200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_208 : span (stateCheck 4) 8 208 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_216 : span (stateCheck 4) 8 216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_224 : span (stateCheck 4) 8 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_232 : span (stateCheck 4) 8 232 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_240 : span (stateCheck 4) 8 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_248 : span (stateCheck 4) 8 248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_256 : span (stateCheck 4) 8 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_264 : span (stateCheck 4) 8 264 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_272 : span (stateCheck 4) 8 272 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_280 : span (stateCheck 4) 8 280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_4_288 : span (stateCheck 4) 1 288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_4 : span (stateCheck 4) 289 0 = true := by
  apply span_join (b := 281) c_4_0
  apply span_join (b := 273) c_4_8
  apply span_join (b := 265) c_4_16
  apply span_join (b := 257) c_4_24
  apply span_join (b := 249) c_4_32
  apply span_join (b := 241) c_4_40
  apply span_join (b := 233) c_4_48
  apply span_join (b := 225) c_4_56
  apply span_join (b := 217) c_4_64
  apply span_join (b := 209) c_4_72
  apply span_join (b := 201) c_4_80
  apply span_join (b := 193) c_4_88
  apply span_join (b := 185) c_4_96
  apply span_join (b := 177) c_4_104
  apply span_join (b := 169) c_4_112
  apply span_join (b := 161) c_4_120
  apply span_join (b := 153) c_4_128
  apply span_join (b := 145) c_4_136
  apply span_join (b := 137) c_4_144
  apply span_join (b := 129) c_4_152
  apply span_join (b := 121) c_4_160
  apply span_join (b := 113) c_4_168
  apply span_join (b := 105) c_4_176
  apply span_join (b := 97) c_4_184
  apply span_join (b := 89) c_4_192
  apply span_join (b := 81) c_4_200
  apply span_join (b := 73) c_4_208
  apply span_join (b := 65) c_4_216
  apply span_join (b := 57) c_4_224
  apply span_join (b := 49) c_4_232
  apply span_join (b := 41) c_4_240
  apply span_join (b := 33) c_4_248
  apply span_join (b := 25) c_4_256
  apply span_join (b := 17) c_4_264
  apply span_join (b := 9) c_4_272
  apply span_join (b := 1) c_4_280
  exact c_4_288
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_0 : span (stateCheck 5) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_8 : span (stateCheck 5) 8 8 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_16 : span (stateCheck 5) 8 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_24 : span (stateCheck 5) 8 24 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_32 : span (stateCheck 5) 8 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_40 : span (stateCheck 5) 8 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_48 : span (stateCheck 5) 8 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_56 : span (stateCheck 5) 8 56 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_64 : span (stateCheck 5) 8 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_72 : span (stateCheck 5) 8 72 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_80 : span (stateCheck 5) 8 80 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_88 : span (stateCheck 5) 8 88 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_96 : span (stateCheck 5) 8 96 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_104 : span (stateCheck 5) 8 104 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_112 : span (stateCheck 5) 8 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_120 : span (stateCheck 5) 8 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_128 : span (stateCheck 5) 8 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_136 : span (stateCheck 5) 8 136 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_144 : span (stateCheck 5) 8 144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_152 : span (stateCheck 5) 8 152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_160 : span (stateCheck 5) 8 160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_168 : span (stateCheck 5) 8 168 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_176 : span (stateCheck 5) 8 176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_184 : span (stateCheck 5) 8 184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_192 : span (stateCheck 5) 8 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_200 : span (stateCheck 5) 8 200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_208 : span (stateCheck 5) 8 208 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_216 : span (stateCheck 5) 8 216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_224 : span (stateCheck 5) 8 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_232 : span (stateCheck 5) 8 232 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_240 : span (stateCheck 5) 8 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_248 : span (stateCheck 5) 8 248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_256 : span (stateCheck 5) 8 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_264 : span (stateCheck 5) 8 264 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_272 : span (stateCheck 5) 8 272 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_280 : span (stateCheck 5) 8 280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_288 : span (stateCheck 5) 8 288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_296 : span (stateCheck 5) 8 296 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_304 : span (stateCheck 5) 8 304 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_312 : span (stateCheck 5) 8 312 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_320 : span (stateCheck 5) 8 320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_328 : span (stateCheck 5) 8 328 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_336 : span (stateCheck 5) 8 336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_344 : span (stateCheck 5) 8 344 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_352 : span (stateCheck 5) 8 352 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_360 : span (stateCheck 5) 8 360 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_368 : span (stateCheck 5) 8 368 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_376 : span (stateCheck 5) 8 376 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_384 : span (stateCheck 5) 8 384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_392 : span (stateCheck 5) 8 392 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_400 : span (stateCheck 5) 8 400 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_408 : span (stateCheck 5) 8 408 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_416 : span (stateCheck 5) 8 416 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_424 : span (stateCheck 5) 8 424 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_432 : span (stateCheck 5) 8 432 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_440 : span (stateCheck 5) 8 440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_448 : span (stateCheck 5) 8 448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_456 : span (stateCheck 5) 8 456 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_464 : span (stateCheck 5) 8 464 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_472 : span (stateCheck 5) 8 472 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_480 : span (stateCheck 5) 8 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_488 : span (stateCheck 5) 8 488 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_496 : span (stateCheck 5) 8 496 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_504 : span (stateCheck 5) 8 504 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_512 : span (stateCheck 5) 8 512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_520 : span (stateCheck 5) 8 520 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_528 : span (stateCheck 5) 8 528 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_536 : span (stateCheck 5) 8 536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_544 : span (stateCheck 5) 8 544 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_552 : span (stateCheck 5) 8 552 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_560 : span (stateCheck 5) 8 560 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_568 : span (stateCheck 5) 8 568 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_576 : span (stateCheck 5) 8 576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_584 : span (stateCheck 5) 8 584 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_592 : span (stateCheck 5) 8 592 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_600 : span (stateCheck 5) 8 600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_608 : span (stateCheck 5) 8 608 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_616 : span (stateCheck 5) 8 616 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_624 : span (stateCheck 5) 8 624 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_632 : span (stateCheck 5) 8 632 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_640 : span (stateCheck 5) 8 640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_648 : span (stateCheck 5) 8 648 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_656 : span (stateCheck 5) 8 656 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_664 : span (stateCheck 5) 8 664 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_672 : span (stateCheck 5) 8 672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_680 : span (stateCheck 5) 8 680 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_688 : span (stateCheck 5) 8 688 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_696 : span (stateCheck 5) 8 696 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_704 : span (stateCheck 5) 8 704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_712 : span (stateCheck 5) 8 712 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_720 : span (stateCheck 5) 8 720 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_728 : span (stateCheck 5) 8 728 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_736 : span (stateCheck 5) 8 736 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_744 : span (stateCheck 5) 8 744 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_752 : span (stateCheck 5) 8 752 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_5_760 : span (stateCheck 5) 1 760 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_5 : span (stateCheck 5) 761 0 = true := by
  apply span_join (b := 753) c_5_0
  apply span_join (b := 745) c_5_8
  apply span_join (b := 737) c_5_16
  apply span_join (b := 729) c_5_24
  apply span_join (b := 721) c_5_32
  apply span_join (b := 713) c_5_40
  apply span_join (b := 705) c_5_48
  apply span_join (b := 697) c_5_56
  apply span_join (b := 689) c_5_64
  apply span_join (b := 681) c_5_72
  apply span_join (b := 673) c_5_80
  apply span_join (b := 665) c_5_88
  apply span_join (b := 657) c_5_96
  apply span_join (b := 649) c_5_104
  apply span_join (b := 641) c_5_112
  apply span_join (b := 633) c_5_120
  apply span_join (b := 625) c_5_128
  apply span_join (b := 617) c_5_136
  apply span_join (b := 609) c_5_144
  apply span_join (b := 601) c_5_152
  apply span_join (b := 593) c_5_160
  apply span_join (b := 585) c_5_168
  apply span_join (b := 577) c_5_176
  apply span_join (b := 569) c_5_184
  apply span_join (b := 561) c_5_192
  apply span_join (b := 553) c_5_200
  apply span_join (b := 545) c_5_208
  apply span_join (b := 537) c_5_216
  apply span_join (b := 529) c_5_224
  apply span_join (b := 521) c_5_232
  apply span_join (b := 513) c_5_240
  apply span_join (b := 505) c_5_248
  apply span_join (b := 497) c_5_256
  apply span_join (b := 489) c_5_264
  apply span_join (b := 481) c_5_272
  apply span_join (b := 473) c_5_280
  apply span_join (b := 465) c_5_288
  apply span_join (b := 457) c_5_296
  apply span_join (b := 449) c_5_304
  apply span_join (b := 441) c_5_312
  apply span_join (b := 433) c_5_320
  apply span_join (b := 425) c_5_328
  apply span_join (b := 417) c_5_336
  apply span_join (b := 409) c_5_344
  apply span_join (b := 401) c_5_352
  apply span_join (b := 393) c_5_360
  apply span_join (b := 385) c_5_368
  apply span_join (b := 377) c_5_376
  apply span_join (b := 369) c_5_384
  apply span_join (b := 361) c_5_392
  apply span_join (b := 353) c_5_400
  apply span_join (b := 345) c_5_408
  apply span_join (b := 337) c_5_416
  apply span_join (b := 329) c_5_424
  apply span_join (b := 321) c_5_432
  apply span_join (b := 313) c_5_440
  apply span_join (b := 305) c_5_448
  apply span_join (b := 297) c_5_456
  apply span_join (b := 289) c_5_464
  apply span_join (b := 281) c_5_472
  apply span_join (b := 273) c_5_480
  apply span_join (b := 265) c_5_488
  apply span_join (b := 257) c_5_496
  apply span_join (b := 249) c_5_504
  apply span_join (b := 241) c_5_512
  apply span_join (b := 233) c_5_520
  apply span_join (b := 225) c_5_528
  apply span_join (b := 217) c_5_536
  apply span_join (b := 209) c_5_544
  apply span_join (b := 201) c_5_552
  apply span_join (b := 193) c_5_560
  apply span_join (b := 185) c_5_568
  apply span_join (b := 177) c_5_576
  apply span_join (b := 169) c_5_584
  apply span_join (b := 161) c_5_592
  apply span_join (b := 153) c_5_600
  apply span_join (b := 145) c_5_608
  apply span_join (b := 137) c_5_616
  apply span_join (b := 129) c_5_624
  apply span_join (b := 121) c_5_632
  apply span_join (b := 113) c_5_640
  apply span_join (b := 105) c_5_648
  apply span_join (b := 97) c_5_656
  apply span_join (b := 89) c_5_664
  apply span_join (b := 81) c_5_672
  apply span_join (b := 73) c_5_680
  apply span_join (b := 65) c_5_688
  apply span_join (b := 57) c_5_696
  apply span_join (b := 49) c_5_704
  apply span_join (b := 41) c_5_712
  apply span_join (b := 33) c_5_720
  apply span_join (b := 25) c_5_728
  apply span_join (b := 17) c_5_736
  apply span_join (b := 9) c_5_744
  apply span_join (b := 1) c_5_752
  exact c_5_760
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_0 : span (stateCheck 6) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_8 : span (stateCheck 6) 8 8 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_16 : span (stateCheck 6) 8 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_24 : span (stateCheck 6) 8 24 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_32 : span (stateCheck 6) 8 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_40 : span (stateCheck 6) 8 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_48 : span (stateCheck 6) 8 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_56 : span (stateCheck 6) 8 56 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_64 : span (stateCheck 6) 8 64 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_72 : span (stateCheck 6) 8 72 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_80 : span (stateCheck 6) 8 80 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_88 : span (stateCheck 6) 8 88 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_96 : span (stateCheck 6) 8 96 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_104 : span (stateCheck 6) 8 104 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_112 : span (stateCheck 6) 8 112 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_120 : span (stateCheck 6) 8 120 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_128 : span (stateCheck 6) 8 128 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_136 : span (stateCheck 6) 8 136 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_144 : span (stateCheck 6) 8 144 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_152 : span (stateCheck 6) 8 152 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_160 : span (stateCheck 6) 8 160 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_168 : span (stateCheck 6) 8 168 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_176 : span (stateCheck 6) 8 176 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_184 : span (stateCheck 6) 8 184 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_192 : span (stateCheck 6) 8 192 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_200 : span (stateCheck 6) 8 200 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_208 : span (stateCheck 6) 8 208 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_216 : span (stateCheck 6) 8 216 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_224 : span (stateCheck 6) 8 224 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_232 : span (stateCheck 6) 8 232 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_240 : span (stateCheck 6) 8 240 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_248 : span (stateCheck 6) 8 248 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_256 : span (stateCheck 6) 8 256 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_264 : span (stateCheck 6) 8 264 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_272 : span (stateCheck 6) 8 272 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_280 : span (stateCheck 6) 8 280 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_288 : span (stateCheck 6) 8 288 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_296 : span (stateCheck 6) 8 296 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_304 : span (stateCheck 6) 8 304 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_312 : span (stateCheck 6) 8 312 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_320 : span (stateCheck 6) 8 320 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_328 : span (stateCheck 6) 8 328 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_336 : span (stateCheck 6) 8 336 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_344 : span (stateCheck 6) 8 344 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_352 : span (stateCheck 6) 8 352 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_360 : span (stateCheck 6) 8 360 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_368 : span (stateCheck 6) 8 368 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_376 : span (stateCheck 6) 8 376 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_384 : span (stateCheck 6) 8 384 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_392 : span (stateCheck 6) 8 392 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_400 : span (stateCheck 6) 8 400 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_408 : span (stateCheck 6) 8 408 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_416 : span (stateCheck 6) 8 416 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_424 : span (stateCheck 6) 8 424 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_432 : span (stateCheck 6) 8 432 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_440 : span (stateCheck 6) 8 440 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_448 : span (stateCheck 6) 8 448 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_456 : span (stateCheck 6) 8 456 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_464 : span (stateCheck 6) 8 464 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_472 : span (stateCheck 6) 8 472 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_480 : span (stateCheck 6) 8 480 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_488 : span (stateCheck 6) 8 488 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_496 : span (stateCheck 6) 8 496 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_504 : span (stateCheck 6) 8 504 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_512 : span (stateCheck 6) 8 512 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_520 : span (stateCheck 6) 8 520 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_528 : span (stateCheck 6) 8 528 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_536 : span (stateCheck 6) 8 536 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_544 : span (stateCheck 6) 8 544 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_552 : span (stateCheck 6) 8 552 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_560 : span (stateCheck 6) 8 560 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_568 : span (stateCheck 6) 8 568 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_576 : span (stateCheck 6) 8 576 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_584 : span (stateCheck 6) 8 584 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_592 : span (stateCheck 6) 8 592 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_600 : span (stateCheck 6) 8 600 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_608 : span (stateCheck 6) 8 608 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_616 : span (stateCheck 6) 8 616 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_624 : span (stateCheck 6) 8 624 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_632 : span (stateCheck 6) 8 632 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_640 : span (stateCheck 6) 8 640 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_648 : span (stateCheck 6) 8 648 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_656 : span (stateCheck 6) 8 656 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_664 : span (stateCheck 6) 8 664 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_672 : span (stateCheck 6) 8 672 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_680 : span (stateCheck 6) 8 680 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_688 : span (stateCheck 6) 8 688 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_696 : span (stateCheck 6) 8 696 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_704 : span (stateCheck 6) 8 704 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_712 : span (stateCheck 6) 8 712 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_720 : span (stateCheck 6) 8 720 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_728 : span (stateCheck 6) 8 728 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_736 : span (stateCheck 6) 8 736 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_744 : span (stateCheck 6) 8 744 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_752 : span (stateCheck 6) 8 752 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_760 : span (stateCheck 6) 8 760 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_768 : span (stateCheck 6) 8 768 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_776 : span (stateCheck 6) 8 776 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_784 : span (stateCheck 6) 8 784 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_792 : span (stateCheck 6) 8 792 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_6_800 : span (stateCheck 6) 5 800 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_6 : span (stateCheck 6) 805 0 = true := by
  apply span_join (b := 797) c_6_0
  apply span_join (b := 789) c_6_8
  apply span_join (b := 781) c_6_16
  apply span_join (b := 773) c_6_24
  apply span_join (b := 765) c_6_32
  apply span_join (b := 757) c_6_40
  apply span_join (b := 749) c_6_48
  apply span_join (b := 741) c_6_56
  apply span_join (b := 733) c_6_64
  apply span_join (b := 725) c_6_72
  apply span_join (b := 717) c_6_80
  apply span_join (b := 709) c_6_88
  apply span_join (b := 701) c_6_96
  apply span_join (b := 693) c_6_104
  apply span_join (b := 685) c_6_112
  apply span_join (b := 677) c_6_120
  apply span_join (b := 669) c_6_128
  apply span_join (b := 661) c_6_136
  apply span_join (b := 653) c_6_144
  apply span_join (b := 645) c_6_152
  apply span_join (b := 637) c_6_160
  apply span_join (b := 629) c_6_168
  apply span_join (b := 621) c_6_176
  apply span_join (b := 613) c_6_184
  apply span_join (b := 605) c_6_192
  apply span_join (b := 597) c_6_200
  apply span_join (b := 589) c_6_208
  apply span_join (b := 581) c_6_216
  apply span_join (b := 573) c_6_224
  apply span_join (b := 565) c_6_232
  apply span_join (b := 557) c_6_240
  apply span_join (b := 549) c_6_248
  apply span_join (b := 541) c_6_256
  apply span_join (b := 533) c_6_264
  apply span_join (b := 525) c_6_272
  apply span_join (b := 517) c_6_280
  apply span_join (b := 509) c_6_288
  apply span_join (b := 501) c_6_296
  apply span_join (b := 493) c_6_304
  apply span_join (b := 485) c_6_312
  apply span_join (b := 477) c_6_320
  apply span_join (b := 469) c_6_328
  apply span_join (b := 461) c_6_336
  apply span_join (b := 453) c_6_344
  apply span_join (b := 445) c_6_352
  apply span_join (b := 437) c_6_360
  apply span_join (b := 429) c_6_368
  apply span_join (b := 421) c_6_376
  apply span_join (b := 413) c_6_384
  apply span_join (b := 405) c_6_392
  apply span_join (b := 397) c_6_400
  apply span_join (b := 389) c_6_408
  apply span_join (b := 381) c_6_416
  apply span_join (b := 373) c_6_424
  apply span_join (b := 365) c_6_432
  apply span_join (b := 357) c_6_440
  apply span_join (b := 349) c_6_448
  apply span_join (b := 341) c_6_456
  apply span_join (b := 333) c_6_464
  apply span_join (b := 325) c_6_472
  apply span_join (b := 317) c_6_480
  apply span_join (b := 309) c_6_488
  apply span_join (b := 301) c_6_496
  apply span_join (b := 293) c_6_504
  apply span_join (b := 285) c_6_512
  apply span_join (b := 277) c_6_520
  apply span_join (b := 269) c_6_528
  apply span_join (b := 261) c_6_536
  apply span_join (b := 253) c_6_544
  apply span_join (b := 245) c_6_552
  apply span_join (b := 237) c_6_560
  apply span_join (b := 229) c_6_568
  apply span_join (b := 221) c_6_576
  apply span_join (b := 213) c_6_584
  apply span_join (b := 205) c_6_592
  apply span_join (b := 197) c_6_600
  apply span_join (b := 189) c_6_608
  apply span_join (b := 181) c_6_616
  apply span_join (b := 173) c_6_624
  apply span_join (b := 165) c_6_632
  apply span_join (b := 157) c_6_640
  apply span_join (b := 149) c_6_648
  apply span_join (b := 141) c_6_656
  apply span_join (b := 133) c_6_664
  apply span_join (b := 125) c_6_672
  apply span_join (b := 117) c_6_680
  apply span_join (b := 109) c_6_688
  apply span_join (b := 101) c_6_696
  apply span_join (b := 93) c_6_704
  apply span_join (b := 85) c_6_712
  apply span_join (b := 77) c_6_720
  apply span_join (b := 69) c_6_728
  apply span_join (b := 61) c_6_736
  apply span_join (b := 53) c_6_744
  apply span_join (b := 45) c_6_752
  apply span_join (b := 37) c_6_760
  apply span_join (b := 29) c_6_768
  apply span_join (b := 21) c_6_776
  apply span_join (b := 13) c_6_784
  apply span_join (b := 5) c_6_792
  exact c_6_800
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_0 : span (stateCheck 7) 8 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_8 : span (stateCheck 7) 8 8 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_16 : span (stateCheck 7) 8 16 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_24 : span (stateCheck 7) 8 24 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_32 : span (stateCheck 7) 8 32 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_40 : span (stateCheck 7) 8 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_48 : span (stateCheck 7) 8 48 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_7_56 : span (stateCheck 7) 5 56 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_7 : span (stateCheck 7) 61 0 = true := by
  apply span_join (b := 53) c_7_0
  apply span_join (b := 45) c_7_8
  apply span_join (b := 37) c_7_16
  apply span_join (b := 29) c_7_24
  apply span_join (b := 21) c_7_32
  apply span_join (b := 13) c_7_40
  apply span_join (b := 5) c_7_48
  exact c_7_56
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem c_8_0 : span (stateCheck 8) 1 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem all_8 : span (stateCheck 8) 1 0 = true := by
  exact c_8_0

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem lowerBound : ∀ t, HasCircuitSize 6 targetFn t → 9 ≤ t := by
  refine prove_base 6 88 8 targetFn sampleRows inputMasks [] stateCount stateHash parentSteps
    ⟨pt 6 1, pt 6 3, by decide +kernel⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide) ?_
  intro s hs
  interval_cases s
  · exact fun j hj => span_ok all_0 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_1 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_2 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_3 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_4 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_5 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_6 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_7 j (Nat.zero_le j) hj
  · exact fun j hj => span_ok all_8 j (Nat.zero_le j) hj

theorem targetEq : targetFn = (fun x : Fin 6 → Bool =>
    (18374403832151735944 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) := by
  funext x
  rfl

def witnessCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
      ⟨.or, [0, 1]⟩,
      ⟨.or, [3, 5]⟩,
      ⟨.and, [6, 7]⟩,
      ⟨.or, [1, 4]⟩,
      ⟨.and, [0, 9]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.and, [2, 11]⟩,
      ⟨.or, [8, 10]⟩,
      ⟨.or, [13, 12]⟩], output := 14 }

theorem witnessFanIn : PEqualNP.MetaComplexity.FanInTwo witnessCircuit := by
  simp [PEqualNP.MetaComplexity.FanInTwo, witnessCircuit]

theorem witnessSize : witnessCircuit.size ≤ 9 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem witnessComputes : ∀ x : Fin 6 → Bool,
    witnessCircuit.eval (List.ofFn x) = targetFn x := by
  decide +kernel

theorem upperBound : PEqualNP.MetaComplexity.HasCircuitSize 6 targetFn 9 :=
  ⟨witnessCircuit, witnessFanIn, witnessSize, witnessComputes⟩

end PEqualNP.Outside.V_meta_9945__k9

theorem PEqualNP.Outside.V_meta_9945__k9 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18374403832151735944 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 9 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (18374403832151735944 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 9 ≤ t) := by
  constructor
  · simpa only [PEqualNP.Outside.V_meta_9945__k9.targetEq] using PEqualNP.Outside.V_meta_9945__k9.upperBound
  · intro t ht
    apply PEqualNP.Outside.V_meta_9945__k9.lowerBound t
    simpa only [PEqualNP.Outside.V_meta_9945__k9.targetEq] using ht
