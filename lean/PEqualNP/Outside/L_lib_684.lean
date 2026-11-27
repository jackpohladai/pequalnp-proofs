import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

namespace PEqualNP.Outside.L_lib_684_aux.Tilt684
open Finset
noncomputable section

abbrev State (q : ℕ) := Bool × Equiv.Perm (Fin q)

set_option maxHeartbeats 1200000 in
private lemma pair_perm {α : Type*} [DecidableEq α] {i j k l : α} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ e : Equiv.Perm α, e i = k ∧ e j = l := by
  let a := Equiv.swap i k
  have hai : a i = k := Equiv.swap_apply_left ..
  have haj : a j ≠ k := hai ▸ a.injective.ne hij.symm
  refine ⟨a.trans (Equiv.swap (a j) l), ?_, ?_⟩
  · change Equiv.swap (a j) l (a i) = k
    rw [hai, Equiv.swap_apply_of_ne_of_ne haj.symm hkl]
  · exact Equiv.swap_apply_left ..

set_option maxHeartbeats 1200000 in
private lemma expand_sq {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (s : α → β → ℝ) (x : β → ℝ) :
    (∑ t, w t * (∑ i, s t i * x i)^2) =
      ∑ i, ∑ j, (∑ t, w t * (s t i * s t j)) * (x i * x j) := by
  simp only [sq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro t _
  ring

set_option maxHeartbeats 1200000 in
private lemma iso {q : ℕ} (hq : 2 ≤ q) {α : Type*} [Fintype α]
    (w : α → ℝ) (s : α → Fin q → ℝ) (hw : ∑ t, w t = 1)
    (hdiag : ∀ t i, s t i * s t i = 1)
    (hsym : ∀ i j k l, i ≠ j → k ≠ l →
     (∑ t, w t * (s t i * s t j)) = ∑ t, w t * (s t k * s t l))
    (hall : (∑ t, w t * (∑ i, s t i)^2) = q) (x : Fin q → ℝ) :
    (∑ t, w t * (∑ i, s t i * x i)^2) = ∑ i, (x i)^2 := by
  classical
  let i₀ : Fin q := ⟨0, by omega⟩
  let i₁ : Fin q := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by intro h; have := congrArg Fin.val h; simp [i₀,i₁] at this
  let c := ∑ t, w t * (s t i₀ * s t i₁)
  have cov (i j : Fin q) : (∑ t, w t * (s t i * s t j)) =
       c + (if i = j then 1-c else 0) := by
    by_cases h : i = j
    · subst j; simp [hdiag,hw]
    · simpa [h] using hsym i j i₀ i₁ h hi
  have ht := expand_sq w s (fun _ => 1)
  simp only [mul_one, one_mul, cov, Finset.sum_add_distrib] at ht
  simp [hall, Finset.sum_add_distrib, nsmul_eq_mul] at ht
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hzero : ((q : ℝ)*((q : ℝ)-1))*c = 0 := by linarith only [ht]
  have hc : c = 0 := (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero (by linarith) (by linarith))
  rw [expand_sq]; simp [cov, hc, sq, ite_mul]

set_option maxHeartbeats 1200000 in
private lemma signed_sum {q : ℕ} (S : Finset (Fin q)) (x : Fin q → ℝ) :
    (∑ i, (if i ∈ S then (-1 : ℝ) else 1) * x i) =
       (∑ i ∈ Sᶜ, x i) - ∑ i ∈ S, x i := by
  classical
  rw [← Finset.sum_add_sum_compl S]
  have h1 : (∑ i ∈ S, (if i ∈ S then (-1 : ℝ) else 1) * x i) = -∑ i ∈ S, x i := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (by intro i hi; simp [hi])
  have h2 : (∑ i ∈ Sᶜ, (if i ∈ S then (-1 : ℝ) else 1) * x i) = ∑ i ∈ Sᶜ, x i := by
    exact Finset.sum_congr rfl (by intro i hi; simp [Finset.mem_compl.mp hi])
  rw [h1,h2]; ring

set_option maxHeartbeats 1200000 in
private lemma signed_bound {q : ℕ} (S : Finset (Fin q)) (m : ℝ)
    (h1 : (S.card : ℝ) ≤ m) (h2 : (Sᶜ.card : ℝ) ≤ m)
    (x : Fin q → ℝ) (hx : ∀ j, 0 ≤ x j) :
    (∑ i, (if i ∈ S then (-1 : ℝ) else 1) * x i)^2 ≤ m * ∑ i, x i ^ 2 := by
  classical
  have hp (A : Finset (Fin q)) : 0 ≤ ∑ i ∈ A, x i := Finset.sum_nonneg fun _ _ => hx _
  have hb (A : Finset (Fin q)) (hA : (A.card : ℝ) ≤ m) :
      (∑ i ∈ A, x i)^2 ≤ m * ∑ i, x i ^ 2 := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1:ℝ)) x
    calc
      _ ≤ (A.card : ℝ) * ∑ i ∈ A, x i^2 := by simpa using hCS
      _ ≤ _ := mul_le_mul hA (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => sq_nonneg (x i))) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (h1.trans' (by positivity))
  rw [signed_sum]
  by_cases h : (∑ i ∈ Sᶜ, x i) ≤ ∑ i ∈ S, x i
  · have ht := mul_nonneg (hp Sᶜ) (sub_nonneg.mpr h)
    nlinarith [hb S h1, mul_nonneg (hp S) (hp Sᶜ)]
  · have ht := mul_nonneg (hp S) (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith [hb Sᶜ h2, mul_nonneg (hp S) (hp Sᶜ)]

set_option maxHeartbeats 1200000 in
private lemma reindex {q : ℕ} (e : Equiv.Perm (Fin q)) (f x : Fin q → ℝ) :
    (∑ i, f (e i) * x i) = ∑ i, f i * x (e.symm i) := by
  simpa using Equiv.sum_comp e (fun i => f i * x (e.symm i))


set_option maxHeartbeats 1200000 in
theorem finite_law (q : ℕ) (hq : 2 ≤ q) :
    ∃ (w M : State q → ℝ) (signs : State q → Fin q → Bool),
      (∀ t, 0 ≤ w t) ∧ (∑ t, w t = 1) ∧ (∀ t, 0 < M t) ∧
      (∑ t, w t * M t = (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)) ∧
      (∀ x : Fin q → ℝ, (∑ t, w t * (∑ i, (if signs t i then (-1 : ℝ) else 1) * x i)^2) = ∑ i, (x i)^2) ∧
      ∀ t (x : Fin q → ℝ), (∀ i, 0 ≤ x i) →
        (∑ i, (if signs t i then (-1 : ℝ) else 1) * x i)^2 ≤ M t * ∑ i, (x i)^2 := by
  classical
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin q)))
      (n := q/2) (by simp; omega)
  let n : ℝ := Fintype.card (Equiv.Perm (Fin q))
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  let a : ℝ := if q%2 = 0 then 1/(q:ℝ) else 1/((q:ℝ)+1)
  let w : State q → ℝ := fun t => (if t.1 then a else 1-a) / n
  let M : State q → ℝ := fun t => if t.1 then q else (q:ℝ) - (S.card:ℝ)
  let signs : State q → Fin q → Bool := fun t i => if t.1 then false else decide (t.2 i ∈ S)
  let s : State q → Fin q → ℝ := fun t i => if signs t i then -1 else 1
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hSC : (Sᶜ.card : ℝ) = (q:ℝ) - S.card := by
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (by rw [hS]; omega)]
  have hS2 : 2*S.card ≤ q := by omega
  have hS2' : 2*(S.card:ℝ) ≤ q := by exact_mod_cast hS2
  have ha : 0 ≤ a := by dsimp [a]; split <;> positivity
  have ha' : a ≤ 1 := by dsimp [a]; split <;> apply (div_le_iff₀ (by positivity)).mpr <;> linarith
  have avg (f : Bool → ℝ) : (∑ t : State q, w t * f t.1) = (1-a)*f false + a*f true := by
    rw [Fintype.sum_prod_type,Fintype.sum_bool]
    simp [w, nsmul_eq_mul, ← show (Fintype.card (Equiv.Perm (Fin q)) : ℝ) = n from rfl]
    change _ = _
    dsimp only [n] at hn ⊢
    field_simp [hn.ne'] <;> ring
  have hw : ∑ t, w t = 1 := by simpa using avg (fun _ => 1)
  have hdiag : ∀ t i, s t i * s t i = 1 := by
    intro t i; dsimp only [s]; cases signs t i <;> norm_num
  have hsym (i j k l : Fin q) (hij : i ≠ j) (hkl : k ≠ l) :
      (∑ t, w t * (s t i * s t j)) = ∑ t, w t * (s t k * s t l) := by
    obtain ⟨e,he,he'⟩ := pair_perm hij hkl
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro u _
    have h := Equiv.sum_comp (Equiv.mulRight e) (fun p : Equiv.Perm (Fin q) => w (u,p) * (s (u,p) i * s (u,p) j))
    simpa [w,s,signs,Equiv.Perm.mul_apply,he,he'] using h.symm
  have sum_bal (e : Equiv.Perm (Fin q)) : (∑ i, s (false,e) i) = (q:ℝ)-2*S.card := by
    have h := Equiv.sum_comp e (fun i => if i ∈ S then (-1:ℝ) else 1)
    have h' := signed_sum S (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one, hSC] at h'
    simp [s,signs] at h ⊢
    linarith
  have sh (t : State q) : (∑ i, s t i)^2 = (if t.1 then (q:ℝ)^2 else ((q:ℝ)-2*S.card)^2) := by
    obtain ⟨u,e⟩ := t; cases u
    · simp [sum_bal]
    · simp [s,signs]
  have moments : (1-a)*((q:ℝ)-2*S.card)^2 + a*(q:ℝ)^2 = q ∧
      (1-a)*((q:ℝ)-S.card) + a*(q:ℝ) = (q:ℝ)/2 + if q%2=0 then 1/2 else (q:ℝ)/(q+1) := by
    by_cases he : q%2=0
    · have hs : 2*S.card = q := by omega
      have hs' : 2*(S.card:ℝ) = q := by exact_mod_cast hs
      have hs2 : (S.card:ℝ) = q/2 := by linarith
      simp only [a,he,ite_true,hs2]; constructor <;> field_simp [show (q:ℝ) ≠ 0 by positivity] <;> ring
    · have hs : 2*S.card+1 = q := by omega
      have hs' : 2*(S.card:ℝ)+1 = q := by exact_mod_cast hs
      have hs2 : (S.card:ℝ) = (q-1)/2 := by linarith
      simp only [a,he,ite_false,hs2]; constructor <;> field_simp [show (q:ℝ)+1 ≠ 0 by positivity] <;> ring
  have hall : (∑ t, w t * (∑ i, s t i)^2) = q := by
    simp_rw [sh]
    exact (avg (fun u => if u then (q:ℝ)^2 else ((q:ℝ)-2*S.card)^2)).trans moments.1
  refine ⟨w,M,signs,?_,hw,?_,?_,iso hq w s hw hdiag hsym hall,?_⟩
  · intro t; dsimp [w]; split <;> exact div_nonneg (by linarith) hn.le
  · intro t; dsimp [M]; split <;> linarith
  · exact (avg (fun u => if u then (q:ℝ) else (q:ℝ)-S.card)).trans moments.2
  · rintro ⟨u,e⟩ x hx; cases u
    · simp only [signs, M, Bool.false_eq_true, if_false, decide_eq_true_eq]
      rw [reindex e (fun j => if j ∈ S then (-1:ℝ) else 1) x]
      have h := signed_bound S ((q:ℝ)-S.card) (by linarith) hSC.le (fun i => x (e.symm i)) (fun i => hx _)
      simpa using h.trans_eq (congrArg (fun z => ((q:ℝ)-S.card) * z) (Equiv.sum_comp e.symm (fun i => x i ^ 2)))
    · simp [signs,M]
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q)) (fun _ => (1:ℝ)) x

end
end PEqualNP.Outside.L_lib_684_aux.Tilt684

namespace PEqualNP.Outside.L_lib_684_aux.Sampling

private lemma exp_quad {t : ℝ} (ht : |t| ≤ 1) :
    Real.exp t ≤ 1 + t + (3 / 4 : ℝ) * t^2 := by
  have H := Real.exp_bound (n := 2) ht (by decide)
  norm_num [Finset.sum_range_succ, sq_abs] at H
  linarith [(abs_le.mp H).2]

private lemma mgf {A : Type*} [Fintype A] (prob z : A → ℝ)
    (hp : ∀ a, 0 ≤ prob a) (h1 : ∑ a, prob a = 1)
    (hz : ∀ a, 0 ≤ z a) {L c : ℝ} (hb : ∀ a, z a ≤ L)
    (hm : ∑ a, prob a * z a = 1) (hc : |c| * L ≤ 1) :
    ∑ a, prob a * Real.exp (c * z a) ≤ Real.exp (c + (3/4 : ℝ) * c^2 * L) := by
  calc
    _ ≤ ∑ a, prob a * (1 + c * z a + (3/4 : ℝ) * c^2 * L * z a) := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left _ (hp a)
      have ht : |c * z a| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (hz a)]
        exact (mul_le_mul_of_nonneg_left (hb a) (abs_nonneg _)).trans hc
      have hz2 := mul_le_mul_of_nonneg_right (hb a) (hz a)
      have hc2 : 0 ≤ (3/4 : ℝ) * c^2 := by positivity
      nlinarith [exp_quad ht, mul_le_mul_of_nonneg_left hz2 hc2]
    _ = 1 + c + (3/4 : ℝ) * c^2 * L := by
      calc
        _ = ∑ a, (prob a + c * (prob a * z a) + ((3/4 : ℝ)*c^2*L) * (prob a * z a)) := by
          apply Finset.sum_congr rfl; intro a _; ring
        _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h1, hm, mul_one]
    _ ≤ _ := by linarith [Real.add_one_le_exp (c + (3/4 : ℝ)*c^2*L)]

private lemma mgf_many {A : Type*} [Fintype A] (prob z : A → ℝ)
    (hp : ∀ a, 0 ≤ prob a) (h1 : ∑ a, prob a = 1)
    (hz : ∀ a, 0 ≤ z a) {L c : ℝ} (hb : ∀ a, z a ≤ L)
    (hm : ∑ a, prob a * z a = 1) (hc : |c| * L ≤ 1) (N : ℕ) :
    ∑ s : Fin N → A, (∏ j, prob (s j)) * Real.exp (c * ∑ j, z (s j)) ≤
      Real.exp ((N:ℝ) * (c + (3/4 : ℝ) * c^2 * L)) := by
  classical
  calc
    _ = (∑ a, prob a * Real.exp (c * z a))^N := by
      rw [Fintype.sum_pow]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    _ ≤ (Real.exp (c + (3/4 : ℝ) * c^2 * L))^N := by
      apply pow_le_pow_left₀ _ (mgf prob z hp h1 hz hb hm hc)
      exact Finset.sum_nonneg fun a _ => mul_nonneg (hp a) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_nat_mul]

private lemma risk {A : Type*} [Fintype A] (prob z : A → ℝ)
    (hp : ∀ a, 0 ≤ prob a) (h1 : ∑ a, prob a = 1)
    (hz : ∀ a, 0 ≤ z a) {L c e : ℝ} (hb : ∀ a, z a ≤ L)
    (hm : ∑ a, prob a * z a = 1) (hc : |c| * L ≤ 1) (N : ℕ) :
    ∑ s : Fin N → A, (∏ j, prob (s j)) *
      Real.exp (c * ((∑ j, z (s j)) - (N:ℝ)) - (N:ℝ) * e) ≤
      Real.exp ((N:ℝ) * ((3/4 : ℝ) * c^2 * L - e)) := by
  let u := -(N:ℝ) * c - (N:ℝ) * e
  calc
    _ = (∑ s : Fin N → A, (∏ j, prob (s j)) * Real.exp (c * ∑ j, z (s j))) *
          Real.exp u := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [u]
      ring
    _ ≤ Real.exp ((N:ℝ) * (c + (3/4 : ℝ) * c^2 * L)) * Real.exp u :=
      mul_le_mul_of_nonneg_right (mgf_many prob z hp h1 hz hb hm hc N) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [u]; ring

theorem exists_samples {A I : Type*} [Fintype A] [Fintype I]
    (prob : A → ℝ) (z : I → A → ℝ)
    (hp : ∀ a, 0 ≤ prob a) (h1 : ∑ a, prob a = 1)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hz : ∀ i a, 0 ≤ z i a) (hb : ∀ i a, z i a ≤ L)
    (hm : ∀ i, ∑ a, prob a * z i a = 1) (N : ℕ) (hN : 0 < N)
    (hcard : 2 * (Fintype.card I : ℝ) * Real.exp (-(N:ℝ) * ε^2 / (3*L)) < 1) :
    ∃ s : Fin N → A, ∀ i, |(∑ j, z i (s j)) / (N:ℝ) - 1| ≤ ε := by
  classical
  let c := 2 * ε / (3*L)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : |c| * L ≤ 1 := by
    rw [abs_of_pos hc]
    dsimp [c]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hε1 hL.le]
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  let wt := fun s : Fin N → A => ∏ j, prob (s j)
  let off := fun (i : I) (s : Fin N → A) => (∑ j, z i (s j)) - (N:ℝ)
  let arg := fun (v : ℝ) (i : I) (s : Fin N → A) => v * off i s - (N:ℝ) * (c*ε)
  let cap := Real.exp (-(N:ℝ)*ε^2/(3*L))
  let B := fun i s => Real.exp (arg c i s) + Real.exp (arg (-c) i s)
  have hwt : ∀ s, 0 ≤ wt s := fun s => Finset.prod_nonneg fun j _ => hp (s j)
  have hw1 : ∑ s, wt s = 1 := by
    dsimp [wt]
    rw [← Fintype.sum_pow, h1, one_pow]
  have harg (i : I) (v : ℝ) (hv : |v| = |c|) : ∑ s, wt s * Real.exp (arg v i s) ≤ cap := by
    have hv2 : v^2 = c^2 := by
      rw [← sq_abs v, hv, sq_abs]
    apply (risk prob (z i) hp h1 (hz i) (hb i) (hm i) (hv ▸ hsmall) N).trans
    dsimp [cap]
    apply Real.exp_le_exp.mpr
    rw [hv2]
    dsimp [c]
    apply le_of_eq
    field_simp
    ring
  have hB (i : I) : ∑ s, wt s * B i s ≤ 2*cap := by
    simp only [B, mul_add, Finset.sum_add_distrib]
    linarith [harg i c rfl, harg i (-c) (abs_neg _)]
  have hbudget : (∑ s, wt s * ∑ i, B i s) < 1 := by
    calc
      _ = ∑ i, ∑ s, wt s * B i s := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ _ : I, 2*cap := Finset.sum_le_sum fun i _ => hB i
      _ = 2*(Fintype.card I : ℝ)*cap := by simp [nsmul_eq_mul]; ring
      _ < _ := hcard
  obtain ⟨s, hs⟩ : ∃ s, (∑ i, B i s) < 1 := by
    by_contra! H
    have : (∑ s, wt s * 1) ≤ ∑ s, wt s * ∑ i, B i s := by
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (H s) (hwt s)
    simp only [mul_one, hw1] at this
    linarith
  refine ⟨s, fun i => ?_⟩
  have hi : B i s < 1 :=
    lt_of_le_of_lt (Finset.single_le_sum (f := fun i => B i s)
      (fun j _ => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Finset.mem_univ i)) hs
  dsimp only [B] at hi
  have hup : arg c i s < 0 := Real.exp_lt_one_iff.mp (by linarith [Real.exp_pos (arg (-c) i s)])
  have hlo : arg (-c) i s < 0 := Real.exp_lt_one_iff.mp (by linarith [Real.exp_pos (arg c i s)])
  dsimp only [arg] at hup hlo
  have hu : off i s < (N:ℝ) * ε := (mul_lt_mul_iff_right₀ hc).mp (by linarith only [hup])
  have hl : -((N:ℝ) * ε) < off i s := (mul_lt_mul_iff_right₀ hc).mp (by linarith only [hlo])
  dsimp only [off] at hu hl
  apply abs_le.mpr
  constructor
  · apply le_sub_iff_add_le.mpr
    apply (le_div_iff₀ hN').mpr
    linarith
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hN').mpr
    linarith

end PEqualNP.Outside.L_lib_684_aux.Sampling

open Finset
namespace PEqualNP.Outside.L_lib_684_aux

noncomputable def gridTarg {q b : ℕ} (x : Fin b → Fin q → ℝ) : ℝ :=
  ∏ i, ∑ j, (x i j)^2

noncomputable def gridEst {q b t : ℕ} (sg : Fin t → Fin b → Fin q → Bool)
    (w : Fin t → ℝ) (x : Fin b → Fin q → ℝ) : ℝ :=
  ∑ h, w h * ∏ i, (∑ j, (if sg h i j then (-1:ℝ) else 1) * x i j)^2

noncomputable def gridErr {q b t : ℕ} (sg : Fin t → Fin b → Fin q → Bool)
    (w : Fin t → ℝ) (x : Fin b → Fin q → ℝ) : ℝ :=
  gridEst sg w x - gridTarg x

lemma gridUpdSum {n : ℕ} (f : Fin n → ℝ → ℝ) (x : Fin n → ℝ) (j : Fin n) (u : ℝ) :
    ∑ k, f k (Function.update x j u k) =
      (∑ k ∈ Finset.univ.erase j, f k (x k)) + f j u := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

lemma gridUpdProd {b : ℕ} {V : Type*} (f : Fin b → V → ℝ) (x : Fin b → V) (i : Fin b) (u : V) :
    ∏ k, f k (Function.update x i u k) =
      (∏ k ∈ Finset.univ.erase i, f k (x k)) * f i u := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

lemma gridProdBlend {b : ℕ} {V : Type*} (f : Fin b → V → ℝ) (x : Fin b → V)
    (i : Fin b) (L H E : V) (l r d : ℝ)
    (he : l*f i L + r*f i H = f i (x i) + d*f i E) :
    l*(∏ k, f k (Function.update x i L k)) + r*(∏ k, f k (Function.update x i H k)) =
      (∏ k, f k (x k)) + d*(∏ k, f k (Function.update x i E k)) := by
  rw [gridUpdProd, gridUpdProd, gridUpdProd,
    ← Finset.prod_erase_mul _ (fun k => f k (x k)) (Finset.mem_univ i)]
  linear_combination (∏ k ∈ Finset.univ.erase i, f k (x k))*he

lemma gridSquareBlend {q : ℕ} (s x : Fin q → ℝ) (j : Fin q) (a M d : ℝ)
    (hs : s j ^ 2 = 1) (hd : d * M^2 = (x j-a)*(a+1-x j)) :
    (a+1-x j)*(∑ k, s k * Function.update x j a k)^2 +
    (x j-a)*(∑ k, s k * Function.update x j (a+1) k)^2 =
    (∑ k, s k*x k)^2 + d*(∑ k, s k * (if k=j then M else 0))^2 := by
  have hE : (∑ k, s k * (if k=j then M else 0)) = s j*M := by
    simp [mul_ite]
  rw [hE, gridUpdSum (fun k v => s k * v), gridUpdSum (fun k v => s k * v),
    ← Finset.sum_erase_add _ (fun k => s k * x k) (Finset.mem_univ j)]
  linear_combination -(s j)^2 * hd

lemma gridNormBlend {q : ℕ} (x : Fin q → ℝ) (j : Fin q) (a M d : ℝ)
    (hd : d*M^2 = (x j-a)*(a+1-x j)) :
    (a+1-x j)*(∑ k, (Function.update x j a k)^2) +
    (x j-a)*(∑ k, (Function.update x j (a+1) k)^2) =
    (∑ k, (x k)^2) + d*(∑ k : Fin q, (if k=j then M else 0)^2) := by
  have hE : (∑ k : Fin q, (if k=j then M else 0)^2) = M^2 := by
    simp [ite_pow]
  rw [hE, gridUpdSum (fun _ v => v^2), gridUpdSum (fun _ v => v^2),
    ← Finset.sum_erase_add _ (fun k => (x k)^2) (Finset.mem_univ j)]
  linear_combination -hd

set_option maxHeartbeats 2400000 in
lemma gridInterpolate {q b t : ℕ} (sg : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ)
    (x : Fin b → Fin q → ℝ) (i : Fin b) (j : Fin q) (a M C : ℝ)
    (ha : a ≤ x i j) (hb : x i j ≤ a+1) (hM : 0 < M) (hC : 0 ≤ C)
    (hrow : M^2 ≤ ∑ k, (x i k)^2)
    (hL : let z := Function.update x i (Function.update (x i) j a)
          |gridErr sg w z| ≤ C*gridTarg z)
    (hH : let z := Function.update x i (Function.update (x i) j (a+1))
          |gridErr sg w z| ≤ C*gridTarg z)
    (hE : let z := Function.update x i (fun k => if k=j then M else 0)
          |gridErr sg w z| ≤ C*gridTarg z) :
    |gridErr sg w x| ≤ (C*(1+2/M^2))*gridTarg x := by
  classical
  let l := a+1-x i j
  let r := x i j-a
  let d := r*l/M^2
  have hl : 0 ≤ l := sub_nonneg.mpr hb
  have hr : 0 ≤ r := sub_nonneg.mpr ha
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hrl : r+l=1 := by dsimp [r,l]; ring
  have hrl1 : r*l ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 1-r) hl]
  have hM2 : 0 < M^2 := by positivity
  have hd : d*M^2 = r*l := div_mul_cancel₀ _ hM2.ne'
  have hdle : d ≤ 1/M^2 := (div_le_div_iff_of_pos_right hM2).2 hrl1
  let L := Function.update (x i) j a
  let H := Function.update (x i) j (a+1)
  let E := fun k : Fin q => if k=j then M else 0
  let zl := Function.update x i L
  let zh := Function.update x i H
  let ze := Function.update x i E
  change |gridErr sg w zl| ≤ C*gridTarg zl at hL
  change |gridErr sg w zh| ≤ C*gridTarg zh at hH
  change |gridErr sg w ze| ≤ C*gridTarg ze at hE
  have ht : l*gridTarg zl + r*gridTarg zh = gridTarg x + d*gridTarg ze :=
    gridProdBlend (fun (_ : Fin b) (y : Fin q → ℝ) => ∑ k, (y k)^2) x i L H E l r d
      (gridNormBlend (x i) j a M d hd)
  let sig := fun h k m => if sg h k m then (-1:ℝ) else 1
  let F := fun (h : Fin t) (k : Fin b) (y : Fin q → ℝ) => (∑ m, sig h k m*y m)^2
  have hF (h : Fin t) :
      l*(∏ k, F h k (zl k)) + r*(∏ k, F h k (zh k)) =
      (∏ k, F h k (x k)) + d*(∏ k, F h k (ze k)) := by
    apply gridProdBlend
    apply gridSquareBlend (sig h i) (x i) j a M d _ hd
    dsimp [sig]
    split <;> norm_num
  have hs : l*gridEst sg w zl + r*gridEst sg w zh =
      gridEst sg w x + d*gridEst sg w ze := by
    change l*(∑ h, w h*∏ k, F h k (zl k)) + r*(∑ h, w h*∏ k, F h k (zh k)) =
      (∑ h, w h*∏ k, F h k (x k)) + d*(∑ h, w h*∏ k, F h k (ze k))
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    linear_combination w h * hF h
  have he : gridErr sg w x = l*gridErr sg w zl + r*gridErr sg w zh - d*gridErr sg w ze := by
    unfold gridErr
    linear_combination ht - hs
  have heT : gridTarg ze ≤ gridTarg x := by
    unfold gridTarg
    change (∏ k, (fun (_ : Fin b) (y : Fin q → ℝ) => ∑ m, (y m)^2) k (Function.update x i E k)) ≤ _
    rw [gridUpdProd (fun (_ : Fin b) (y : Fin q → ℝ) => ∑ m, (y m)^2) x i E,
      ← Finset.prod_erase_mul _ (fun k => ∑ m, (x k m)^2) (Finset.mem_univ i)]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    simpa [E, ite_pow] using hrow
  have ht0 : 0 ≤ gridTarg x := Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : d * gridTarg ze ≤ (1/M^2)*gridTarg x :=
    (mul_le_mul_of_nonneg_left heT hd0).trans (mul_le_mul_of_nonneg_right hdle ht0)
  calc
    |gridErr sg w x| = |l*gridErr sg w zl + r*gridErr sg w zh - d*gridErr sg w ze| := by rw [he]
    _ ≤ (|l*gridErr sg w zl| + |r*gridErr sg w zh|) + |d*gridErr sg w ze| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ l*(C*gridTarg zl) + r*(C*gridTarg zh) + d*(C*gridTarg ze) := by
      simp only [abs_mul, abs_of_nonneg hl, abs_of_nonneg hr, abs_of_nonneg hd0]
      gcongr
    _ = C*(gridTarg x + 2*(d*gridTarg ze)) := by linear_combination C*ht
    _ ≤ C*(gridTarg x + 2*((1/M^2)*gridTarg x)) := by gcongr
    _ = (C*(1+2/M^2))*gridTarg x := by ring


lemma gridScaleTarg {q b : ℕ} (d : Fin b → ℝ) (x : Fin b → Fin q → ℝ) :
    gridTarg (fun i j => d i * x i j) = (∏ i, d i ^ 2) * gridTarg x := by
  simp only [gridTarg, mul_pow, ← Finset.mul_sum, Finset.prod_mul_distrib]

lemma gridScaleErr {q b t : ℕ} (sg : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ)
    (d : Fin b → ℝ) (x : Fin b → Fin q → ℝ) :
    gridErr sg w (fun i j => d i * x i j) = (∏ i, d i ^ 2) * gridErr sg w x := by
  rw [gridErr, gridScaleTarg, gridErr, mul_sub]
  congr 1
  unfold gridEst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have H (i : Fin b) :
      ∑ j, (if sg h i j then (-1 : ℝ) else 1) * (d i * x i j) =
      d i * ∑ j, (if sg h i j then (-1 : ℝ) else 1) * x i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [H, mul_pow, Finset.prod_mul_distrib]
  ring

lemma gridRowNormalize {q M : ℕ} (hq : 0 < q) (hM : 0 < (M:ℝ))
    (x : Fin q → ℝ) (hx : ∀ j, 0 ≤ x j) :
    ∃ (d : ℝ) (y : Fin q → ℝ), (∀ j, x j = d * y j) ∧
      (∀ j, 0 ≤ y j ∧ y j ≤ M) ∧ ∃ j, y j = M := by
  classical
  let z : Fin q := ⟨0, hq⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ x ⟨z, Finset.mem_univ z⟩
  have hmax (j : Fin q) : x j ≤ x k := hk j (Finset.mem_univ j)
  by_cases hz : x k = 0
  · refine ⟨0, fun _ => M, ?_, fun _ => ⟨hM.le, le_rfl⟩, k, rfl⟩
    intro j
    simpa using le_antisymm ((hmax j).trans_eq hz) (hx j)
  · have hp : 0 < x k := lt_of_le_of_ne (hx k) (Ne.symm hz)
    refine ⟨x k / M, fun j => M * x j / x k, ?_, ?_, k, ?_⟩
    · intro j
      field_simp
    · intro j
      refine ⟨div_nonneg (mul_nonneg hM.le (hx j)) hp.le, (div_le_iff₀ hp).2 ?_⟩
      exact mul_le_mul_of_nonneg_left (hmax j) hM.le
    · field_simp

def gridGood {q b : ℕ} (M : ℕ) (S : Finset (Fin b × Fin q)) (x : Fin b → Fin q → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j ∧ x i j ≤ M) ∧ (∀ i, ∃ j, x i j = M) ∧
  ∀ i j, (i,j) ∉ S → ∃ k : Fin (M+1), x i j = k.val

lemma gridAddGood {q b M : ℕ} {S : Finset (Fin b × Fin q)} {x : Fin b → Fin q → ℝ}
    {i : Fin b} {j : Fin q} (hx : gridGood M (insert (i,j) S) x)
    (hjm : x i j ≠ M) (k : Fin (M+1)) :
    gridGood M S (Function.update x i (Function.update (x i) j (k.val : ℝ))) := by
  classical
  have hkn : (k.val : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  refine ⟨?_, ?_, ?_⟩
  · intro i' j'
    by_cases hi : i' = i
    · subst i'
      by_cases hj : j' = j
      · subst j'
        simpa using And.intro (Nat.cast_nonneg (α := ℝ) k.val) hkn
      · simpa [Function.update_of_ne hj] using hx.1 i j'
    · simpa [Function.update_of_ne hi] using hx.1 i' j'
  · intro i'
    obtain ⟨l, hl⟩ := hx.2.1 i'
    refine ⟨l, ?_⟩
    by_cases hi : i' = i
    · subst i'
      have hlj : l ≠ j := fun h => hjm (h ▸ hl)
      simpa [Function.update_of_ne hlj] using hl
    · simpa [Function.update_of_ne hi] using hl
  · intro i' j' hs
    by_cases hi : i' = i
    · subst i'
      by_cases hj : j' = j
      · subst j'
        exact ⟨k, by simp⟩
      · have hin : (i,j') ∉ insert (i,j) S := by simp [hj, hs]
        simpa [Function.update_of_ne hj] using hx.2.2 i j' hin
    · have hin : (i',j') ∉ insert (i,j) S := by simp [hi, hs]
      simpa [Function.update_of_ne hi] using hx.2.2 i' j' hin

lemma gridSingletonGood {q b M : ℕ} {S : Finset (Fin b × Fin q)} {x : Fin b → Fin q → ℝ}
    {i : Fin b} {j : Fin q} (hx : gridGood M (insert (i,j) S) x) :
    gridGood M S (Function.update x i (fun k => if k=j then (M:ℝ) else 0)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i' j'
    by_cases hi : i' = i
    · subst i'
      by_cases hj : j'=j <;> simp [hj]
    · simpa [Function.update_of_ne hi] using hx.1 i' j'
  · intro i'
    by_cases hi : i' = i
    · subst i'
      exact ⟨j, by simp⟩
    · simpa [Function.update_of_ne hi] using hx.2.1 i'
  · intro i' j' hs
    by_cases hi : i'=i
    · subst i'
      by_cases hj : j'=j
      · exact ⟨⟨M, Nat.lt_succ_self M⟩, by simp [hj]⟩
      · exact ⟨⟨0, Nat.zero_lt_succ M⟩, by simp [hj]⟩
    · have hin : (i',j') ∉ insert (i,j) S := by simp [hi, hs]
      simpa [Function.update_of_ne hi] using hx.2.2 i' j' hin

lemma gridExtend {q b t M : ℕ} (hq : 0 < q) (hM : 4*(b+1)*q ≤ M)
    (ε : ℝ) (hε : 0 ≤ ε) (sg : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ)
    (hgrid : ∀ g : Fin b → Fin q → Fin (M+1),
      |gridErr sg w (fun i j => ((g i j).val:ℝ))| ≤ ε*gridTarg (fun i j => ((g i j).val:ℝ))) :
    ∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) →
      |gridErr sg w x| ≤ (2*ε)*gridTarg x := by
  classical
  have hMb : b*q ≤ M := by nlinarith [Nat.mul_pos (Nat.succ_pos b) hq]
  have hM4 : 4 ≤ M := by nlinarith [Nat.mul_pos (Nat.succ_pos b) hq]
  have hM4' : (4:ℝ) ≤ M := by exact_mod_cast hM4
  have hMp : 0 < (M:ℝ) := by linarith
  have hT (x : Fin b → Fin q → ℝ) : 0 ≤ gridTarg x := by
    unfold gridTarg
    exact Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  let C := fun n : ℕ => ε*(1+(n:ℝ)/M)
  have hC (n : ℕ) : 0 ≤ C n := by dsimp [C]; positivity
  have hstep (n : ℕ) (hn : n ≤ M) : C n * (1+2/(M:ℝ)^2) ≤ C (n+1) := by
    have hn' : (n:ℝ) ≤ M := by exact_mod_cast hn
    dsimp [C]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hε
    push_cast
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ (M:ℝ) - 4 by linarith) hMp.le]
  have H (S : Finset (Fin b × Fin q)) : ∀ x, gridGood M S x →
      |gridErr sg w x| ≤ C S.card * gridTarg x := by
    induction S using Finset.induction_on with
    | empty =>
      intro x hx
      have hp (i j) := hx.2.2 i j (Finset.notMem_empty _)
      choose g hg using hp
      have he : x = fun i j => ((g i j).val:ℝ) := funext fun i => funext fun j => hg i j
      subst x
      simpa [C] using hgrid g
    | @insert ij S hnot ih =>
      rcases ij with ⟨i,j⟩
      intro x hx
      rw [Finset.card_insert_of_notMem hnot]
      have hcard : S.card ≤ M := (by simpa using S.card_le_univ : S.card ≤ b*q).trans hMb
      by_cases hgj : ∃ k : Fin (M+1), x i j = k.val
      · have good : gridGood M S x := by
          refine ⟨hx.1, hx.2.1, ?_⟩
          intro i' j' hs
          by_cases he : (i',j') = (i,j)
          · cases he
            exact hgj
          · exact hx.2.2 i' j' (by simp [he, hs])
        have hc : C S.card ≤ C (S.card+1) := by
          dsimp [C]
          gcongr
          exact_mod_cast Nat.le_succ _
        exact (ih x good).trans (mul_le_mul_of_nonneg_right hc (hT x))
      · have hjm : x i j ≠ M := fun he => hgj ⟨⟨M, Nat.lt_succ_self M⟩, he⟩
        let a := ⌊x i j⌋₊
        have ha : (a:ℝ) ≤ x i j := Nat.floor_le (hx.1 i j).1
        have hb : x i j ≤ (a:ℝ)+1 := (Nat.lt_floor_add_one _).le
        have halt : (a:ℝ) < M := ha.trans_lt (lt_of_le_of_ne (hx.1 i j).2 hjm)
        have hak : a < M := by exact_mod_cast halt
        let kl : Fin (M+1) := ⟨a, by omega⟩
        let ku : Fin (M+1) := ⟨a+1, by omega⟩
        have hl := ih _ (gridAddGood hx hjm kl)
        have hu := ih _ (gridAddGood hx hjm ku)
        have hs := ih _ (gridSingletonGood hx)
        obtain ⟨k, hk⟩ := hx.2.1 i
        have hrow : (M:ℝ)^2 ≤ ∑ k, (x i k)^2 := by
          rw [← hk]
          exact Finset.single_le_sum (fun l _ => sq_nonneg (x i l)) (Finset.mem_univ k)
        have hi := gridInterpolate sg w x i j a M (C S.card) ha hb hMp (hC _) hrow hl
          (by simpa [ku] using hu) hs
        exact hi.trans (mul_le_mul_of_nonneg_right (hstep _ hcard) (hT x))
  intro x hx
  choose d y hxy hbnd hanchor using fun i => gridRowNormalize hq hMp (x i) (hx i)
  have he : x = fun i j => d i * y i j := funext fun i => funext (hxy i)
  rw [he, gridScaleErr, gridScaleTarg, abs_mul, abs_of_nonneg (show 0 ≤ ∏ i, d i^2 by positivity)]
  have hy : gridGood M Finset.univ y := ⟨hbnd, hanchor, by simp⟩
  have hc : C (Finset.univ : Finset (Fin b × Fin q)).card ≤ 2*ε := by
    have hn : ((Finset.univ : Finset (Fin b × Fin q)).card:ℝ) ≤ M := by exact_mod_cast (by simpa using hMb : (Finset.univ : Finset (Fin b × Fin q)).card ≤ M)
    have hd := (div_le_one hMp).mpr hn
    change ε * (1 + ((Finset.univ : Finset (Fin b × Fin q)).card:ℝ) / M) ≤ 2*ε
    nlinarith only [mul_nonneg hε (sub_nonneg.mpr hd)]
  have hg := (H _ y hy).trans (mul_le_mul_of_nonneg_right hc (hT y))
  calc
    _ ≤ (∏ i, d i^2)*((2*ε)*gridTarg y) := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := by ring

end PEqualNP.Outside.L_lib_684_aux

namespace PEqualNP.Outside.L_lib_684_aux

theorem asmSize (q b p : ℕ) (hp : 2 ≤ p) (K : ℝ) (hK : 0 < K) :
    let M := 72 * (b + 1) * q
    let I := Fin b → Fin q → Fin (M + 1)
    ∃ N : ℕ, 0 < N ∧ (N:ℝ) ≤ 1 + 192*(p:ℝ)^2*K^b *
        (2+(b:ℝ)*q*Real.log (2+72*((b:ℝ)+1)*q)) ∧
      2*(Fintype.card I:ℝ)*Real.exp (-(N:ℝ)*(1/(8*(p:ℝ)))^2/(3*K^b)) < 1 := by
  classical
  intro M I
  let B : ℝ := 2 + (M:ℝ)
  let S := 192 * (p:ℝ)^2 * K^b
  let H := 2 + (b:ℝ) * q * Real.log B
  have hpR : 0 < (p:ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hS : 0 < S := by dsimp [S]; positivity
  have hB : B = 2+72*((b:ℝ)+1)*q := by dsimp [B, M]; push_cast; ring
  have hB1 : 1 ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) M]
  have hBlog := Real.log_nonneg hB1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let N := ⌊S * H⌋₊ + 1
  have hlow : S * H < (N:ℝ) := by dsimp [N]; push_cast; exact Nat.lt_floor_add_one _
  have hhigh : (N:ℝ) ≤ 1 + S * H := by
    dsimp [N]; push_cast; linarith [Nat.floor_le (mul_nonneg hS.le hH)]
  refine ⟨N, Nat.zero_lt_succ _, by simpa only [S, H, hB] using hhigh, ?_⟩
  have hc : Fintype.card I = (M+1) ^ (q*b) := by simp [I, ← pow_mul]
  have hcR : (Fintype.card I:ℝ) ≤ B ^ (q*b) := by
    rw [hc]
    push_cast
    exact pow_le_pow_left₀ (by positivity) (by dsimp [B]; linarith) _
  have hex : Real.exp H = Real.exp 2 * B ^ (q*b) := by
    have hd : (b:ℝ)*q = ((q*b:ℕ):ℝ) := by push_cast; ring
    dsimp [H]
    rw [hd, Real.exp_add, Real.exp_nat_mul, Real.exp_log (lt_of_lt_of_le zero_lt_one hB1)]
  have h2 : (2:ℝ) < Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have hrate : H < (N:ℝ)/S := by rw [lt_div_iff₀ hS, mul_comm]; exact hlow
  have htail : 2*(Fintype.card I:ℝ) < Real.exp ((N:ℝ)/S) := calc
    2*(Fintype.card I:ℝ) ≤ 2*B^(q*b) := by gcongr
    _ < Real.exp 2*B^(q*b) := mul_lt_mul_of_pos_right h2 (pow_pos (lt_of_lt_of_le zero_lt_one hB1) _)
    _ = Real.exp H := hex.symm
    _ < Real.exp ((N:ℝ)/S) := Real.exp_lt_exp.mpr hrate
  have heq : -(N:ℝ)*(1/(8*(p:ℝ)))^2/(3*K^b) = -((N:ℝ)/S) := by
    dsimp [S]; field_simp <;> ring
  rw [heq, Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  exact htail

end PEqualNP.Outside.L_lib_684_aux

namespace PEqualNP.Outside.L_lib_684_aux

private lemma asmSumDiv {A : Type*} [Fintype A] (f : A → ℝ) (d : ℝ) :
    (∑ a, f a) / d = ∑ a, f a / d := by simp only [div_eq_mul_inv, Finset.sum_mul]

private lemma asmNormalize {R T D e : ℝ} (hT : 0 ≤ T) (he : 0 ≤ e) (hs : e ≤ 1/2)
    (hR : |R-T| ≤ e*T) (hD : |D-1| ≤ e) : |R/D - T| ≤ (4*e)*T := by
  have hh := (abs_le.mp hD).1
  have hd : 0 < D := by linarith
  rw [div_sub' hd.ne', abs_div, abs_of_pos hd, div_le_iff₀ hd]
  calc
    |R-D*T| = |(R-T) + T*(1-D)| := by congr 1; ring
    _ ≤ |R-T| + |T*(1-D)| := abs_add_le ..
    _ ≤ e*T + T*e := by
      rw [abs_mul, abs_of_nonneg hT, abs_sub_comm 1 D]
      exact add_le_add hR (mul_le_mul_of_nonneg_left hD hT)
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg he hT) (show 0 ≤ 2*D-1 by linarith)]

private lemma asmConvert {A I : Type*} [Fintype A] [Fintype I] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (f : I → A → ℝ) (T : I → ℝ)
    (hT : ∀ i, 0 ≤ T i) (hf : ∀ i a, 0 ≤ f i a) {L : ℝ} (hL : 1 ≤ L)
    (hb : ∀ i a, f i a ≤ L * T i) (hm : ∀ i, ∑ a, p a * f i a = T i)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) (N : ℕ) (hN : 0 < N)
    (hc : 2*(Fintype.card I:ℝ)*Real.exp (-(N:ℝ)*e^2/(3*L)) < 1) :
    ∃ s : Fin N → A, ∀ i, |(∑ j, f i (s j))/(N:ℝ) - T i| ≤ e*T i := by
  classical
  let z (i : I) (a : A) := if T i = 0 then 1 else f i a / T i
  have hz (i a) : 0 ≤ z i a := by
    dsimp [z]; split <;> first | positivity | exact div_nonneg (hf i a) (hT i)
  have hzb (i a) : z i a ≤ L := by
    dsimp [z]; split
    · exact hL
    · rename_i h
      exact (div_le_iff₀ (lt_of_le_of_ne (hT i) (Ne.symm h))).2 (hb i a)
  have hzm (i) : ∑ a, p a * z i a = 1 := by
    by_cases h : T i = 0
    · simpa [z,h] using hp1
    · simp only [z,h,ite_false,mul_div_assoc',← asmSumDiv,hm,div_self h]
  obtain ⟨s, hs⟩ := PEqualNP.Outside.L_lib_684_aux.Sampling.exists_samples p z hp hp1
    (zero_lt_one.trans_le hL) he he1 hz hzb hzm N hN hc
  refine ⟨s, fun i => ?_⟩
  have hid (a : A) : f i a = z i a * T i := by
    by_cases h : T i = 0
    · simpa [z,h] using (le_antisymm ((hb i a).trans_eq (by simp [h])) (hf i a))
    · simp [z,h]
  calc
    _ = |((∑ j, z i (s j))/(N:ℝ) - 1)*T i| := by
      simp_rw [hid]; rw [← Finset.sum_mul]; congr 1; ring
    _ ≤ _ := by rw [abs_mul, abs_of_nonneg (hT i)]; exact mul_le_mul_of_nonneg_right (hs i) (hT i)

lemma asmMain (q b p : ℕ) (hq : 2 ≤ q) (hp : 2 ≤ p) :
    let K := (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)
    ∃ (t : ℕ) (signs : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ),
      (∀ h, 0 ≤ w h) ∧ (∑ h : Fin t, w h) = 1 ∧
      (t : ℝ) ≤ 1 + 192*(p : ℝ)^2*K^b * (2+(b : ℝ)*q*Real.log (2+72*((b : ℝ)+1)*q)) ∧
      ∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) →
        ((p:ℝ)-1)*gridTarg x ≤ (p:ℝ)*gridEst signs w x ∧
        (p:ℝ)*gridEst signs w x ≤ ((p:ℝ)+1)*gridTarg x := by
  classical
  let K := (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)
  let m := 72*(b+1)*q
  let I := Fin b → Fin q → Fin (m+1)
  let A := Fin b → PEqualNP.Outside.L_lib_684_aux.Tilt684.State q
  let e := 1/(8*(p:ℝ))
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hp' : 0 < (p:ℝ) := by linarith
  have hk : 1 ≤ K := by
    dsimp [K]; split
    · linarith
    · have : 0 ≤ (q:ℝ)/(q+1) := by positivity
      linarith
  have hk' := zero_lt_one.trans_le hk
  have he : 0 < e := by dsimp [e]; positivity
  have he' : e ≤ 1/2 := by dsimp [e]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨N, hN, hsize, hc⟩ := asmSize q b p hp K hk'
  obtain ⟨w,M,sg,hw,_,hM,hK,hiso,henv⟩ := PEqualNP.Outside.L_lib_684_aux.Tilt684.finite_law q hq
  let d := fun a => w a * M a / K
  let c := fun a => K / M a
  let prob (a : A) := ∏ i, d (a i)
  let corr (a : A) := ∏ i, c (a i)
  let x (g : I) (i : Fin b) (j : Fin q) := ((g i j).val:ℝ)
  let T (g : I) := gridTarg (x g)
  let U (g : I) (a : A) := ∏ i, (∑ j, (if sg (a i) j then (-1:ℝ) else 1) * x g i j)^2
  let F (g : I) (a : A) := corr a * U g a
  have hd (a) : 0 ≤ d a := div_nonneg (mul_nonneg (hw a) (hM a).le) hk'.le
  have hc' (a) : 0 ≤ c a := div_nonneg hk'.le (hM a).le
  have hp0 (a : A) : 0 ≤ prob a := Finset.prod_nonneg fun i _ => hd _
  have hc0 (a : A) : 0 ≤ corr a := Finset.prod_nonneg fun i _ => hc' _
  have hd1 : ∑ a, d a = 1 := by
    dsimp only [d]; rw [← asmSumDiv, hK]; exact div_self hk'.ne'
  have hp1 : ∑ a, prob a = 1 := by
    change (∑ a : Fin b → _, ∏ i, d (a i)) = 1
    rw [← Fintype.prod_sum]; simp [hd1]
  have hT (g : I) : 0 ≤ T g := Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hF (g : I) (a : A) : 0 ≤ F g a := mul_nonneg (hc0 a) (Finset.prod_nonneg fun i _ => sq_nonneg _)
  have hb (g : I) (a : A) : F g a ≤ K^b*T g := by
    change (∏ i, c (a i)) * (∏ i, _) ≤ K^b * (∏ i, ∑ j, (x g i j)^2)
    rw [← Finset.prod_mul_distrib]
    calc
      _ ≤ ∏ i, (K * ∑ j, (x g i j)^2) := by
        apply Finset.prod_le_prod₀ (fun i _ => mul_nonneg (hc' _) (sq_nonneg _))
        intro i _
        calc
          _ ≤ c (a i) * (M (a i) * ∑ j, (x g i j)^2) :=
            mul_le_mul_of_nonneg_left (henv _ _ (fun _ => Nat.cast_nonneg _)) (hc' _)
          _ = _ := by dsimp only [c]; field_simp [(hM _).ne']
      _ = _ := by simp [Finset.prod_mul_distrib]
  have hm (g : I) : ∑ a, prob a * F g a = T g := by
    calc
      _ = ∑ a : A, ∏ i, (w (a i) * (∑ j, (if sg (a i) j then (-1:ℝ) else 1) * x g i j)^2) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp only [prob,F,corr,U]
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        dsimp only [d,c]; field_simp [hk'.ne',(hM _).ne']
      _ = _ := by
        rw [← Fintype.prod_sum (fun (i : Fin b) a => w a * (∑ j, (if sg a j then (-1:ℝ) else 1) * x g i j)^2)]
        exact Finset.prod_congr rfl fun i _ => hiso (x g i)
  obtain ⟨s, hs⟩ := asmConvert prob hp0 hp1 F T hT hF (one_le_pow₀ hk) hb hm he
    (he'.trans (by norm_num)) N hN hc
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  let raw (n : Fin N) := corr (s n)/(N:ℝ)
  let D := ∑ n, raw n
  let signs (n : Fin N) (i : Fin b) := sg (s n i)
  have hr (g : I) : |gridEst signs raw (x g) - T g| ≤ e*T g := by
    have H : gridEst signs raw (x g) = (∑ n, F g (s n))/(N:ℝ) := by
      unfold gridEst
      rw [asmSumDiv]
      apply Finset.sum_congr rfl
      intro n _
      change (corr (s n)/(N:ℝ))*U g (s n) = (corr (s n)*U g (s n))/(N:ℝ)
      ring
    rw [H]; exact hs g
  let j0 : Fin q := ⟨0, by omega⟩
  let v1 : Fin (m+1) := ⟨1, by dsimp [m]; nlinarith [Nat.mul_pos (Nat.succ_pos b) (show 0 < q by omega)]⟩
  let g0 : I := fun _ j => if j = j0 then v1 else 0
  have hx0 (i j) : x g0 i j = if j = j0 then 1 else 0 := by by_cases h : j = j0 <;> simp [x,g0,h,v1]
  have ht0 : T g0 = 1 := by simp [T,gridTarg,hx0,ite_pow]
  have hu0 (n : Fin N) (i : Fin b) : (∑ j, (if signs n i j then (-1:ℝ) else 1) * x g0 i j)^2 = 1 := by
    simp only [hx0, mul_ite, mul_one,mul_zero,Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    split <;> norm_num
  have hr0 : gridEst signs raw (x g0) = D := by simp only [gridEst,hu0,Finset.prod_const_one,mul_one,D]
  have hD : |D-1| ≤ e := by simpa only [hr0,ht0,mul_one] using hr g0
  have hDp : 0 < D := by linarith [(abs_le.mp hD).1]
  let wt (n : Fin N) := raw n / D
  have hwt (n : Fin N) : 0 ≤ wt n := div_nonneg (div_nonneg (hc0 _) hN'.le) hDp.le
  have hwt1 : ∑ n, wt n = 1 := by dsimp only [wt]; rw [← asmSumDiv]; exact div_self hDp.ne'
  refine ⟨N,signs,wt,hwt,hwt1,hsize,?_⟩
  have hgr (g : I) : |gridErr signs wt (x g)| ≤ (4*e)*T g := by
    have hh : gridEst signs wt (x g) = gridEst signs raw (x g)/D := by
      unfold gridEst; rw [asmSumDiv]; apply Finset.sum_congr rfl
      intro n _; dsimp only [wt]; ring
    rw [gridErr,hh]; exact asmNormalize (hT g) he.le he' (hr g) hD
  have hmg : 4*(b+1)*q ≤ m := by dsimp [m]; nlinarith [Nat.zero_le ((b+1)*q)]
  intro y hy
  have hg := gridExtend (by omega : 0 < q) hmg (4*e) (by positivity) signs wt hgr y hy
  rw [gridErr,abs_le] at hg
  have hp8 : (p:ℝ)*(2*(4*e)) = 1 := by dsimp only [e]; field_simp; norm_num
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hg.1 hp'.le, congrArg (fun z : ℝ => z * gridTarg y) hp8]
  · nlinarith [mul_le_mul_of_nonneg_left hg.2 hp'.le, congrArg (fun z : ℝ => z * gridTarg y) hp8]

end PEqualNP.Outside.L_lib_684_aux

theorem PEqualNP.Outside.L_lib_684 : ∀ (q b p : ℕ), 2 ≤ q → 2 ≤ p →
  let K := (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)
  ∃ (t : ℕ) (signs : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ),
    (∀ h, 0 ≤ w h) ∧ (∑ h : Fin t, w h) = 1 ∧
    (t : ℝ) ≤ 1 + 192*(p : ℝ)^2*K^b * (2+(b : ℝ)*q*Real.log (2+72*((b : ℝ)+1)*q)) ∧
    ∀ x : Fin b → Fin q → ℝ, (∀ i j, 0 ≤ x i j) →
      let target := ∏ i : Fin b, ∑ j : Fin q, (x i j)^2
      let est := ∑ h : Fin t, w h * ∏ i : Fin b,
        (∑ j : Fin q, (if signs h i j then (-1 : ℝ) else 1) * x i j)^2
      ((p : ℝ)-1)*target ≤ (p : ℝ)*est ∧ (p : ℝ)*est ≤ ((p : ℝ)+1)*target := by
  exact PEqualNP.Outside.L_lib_684_aux.asmMain
