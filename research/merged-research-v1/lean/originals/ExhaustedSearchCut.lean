import MatchingCertificates
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.MatchingSearch
open PEqualNP.Outside.GuardedHall
open PEqualNP.Outside.MatchingCertificates
variable {r h : Nat}

/-- Consistency of the two partial-matching tables. One row cannot own two
different holes, since its row-to-hole table has a single Option value. -/
def InverseConsistent (rowMatch : Fin r → Option (Fin h))
    (owner : Fin h → Option (Fin r)) : Prop :=
  ∀ k i, owner k = some i → rowMatch i = some k

/-- Exact failed-BFS terminal invariant: every neighbor of reached rows has
a matched owner in the reached set, while the start row remains unmatched.
The cardinal inequality is a conclusion, not an assumed search condition. -/
theorem exhausted_cut_deficient (N : Fin r → Finset (Fin h))
    (rowMatch : Fin r → Option (Fin h)) (owner : Fin h → Option (Fin r))
    (S : Finset (Fin r)) (root : Fin r) (rootIn : root ∈ S)
    (unmatched : rowMatch root = none) (consistent : InverseConsistent rowMatch owner)
    (closed : ∀ k ∈ S.biUnion N, ∃ i ∈ S, owner k = some i) :
    (S.biUnion N).card < S.card := by
  have ownerIn : ∀ k ∈ S.biUnion N, ∃ i ∈ S.erase root, owner k = some i := by
    intro k hk
    obtain ⟨i, hi, owned⟩ := closed k hk
    have notRoot : i ≠ root := by
      intro same
      subst i
      have contradiction := consistent k root owned
      simp [unmatched] at contradiction
    exact ⟨i, Finset.mem_erase.mpr ⟨notRoot,hi⟩, owned⟩
  have injective : Set.InjOn owner (S.biUnion N) := by
    intro k hk l hl same
    obtain ⟨i, _, owned⟩ := closed k hk
    have other : owner l = some i := same.symm.trans owned
    exact Option.some.inj ((consistent k i owned).symm.trans (consistent l i other))
  have subset : (S.biUnion N).image owner ⊆ (S.erase root).image Option.some := by
    intro value member
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨i, hi, owned⟩ := ownerIn k hk
    exact Finset.mem_image.mpr ⟨i,hi,owned.symm⟩
  have bound : (S.biUnion N).card ≤ (S.erase root).card := by
    calc
      (S.biUnion N).card = ((S.biUnion N).image owner).card :=
        (Finset.card_image_of_injOn injective).symm
      _ ≤ ((S.erase root).image Option.some).card := Finset.card_le_card subset
      _ = (S.erase root).card := Finset.card_image_of_injective _ (Option.some_injective (Fin r))
  exact bound.trans_lt (Finset.card_erase_lt_of_mem rootIn)

theorem exhausted_cut_accepted (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (rowMatch : Fin r → Option (Fin h)) (owner : Fin h → Option (Fin r))
    (S : Finset (Fin r)) (root : Fin r) (rootIn : root ∈ S)
    (unmatched : rowMatch root = none) (consistent : InverseConsistent rowMatch owner)
    (closed : ∀ k ∈ S.biUnion N, ∃ i ∈ S, owner k = some i)
    (active : ∀ i ∈ S, g i = false) : failureCheck N g S = true := by
  exact (failureCheck_iff N g S).mpr ⟨active,
    exhausted_cut_deficient N rowMatch owner S root rootIn unmatched consistent closed⟩

theorem exhausted_cut_no_matching (N : Fin r → Finset (Fin h)) (g : Fin r → Bool)
    (rowMatch : Fin r → Option (Fin h)) (owner : Fin h → Option (Fin r))
    (S : Finset (Fin r)) (root : Fin r) (rootIn : root ∈ S)
    (unmatched : rowMatch root = none) (consistent : InverseConsistent rowMatch owner)
    (closed : ∀ k ∈ S.biUnion N, ∃ i ∈ S, owner k = some i)
    (active : ∀ i ∈ S, g i = false) : ¬ HasMatching N g :=
  accepted_failure_no_matching N g S
    (exhausted_cut_accepted N g rowMatch owner S root rootIn unmatched consistent closed active)

#print axioms exhausted_cut_deficient
#print axioms exhausted_cut_accepted
#print axioms exhausted_cut_no_matching
end PEqualNP.Outside.MatchingSearch
