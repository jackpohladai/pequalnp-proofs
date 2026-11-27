import MatchingCertificates

namespace PEqualNP.Outside.MatchingCertificates
open PEqualNP.Outside.GuardedHall
variable {r h : Nat}

/-- Ignore every inactive row, including arbitrary ignored certificate
entries, before constructing actual edge Booleans. -/
def certificateEdges (g : Fin r → Bool) (certificate : SuccessCertificate r h)
    (i : Fin r) (k : Fin h) : Bool :=
  if g i = false then decide (certificate i = some k) else false

theorem certificateEdges_true_iff (g : Fin r → Bool)
    (certificate : SuccessCertificate r h) (i : Fin r) (k : Fin h) :
    certificateEdges g certificate i k = true ↔
      g i = false ∧ certificate i = some k := by
  cases hg : g i <;> simp [certificateEdges, hg]

theorem accepted_certificate_edges (N : Fin r → Finset (Fin h))
    (g : Fin r → Bool) (certificate : SuccessCertificate r h)
    (accepted : successCheck N g certificate = true) :
    (∀ i k, certificateEdges g certificate i k = true → k ∈ N i) ∧
    (∀ i, g i = true ∨ ∃ k ∈ N i, certificateEdges g certificate i k = true) ∧
    (∀ i j k, certificateEdges g certificate i k = true →
      certificateEdges g certificate j k = true → i = j) := by
  obtain ⟨rows, unique⟩ := (successCheck_iff N g certificate).mp accepted
  refine ⟨?_, ?_, ?_⟩
  · intro i k he
    obtain ⟨hi, hc⟩ := (certificateEdges_true_iff g certificate i k).mp he
    obtain ⟨chosen, hchosen, neighbor⟩ := rows i hi
    have same : chosen = k := Option.some.inj (hchosen.symm.trans hc)
    simpa [same] using neighbor
  · intro i
    cases hi : g i with
    | true => exact Or.inl rfl
    | false =>
        obtain ⟨k, hc, neighbor⟩ := rows i hi
        exact Or.inr ⟨k, neighbor, (certificateEdges_true_iff g certificate i k).mpr ⟨hi,hc⟩⟩
  · intro i j k ei ej
    obtain ⟨hi, ci⟩ := (certificateEdges_true_iff g certificate i k).mp ei
    obtain ⟨hj, cj⟩ := (certificateEdges_true_iff g certificate j k).mp ej
    exact unique i j hi hj (ci.trans cj.symm)

theorem accepted_certificate_private_edges (N : Fin r → Finset (Fin h))
    (g : Fin r → Bool) (certificate : SuccessCertificate r h)
    (accepted : successCheck N g certificate = true) : HasPrivateEdges N g :=
  ⟨certificateEdges g certificate, accepted_certificate_edges N g certificate accepted⟩

example : successCheck (fun _ : Fin 2 => ({0} : Finset (Fin 1)))
    (fun i => decide (i = 1)) (fun _ => some 0) = true := by decide
example : certificateEdges (fun i : Fin 2 => decide (i = 1))
    (fun _ => (some 0 : Option (Fin 1))) 1 0 = false := by decide

#print axioms accepted_certificate_edges
#print axioms accepted_certificate_private_edges
end PEqualNP.Outside.MatchingCertificates
