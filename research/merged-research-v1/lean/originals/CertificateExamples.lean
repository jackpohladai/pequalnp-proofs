import MatchingCertificates

namespace PEqualNP.Outside.MatchingCertificates

def fullTwo : Fin 2 → Finset (Fin 2) := fun _ => Finset.univ
def oneHole : Fin 2 → Finset (Fin 1) := fun _ => {0}
def activeTwo : Fin 2 → Bool := fun _ => false
def validTwo : SuccessCertificate 2 2 := fun i => some i
def collision : SuccessCertificate 2 2 := fun _ => some 0
def missing : SuccessCertificate 2 2 := fun _ => none

example : successCheck fullTwo activeTwo validTwo = true := by decide
example : successCheck fullTwo activeTwo collision = false := by decide
example : successCheck fullTwo activeTwo missing = false := by decide
example : successCheck (fun _ : Fin 1 => (∅ : Finset (Fin 1)))
    (fun _ => false) (fun _ => some 0) = false := by decide
example : successCheck (fun _ : Fin 2 => (∅ : Finset (Fin 0)))
    (fun _ => true) (fun _ => none) = true := by decide
example : failureCheck oneHole activeTwo Finset.univ = true := by decide
example : failureCheck oneHole activeTwo (∅ : Finset (Fin 2)) = false := by decide
example : failureCheck oneHole (fun _ => true) Finset.univ = false := by decide
example : failureCheck fullTwo activeTwo Finset.univ = false := by decide
example : successCheck (fun _ : Fin 1 => (∅ : Finset (Fin 1)))
    (fun _ => true) (fun _ => some 0) = true := by decide

#eval successCheck fullTwo activeTwo validTwo
#eval successCheck fullTwo activeTwo collision
#eval failureCheck oneHole activeTwo Finset.univ
end PEqualNP.Outside.MatchingCertificates
