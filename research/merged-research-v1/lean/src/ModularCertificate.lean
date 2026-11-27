import Std.Tactic

namespace ModularCertificate

def block (a b c d e : Bool) : Bool :=
  (!a || b || c || d) &&
  (!a || b || c || e) &&
  (!a || b || d || e) &&
  (!a || c || d || e) &&
  (!b || a || c || d) &&
  (!b || a || c || e) &&
  (!b || a || d || e) &&
  (!b || c || d || e) &&
  (!c || a || b || d) &&
  (!c || a || b || e) &&
  (!c || a || d || e) &&
  (!c || b || d || e) &&
  (!d || a || b || c) &&
  (!d || a || b || e) &&
  (!d || a || c || e) &&
  (!d || b || c || e) &&
  (!e || a || b || c) &&
  (!e || a || b || d) &&
  (!e || a || c || d) &&
  (!e || b || c || d) &&
  (!a || !b || !c || !d) &&
  (!a || !b || !c || !e) &&
  (!a || !b || !d || !e) &&
  (!a || !c || !d || !e) &&
  (!b || !c || !d || !e)

theorem block_mod3 (a b c d e : Bool) (h : block a b c d e = true) :
    ((Int.ofNat a.toNat) + (Int.ofNat b.toNat) + (Int.ofNat c.toNat) + (Int.ofNat d.toNat) + (Int.ofNat e.toNat)) % 3 = 0 := by
  decide +revert

theorem modular_impossible (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Int)
    (h0 : (x1 + x3 + x4 + x5 + x12) % 3 = 0)
    (h1 : (x1 + x3 + x6 + x10 + x11) % 3 = 0)
    (h2 : (x1 + x4 + x8 + x9 + x10) % 3 = 0)
    (h3 : (x2 + x3 + x5 + x7 + x8) % 3 = 0)
    (h4 : (x2 + x4 + x6 + x7 + x11) % 3 = 0)
    (h5 : (x2 + x5 + x9 + x10 + x11) % 3 = 0)
    (h6 : ((1 - x12) + x6 + x7 + x8 + x9) % 3 = 0)
    : False := by
  omega

theorem neon_cnf_unsatisfiable (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Bool)
    (h0 : block x1 x3 x4 x5 x12 = true)
    (h1 : block x1 x3 x6 x10 x11 = true)
    (h2 : block x1 x4 x8 x9 x10 = true)
    (h3 : block x2 x3 x5 x7 x8 = true)
    (h4 : block x2 x4 x6 x7 x11 = true)
    (h5 : block x2 x5 x9 x10 x11 = true)
    (h6 : block (!x12) x6 x7 x8 x9 = true)
    : False := by
  have complement : Int.ofNat (!x12).toNat = 1 - Int.ofNat x12.toNat := by
    cases x12 <;> decide
  have k0 := block_mod3 x1 x3 x4 x5 x12 h0
  have k1 := block_mod3 x1 x3 x6 x10 x11 h1
  have k2 := block_mod3 x1 x4 x8 x9 x10 h2
  have k3 := block_mod3 x2 x3 x5 x7 x8 h3
  have k4 := block_mod3 x2 x4 x6 x7 x11 h4
  have k5 := block_mod3 x2 x5 x9 x10 x11 h5
  have k6 := block_mod3 (!x12) x6 x7 x8 x9 h6
  rw [complement] at k6
  exact modular_impossible (Int.ofNat x1.toNat) (Int.ofNat x2.toNat) (Int.ofNat x3.toNat) (Int.ofNat x4.toNat) (Int.ofNat x5.toNat) (Int.ofNat x6.toNat) (Int.ofNat x7.toNat) (Int.ofNat x8.toNat) (Int.ofNat x9.toNat) (Int.ofNat x10.toNat) (Int.ofNat x11.toNat) (Int.ofNat x12.toNat) k0 k1 k2 k3 k4 k5 k6

#print axioms block_mod3
#print axioms modular_impossible
#print axioms neon_cnf_unsatisfiable
end ModularCertificate
