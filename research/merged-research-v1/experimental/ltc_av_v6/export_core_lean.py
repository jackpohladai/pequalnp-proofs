"""Exact normalized-instance proof for an UNSAT-only core certificate.

This proof adapter currently enumerates only a small binary quotient (<=8 vars),
never all original assignments. Larger quotients remain explicitly unverified
by this adapter. This cap does not limit the existing independent SAT test.
"""
from export_compression_lean import render, lean_cnf, boolean_formula
from core_refutation import normalize
from compression import verify_certificate


RULE = '''
namespace CoreRefutations
open CompressionSoundness CompressionInstances
theorem evalCNF_true_iff (F : CNF) (a : Assignment) :
    evalCNF F a = true ↔ ∀ c ∈ F, evalClause c a = true := by
  induction F with
  | nil => simp [evalCNF]
  | cons c cs ih => simp [evalCNF, ih]

theorem subset_refutation (F C : CNF)
    (included : C.all (fun c => decide (c ∈ F)) = true)
    (refuted : ∀ a, evalCNF C a = false) :
    ¬ ∃ a, evalCNF F a = true := by
  rintro ⟨a, ha⟩
  have hc : evalCNF C a = true := (evalCNF_true_iff C a).mpr (by
    intro c hmem
    have inF := of_decide_eq_true ((List.all_eq_true.mp included) c hmem)
    exact (evalCNF_true_iff F a).mp ha c inF)
  rw [refuted] at hc
  contradiction
'''


def render_core(formula, refutation):
    f,core=normalize(formula),normalize(refutation['core'])
    compression=refutation['compression'];cert=compression['certificate']
    n=compression['quotient_variables']
    if n>8:raise ValueError('Binary-quotient Lean adapter limited to8variables; no full proof claimed.')
    if not set(core).issubset(set(f)):raise ValueError('Core is not a subset of the original input')
    if not verify_certificate(core,cert):raise ValueError('Core compression certificate rejected')
    if sorted({abs(l) for c in f for l in c})!=cert['variables']:raise ValueError('Variable map mismatch')
    mapping={v:j+1 for j,v in enumerate(cert['variables'])}
    dense=[[mapping[abs(l)]*(1 if l>0 else -1) for l in c] for c in f]
    source=render([('core',core,compression)])+RULE
    expression=boolean_formula(cert['quotient'],lambda j:'y'+str(j))
    args=' '.join('y'+str(j) for j in range(n))
    source+='\ndef core_full : CNF := '+lean_cnf(dense)+'\n'
    source+='set_option maxRecDepth 100000 in\nset_option maxHeartbeats 20000000 in\n'
    source+='theorem core_contained : core_original.all (fun c => decide (c ∈ core_full)) = true := by\n  decide\n'
    source+='theorem core_qfalse_table ('+args+' : Bool) : '+expression+' = false := by\n  decide +revert\n'
    source+='theorem core_qfalse (a : Assignment) : evalCNF core_quotient a = false := by\n  exact core_qfalse_table '+' '.join('(a '+str(j)+')' for j in range(n))+'\n'
    source+='theorem core_false (a : Assignment) : evalCNF core_original a = false := by\n  rw [core_forward, core_qfalse]\n'
    source+='theorem core_full_unsat : ¬ ∃ a, evalCNF core_full a = true :=\n  subset_refutation _ _ core_contained core_false\n'
    source+='#print axioms core_full_unsat\nend CoreRefutations\n'
    if len(source.encode())>512*1024:raise ValueError('Generated proof exceeds the finite source budget')
    return source


def render_quotient_core(formula,outer,inner):
    """Refute the original input through an exact quotient and its UNSAT core."""
    f=normalize(formula)
    if inner['status']!='UNSAT':raise ValueError('No refutation')
    if outer.get('status')!='compressed' or not verify_certificate(f,outer['certificate']):
        raise ValueError('Outer compression certificate rejected')
    quotient=outer['certificate']['quotient'];core=normalize(inner['core'])
    if inner['compression']['certificate']['variables']!=list(range(1,outer['quotient_variables']+1)):
        raise ValueError('Composition adapter requires contiguous quotient IDs')
    inner_source=render_core(quotient,inner)
    inner_prefix=render([('core',core,inner['compression'])])
    if not inner_source.startswith(inner_prefix):raise ValueError('Inner proof header mismatch')
    source=render([('outer',f,outer),('core',core,inner['compression'])])+inner_source[len(inner_prefix):]
    source+='''
namespace CoreComposition
open CompressionSoundness CompressionInstances CoreRefutations

local instance : Std.Associative Bool.and := ⟨Bool.and_assoc⟩
local instance : Std.Commutative Bool.and := ⟨Bool.and_comm⟩
local instance : Std.Associative Bool.or := ⟨Bool.or_assoc⟩
local instance : Std.Commutative Bool.or := ⟨Bool.or_comm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem outer_quotient_equivalent (a : Assignment) :
    evalCNF outer_quotient a = evalCNF core_full a := by
  change OUTER_BOOLEAN = INNER_BOOLEAN
  simp only [Bool.and_true, Bool.or_false]
  ac_rfl

theorem outer_quotient_unsat : ¬ ∃ a, evalCNF outer_quotient a = true := by
  rintro ⟨a, ha⟩
  apply core_full_unsat
  exact ⟨a, (outer_quotient_equivalent a).symm.trans ha⟩

theorem original_unsat : ¬ ∃ a, evalCNF outer_original a = true := by
  intro h
  exact outer_quotient_unsat (outer_equisatisfiable.mp h)

#print axioms original_unsat
end CoreComposition
'''
    source=source.replace('OUTER_BOOLEAN',boolean_formula(quotient,lambda j:'(a '+str(j)+')'))
    source=source.replace('INNER_BOOLEAN',boolean_formula(normalize(quotient),lambda j:'(a '+str(j)+')'))
    if len(source.encode())>512*1024:raise ValueError('Finite proof source budget exceeded')
    return source
