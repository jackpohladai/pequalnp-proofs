from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ialh_counting'))
from export_compression_lean import render,lean_cnf,boolean_formula
from solver import normalize


def main():
    data=json.loads((HERE/'core-test-receipt.json').read_text())
    cases=[('core'+str(i),normalize(c['result']['core']),c['result']['compression']) for i,c in enumerate(data['cases'])]
    source=render(cases)
    source+='''
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
    for i,c in enumerate(data['cases']):
        name='core'+str(i);n=c['result']['compression']['quotient_variables']
        cert=c['result']['compression']['certificate'];mapping={v:j+1 for j,v in enumerate(cert['variables'])}
        # Check the full original input has exactly the same variable universe.
        assert sorted({abs(l) for cl in c['formula'] for l in cl})==cert['variables']
        dense=[[mapping[abs(l)]*(1 if l>0 else -1) for l in cl] for cl in normalize(c['formula'])]
        expression=boolean_formula(cert['quotient'],lambda j:'y'+str(j))
        args=' '.join('y'+str(j) for j in range(n))
        source+='\ndef '+name+'_full : CNF := '+lean_cnf(dense)+'\n'
        source+='set_option maxRecDepth 100000 in\nset_option maxHeartbeats 20000000 in\n'
        source+='theorem '+name+'_contained : '+name+'_original.all (fun c => decide (c ∈ '+name+'_full)) = true := by\n  decide\n'
        source+='theorem '+name+'_qfalse_table ('+args+' : Bool) : '+expression+' = false := by\n  decide +revert\n'
        source+='theorem '+name+'_qfalse (a : Assignment) : evalCNF '+name+'_quotient a = false := by\n  exact '+name+'_qfalse_table '+' '.join('(a '+str(j)+')' for j in range(n))+'\n'
        source+='theorem '+name+'_false (a : Assignment) : evalCNF '+name+'_original a = false := by\n  rw ['+name+'_forward, '+name+'_qfalse]\n'
        source+='theorem '+name+'_full_unsat : ¬ ∃ a, evalCNF '+name+'_full a = true :=\n  subset_refutation _ _ '+name+'_contained '+name+'_false\n'
        source+='#print axioms '+name+'_full_unsat\n'
    source+='\nend CoreRefutations\n'
    path=HERE/'CoreRefutations.lean';path.write_text(source);started=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='pnp-core-refutation-') as tmp:
        f=Path(tmp)/path.name;f.write_text(source)
        try:
            p=subprocess.run([str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'),'-j','1','-DElab.async=false',str(f)],cwd=tmp,capture_output=True,text=True,timeout=120)
            receipt={'status':'checked' if p.returncode==0 and 'sorryAx' not in p.stdout else 'failed','exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
        except subprocess.TimeoutExpired as exc:
            receipt={'status':'inconclusive','reason':'finite Lean check120second budget exhausted','stdout':(exc.stdout or b'').decode() if isinstance(exc.stdout,bytes) else exc.stdout}
    receipt.update(at=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-started,source_sha256=hashlib.sha256(source.encode()).hexdigest(),cases=len(cases),
                   scope='Exact UNSAT proofs for three original inputs via explicit clause-subset certificates, compression equivalence, and finite binary-quotient refutation.',general_polynomial_sat_proof=False,python_implementation_verified=False)
    (HERE/'core-lean-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps({k:v for k,v in receipt.items() if k not in ['stdout','stderr']}))
    assert receipt['status']=='checked',str(receipt)[-4000:]


if __name__=='__main__':main()
