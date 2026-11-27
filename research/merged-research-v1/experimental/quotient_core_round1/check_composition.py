"""Experiment: refute an exact quotient using an UNSAT-only subformula.

No recursive search or raised discovery limits. The complete normalized original
instance is proved UNSAT by composing two exact compressions and containment.
"""
from pathlib import Path
import datetime as dt
import hashlib
import json
import random
import subprocess
import sys
import tempfile
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ialh_counting'))
from compression import compress_root,verify_certificate
from core_refutation import probe,normalize
from export_compression_lean import render,boolean_formula
from export_core_lean import render_core
from test_compression import lifted,oracle


def composed_probe(formula):
    started=time.monotonic();f=normalize(formula);outer=compress_root(f)
    if outer['status']!='compressed':
        return {'status':'UNKNOWN','reason':'outer_compression_skipped','outer':outer}
    if not verify_certificate(f,outer['certificate']):
        raise ValueError('Outer certificate rejected')
    inner=probe(outer['certificate']['quotient'])
    return {'status':inner['status'],'outer':outer,'inner':inner,
            'seconds':time.monotonic()-started,'general_polynomial_sat_proof':False}


def render_composition(formula,result):
    f=normalize(formula);outer=result['outer'];inner=result['inner']
    if result['status']!='UNSAT':raise ValueError('No refutation')
    if not verify_certificate(f,outer['certificate']):raise ValueError('Outer certificate rejected')
    quotient=outer['certificate']['quotient'];core=normalize(inner['core'])
    if inner['compression']['certificate']['variables']!=list(range(1,outer['quotient_variables']+1)):
        raise ValueError('Composition adapter requires contiguous quotient IDs')
    # Reuse exactly the checked inner proof generator with a shared header.
    inner_source=render_core(quotient,inner)
    inner_prefix=render([('core',core,inner['compression'])])
    assert inner_source.startswith(inner_prefix)
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


def main():
    began=time.monotonic();rng=random.Random(56118)
    counts={'controls':0,'sat':0,'unsat':0,'refuted':0,'unknown':0,'wrong_answers':0}
    controls=[[],[[]],[[1],[-1]],[[1,-1]]]
    for _ in range(240):
        n=rng.randint(2,4)
        base=[[rng.choice([-1,1])*v for v in rng.sample(range(1,n+1),rng.randint(1,min(3,n)))] for _ in range(rng.randint(1,14))]
        # Perturb before lifting so compression preserves ambiguous extra clauses.
        for _ in range(rng.randint(0,4)):
            base.append([rng.choice([-1,1])*v for v in rng.sample(range(1,n+1),rng.randint(1,n))])
        controls.append(lifted(base,[[2*i+1,2*i+2] for i in range(n)]))
    for f in controls:
        truth=oracle(f);r=composed_probe(f)
        assert r['status'] in ['UNKNOWN','UNSAT']
        assert r['status']!='UNSAT' or truth is False
        counts['controls']+=1;counts['sat' if truth else 'unsat']+=1
        counts['refuted' if r['status']=='UNSAT' else 'unknown']+=1
    p=json.loads((HERE.parent/'neon_worstcase_auto_00056/structured-output.json').read_text())
    result=composed_probe(p['formula']);assert result['status']=='UNSAT'
    source=render_composition(p['formula'],result);(HERE/'ComposedRefutation.lean').write_text(source)
    report={'at':dt.datetime.now(dt.timezone.utc).isoformat(),'checks':counts,'fixture':'neon_worstcase_auto_00056',
            'formula':p['formula'],'result':result,'seconds':time.monotonic()-began,
            'scope':'Finite prototype; no universal complexity theorem. Not yet deployed.','general_polynomial_sat_proof':False}
    (HERE/'test-receipt.json').write_text(json.dumps(report,indent=2))
    print(json.dumps({'checks':counts,'fixture_status':result['status'],'quotient_clauses':len(result['outer']['certificate']['quotient']),
                      'removed_quotient_clauses':result['inner']['removed_clauses'],'prototype_seconds':result['seconds']}),flush=True)
    began=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='pnp-composed-core-') as directory:
        path=Path(directory)/'ComposedRefutation.lean';path.write_text(source)
        try:
            p=subprocess.run([str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'),'-j','1','-DElab.async=false',str(path)],
                             cwd=directory,capture_output=True,text=True,timeout=180)
            receipt={'status':'checked' if p.returncode==0 and 'sorryAx' not in p.stdout else 'failed','exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
        except subprocess.TimeoutExpired as exc:
            receipt={'status':'inconclusive','reason':'Finite Lean180second budget exhausted'}
    receipt.update(seconds=time.monotonic()-began,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                   scope='Exact normalized456-clause original-input UNSAT proof via outer compression, quotient core containment and inner compression. No Python or runtime proof.',
                   general_polynomial_sat_proof=False)
    (HERE/'lean-receipt.json').write_text(json.dumps(receipt,indent=2))
    print(json.dumps({k:v for k,v in receipt.items() if k not in ['stdout','stderr']}),flush=True)
    assert receipt['status']=='checked',str(receipt)[-4000:]


if __name__=='__main__':main()
