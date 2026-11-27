import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'runtime'))
"""Independent oracles and mutation tests for the integrated root compressor."""
import copy
import datetime as dt
import hashlib
import itertools as it
import json
from pathlib import Path
import random
import time

from compression import compress_root, verify_certificate
from solver import normalize, run_counting, source_hash, variables, VERSION
from solver_v1 import run_counting as old_solver

HERE = Path(__file__).resolve().parent


def oracle(formula):
    vs = variables(formula)
    for t in it.product((False, True), repeat=len(vs)):
        a = dict(zip(vs, t))
        if all(any(a[abs(l)] == (l > 0) for l in c) for c in formula):
            return True
    return False


def lifted(base, groups):
    output = []
    for c in base:
        support = sorted({v for l in c for v in groups[abs(l)-1]})
        for bits in it.product((False, True), repeat=len(support)):
            a = dict(zip(support, bits))
            if not any(sum(a[v] for v in groups[abs(l)-1]) % 2 == (l > 0) for l in c):
                output.append([(-v if a[v] else v) for v in support])
    return output


def main():
    start, rng = time.monotonic(), random.Random(26112026)
    fixtures = []
    for name in ['neon_antigravity_round6', 'neon_worstcase_auto_00005', 'neon_worstcase_auto_00006',
                 'neon_worstcase_auto_00007', 'neon_worstcase_auto_00008']:
        a = json.loads((HERE.parent/'evidence'/name/'structured-output.json').read_text())
        t = time.monotonic(); result = run_counting(a['formula'], a['order']); elapsed = time.monotonic()-t
        t = time.monotonic(); old = old_solver(a['formula'], a['order']); before = time.monotonic()-t
        assert result['sat'] == old['sat'] == oracle(a['formula'])
        fixtures.append(dict(source=name, formula=a['formula'], order=a['order'], updated=result,
                             previous_peak=old['peak'], previous_seconds=before, updated_seconds=elapsed))
    negative = json.loads((HERE.parent/'evidence/fable_quotient_review/fragility-receipt.json').read_text())
    for case in negative['results']:
        a = json.loads((HERE.parent/'evidence'/case['source']/'structured-output.json').read_text())
        f = a['formula'] + case['added_clauses']
        result = run_counting(f, a['order'])
        assert result['sat'] is False and result['compression']['status'] == 'skipped'
        fixtures.append(dict(source=case['source']+'-extra-clauses', formula=f, order=a['order'], updated=result))
    controls = [[], [[]], [[1,-1]], [[1],[-1]], [[1,1],[-1,-1]], [[101,203],[-101,-203]]]
    for _ in range(120):
        groups = [[2*i+1,2*i+2] for i in range(rng.randint(2,4))]
        logical = list(range(1,len(groups)+1))
        base = [tuple(rng.choice((-1,1))*v for v in rng.sample(logical,rng.randint(1,min(3,len(logical)))))
                for _ in range(rng.randint(1,12))]
        f = lifted(base,groups)
        if rng.randrange(2):
            vs = variables(f)
            for _ in range(rng.randint(1,4)):
                f.append([rng.choice((-1,1))*v for v in rng.sample(vs,rng.randint(1,min(4,len(vs))))])
        controls.append(f)
    for _ in range(200):
        vs = list(range(1,rng.randint(4,7)+1))
        controls.append([[rng.choice((-1,1))*v for v in rng.sample(vs,rng.randint(1,min(4,len(vs))))]
                         for _ in range(rng.randint(1,24))])
    counts = dict(total=len(controls),sat=0,unsat=0,compressed=0,skipped=0,failures=0)
    for f in controls:
        truth = oracle(f); result = run_counting(f,variables(f))
        assert result['sat'] == truth,(f,result)
        counts['sat' if truth else 'unsat'] += 1
        counts['compressed' if result['compression']['status']=='compressed' else 'skipped'] += 1
    example = next(r for r in fixtures if r['source']=='neon_worstcase_auto_00006')
    f = normalize(example['formula']); cert=example['updated']['compression']['certificate']
    assert verify_certificate(f,cert)
    mutations=[]
    for field in ['basis_forms','right_inverse','quotient','variables']:
        bad=copy.deepcopy(cert)
        if field=='basis_forms':bad[field][0]=0
        elif field=='right_inverse':bad[field][0]=0
        elif field=='quotient':bad[field]=[]
        else:bad[field]=list(reversed(bad[field]))
        assert not verify_certificate(f,bad),field
        mutations.append(field)
    for key in ['max_variables','max_block_width','max_clauses','max_space_points','max_verification_work']:
        skipped=run_counting(f,variables(f),compression_limits={key:0})
        assert skipped['compression']['status']=='skipped' and skipped['sat'] is False
    large=lifted([(1,2),(-1,3)],[[1,2],[3,4],[5,6]])+[[v,-v] for v in range(7,14)]
    assert run_counting(large,variables(large))['sat']==oracle(large)
    too_many=[[i] for i in range(1,66)]
    assert compress_root(too_many)['reason']=='variable_budget_or_trivial'
    # Lift coordinates back to large original IDs without large bit-vector allocation.
    renamed=[[1000*abs(l)*(1 if l>0 else -1) for l in c] for c in example['formula']]
    result=run_counting(renamed,variables(renamed));assert result['sat'] is False and result['compression']['status']=='compressed'
    positive=lifted([(1,2),(-1,3)],[[1,2],[3,4],[5,6]])
    p=run_counting(positive,variables(positive));assert p['sat'] is True and p['compression']['status']=='compressed'
    fixtures.append(dict(source='positive-control',formula=positive,order=variables(positive),updated=p))
    out=dict(at=dt.datetime.now(dt.timezone.utc).isoformat(),solver=VERSION,source_sha256=source_hash(),
             compression_sha256=hashlib.sha256((HERE.parent/'runtime/compression.py').read_bytes()).hexdigest(),
             controls=counts,mutation_rejections=mutations,budget_fallbacks=5,fixtures=fixtures,
             seconds=time.monotonic()-start,general_polynomial_sat_proof=False)
    (HERE/'compression-test-receipt.json').write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k!='fixtures'}),flush=True)
    print(json.dumps([{k:r[k] for k in ['source','previous_peak','updated_seconds'] if k in r}|
                      {'new_peak':r['updated']['peak'],'compression':r['updated']['compression']['status'],
                       'reason':r['updated']['compression'].get('reason')} for r in fixtures]),flush=True)


if __name__=='__main__':
    main()
