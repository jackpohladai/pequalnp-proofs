from pathlib import Path
import datetime
import json
import random
import sys
import time

from core_probe import probe
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ialh_counting'))
from test_compression import lifted,oracle


def main():
    start=time.monotonic();cases=[]
    a=json.loads((HERE.parent/'neon_worstcase_auto_00053/structured-output.json').read_text())
    r=probe(a['formula']);assert r['status']=='UNSAT'
    cases.append({'name':'neon53','formula':a['formula'],'original_order':a['order'],'result':r})
    fragility=json.loads((HERE.parent/'fable_quotient_review/fragility-receipt.json').read_text())
    for v in fragility['results']:
        a=json.loads((HERE.parent/v['source']/'structured-output.json').read_text())
        f=a['formula']+v['added_clauses'];r=probe(f);assert r['status']=='UNSAT'
        cases.append({'name':v['source']+'-extra','formula':f,'original_order':a['order'],'result':r})
    rng=random.Random(53004);counts={'controls':0,'sat_controls':0,'unsat_controls':0,'refuted':0,'unknown':0,'wrong_answers':0}
    # In many of these, deleting clauses turns an UNSAT input SAT. No SAT answer is allowed.
    controls=[[],[[]],[[1],[-1]],[[1,-1]]]
    for _ in range(200):
        groups=[[2*i+1,2*i+2] for i in range(rng.randint(2,4))]
        base=[[rng.choice([-1,1])*v for v in rng.sample(range(1,len(groups)+1),rng.randint(1,2))] for _ in range(rng.randint(1,12))]
        f=lifted(base,groups)
        for _ in range(rng.randint(0,5)):
            f.append([rng.choice([-1,1])*v for v in rng.sample(range(1,2*len(groups)+1),rng.randint(1,4))])
        controls.append(f)
    for f in controls:
        truth=oracle(f);r=probe(f)
        assert r['status'] in ['UNKNOWN','UNSAT']
        assert r['status']!='UNSAT' or truth is False
        counts['controls']+=1;counts['sat_controls' if truth else 'unsat_controls']+=1
        counts['refuted' if r['status']=='UNSAT' else 'unknown']+=1
    result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cases':cases,'checks':counts,
            'seconds':time.monotonic()-start,'deployed':False,'scope':'Experimental UNSAT-only subformula shortcut. No general growth theorem; not deployed.',
            'general_polynomial_sat_proof':False}
    (HERE/'core-test-receipt.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({'checks':counts,'cases':[{'name':c['name'],'status':c['result']['status'],'removed':c['result']['removed_clauses'],'seconds':c['result']['seconds']} for c in cases]}))


if __name__=='__main__':main()
