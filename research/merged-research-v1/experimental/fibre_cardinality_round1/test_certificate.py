import copy
import datetime
import itertools
import json
from pathlib import Path
import random
import sys
import time

from certificate import verify, project

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ialh_counting'))
from compression import basis, right_inverse, span, lift


def main():
    rng=random.Random(27001126)
    checks={'valid_small_certificates':0,'global_equivalence_points':0,'invalid_certificates_rejected':0,'arbitrary_bad_certificates_crosschecked':0}
    start=time.monotonic()
    for _ in range(400):
        n=rng.randint(1,8)
        rows=list(basis(rng.randrange(1,1<<n) for _ in range(rng.randint(0,n))))
        columns=right_inverse(rows,n);d=len(rows)
        q=rng.sample(range(1<<d),rng.randint(0,1<<d))
        p=[x for x in range(1<<n) if project(x,rows) in q]
        assert verify(n,p,q,rows,columns)
        assert all((x in p)==(project(x,rows) in q) for x in range(1<<n))
        checks['valid_small_certificates']+=1
        checks['global_equivalence_points']+=1<<n
        if p:
            assert not verify(n,p+[p[0]],q,rows,columns)
            assert not verify(n,p[:-1],q,rows,columns)
            checks['invalid_certificates_rejected']+=2
        if q:
            assert not verify(n,p,q+[q[0]],rows,columns)
            checks['invalid_certificates_rejected']+=1
        if rows:
            bad=columns[:];bad[0]=0
            assert not verify(n,p,q,rows,bad)
            checks['invalid_certificates_rejected']+=1
    for _ in range(600):
        n=rng.randint(1,6);d=rng.randint(0,n)
        rows=[rng.randrange(1<<n) for _ in range(d)]
        columns=[rng.randrange(1<<n) for _ in range(d)]
        p=rng.sample(range(1<<n),rng.randint(0,1<<n))
        q=rng.sample(range(1<<d),rng.randint(0,1<<d))
        accepted=verify(n,p,q,rows,columns)
        if accepted:
            assert all((x in p)==(project(x,rows) in q) for x in range(1<<n))
            assert all(project(lift(y,columns),rows)==y for y in range(1<<d))
        checks['arbitrary_bad_certificates_crosschecked']+=1
    large=[]
    for n in [16,32,64,128]:
        # Dense invertible row mixing, two free coordinates, four explicit points.
        rows=[1<<i for i in range(n-2)]
        for _ in range(n*4):
            i,j=rng.sample(range(n-2),2);rows[i]^=rows[j]
        # Add random coefficients in the two free columns.
        rows=[v | (rng.randrange(4) << (n-2)) for v in rows]
        columns=right_inverse(rows,n)
        kernel=basis((1<<j)^lift(project(1<<j,rows),columns) for j in range(n))
        assert len(kernel)==2
        p=sorted(span(kernel));q=[0]
        t=time.monotonic();assert verify(n,p,q,rows,columns);elapsed=time.monotonic()-t
        # Only sampled comparisons for wide blocks; explicitly not exhaustive.
        for _ in range(200):
            x=rng.randrange(1<<n);assert (x in p)==(project(x,rows) in q)
        large.append({'width':n,'rank':len(rows),'explicit_forbidden_points':len(p),
                      'global_truth_table_points':str(1<<n),'verification_seconds':elapsed,
                      'validation':'numeric certificate plus200sampled assignments; no global enumeration'})
    receipt={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'large_blocks':large,
             'seconds':time.monotonic()-start,'scope':'Experimental verifier controls. Python and general SAT runtime are not formally verified.',
             'general_polynomial_sat_proof':False,'deployed':False}
    (HERE/'test-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt),flush=True)


if __name__=='__main__':main()
