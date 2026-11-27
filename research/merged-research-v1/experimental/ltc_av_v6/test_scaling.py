"""Larger controls, adversarial mutations, and independent oracle comparisons."""
import copy
import datetime
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import tempfile
import time

from compression import compress_root, verify_certificate, right_inverse, basis, evaluate, project, lift
from export_compression_lean import render
from finite_oracle import solve
from solver import run_counting, normalize, variables, source_hash, VERSION
from test_compression import lifted, oracle

HERE = Path(__file__).resolve().parent


def main():
    start = time.monotonic()
    rng = random.Random(27112026)
    checks = {'large_controls': 0, 'global_equivalence_comparisons': 0,
              'right_inverse_matrices': 0, 'dpll_vs_exhaustive': 0,
              'certificate_mutations_rejected': 0, 'original_oracle_inconclusive': 0}
    cases, lean_cases = [], []
    for n in [16, 24, 32, 64]:
        m = n // 2
        groups = [[2*i+1, 2*i+2] for i in range(m)]
        for sat in [True, False]:
            base = [[1], [m if sat else -m]] + [[-i, i+1] for i in range(1, m)]
            f = lifted(base, groups)
            t = time.monotonic()
            result = run_counting(f, variables(f))
            seconds = time.monotonic()-t
            assert result['sat'] == sat and result['compression']['status'] == 'compressed'
            independent = solve(f, max_seconds=1)
            assert independent['sat'] is None or independent['sat'] == sat
            checks['original_oracle_inconclusive'] += independent['sat'] is None
            c = result['compression']
            assert verify_certificate(normalize(f), c['certificate'])
            quotient_oracle = solve(c['certificate']['quotient'])
            assert quotient_oracle['status'] == 'completed' and quotient_oracle['sat'] == sat
            checks['large_controls'] += 1
            name = 'pairs'+str(n)+('sat' if sat else 'unsat')
            cases.append(dict(name=name, variables=n, clauses=len(f), sat=sat, seconds=seconds,
                              oracle=independent, quotient_oracle=quotient_oracle, result=result))
            if n <= 32:
                lean_cases.append((name, normalize(f), c))
    # Overlapping forms produce long inverse expressions with many cancellations.
    for n in [16, 32, 64]:
        f = [[-i, i+1] for i in range(1,n)] + [[i, -(i+1)] for i in range(1,n)]
        t=time.monotonic();r=run_counting(f,variables(f));seconds=time.monotonic()-t
        assert r['sat'] is True and r['compression']['quotient_variables']==n-1
        assert verify_certificate(normalize(f),r['compression']['certificate'])
        checks['large_controls'] += 1
        cases.append(dict(name='overlap'+str(n),variables=n,clauses=len(f),sat=True,seconds=seconds,result=r))
        if n<=32:lean_cases.append(('overlap'+str(n),normalize(f),r['compression']))
    # Added clauses deliberately break symmetry; a skipped reduction is not a wrong answer.
    for n in [16,24,32]:
        groups=[[2*i+1,2*i+2] for i in range(n//2)]
        base=[[1],[-n//2]]+[[-i,i+1] for i in range(1,n//2)]
        f=lifted(base,groups)
        supports=sorted({tuple(sorted(map(abs,c))) for c in f})
        for support in supports:
            existing={tuple(sorted(c)) for c in f if tuple(sorted(map(abs,c)))==support}
            extra=next(tuple(sign*v for sign,v in zip(bits,support))
                       for bits in itertools.product((-1,1),repeat=len(support))
                       if tuple(sorted(sign*v for sign,v in zip(bits,support))) not in existing)
            f.append(list(extra))
        t=time.monotonic();r=run_counting(f,variables(f));seconds=time.monotonic()-t
        assert r['sat'] is False and r['compression']['status']=='skipped'
        independent=solve(f)
        assert independent['sat'] is None or independent['sat'] is False
        checks['original_oracle_inconclusive'] += independent['sat'] is None
        checks['large_controls'] += 1
        cases.append(dict(name='added_clauses'+str(n),variables=n,clauses=len(f),sat=False,seconds=seconds,result=r,oracle=independent))
    # Different implementation and independent global enumeration validate local certificates.
    for _ in range(80):
        groups=[[2*i+1,2*i+2] for i in range(4)]
        base=[[rng.choice([-1,1])*v for v in rng.sample(range(1,5),rng.randint(1,3))] for _ in range(rng.randint(2,9))]
        f=normalize(lifted(base,groups));c=compress_root(f)
        if c['status']=='compressed':
            cert=c['certificate'];ids=cert['variables'];mapping={v:i+1 for i,v in enumerate(ids)}
            dense=[[mapping[abs(l)]*(1 if l>0 else -1) for l in clause] for clause in f]
            assert all(evaluate(dense,x)==evaluate(cert['quotient'],project(x,cert['basis_forms'])) for x in range(2**len(ids)))
            assert all(project(lift(y,cert['right_inverse']),cert['basis_forms'])==y for y in range(2**len(cert['basis_forms'])))
            checks['global_equivalence_comparisons'] += 1
    for _ in range(200):
        n=rng.randint(2,32);forms=list(basis(rng.randrange(1,2**n) for _ in range(rng.randint(1,n))))
        columns=right_inverse(forms,n)
        assert columns is not None
        assert all(project(columns[i],forms)==1<<i for i in range(len(forms)))
        assert right_inverse(forms+[forms[0]],n) is None
        checks['right_inverse_matrices'] += 1
    for _ in range(200):
        f=[[rng.choice([-1,1])*v for v in rng.sample(range(1,7),rng.randint(1,4))] for _ in range(rng.randint(1,20))]
        truth=oracle(f)
        padded=f+[[i,-i] for i in range(1,14)]
        result=solve(padded)
        assert result['method']=='independent_bounded_dpll' and result['sat']==truth
        checks['dpll_vs_exhaustive'] += 1
    assert solve([[i,-i] for i in range(1,14)],max_nodes=0)['status']=='inconclusive'
    f=normalize(lifted([[1,2],[-1,3]],[[1,2],[3,4],[5,6]]))
    cert=compress_root(f)['certificate']
    for field in ['variables','basis_forms','right_inverse','quotient','block_clause_counts']:
        bad=copy.deepcopy(cert)
        bad[field]=[]
        assert not verify_certificate(f,bad)
        checks['certificate_mutations_rejected'] += 1
    bad=copy.deepcopy(cert);bad['quotient'][0][0]*=-1
    assert not verify_certificate(f,bad)
    checks['certificate_mutations_rejected'] += 1
    out=dict(at=datetime.datetime.now(datetime.timezone.utc).isoformat(),solver=VERSION,source_sha256=source_hash(),
             checks=checks,cases=cases,general_polynomial_sat_proof=False,implementation_lean_verified=False)
    # Save empirical results before the independently bounded Lean check.
    (HERE/'scaling-test-receipt.json').write_text(json.dumps(out,indent=2))
    source=render(lean_cases)
    (HERE/'LargerCompressionInstances.lean').write_text(source)
    # The solver changed, but these compression proof terms need not change.
    # Reuse only an already checked receipt whose source hash matches exactly.
    prior_path=HERE.parent/'ialh_counting/scaling-lean-receipt.json'
    prior=json.loads(prior_path.read_text())
    if prior.get('status')=='checked' and prior.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest():
        prior=dict(prior,reused_unchanged_proof_from=str(prior_path))
        (HERE/'scaling-lean-receipt.json').write_text(json.dumps(prior,indent=2))
        print(json.dumps(dict(checks=checks,unchanged_lean_proof_reused=True,seconds=time.monotonic()-start)),flush=True)
        return
    lean_start=time.monotonic()
    with tempfile.TemporaryDirectory(prefix='pnp-large-lean-') as tmp:
        path=Path(tmp)/'LargerCompressionInstances.lean';path.write_text(source)
        process=subprocess.run([str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'),'-j','1','-DElab.async=false',str(path)],
                               cwd=tmp,capture_output=True,text=True,timeout=120)
    receipt=dict(status='checked' if process.returncode==0 and 'sorryAx' not in process.stdout else 'failed',
                 exit_code=process.returncode,seconds=time.monotonic()-lean_start,cases=len(lean_cases),
                 source_sha256=hashlib.sha256(source.encode()).hexdigest(),stdout=process.stdout,stderr=process.stderr,
                 scope='Exact transformations and lifting for larger concrete inputs; not general SAT runtime or Python verification.')
    (HERE/'scaling-lean-receipt.json').write_text(json.dumps(receipt,indent=2))
    assert receipt['status']=='checked',receipt
    print(json.dumps(dict(checks=checks,lean={k:v for k,v in receipt.items() if k not in ['stdout','stderr']},seconds=time.monotonic()-start)),flush=True)


if __name__=='__main__':
    main()
