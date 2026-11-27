"""Trusted automatic checker, copied beside a pinned ialh_target.py per job."""
import itertools as it
import hashlib
import json
from pathlib import Path
import time
import subprocess
import tempfile

from ialh_target import VERSION, run_counting, source_hash, variables, normalize
from check_scc_and_growth import run_plus
from finite_oracle import solve as finite_oracle
import multiprocessing


def _child(connection, function, args):
    try:
        connection.send({'status': 'completed', 'result': function(*args)})
    except Exception as exc:
        connection.send({'status': 'error', 'error': type(exc).__name__ + ': ' + str(exc)[:300]})
    finally:
        connection.close()


def bounded(function, args, seconds):
    context = multiprocessing.get_context('fork')
    parent, child = context.Pipe(duplex=False)
    process = context.Process(target=_child, args=(child, function, args))
    process.start()
    child.close()
    try:
        if parent.poll(seconds):
            try:
                return parent.recv()
            except EOFError:
                return {'status': 'error', 'error': 'Finite checker process exited without result'}
        return {'status': 'inconclusive', 'reason': 'Finite test exceeded ' + str(seconds) + ' seconds; no result inferred.'}
    finally:
        parent.close()
        process.join(0.1)
        if process.is_alive():
            process.terminate()
            process.join(1)
        if process.is_alive():
            process.kill()
            process.join()


def check(data):
    neon = 'verdict' in data
    if neon:
        assert data['verdict'] in ('growth_fixture', 'correctness_fixture', 'no_fixture')
    fixture = data if neon and data['verdict'] != 'no_fixture' else data.get('fixture')
    if fixture is None:
        return dict(status='no_fixture', summary='Mathematical proposal saved without a finite fixture; its claims remain unverified.')
    f, order = fixture['formula'], fixture['order']
    assert isinstance(f, list) and len(f) <= 512
    assert all(isinstance(c, list) and len(c) <= 12 and all(type(l) is int and 1 <= abs(l) <= 32 for l in c) for c in f)
    vs = variables(f)
    assert isinstance(order, list) and len(order) == len(set(order)) and sorted(order) == vs
    assert all(type(v) is int for v in order)
    oracle_result = finite_oracle(f)
    truth = oracle_result['sat']
    began = time.monotonic()
    baseline_check = bounded(run_plus, (f, order), 8)
    baseline_seconds = time.monotonic() - began
    baseline = baseline_check.get('result', baseline_check)
    began = time.monotonic()
    updated_check = bounded(run_counting, (f, order), 20)
    updated_seconds = time.monotonic() - began
    if updated_check['status'] != 'completed':
        return dict(status='inconclusive', summary='Candidate search did not complete within the finite test budget; no correctness or complexity conclusion.',
                    oracle_sat=truth, oracle=oracle_result, baseline=baseline, updated_check=updated_check,
                    baseline_seconds=baseline_seconds, updated_seconds=updated_seconds)
    observed = updated_check['result']
    if truth is None:
        return dict(status='inconclusive', summary='Independent SAT oracle exhausted its finite budget; candidate correctness remains unverified.',
                    oracle_sat=None, oracle=oracle_result, observed=observed, baseline=baseline,
                    baseline_seconds=baseline_seconds, updated_seconds=updated_seconds)
    if observed['sat'] != truth:
        status = 'confirmed_correctness_failure'
        summary = 'Implementation correctness failure: the updated solver disagrees with the independent SAT oracle. Stop promotion of this implementation.'
    elif neon:
        confirmed = data['verdict'] == 'growth_fixture' and not truth and observed['peak'] >= 4
        status = 'confirmed_finite_growth_fixture' if confirmed else 'not_confirmed'
        summary = ('The deployed solver still reaches at least four simultaneous states on this finite UNSAT fixture.' if confirmed
                   else 'The submitted fixture did not break the deployed solver under the requested criterion.')
        summary += ' This is a finite test, not a general complexity result.'
    else:
        assert type(fixture['predicted_sat']) is bool and type(fixture['predicted_peak']) is int
        match = fixture['predicted_sat'] == truth and fixture['predicted_peak'] == observed['peak']
        status = 'fixture_predictions_match' if match else 'fixture_prediction_failed'
        summary = 'Fable finite prediction ' + ('matched' if match else 'failed') + ' on the deployed solver; broader mathematical claims remain unverified.'
    compression = observed.get('compression', {})
    summary += ' Observed peak: ' + str(observed['peak']) + '; compression: ' + str(compression.get('status', 'not_present')) + '.'
    if compression.get('reason'):
        summary += ' Skip reason: ' + compression['reason'] + '.'
    core=observed.get('core_refutation',{})
    if core.get('status')=='UNSAT':
        summary += ' UNSAT-only core shortcut refuted after removing '+str(core['removed_clauses'])+' '+core.get('input_stage','original')+' clauses; no branching.'
    return dict(status=status, summary=summary, oracle_sat=truth, oracle=oracle_result, observed=observed,
                baseline=baseline, baseline_seconds=baseline_seconds, updated_seconds=updated_seconds)


def check_compression_in_lean(folder, data, result):
    compression = result.get('observed', {}).get('compression', {})
    if compression.get('status') != 'compressed':
        return
    from export_compression_lean import render
    fixture = data if 'verdict' in data else data['fixture']
    source = render([('candidate', normalize(fixture['formula']), compression)])
    path = folder / 'CompressionCandidate.lean'
    path.write_text(source)
    began = time.monotonic()
    receipt = dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(), lean_version='4.36.0',
                   scope='Exact candidate compression equivalence and constructive lifting; not a verification of Python or runtime.',
                   general_polynomial_sat_proof=False)
    try:
        with tempfile.TemporaryDirectory(prefix='pnp-candidate-lean-') as directory:
            target = Path(directory) / path.name
            target.write_text(source)
            process = subprocess.run([str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'),
                                      '-j','1','-DElab.async=false',str(target)],cwd=directory,
                                     capture_output=True,text=True,timeout=45)
        success = process.returncode == 0 and 'sorryAx' not in process.stdout
        receipt.update(status='checked' if success else 'failed', exit_code=process.returncode,
                       stdout=process.stdout, stderr=process.stderr)
    except subprocess.TimeoutExpired:
        receipt.update(status='inconclusive',reason='Finite Lean certificate check exceeded45seconds; no proof claimed.')
    receipt['seconds'] = time.monotonic()-began
    (folder/'compression-lean-receipt.json').write_text(json.dumps(receipt,indent=2))
    result['compression_lean'] = {k:v for k,v in receipt.items() if k not in ('stdout','stderr')}
    result['summary'] += (' Exact compression certificate also checked in Lean.' if receipt['status']=='checked'
                          else ' The concrete Lean compression check did not pass; inspect its separate receipt.')


def check_core_in_lean(folder, data, result):
    from export_core_lean import render_core,render_quotient_core
    fixture=data if 'verdict' in data else data['fixture']
    began=time.monotonic()
    receipt=dict(lean_version='4.36.0',general_polynomial_sat_proof=False,
                 scope='UNSAT of the normalized, densely renamed instance via clause subset, exact core compression and binary-quotient refutation. No Python or runtime verification.')
    try:
        observed=result['observed'];core=observed['core_refutation']
        source=(render_quotient_core(fixture['formula'],observed['compression'],core)
                if core.get('input_stage')=='quotient' else render_core(fixture['formula'],core))
        receipt['source_sha256']=hashlib.sha256(source.encode()).hexdigest()
        (folder/'CoreCandidate.lean').write_text(source)
        with tempfile.TemporaryDirectory(prefix='pnp-core-candidate-') as tmp:
            target=Path(tmp)/'CoreCandidate.lean';target.write_text(source)
            process=subprocess.run([str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'),
                                    '-j','1','-DElab.async=false',str(target)],cwd=tmp,capture_output=True,text=True,timeout=120)
        success=process.returncode==0 and 'sorryAx' not in process.stdout
        receipt.update(status='checked' if success else 'failed',exit_code=process.returncode,stdout=process.stdout,stderr=process.stderr)
    except (subprocess.TimeoutExpired,ValueError) as exc:
        receipt.update(status='inconclusive',reason=str(exc)[:300])
    receipt['seconds']=time.monotonic()-began
    (folder/'core-lean-receipt.json').write_text(json.dumps(receipt,indent=2))
    result['core_lean']={k:v for k,v in receipt.items() if k not in ['stdout','stderr']}
    result['summary']+=(' The normalized-input UNSAT refutation also passed Lean.' if receipt['status']=='checked'
                       else ' Full Lean refutation remains unverified; see its separate receipt.')


if __name__ == '__main__':
    folder = Path(__file__).resolve().parent
    manifest = json.loads((folder / 'implementation-target.json').read_text())
    assert source_hash() == manifest['source_sha256'], 'Pinned solver changed after assignment'
    for filename, details in manifest.get('snapshot_files', {}).items():
        assert hashlib.sha256((folder / filename).read_bytes()).hexdigest() == details['sha256'], 'Pinned compression helper changed after assignment'
    for relative, digest in manifest['dependencies_sha256'].items():
        assert hashlib.sha256((folder.parent / relative).read_bytes()).hexdigest() == digest, 'Baseline dependency changed after assignment'
    start = time.monotonic()
    data = json.loads((folder / 'structured-output.json').read_text())
    result = check(data)
    if result.get('observed',{}).get('core_refutation',{}).get('status')=='UNSAT':
        check_core_in_lean(folder,data,result)
    else:
        check_compression_in_lean(folder, data, result)
    result.update(seconds=time.monotonic() - start, solver=VERSION, source_sha256=source_hash(),
                  general_polynomial_sat_proof=False, implementation_lean_verified=False)
    (folder / 'test-receipt.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
