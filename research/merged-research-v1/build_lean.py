"""Compile the consolidated existing components together, without new research."""
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
from pathlib import Path
import datetime,hashlib,json,os,subprocess,time

HERE=Path(__file__).resolve().parent
PROJECT=Path(os.environ.get('PNP_LEAN_PROJECT', str(HERE.parents[1]/'lean'))).expanduser().resolve()
LEAN=Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'


def main():
    modules=json.loads((HERE/'lean/source-manifest.json').read_text())
    lib=HERE/'lean/lib';lib.mkdir(exist_ok=True)
    packages=json.loads((PROJECT/'lake-manifest.json').read_text())
    paths=[lib,PROJECT/'.lake/build/lib/lean']
    for p in packages['packages']:
        path=PROJECT/packages['packagesDir']/p['name']/(p.get('subDir') or '')/'.lake/build/lib/lean'
        if path.is_dir():paths.append(path)
    env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,paths))
    version=subprocess.check_output([str(LEAN),'--version'],text=True).strip()
    assert 'version 4.36.0,' in version
    def compile_one(name,row):
        source=HERE/row['merged_source'];assert hashlib.sha256(source.read_bytes()).hexdigest()==row['merged_sha256']
        start=time.monotonic();command=[str(LEAN),'-j','1','-DElab.async=false','--root='+str(HERE/'lean/src'),'-o',str(lib/(name+'.olean')),str(source)]
        try:
            p=subprocess.run(command,cwd=HERE/'lean/src',env=env,capture_output=True,text=True,timeout=240)
            result={'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,
                    'status':'checked' if p.returncode==0 and 'sorryAx' not in p.stdout else 'failed'}
        except subprocess.TimeoutExpired:
            result={'status':'inconclusive','reason':'Integration compilation exceeded240seconds'}
        result.update(seconds=time.monotonic()-start,source_sha256=row['merged_sha256'],command=command)
        return result
    pending=set(modules);done={};running={};started=time.monotonic()
    previous_path=HERE/'lean/build-progress.json'
    previous=json.loads(previous_path.read_text()).get('modules',{}) if previous_path.exists() else {}
    # Reuse only this integration build's successful modules and their unchanged
    # local dependency closure; changed sources are always recompiled.
    while True:
        reused=[]
        for name in sorted(pending):
            row=previous.get(name,{});artifact=lib/(name+'.olean')
            if (row.get('status')=='checked' and row.get('source_sha256')==modules[name]['merged_sha256']
                    and artifact.exists() and all(d in done for d in modules[name]['imports'])):
                row=dict(row,reused_artifact_sha256=hashlib.sha256(artifact.read_bytes()).hexdigest())
                done[name]=row;reused.append(name)
        pending.difference_update(reused)
        if not reused:break
    print('Reused unchanged checked modules:',len(done),flush=True)
    with ThreadPoolExecutor(max_workers=2) as pool:
        while pending or running:
            ready=[n for n in sorted(pending) if all(d in done and done[d]['status']=='checked' for d in modules[n]['imports'])]
            for n in ready[:2-len(running)]:
                pending.remove(n);running[pool.submit(compile_one,n,modules[n])]=n
            if not running:break
            complete,_=wait(running,return_when=FIRST_COMPLETED)
            for future in complete:
                n=running.pop(future)
                try:done[n]=future.result()
                except Exception as exc:done[n]={'status':'failed','seconds':0,'reason':repr(exc)}
                print(n,done[n]['status'],round(done[n]['seconds'],2),flush=True)
            (HERE/'lean/build-progress.json').write_text(json.dumps({'modules':done,'pending':sorted(pending)},indent=2))
    smoke=HERE/'lean/src/AllComponents.lean';smoke.write_text('\n'.join('import '+n for n in sorted(modules))+'\n')
    if not pending and all(v['status']=='checked' for v in done.values()):
        sm=compile_one('AllComponents',{'merged_source':str(smoke.relative_to(HERE)),'merged_sha256':hashlib.sha256(smoke.read_bytes()).hexdigest()})
    else:sm={'status':'blocked_by_failed_module'}
    receipt={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lean_version':version,'lean_path':env['LEAN_PATH'],
             'modules':done,'pending':sorted(pending),'all_components':sm,'seconds':time.monotonic()-started,
             'status':'checked' if sm['status']=='checked' else 'failed','general_polynomial_sat_proof':False,
             'scope':'Existing components compile and import together. Their individual hypotheses remain; this does not compose a polynomial general SAT proof.'}
    (HERE/'lean/build-receipt.json').write_text(json.dumps(receipt,indent=2));print('INTEGRATION',receipt['status'],len(done),flush=True)
    assert receipt['status']=='checked'


if __name__=='__main__':main()
