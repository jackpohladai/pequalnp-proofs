"""Integration checks for existing solver, ordering experiment and shared cache."""
from pathlib import Path
import json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'runtime'))
from solver import run_counting,variables,source_hash,VERSION


def main():
    evidence=ROOT/'evidence';out=[]
    data=json.loads((evidence/'fable_worstcase_auto_00072/structured-output.json').read_text())['fixture']
    without=run_counting(data['formula'],data['order'],cache_counting=False)
    with_cache=run_counting(data['formula'],data['order'])
    assert without['sat']==with_cache['sat']==False and without['layers']==with_cache['layers']
    assert without['counting']['calls']==12 and with_cache['counting']['calls']==8 and with_cache['counting']['cache_hits']==4
    out.append({'source':'fable72','cache_off_calls':12,'cache_on_calls':8,'same_decision_and_layers':True})
    data=json.loads((evidence/'neon_worstcase_auto_00058/structured-output.json').read_text())
    order=[1,9,3,11,5,13,7,15,2,10,4,12,6,14,8,16]
    base=run_counting(data['formula'],data['order'])
    reordered=run_counting(data['formula'],data['order'],quotient_order=order)
    assert base['sat']==reordered['sat']==False and base['peak']==8 and reordered['peak']==2
    out.append({'source':'neon58','default_peak':8,'explicit_quotient_order_peak':2,'sat':False})
    for invalid in [order[:-1],order+[order[0]],[False]+order[1:]]:
        try:run_counting(data['formula'],data['order'],quotient_order=invalid)
        except ValueError:pass
        else:raise AssertionError('Invalid quotient order was accepted')
    for name in ['neon_worstcase_auto_00053','neon_worstcase_auto_00056']:
        data=json.loads((evidence/name/'structured-output.json').read_text());r=run_counting(data['formula'],data['order'])
        assert r['sat'] is False and r['peak']==0 and r['core_refutation']['status']=='UNSAT'
        out.append({'source':name,'core_preserved':True,'peak':0,'sat':False})
    for f in [[],[[]],[[1,-1]],[[1],[-1]],[[1,2],[-1,2]]]:
        a=run_counting(f,variables(f));b=run_counting(f,variables(f),cache_counting=False);assert a['sat']==b['sat']
    receipt={'status':'passed','solver':VERSION,'source_sha256':source_hash(),'checks':out,'invalid_order_cases':3,'basic_cache_parity_cases':5,
             'general_polynomial_sat_proof':False,'scope':'Integration checks only; no new conjectures tested.'}
    (HERE/'merge-test-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))


if __name__=='__main__':main()
