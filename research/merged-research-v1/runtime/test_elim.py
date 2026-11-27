import sys,itertools as it,json,time,random,functools
from pathlib import Path
from test_mra import canon,models,cyclic,restrict,prune,two_sat,mra

def variables(f):return sorted({abs(l) for c in f for l in c})
def attempt(f,v):
 pos=[c for c in f if v in c];neg=[c for c in f if -v in c];rest=[c for c in f if v not in c and -v not in c]
 res=[]
 for c in pos:
  for d in neg:
   r=(set(c)-{v})|(set(d)-{-v})
   if not any(-x in r for x in r):res.append(tuple(sorted(r)))
 result=canon(rest+res)
 return result,len(result or [()])<=len(f),{'variable':v,'pairs':len(pos)*len(neg),'resolvents_before_dedup':len(res),'unique_resolvents':len(set(res)),'clauses_before':len(f),'temporary_clauses':len(set(rest+res)),'clauses_after':1 if result is None else len(result),'pos':pos,'neg':neg}

def elim(f,tie=None):
 f=canon(f);steps=[];stack=[]
 while f is not None and variables(f):
  ranks={v:i for i,v in enumerate(tie or variables(f))}
  order=sorted(variables(f),key=lambda v:(sum(v in c for c in f)*sum(-v in c for c in f),ranks.get(v,v)))
  for v in order:
   new,allowed,record=attempt(f,v)
   if allowed:
    steps.append(record);stack.append((v,record['pos'],record['neg']));f=new;break
  else:return {'status':'STUCK','formula':f,'steps':steps,'stack':stack}
 return {'status':'UNSAT' if f is None else 'SAT','formula':f,'steps':steps,'stack':stack}

def reconstruct(stack,assignment=None):
 a=dict(assignment or {})
 for v,pos,neg in reversed(stack):a[v]=any(all(not (a.get(abs(l),False)==(l>0)) for l in c if l!=v) for c in pos)
 return a

def evaluates(f,a):return all(any(a.get(abs(l),False)==(l>0) for l in c) for c in f)

def emra(f,order):
 first=elim(f)
 if first['status']!='STUCK':return {'sat':first['status']=='SAT','max_states':0,'branches':0}
 S={first['formula']};peak=1;branches=0
 for v in order:
  T=set()
  for g in sorted(S):
   for b in (False,True):
    branches+=1;e=elim(restrict(g,v,b))
    if e['status']=='UNSAT':continue
    if e['status']=='SAT':return {'sat':True,'max_states':peak,'branches':branches}
    h=e['formula']
    if all(len(c)<=2 for c in h):
     if two_sat(h):return {'sat':True,'max_states':peak,'branches':branches}
     continue
    T.add(h)
  S=prune(T);peak=max(peak,len(S))
  if not S:return {'sat':False,'max_states':peak,'branches':branches}
 return {'sat':True if any(not g for g in S) else None,'max_states':peak,'branches':branches}

def family(n):
 corevars=[n+1,2*n+1,2*n+2]
 core=[tuple(s*v for s,v in zip(signs,corevars)) for signs in it.product((-1,1),repeat=3)]
 return cyclic(n)+core

@functools.lru_cache(None)
def all_admissible(f):
 if f is None:return (True,0,1)
 if not variables(f):return (False,0,1)
 allowed=[]
 for v in variables(f):
  g,ok,_=attempt(f,v)
  if ok:allowed.append(g)
 if not allowed:return (False,1,1)
 children=[all_admissible(g) for g in allowed]
 return (all(c[0] for c in children),sum(c[1] for c in children),sum(c[2] for c in children))

def main():
 start=time.time();base=family(2);control=[c for c in base if tuple(c)!=(3,5,6)];rows=[]
 for label,f in [('G2',base),('G2_control',control)]:
  result=elim(f);a=reconstruct(result['stack']) if result['status']=='SAT' else None
  rows.append({'name':label,'status':result['status'],'model_count':len(models(f,list(range(1,7)))),'variable_order':[s['variable'] for s in result['steps']],'clause_counts':[len(canon(f))]+[s['clauses_after'] for s in result['steps']],'non_tautological_resolvents_before_up':sum(s['resolvents_before_dedup'] for s in result['steps']),'model':a,'model_valid':evaluates(f,a) if a is not None else None})
 corpus=0;decisions=0;wrong=[];badwitness=[];projection_failures=[]
 clauses=[tuple(s*v for s,v in zip(signs,vs)) for k in (1,2,3) for vs in it.combinations(range(1,4),k) for signs in it.product((-1,1),repeat=k)]
 for size in range(4):
  for f in it.combinations(clauses,size):
   expected=bool(models(f,[1,2,3]));corpus+=1;simple=elim(f)
   if simple['status']=='SAT' and not evaluates(f,reconstruct(simple['stack'])):badwitness.append(f)
   g=canon(f)
   if g is not None:
    for v in variables(g):
     h,_,_=attempt(g,v);remaining=[x for x in [1,2,3] if x!=v]
     projected={tuple(b for x,b in zip([1,2,3],a) if x!=v) for a in models(g,[1,2,3])}
     if models(h,remaining)!=projected:projection_failures.append((f,v))
   for order in it.permutations([1,2,3]):
    decisions+=1
    if emra(f,order)['sat']!=expected:wrong.append((f,order))
 for f in [[],[[]],[(1,),(-1,)],[(1,-1)],[(1,),(1,2),(-2,)]]:
  corpus+=1;expected=bool(models(f,[1,2,3]))
  for order in it.permutations([1,2,3]):
   decisions+=1
   if emra(f,order)['sat']!=expected:wrong.append((f,order))
 rng=random.Random(831126);stress=0
 for i in range(500):
  n=4+i%3;cs=[tuple(s*v for s,v in zip(signs,vs)) for vs in it.combinations(range(1,n+1),3) for signs in it.product((-1,1),repeat=3)]
  f=rng.sample(cs,min(len(cs),rng.randint(3*n,6*n)));truth=bool(models(f,list(range(1,n+1))));e=elim(f)
  if e['status']=='SAT' and not evaluates(f,reconstruct(e['stack'])):badwitness.append(f)
  order=list(range(1,n+1));rng.shuffle(order)
  for o in [list(range(1,n+1)),list(range(n,0,-1)),order]:
   stress+=1
   if emra(f,o)['sat']!=truth:wrong.append((f,o))
 familyrows=[]
 for n in range(2,13):
  f=family(n);e=elim(f)
  familyrows.append({'n':n,'variables':2*n+2,'status':e['status'],'eliminations':len(e['steps']),'non_taut_resolvents':sum(s['resolvents_before_dedup'] for s in e['steps'])})
 robust=[]
 for n in [2,3]:
  all_admissible.cache_clear();answer=all_admissible(canon(family(n)));robust.append({'n':n,'all_end_unsat':answer[0],'stuck_paths':answer[1],'terminal_paths':answer[2],'distinct_states':all_admissible.cache_info().currsize})
 out={'examples':rows,'exhaustive_formulas':corpus,'exhaustive_solver_runs':decisions,'stress_solver_runs':stress,'wrong_answers':len(wrong),'invalid_reconstructed_models':len(badwitness),'projection_mismatches':len(projection_failures),'counterexamples':wrong[:2],'family_min_product_checks':familyrows,'all_admissible_order_checks':robust,'elapsed_seconds':time.time()-start,'limits':'Finite tests, not proof of universal frontier bound. Resolution proof-size and full memory bound not established. Resolvent counts exclude unit-propagation proof steps.'}
 Path(__file__).with_name('test-receipt.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
if __name__=='__main__':main()
