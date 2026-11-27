"""Independent implementation of Fable round7 pseudocode and exhaustive SAT oracle.
No candidate-provided code is executed. Finite checks do not establish a general bound.
"""
import itertools as it,json,time,random,hashlib
from pathlib import Path

def canon(formula):
    work={frozenset(c) for c in formula if not any(-x in c for x in c)}
    units={}
    while True:
        if frozenset() in work:return None
        found={next(iter(c)) for c in work if len(c)==1}
        fresh=False
        for lit in found:
            v,b=abs(lit),lit>0
            if v in units and units[v]!=b:return None
            if v not in units:units[v]=b;fresh=True
        if not fresh:break
        nextwork=set()
        for c in work:
            if any(abs(l) in units and units[abs(l)]==(l>0) for l in c):continue
            nextwork.add(frozenset(l for l in c if abs(l) not in units))
        work=nextwork
    work|={frozenset([v if b else -v]) for v,b in units.items()}
    work={c for c in work if not any(d<c for d in work)}
    return tuple(sorted((tuple(sorted(c)) for c in work),key=lambda c:(len(c),c)))

def restrict(f,v,b):
    lit=v if b else -v
    return [tuple(x for x in c if x!=-lit) for c in f if lit not in c]

def below(g,h):
    return all(any(set(c)<=set(d) for c in g) for d in h)

def prune(states):
    return {g for g in states if not any(g!=h and below(g,h) for h in states)}

def models(f,variables):
    if f is None:return set()
    return {bits for bits in it.product((False,True),repeat=len(variables))
            if all(any(dict(zip(variables,bits))[abs(l)]==(l>0) for l in c) for c in f)}

def two_sat(f):
    vertices={l for c in f for x in c for l in (x,-x)}
    edges={v:set() for v in vertices}
    for c in f:
        if not c:return False
        assert len(c)<=2
        a,b=(c[0],c[0]) if len(c)==1 else c
        edges[-a].add(b);edges[-b].add(a)
    def reachable(a,b):
        seen={a};todo=[a]
        while todo:
            u=todo.pop()
            for v in edges[u]-seen:seen.add(v);todo.append(v)
        return b in seen
    return not any(reachable(v,-v) and reachable(-v,v) for v in vertices if v>0)

def mra(f,order,dispatch=False):
    root=canon(f);S=set() if root is None else {root};layers=[];calls=0
    if not S:return {'sat':False,'layers':layers,'terminal_calls':calls}
    for v in order:
        T=set()
        for g in sorted(S):
            for b in (False,True):
                h=canon(restrict(g,v,b))
                if h is None:continue
                if dispatch and all(len(c)<=2 for c in h):
                    calls+=1
                    if two_sat(h):return {'sat':True,'layers':layers,'terminal_calls':calls,'halt_depth':len(layers)+1}
                    continue
                T.add(h)
        S=prune(T)
        layers.append({'pre_prune':len(T),'post_prune':len(S)})
        if not S:return {'sat':False,'layers':layers,'terminal_calls':calls,'halt_depth':len(layers)}
    return {'sat':True if any(not g for g in S) else None,'layers':layers,'terminal_calls':calls,'halt_depth':len(layers),'partial_order':any(g for g in S)}

def cyclic(n):
    return [(i+1,n+i+1,-(n+(i+1)%n+1)) for i in range(n)]+[(-(i+1),-(n+i+1),n+(i+1)%n+1) for i in range(n)]

def tseitin():
    incidences=[([1,2,3],1),([1,4,5],0),([2,4,6],0),([3,5,6],0)]
    return [tuple(-v if b else v for v,b in zip(vs,bits)) for vs,parity in incidences
            for bits in it.product((0,1),repeat=3) if sum(bits)%2!=parity]

def claim(name,observed,expected,results):
    results.append({'claim':name,'observed':observed,'expected':expected,'pass':observed==expected})

def main():
    started=time.time();results=[];details={}
    specs=[('F2_x',[1,2],[(2,2),(3,2)]),('F2_y',[3,4],[(2,2),(3,1)]),
           ('F3_x',[1,2,3],[(2,2),(4,4),(8,8)]),
           ('F3_interleaved',[4,1,5,2,6,3],[(2,2),(4,2),(4,4),(6,2),(3,1),(1,1)])]
    for name,order,expected in specs:
        n=2 if name.startswith('F2') else 3
        observed=mra(cyclic(n),order);details[name]=observed
        pairs=[(x['pre_prune'],x['post_prune']) for x in observed['layers']]
        claim(name+' counting layers',pairs,expected,results)
    for n,want in [(2,10),(3,28)]:
        f=cyclic(n);claim('F'+str(n)+' model count',len(models(f,list(range(1,2*n+1)))),want,results)
        residuals={canon([*f])}
        for v in range(1,n+1):residuals={canon(restrict(g,v,b)) for g in residuals for b in (False,True)}
        functions={frozenset(models(g,list(range(n+1,2*n+1)))) for g in residuals}
        maximal={g for g in functions if not any(g<h for h in functions)}
        claim('F'+str(n)+' distinct residual functions',len(functions),2**n-1,results)
        claim('F'+str(n)+' semantically maximal residuals',len(maximal),2**n-2,results)
    for order,depth in [([1,2,3,4],2),([3,4,1,2],1)]:
        obs=mra(cyclic(2),order,True);claim('F2 dispatch depth '+str(order),obs['halt_depth'],depth,results)
    f=tseitin();claim('K4 Tseitin UNSAT oracle',len(models(f,list(range(1,7)))),0,results)
    histogram={};failures=[]
    for order in it.permutations(range(1,7)):
        obs=mra(f,order,True);k=(obs['sat'],obs['halt_depth'],obs['terminal_calls'],obs['layers'][0]['post_prune']);histogram[str(k)]=histogram.get(str(k),0)+1
        count=mra(f,order[:2]);t2=count['layers'][1]['pre_prune']
        if obs['sat'] or obs['terminal_calls']!=4 or obs['halt_depth']!=2 or obs['layers'][0]['post_prune']!=2 or t2!=4:failures.append({'order':order,'result':obs,'counting_T2':t2})
    claim('K4 all 720 orders follow predicted terminal behavior',len(failures),0,results)
    # Every <=3-clause non-tautological CNF on 3 variables; all six orders.
    clauses=[tuple(sign*v for sign,v in zip(signs,vs)) for k in (1,2,3)
             for vs in it.combinations(range(1,4),k) for signs in it.product((-1,1),repeat=k)]
    cases=0;decisions=0;correctness_failures=[];canon_failures=[]
    for size in range(4):
        for f in it.combinations(clauses,size):
            expected=models(f,[1,2,3]);g=canon(f);cases+=1
            if models(g,[1,2,3])!=expected:canon_failures.append(f)
            for order in it.permutations(range(1,4)):
                observed=mra(f,order,True);decisions+=1
                if observed['sat']!=bool(expected):correctness_failures.append({'f':f,'order':order,'result':observed})
    # Empty-clause and complementary-unit edge cases; oracle uses every assignment.
    for f in [[],[[]],[(1,),(-1,)],[(1,-1)],[(1,),(1,2),(-2,)]]:
        expected=bool(models(f,[1,2,3]));cases+=1
        for order in it.permutations(range(1,4)):
            decisions+=1
            if mra(f,order,True)['sat']!=expected:correctness_failures.append({'f':f,'order':order})
    # Probe the proposed interleaved width bound beyond the hand-worked F3.
    interleaved=[]
    for n in range(2,13):
        order=[v for i in range(1,n+1) for v in (n+i,i)];obs=mra(cyclic(n),order)
        interleaved.append({'n':n,'max_S':max(x['post_prune'] for x in obs['layers']),
                            'max_T':max(x['pre_prune'] for x in obs['layers'])})
    out={'source_proposal_sha256':hashlib.sha256(Path(__file__).parent.parent.joinpath('fable_synthesis_round7/proposal.txt').read_bytes()).hexdigest(),
         'claims':results,'claim_failures':sum(not r['pass'] for r in results),'details':details,
         'k4_order_histogram':histogram,'k4_counterexamples':failures[:3],
         'correctness':{'formulas':cases,'solver_runs':decisions,'wrong_answers':len(correctness_failures),'counterexamples':correctness_failures[:3], 'canonicalization_mismatches':len(canon_failures)},
         'interleaved_cycle_widths':interleaved,'elapsed_seconds':time.time()-started,
         'limits':'Finite independent tests only. No general polynomial width bound, order discovery theorem, or full solver formalization.'}
    Path(__file__).with_name('test-receipt.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
