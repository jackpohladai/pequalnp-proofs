"""Independent finite test of Fable58's unimplemented adapted-basis claim.

Uses explicit small vector spaces only for testing. It establishes neither a
general theorem nor the proposed polynomial complexity bound.
"""
from pathlib import Path
import datetime
import itertools
import json
import random
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'ialh_counting'))
from compression import basis, span


def refine(spaces):
    v=frozenset(span(set().union(*spaces))) if spaces else frozenset([0])
    dimension=len(basis(v))
    if not dimension:return True,[]
    types=[frozenset()]
    def intersection(s):
        answer=set(v)
        for i in s:answer.intersection_update(spaces[i])
        return answer
    for i in range(len(spaces)):
        candidates=set(types)|{t|{i} for t in types}
        table={s:intersection(s) for s in candidates}
        counts={}
        for s in candidates:
            above=set().union(*(a for t,a in table.items() if s<t))
            counts[s]=len(basis(table[s]))-len(basis(above))
        if sum(counts.values())!=dimension:return False,[]
        types=[s for s in candidates if counts[s]>0]
    result=[]
    for s in sorted(types,key=lambda t:(-len(t),sorted(t))):
        above=basis(set().union(*(intersection(t) for t in types if s<t)))
        local=list(above)
        for x in sorted(intersection(s)):
            if len(basis(local+[x]))>len(local):local.append(x);result.append(x)
    accepted=len(result)==dimension and len(basis(result))==dimension and all(span(x for x in result if x in a)==a for a in spaces)
    return accepted,result


def direct(spaces):
    v=span(set().union(*spaces)) if spaces else {0}
    r=len(basis(v))
    for b in itertools.combinations(sorted(v-{0}),r):
        if len(basis(b))==r and all(span(x for x in b if x in a)==a for a in spaces):return True
    return False


def main():
    started=time.monotonic();rng=random.Random(58)
    spaces=sorted({frozenset(span(c)) for k in range(4) for c in itertools.combinations(range(1,8),k)},key=lambda a:(len(a),sorted(a)))
    tests=accepted=0
    for count in range(1,5):
        for family in itertools.combinations_with_replacement(spaces,count):
            family=list(family);rng.shuffle(family)
            oracle=direct(family);value,certificate=refine(family)
            assert value==oracle, (family,value,oracle)
            tests+=1;accepted+=value
    extras=[]
    for n in [4,6,8]:
        for _ in range(100):
            b=list(basis(rng.randrange(1,1<<n) for _ in range(n*2)))
            family=[span(rng.sample(b,rng.randint(0,len(b)))) for _ in range(rng.randint(1,8))]
            value,cert=refine(family);assert value
            extras.append(n)
    # Three dependent distinct lines have no common adapted basis.
    assert refine([{0,1},{0,2},{0,3}])[0] is False
    result={'at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'proposal':'Fable auto00058 ATOM-REFINE',
            'all_subspaces_GF2_dimension3':len(spaces),'families_compared_with_exhaustive_basis_search':tests,
            'accepted':accepted,'rejected':tests-accepted,'planted_compatible_families_dimensions4_6_8':len(extras),
            'mismatches':0,'seconds':time.monotonic()-started,'general_theorem_verified':False,
            'polynomial_cost_verified':False,'deployed':False}
    (HERE/'atom-test-receipt.json').write_text(json.dumps(result,indent=2));print(json.dumps(result))


if __name__=='__main__':main()
