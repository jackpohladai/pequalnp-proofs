"""Bounded symmetric-subformula refutation, never a SAT answer.

Only explicit input clauses may be dropped. An accepted compressed subformula
is sent to 2-SAT only. SAT or a failed detector means UNKNOWN; the original
solver must still decide the original input. Nothing here bounds general SAT.
"""
from collections import Counter
from pathlib import Path
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'neon_antigravity_round4_review'))
from check_scc_and_growth import variables, two_sat
from compression import basis, span, compress_root


def normalize(formula):
    clauses=set()
    for clause in formula:
        if any(type(l) is not int or l==0 for l in clause):
            raise ValueError('CNF literals must be nonzero integers')
        c=set(clause)
        if not any(-l in c for l in c):clauses.add(tuple(sorted(c)))
    return tuple(sorted(clauses))


def probe(formula, max_removed_per_block=4, max_pairs=300000, max_width=8):
    started=time.monotonic();f=normalize(formula);ids=variables(f)
    def unknown(reason,**extra):return dict(status='UNKNOWN',reason=reason,seconds=time.monotonic()-started,**extra)
    if len(ids)>64 or len(f)>1024:return unknown('input_budget')
    mapping={v:i for i,v in enumerate(ids)}
    blocks={}
    for c in f:
        support=tuple(sorted(abs(l) for l in c))
        if len(support)>max_width:return unknown('block_width_budget')
        point=sum(1<<mapping[abs(l)] for l in c if l<0)
        blocks.setdefault(support,{})[point]=c
    if sum(len(b)**2 for b in blocks.values())>max_pairs:return unknown('pair_budget')
    core=[];details=[]
    for support,clauses in sorted(blocks.items()):
        z=set(clauses);counts=Counter(x^y for x in z for y in z)
        best=z;best_key=(-1,0)
        for delta in range(min(max_removed_per_block,len(z)-1)+1):
            translations=[v for v,count in counts.items() if count>=len(z)-delta]
            group=span(translations)
            kept={x for x in z if all(x^v in z for v in group)}
            if not kept or len(z)-len(kept)>max_removed_per_block:continue
            key=(len(basis(group)),len(kept))
            if key>best_key:best_key=key;best=kept
        core.extend(clauses[x] for x in sorted(best))
        details.append({'support':list(support),'before':len(z),'after':len(best)})
    core=normalize(core)
    # Independent containment gate. Proposals cannot inject new constraints.
    if not set(core).issubset(set(f)):return unknown('subset_certificate_failed')
    if core==f:return unknown('no_clauses_removed')
    compressed=compress_root(core)
    if compressed['status']!='compressed':return unknown('core_not_compressed',core=[list(c) for c in core],compression=compressed)
    q=compressed['certificate']['quotient']
    if any(len(c)>2 for c in q):return unknown('core_quotient_not_2sat',core=[list(c) for c in core],compression=compressed)
    if two_sat(q):return unknown('core_quotient_is_sat',core=[list(c) for c in core],compression=compressed)
    return dict(status='UNSAT',core=[list(c) for c in core],original_clauses=len(f),core_clauses=len(core),
                removed_clauses=len(f)-len(core),blocks=details,compression=compressed,
                seconds=time.monotonic()-started,subset_checked=True,search_branching_used=False,
                general_polynomial_sat_proof=False,implementation_lean_verified=False)
