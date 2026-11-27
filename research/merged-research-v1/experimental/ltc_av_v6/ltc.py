"""Bounded Link-Twin Contraction (LTC) with independent syntactic certification.

An OR-twin contraction eliminates v2 = |l2| into v1 = |l1| via t = l1 OR l2,
rewriting (l1 | l2 | R) -> (+v1 | R) and each pair (-l1 | S), (-l2 | S) -> (-v1 | S),
leaving clauses without v1, v2 untouched. (AND-twins are OR-twins on negated
literals.) Discovery is untrusted; every accepted chain is checked by
verify_ltc_certificate before use.
"""
import time


def _normalize(formula):
    clauses = set()
    for clause in formula:
        if any(type(l) is not int or l == 0 for l in clause):
            raise ValueError('CNF literals must be nonzero integers')
        c = set(clause)
        if not any(-l in c for l in c):
            clauses.add(tuple(sorted(c)))
    return tuple(sorted(clauses))


def find_ltc_step(formula):
    """Find one syntactic OR-twin pair (l1, l2) with |l1| < |l2| if one exists."""
    f = _normalize(formula)
    vs = sorted({abs(l) for c in f for l in c})
    if len(vs) < 2 or not f:
        return None
    occ = {l: [] for v in vs for l in (v, -v)}
    for idx, c in enumerate(f):
        for l in c:
            occ[l].append(idx)
    occ_t = {l: tuple(idxs) for l, idxs in occ.items()}
    neg_links = {}
    for l in occ_t:
        neg = -l
        links = tuple(sorted(tuple(x for x in f[idx] if x != neg) for idx in occ_t[neg]))
        neg_links[l] = links

    buckets = {}
    for l in occ_t:
        key = (occ_t[l], neg_links[l])
        buckets.setdefault(key, []).append(l)

    best = None
    for (co_idxs, neg_l), lits in buckets.items():
        if len(lits) < 2 or (not co_idxs and not neg_l):
            continue
        # Sort by (abs(l), l < 0) so smallest variable ID is retained.
        lits_sorted = sorted(lits, key=lambda x: (abs(x), x < 0))
        for i in range(len(lits_sorted)):
            l1 = lits_sorted[i]
            v1 = abs(l1)
            set_neg1 = set(occ_t[-l1])
            for j in range(i + 1, len(lits_sorted)):
                l2 = lits_sorted[j]
                v2 = abs(l2)
                if v1 == v2:
                    continue
                set_neg2 = set(occ_t[-l2])
                if not set_neg1.isdisjoint(set_neg2):
                    continue
                # Ensure remainders do not mention v1 or v2.
                if any(abs(x) in (v1, v2) for r in neg_l for x in r):
                    continue
                co_set = set(co_idxs)
                used = co_set | set_neg1 | set_neg2
                co_rem = tuple(sorted(tuple(x for x in f[idx] if x not in (l1, l2)) for idx in co_idxs))
                if any(abs(x) in (v1, v2) for r in co_rem for x in r):
                    continue
                rest = tuple(f[idx] for idx in range(len(f)) if idx not in used)
                cand = (v1, v2, l1, l2, co_rem, neg_l, rest)
                if best is None or (v1, v2) < (best[0], best[1]):
                    best = cand
                break
    if best is None:
        return None
    v1, v2, l1, l2, co_rem, neg_rem, rest = best
    next_clauses = (
        [(v1,) + r for r in co_rem]
        + [(-v1,) + s for s in neg_rem]
        + list(rest)
    )
    next_f = _normalize(next_clauses)
    step = {
        'l1': l1,
        'l2': l2,
        'co_remainders': [list(r) for r in co_rem],
        'neg_remainders': [list(s) for s in neg_rem],
        'rest_clauses': [list(c) for c in rest],
        'input': [list(c) for c in f],
        'output': [list(c) for c in next_f],
    }
    return step, next_f


def verify_ltc_certificate(formula, cert):
    """Independently check every step of an LTC certificate without trusting discovery."""
    try:
        return _verify_ltc_certificate(formula, cert)
    except (KeyError, TypeError, ValueError, IndexError):
        return False


def _verify_ltc_certificate(formula, cert):
    if not isinstance(cert, dict):
        return False
    steps = cert.get('steps')
    quotient = cert.get('quotient')
    if not isinstance(steps, list) or not isinstance(quotient, list):
        return False
    cur = _normalize(formula)
    for step in steps:
        if not isinstance(step, dict):
            return False
        l1, l2 = step['l1'], step['l2']
        if type(l1) is not int or type(l2) is not int or l1 == 0 or l2 == 0:
            return False
        v1, v2 = abs(l1), abs(l2)
        if v1 == v2:
            return False
        co_rem = [tuple(sorted(r)) for r in step['co_remainders']]
        neg_rem = [tuple(sorted(s)) for s in step['neg_remainders']]
        rest = [tuple(sorted(c)) for c in step['rest_clauses']]
        if len(co_rem) + len(neg_rem) == 0:
            return False
        for c in co_rem + neg_rem + rest:
            if any(type(x) is not int or x == 0 or abs(x) in (v1, v2) for x in c):
                return False
            if len(set(c)) != len(c) or any(-x in c for x in c):
                return False
        if len(set(co_rem)) != len(co_rem) or len(set(neg_rem)) != len(neg_rem) or len(set(rest)) != len(rest):
            return False
        co_clauses = [tuple(sorted((l1, l2) + r)) for r in co_rem]
        neg1_clauses = [tuple(sorted((-l1,) + s)) for s in neg_rem]
        neg2_clauses = [tuple(sorted((-l2,) + s)) for s in neg_rem]
        reconstructed_list = co_clauses + neg1_clauses + neg2_clauses + rest
        reconstructed = _normalize(reconstructed_list)
        if len(reconstructed_list) != len(reconstructed) or reconstructed != cur:
            return False
        out_list = [(v1,) + r for r in co_rem] + [(-v1,) + s for s in neg_rem] + rest
        next_cur = _normalize(out_list)
        if len(out_list) != len(next_cur):
            return False
        if _normalize(step.get('input', [])) != cur or _normalize(step.get('output', [])) != next_cur:
            return False
        cur = next_cur
    return cur == _normalize(quotient)


def lift_ltc_assignment(cert, assignment):
    """Constructively lift a satisfying assignment of the LTC quotient back to original variables."""
    a = dict(assignment)
    for step in reversed(cert['steps']):
        l1, l2 = step['l1'], step['l2']
        v1, v2 = abs(l1), abs(l2)
        target = bool(a.get(v1, False))
        # Set l2 false, so l1 must realize target = (l1 OR l2).
        a[v2] = (l2 < 0)
        a[v1] = target if l1 > 0 else (not target)
    return a


def compress_ltc(formula, max_steps=64, max_variables=64, max_clauses=1024):
    """Run bounded Link-Twin Contraction and independently verify its certificate."""
    start = time.monotonic()
    f = _normalize(formula)
    vs = sorted({abs(l) for c in f for l in c})
    if len(vs) > max_variables or len(f) > max_clauses or len(vs) < 2:
        return dict(status='skipped', reason='budget_or_trivial',
                    original_variables=len(vs), original_clauses=len(f),
                    quotient_variables=len(vs), quotient_clauses=len(f),
                    steps=0, seconds=time.monotonic() - start, certificate_verified=False)
    cur = f
    steps = []
    while len(steps) < max_steps:
        found = find_ltc_step(cur)
        if found is None:
            break
        step, cur = found
        steps.append(step)
    if not steps:
        return dict(status='skipped', reason='no_link_twins',
                    original_variables=len(vs), original_clauses=len(f),
                    quotient_variables=len(vs), quotient_clauses=len(f),
                    steps=0, seconds=time.monotonic() - start, certificate_verified=False)
    cert = {'steps': steps, 'quotient': [list(c) for c in cur]}
    if not verify_ltc_certificate(f, cert):
        return dict(status='skipped', reason='certificate_rejected',
                    original_variables=len(vs), original_clauses=len(f),
                    quotient_variables=len(vs), quotient_clauses=len(f),
                    steps=0, seconds=time.monotonic() - start, certificate_verified=False)
    q_vars = sorted({abs(l) for c in cur for l in c})
    return dict(status='compressed',
                original_variables=len(vs), original_clauses=len(f),
                quotient_variables=len(q_vars), quotient_clauses=len(cur),
                steps=len(steps), certificate=cert,
                seconds=time.monotonic() - start,
                certificate_verified=True,
                general_polynomial_sat_proof=False)
