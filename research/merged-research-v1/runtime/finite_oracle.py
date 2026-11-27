"""Independent finite SAT testing oracle, not part of the research algorithm.

Small inputs use exhaustive enumeration. Larger inputs use bounded DPLL, with
unit propagation and binary branching only. A deadline/node cap gives UNKNOWN,
never a guessed SAT/UNSAT verdict. A completed UNSAT search is empirical test
evidence, not a Lean proof or a polynomial-time algorithm.
"""
import itertools
import time


def solve(formula, max_seconds=8, max_nodes=200000):
    started = time.monotonic()
    vs = sorted({abs(l) for c in formula for l in c})
    nodes = 0
    method = 'exhaustive' if len(vs) <= 12 else 'independent_bounded_dpll'

    def budget():
        if nodes > max_nodes or time.monotonic() - started > max_seconds:
            raise TimeoutError('Independent test oracle budget exhausted')

    def dpll(clauses, assignment):
        nonlocal nodes
        nodes += 1
        budget()
        while True:
            if not clauses:
                return assignment
            if any(not c for c in clauses):
                return None
            unit = next((c[0] for c in clauses if len(c) == 1), None)
            if unit is None:
                break
            assignment = dict(assignment)
            assignment[abs(unit)] = unit > 0
            clauses = [tuple(l for l in c if l != -unit) for c in clauses if unit not in c]
        literal = min(clauses, key=len)[0]
        for l in [literal, -literal]:
            child = dict(assignment)
            child[abs(l)] = l > 0
            result = dpll([tuple(x for x in c if x != -l) for c in clauses if l not in c], child)
            if result is not None:
                return result
        return None

    try:
        witness = None
        if method == 'exhaustive':
            for bits in itertools.product((False, True), repeat=len(vs)):
                nodes += 1
                budget()
                a = dict(zip(vs, bits))
                if all(any(a[abs(l)] == (l > 0) for l in c) for c in formula):
                    witness = a
                    break
        else:
            cleaned = [tuple(set(c)) for c in formula if not any(-l in c for l in c)]
            witness = dpll(cleaned, {})
        if witness is not None:
            witness = {v: witness.get(v, False) for v in vs}
            assert all(any(witness[abs(l)] == (l > 0) for l in c) for c in formula)
        return dict(status='completed', sat=witness is not None, witness=witness,
                    method=method, nodes=nodes, seconds=time.monotonic()-started,
                    formally_checked=False, general_polynomial_sat_proof=False)
    except TimeoutError:
        return dict(status='inconclusive', sat=None, method=method, nodes=nodes,
                    seconds=time.monotonic()-started, formally_checked=False,
                    reason='Test oracle deadline or node cap reached; no SAT verdict.')
