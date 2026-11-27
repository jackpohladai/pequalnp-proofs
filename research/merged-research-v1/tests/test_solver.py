import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'runtime'))
"""Independent finite-oracle regressions; passing is not a general proof."""
import copy
import datetime as dt
import itertools as it
import json
from pathlib import Path
import random
import time

from sympy import Matrix, zeros
from sympy.matrices.normalforms import hermite_normal_form
from solver import (DEFAULTS, VERSION, dual_certificate, hull_rows, normalize,
                    refute, row_holds, run_counting, source_hash, system,
                    up_survives, variables, verify_certificate, verify_dual)
from check_scc_and_growth import run_plus, neon_family

HERE = Path(__file__).resolve().parent


def oracle(formula):
    vs = variables(formula)
    for t in it.product((False, True), repeat=len(vs)):
        a = dict(zip(vs, t))
        if all(any(a[abs(l)] == (l > 0) for l in c) for c in formula):
            return True
    return False


def main():
    start = time.monotonic()
    rng = random.Random(20261126)
    checks = {}
    # Check all tiny tables against direct column-lattice membership, including
    # non-coordinate rank-deficient hulls and Boolean points outside the table.
    tables, points = 0, 0
    for n in (1, 2, 3):
        cube = list(it.product((0, 1), repeat=n))
        for mask in range(1, 2 ** len(cube)):
            ts = [t for i, t in enumerate(cube) if mask >> i & 1]
            rows = hull_rows(tuple(range(1, n + 1)), ts)
            d = Matrix(n, len(ts) - 1, lambda i, j: ts[j + 1][i] - ts[0][i])
            h = hermite_normal_form(d) if d.cols else zeros(n, 0)
            for t in cube:
                augmented = d.row_join(Matrix([t[i] - ts[0][i] for i in range(n)]))
                expected = hermite_normal_form(augmented) == h
                assert all(row_holds(r, t) for r in rows) == expected, (ts, t, rows)
                points += 1
            tables += 1
    checks.update(exhaustive_hull_tables=tables, hull_membership_points=points)
    # Explicit ordinary equality and composite-modulus cases.
    for n, weights in [(4, {2}), (5, {0, 3}), (5, {0, 4}), (6, {0, 5})]:
        ts = [t for t in it.product((0, 1), repeat=n) if sum(t) in weights]
        rows = hull_rows(tuple(range(1, n + 1)), ts)
        for t in it.product((0, 1), repeat=n):
            assert all(row_holds(r, t) for r in rows) == (sum(t) in weights)
    checks['equality_mod3_mod4_mod5_tables'] = 4
    # An actual determinant multiple is used by modular HNF; test exact duals
    # on inconsistent rank-deficient and full-rank systems and planted solutions.
    cases = [([[0]], [1]), ([[2]], [1]), ([[3]], [1]), ([[4]], [2]),
             ([[1], [1]], [0, 1]), ([[2, 0], [0, 4]], [0, 2])]
    for a, b in cases:
        u = dual_certificate(a, b)
        assert u is not None and verify_dual(a, b, u)
    for _ in range(200):
        m, n = rng.randint(1, 6), rng.randint(1, 8)
        a = [[rng.randint(-4, 4) for _ in range(n)] for _ in range(m)]
        witness = [rng.randint(-10, 10) for _ in range(n)]
        b = [sum(c * x for c, x in zip(row, witness)) for row in a]
        assert dual_certificate(a, b) is None, (a, b)
    checks.update(contradiction_kernel_cases=len(cases), planted_integer_solutions=200)
    edge = [[], [[]], [[1], [-1]], [[1, -1]], [[1, 1]], [[1, -1], [2]],
            [[-1, -2], [1, 2]], [[1, 2], [1, -2], [-1, 2], [-1, -2]],
            [[101, -203], [-101, 203]], [[1, 1], [-1, -1]]]
    random_cases = []
    # Random and planted SAT cases exercise raw-table filtering separately from
    # the branch solver, so easy DP exits cannot hide false counting rejections.
    for index in range(400):
        n = rng.randint(3, 7)
        vs = list(range(1, n + 1))
        formula = [tuple(rng.choice((-1, 1)) * v for v in rng.sample(vs, rng.randint(2, min(4, n))))
                   for _ in range(rng.randint(2, 32))]
        if index % 2 == 0:
            planted = {v: rng.choice((False, True)) for v in vs}
            formula = [c if any(planted[abs(l)] == (l > 0) for l in c) else (-c[0],) + c[1:] for c in formula]
        random_cases.append(formula)
    sat_count, direct_rejections = 0, 0
    for f in edge + random_cases:
        truth = oracle(f)
        direct = refute(f)
        assert not (truth and direct['status'] == 'UNSAT'), (f, direct)
        if direct['status'] == 'UNSAT':
            assert verify_certificate(f, direct['certificate'])
            direct_rejections += 1
        full = run_counting(f, variables(f))
        assert full['sat'] == truth, (f, full)
        assert run_plus(f, variables(f))['sat'] == truth
        sat_count += truth
    checks.update(exhaustive_cnf_cases=len(edge) + len(random_cases), satisfiable_cases=sat_count,
                  direct_counting_rejections=direct_rejections, correctness_failures=0)
    f = [[1, 2, 3], [-1, 2, 3], [1, -2, 3], [1, 2, -3]]
    assert refute(f, max_windows=0)['status'] == 'UNKNOWN'
    assert refute(f, max_tuples=0)['status'] == 'UNKNOWN'
    assert refute(f, max_rows=0)['status'] == 'UNKNOWN'
    assert run_counting(f, [1, 2, 3], max_windows=0)['sat'] == oracle(f)
    try:
        run_counting(f, [1])
    except ValueError:
        pass
    else:
        raise AssertionError('Incomplete full order was accepted')
    checks['budget_and_order_cases'] = 5
    fixtures = []
    for name in ['neon_antigravity_round2', 'neon_antigravity_round3', 'fable_worstcase_round5',
                 'neon_antigravity_round5', 'neon_antigravity_round6', 'neon_worstcase_auto_00002',
                 'neon_worstcase_auto_00003']:
        data = json.loads((HERE.parent/'evidence' / name / 'structured-output.json').read_text())
        candidate = data.get('fixture') or data
        if not candidate.get('formula'):
            continue
        f, order = candidate['formula'], candidate['order']
        truth = oracle(f)
        began = time.monotonic()
        before = run_plus(f, order)
        old_seconds = time.monotonic() - began
        began = time.monotonic()
        after = run_counting(f, order)
        new_seconds = time.monotonic() - began
        assert after['sat'] == before['sat'] == truth
        fixtures.append(dict(source=name, variables=len(variables(f)), clauses=len(f), oracle_sat=truth,
                             baseline=before, updated=after, baseline_seconds=old_seconds, updated_seconds=new_seconds))
        if name == 'neon_antigravity_round6':
            assert after['peak'] == 0 and after['accepted_dp'] == 0
            cert = after['root_counting']['certificate']
            assert cert['kind'] == 'integer_contradiction'
            wrong = copy.deepcopy(cert)
            wrong['dual'] = ['0'] * len(wrong['dual'])
            assert not verify_certificate(f, wrong)
            wrong = copy.deepcopy(cert)
            wrong['rows'][0]['rhs'] += 1
            assert not verify_certificate(f, wrong)
    # Previously checked prefix-growth family, caught now by local hulls at k=5.
    family = []
    for k in (2, 3, 4):
        f = neon_family(k)
        after = run_counting(f, list(range(1, k + 1)), partial=True)
        assert after['sat'] is False
        family.append(dict(k=k, result=after))
    receipt = dict(at=dt.datetime.now(dt.timezone.utc).isoformat(), solver=VERSION,
                   source_sha256=source_hash(), options=DEFAULTS, checks=checks, fixtures=fixtures,
                   xor_family=family, seconds=time.monotonic() - start,
                   general_polynomial_sat_proof=False, implementation_lean_verified=False,
                   scope='Finite exhaustive oracles and exact certificate arithmetic; no universal growth bound.')
    (HERE / 'test-receipt.json').write_text(json.dumps(receipt, indent=2))
    print(json.dumps({k: v for k, v in receipt.items() if k not in ['fixtures', 'xor_family']}), flush=True)
    print(json.dumps([dict(source=r['source'], before=r['baseline']['peak'], after=r['updated']['peak'],
                          old_seconds=r['baseline_seconds'], new_seconds=r['updated_seconds']) for r in fixtures]), flush=True)


if __name__ == '__main__':
    main()
