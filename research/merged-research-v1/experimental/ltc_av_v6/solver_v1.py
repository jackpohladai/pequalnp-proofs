"""IALH-5 v1: a certificate-checked integer counting prefilter for SCC-E-MRA.

UNKNOWN means use the existing exact search, never SAT. This experimental code
has no universal search bound and is not Lean-verified. SymPy only proposes
integer-lattice consequences: rejection requires a separate Fraction checker.
"""
from fractions import Fraction
from functools import lru_cache
import hashlib
import itertools as it
import math
from pathlib import Path
import sys
import time

from sympy import Matrix, zeros
from sympy.matrices.normalforms import hermite_normal_form

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'neon_antigravity_round4_review'))
from check_scc_and_growth import canon_plus, elim_plus, restrict, prune, two_sat, variables

VERSION = 'scc-emra-ialh5-v1'
DEFAULTS = dict(k=5, max_windows=256, max_pairs=200000, max_tuples=8192, max_rows=128)


def source_hash():
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def normalize(formula):
    clauses = set()
    for clause in formula:
        if any(type(l) is not int or l == 0 for l in clause):
            raise ValueError('CNF literals must be nonzero integers')
        c = set(clause)
        if not any(-l in c for l in c):
            clauses.add(tuple(sorted(c)))
    return tuple(sorted(clauses))


def up_survives(formula, assignment):
    """Only unit propagation; no full SAT oracle in table construction."""
    values = dict(assignment)
    while True:
        changed = False
        for clause in formula:
            if any(abs(l) in values and values[abs(l)] == (l > 0) for l in clause):
                continue
            unset = [l for l in clause if abs(l) not in values]
            if not unset:
                return False
            if len(unset) == 1:
                l = unset[0]
                values[abs(l)] = l > 0
                changed = True
        if not changed:
            return True


def table(formula, window):
    return [t for t in it.product((0, 1), repeat=len(window))
            if up_survives(formula, zip(window, t))]


def windows(formula, k, max_windows, max_pairs):
    supports = sorted({tuple(sorted(map(abs, c))) for c in formula if len(c) <= k})
    found = set(supports)
    truncated, pairs = False, 0
    for i, s in enumerate(supports):
        for t in supports[i + 1:]:
            if pairs >= max_pairs:
                truncated = True
                break
            pairs += 1
            union = tuple(sorted(set(s) | set(t)))
            if len(union) <= k:
                found.add(union)
        if truncated:
            break
    ordered = sorted(found, key=lambda s: (len(s), s))
    return ordered[:max_windows], truncated or len(ordered) > max_windows


def integer_row(row):
    denominator = math.lcm(*(int(x.q) for x in row)) if row else 1
    return [int(x * denominator) for x in row], denominator


def hull_rows(window, tuples):
    """Compress t0 + integer span(t-t0) into equalities and congruences."""
    n, origin = len(window), Matrix(tuples[0])
    differences = Matrix(n, len(tuples) - 1,
                         lambda i, j: tuples[j + 1][i] - tuples[0][i])
    h = hermite_normal_form(differences) if differences.cols else zeros(n, 0)
    pivots = list(h.T.rref()[1])
    inverse = h.extract(pivots, range(h.cols)).inv() if pivots else zeros(0, 0)
    raw = []
    for i in range(h.cols):
        row = zeros(1, n)
        for j, p in enumerate(pivots):
            row[p] = inverse[i, j]
        a, modulus = integer_row(list(row))
        if modulus > 1:
            raw.append((a, modulus))
    for i in range(n):
        if i in pivots:
            continue
        row = zeros(1, n)
        row[i] = 1
        coefficients = h[i, :] * inverse
        for j, p in enumerate(pivots):
            row[p] -= coefficients[j]
        a, _ = integer_row(list(row))
        raw.append((a, 0))
    return [dict(window=list(window), coefficients=a,
                 rhs=sum(x * int(y) for x, y in zip(a, origin)), modulus=m)
            for a, m in raw]


def row_holds(row, bits):
    value = sum(a * b for a, b in zip(row['coefficients'], bits)) - row['rhs']
    return value == 0 if row['modulus'] == 0 else value % row['modulus'] == 0


def system(rows):
    vs = sorted({v for r in rows for v in r['window']})
    mod_rows = [i for i, r in enumerate(rows) if r['modulus']]
    a = [[0] * (len(vs) + len(mod_rows)) for _ in rows]
    index = {v: i for i, v in enumerate(vs)}
    aux = {row: len(vs) + j for j, row in enumerate(mod_rows)}
    for i, row in enumerate(rows):
        for v, c in zip(row['window'], row['coefficients']):
            a[i][index[v]] += c
        if row['modulus']:
            a[i][aux[i]] = -row['modulus']
    return a, [r['rhs'] for r in rows]


def dual_certificate(a, b):
    """Find u with uA integer and ub noninteger, using exact HNF membership.

    Modular HNF requires a determinant MULTIPLE, not merely a size bound.
    Use an actual nonzero full-rank minor; rank-deficient matrices use ordinary
    exact HNF. No bit-complexity claim is made for this implementation.
    """
    if not a:
        return None
    matrix, target = Matrix(a), Matrix(b)
    cols = list(matrix.rref()[1])
    determinant = abs(int(matrix[:, cols].det())) if len(cols) == matrix.rows else None
    h = hermite_normal_form(matrix, D=determinant) if determinant else hermite_normal_form(matrix)
    pivots = list(h.T.rref()[1])
    inverse = h.extract(pivots, range(h.cols)).inv() if pivots else zeros(0, 0)
    y = inverse * target.extract(pivots, [0])
    for i in range(matrix.rows):
        if i in pivots:
            continue
        u = zeros(1, matrix.rows)
        u[i] = 1
        c = h[i, :] * inverse
        for j, p in enumerate(pivots):
            u[p] -= c[j]
        value = (u * target)[0]
        if value:
            u /= 2 * value
            return [str(x) for x in u]
    for i, value in enumerate(y):
        if value.q != 1:
            u = zeros(1, matrix.rows)
            for j, p in enumerate(pivots):
                u[p] = inverse[i, j]
            return [str(x) for x in u]
    return None


def verify_dual(a, b, encoded):
    """No SymPy/HNF: exact rational arithmetic checks the contradiction."""
    if not a or len(encoded) != len(a):
        return False
    u = [Fraction(x) for x in encoded]
    return (all(sum(u[i] * a[i][j] for i in range(len(a))).denominator == 1
                for j in range(len(a[0])))
            and sum(x * y for x, y in zip(u, b)).denominator != 1)


def verify_certificate(formula, certificate):
    """Rebuild UP tables and check every local consequence and global dual."""
    formula = normalize(formula)
    if certificate['kind'] == 'empty_table':
        return not table(formula, certificate['window'])
    if certificate['kind'] != 'integer_contradiction':
        return False
    rows, tables = certificate['rows'], {}
    for row in rows:
        w = tuple(row['window'])
        if (len(w) != len(set(w)) or len(row['coefficients']) != len(w)
                or row['modulus'] < 0):
            return False
        if w not in tables:
            tables[w] = table(formula, w)
        if not all(row_holds(row, t) for t in tables[w]):
            return False
    a, b = system(rows)
    return verify_dual(a, b, certificate['dual'])


def refute(formula, **options):
    options = dict(DEFAULTS, **options)
    if any(type(x) is not int or x < 0 for x in options.values()):
        raise ValueError('Budgets must be nonnegative integers')
    start = time.monotonic()
    formula = normalize(formula)
    ws, truncated = windows(formula, options['k'], options['max_windows'], options['max_pairs'])
    rows, seen, tried, checked = [], set(), 0, 0
    certificate = None
    for w in ws:
        if tried + 2 ** len(w) > options['max_tuples']:
            truncated = True
            break
        tried += 2 ** len(w)
        checked += 1
        ts = table(formula, w)
        if not ts:
            certificate = dict(kind='empty_table', window=list(w))
            break
        for row in hull_rows(w, ts):
            # Validate even when HNF merely proposed an invalid consequence.
            if not all(row_holds(row, t) for t in ts):
                raise ArithmeticError('Invalid local lattice consequence')
            key = (tuple(row['window']), tuple(row['coefficients']), row['rhs'], row['modulus'])
            if key in seen:
                continue
            seen.add(key)
            if len(rows) >= options['max_rows']:
                truncated = True
                continue
            rows.append(row)
    if certificate is None and rows:
        a, b = system(rows)
        dual = dual_certificate(a, b)
        if dual is not None:
            certificate = dict(kind='integer_contradiction', rows=rows, dual=dual)
    verified = certificate is not None and verify_certificate(formula, certificate)
    if certificate is not None and not verified:
        raise ArithmeticError('Invalid counting rejection certificate')
    return dict(status='UNSAT' if verified else 'UNKNOWN', certificate=certificate,
                windows=checked, tuples=tried, constraints=len(rows), truncated=truncated,
                seconds=time.monotonic() - start, options=options,
                certificate_verified=verified, general_polynomial_sat_proof=False)


def run_counting(formula, order, partial=False, **options):
    """Canonicalize/SCC, counting rejection, then original full ELIM at each node.

    No new unit/equivalence inference or tuple pruning. Full variable orders are
    required for a SAT decision; partial orders explicitly return unknown.
    """
    raw_variables = set(variables(formula))
    original = normalize(formula)
    if (len(order) != len(set(order)) or any(type(v) is not int or v <= 0 for v in order)
            or not set(order).issubset(raw_variables)
            or (not partial and set(order) != raw_variables)):
        raise ValueError('A decision requires every used variable exactly once')
    stats = dict(calls=0, refutations=0, windows=0, tuples=0, seconds=0.0, truncated_calls=0)
    root_check = None

    @lru_cache(maxsize=1024)
    def step(state):
        nonlocal root_check
        reduced, maps = canon_plus(state)
        if reduced is None:
            return 'UNSAT', None, len(maps), 0
        if not reduced:
            return 'SAT', reduced, len(maps), 0
        check = refute(reduced, **options)
        if root_check is None:
            root_check = check
        stats['calls'] += 1
        stats['refutations'] += check['status'] == 'UNSAT'
        for key in ('windows', 'tuples', 'seconds'):
            stats[key] += check[key]
        stats['truncated_calls'] += check['truncated']
        if check['status'] == 'UNSAT':
            return 'UNSAT', None, len(maps), 0
        status, residual, merges, accepted = elim_plus(reduced)
        return status, residual, merges + len(maps), accepted

    status, root, merges, accepted = step(original)
    peak, layers = 0, []
    def result(sat, remaining=0):
        return dict(sat=sat, peak=peak, layers=layers, scc_rounds=merges, accepted_dp=accepted,
                    counting=stats, root_counting=root_check, partial_order=partial,
                    remaining_states=remaining, solver=VERSION, source_sha256=source_hash(),
                    general_polynomial_sat_proof=False)
    if status != 'STUCK':
        return result(status == 'SAT')
    if all(len(c) <= 2 for c in root):
        return result(two_sat(root))
    states, peak = {root}, 1
    for variable in order:
        children = set()
        for state in sorted(states):
            for value in (False, True):
                status, residual, nm, nd = step(tuple(restrict(state, variable, value)))
                merges += nm
                accepted += nd
                if status == 'UNSAT':
                    continue
                if status == 'SAT':
                    return result(True)
                if all(len(c) <= 2 for c in residual):
                    if two_sat(residual):
                        return result(True)
                    continue
                children.add(residual)
        states = prune(children)
        peak = max(peak, len(states))
        layers.append(dict(variable=variable, retained=len(states)))
        if not states:
            return result(False)
    if states and not partial:
        raise ArithmeticError('Full order left undecided residuals')
    return result(None, len(states))
