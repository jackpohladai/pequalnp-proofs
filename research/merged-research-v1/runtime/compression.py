"""Bounded BLQ compression with compositional certificate checking.

Discovery uses bounded vector-space enumeration and a greedy compatible basis,
not Fable's unproved polynomial atom-descent procedure. Compression runs once
at the root. Any skip preserves the original input for the existing solver.
"""
import itertools as it
import time

LIMITS = dict(max_variables=64, max_block_width=8, max_clauses=1024,
              max_space_points=16384, max_verification_work=8000000)


def parity(x):
    return bin(x).count('1') % 2


def basis(vectors):
    rows = {}
    for v in vectors:
        while v:
            pivot = v.bit_length() - 1
            if pivot in rows:
                v ^= rows[pivot]
            else:
                rows[pivot] = v
                break
    return tuple(rows[k] for k in sorted(rows, reverse=True))


def span(vectors):
    result = {0}
    for v in basis(vectors):
        result |= {x ^ v for x in result}
    return result


def points(support):
    return [sum(bit << (v - 1) for v, bit in zip(support, bits))
            for bits in it.product((0, 1), repeat=len(support))]


def dense_formula(formula, ids):
    mapping = {v: i + 1 for i, v in enumerate(ids)}
    return [tuple(mapping[abs(l)] if l > 0 else -mapping[abs(l)] for l in c) for c in formula]


def evaluate(formula, assignment):
    return all(any(bool(assignment & (1 << (abs(l) - 1))) == (l > 0) for l in c) for c in formula)


def project(assignment, forms):
    return sum(parity(assignment & v) << i for i, v in enumerate(forms))


def lift(assignment, columns):
    result = 0
    for i, column in enumerate(columns):
        if assignment & (1 << i):
            result ^= column
    return result


def right_inverse(forms, n):
    """Gauss-Jordan elimination over GF(2); never enumerate global assignments."""
    rows = [[v, 1 << i] for i, v in enumerate(forms)]
    pivots, rank = [], 0
    for bit in range(n):
        pivot = next((j for j in range(rank, len(rows)) if rows[j][0] & (1 << bit)), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        for j in range(len(rows)):
            if j != rank and rows[j][0] & (1 << bit):
                rows[j][0] ^= rows[rank][0]
                rows[j][1] ^= rows[rank][1]
        pivots.append(bit)
        rank += 1
    if rank != len(forms):
        return None
    return [sum(1 << pivots[j] for j in range(rank) if rows[j][1] & (1 << i))
            for i in range(rank)]


def verify_certificate(formula, cert):
    """Check local truth tables and every entry of P*L=I independently.

    The certificate partitions quotient clauses by exact original support.
    Every referenced form must be supported in that block. Equality for all
    local assignments gives equality for every global assignment by conjunction.
    The matrix identity proves surjectivity by linearity; no global truth table.
    No stabilizer or greedy-basis discovery result is trusted here.
    """
    try:
        return _verify_certificate(formula, cert)
    except (KeyError, TypeError, ValueError, IndexError):
        return False


def _verify_certificate(formula, cert):
    ids = sorted({abs(l) for c in formula for l in c})
    if cert.get('variables') != ids or len(ids) > LIMITS['max_variables']:
        return False
    n, forms, quotient, columns = len(ids), cert['basis_forms'], cert['quotient'], cert['right_inverse']
    r = len(forms)
    if not (0 < r < n) or len(columns) != r:
        return False
    if any(type(v) is not int or not 0 <= v < 2 ** n for v in forms + columns):
        return False
    if any(type(l) is not int or not 1 <= abs(l) <= r for c in quotient for l in c):
        return False
    original = dense_formula(formula, ids)
    blocks = {}
    for c in original:
        if len(set(map(abs, c))) != len(c):
            return False
        blocks.setdefault(tuple(sorted(map(abs, c))), []).append(c)
    counts = cert['block_clause_counts']
    if len(counts) != len(blocks) or any(type(c) is not int or c < 0 for c in counts) or sum(counts) != len(quotient):
        return False
    if len(original) > LIMITS['max_clauses'] or len(quotient) > LIMITS['max_clauses']:
        return False
    offset, work, space = 0, 0, 0
    for (support, clauses), count in zip(sorted(blocks.items()), counts):
        if len(support) > LIMITS['max_block_width']:
            return False
        q = quotient[offset:offset+count]
        offset += count
        indices = {abs(l)-1 for c in q for l in c}
        mask = sum(1 << (v-1) for v in support)
        if any(forms[i] & ~mask for i in indices):
            return False
        space += 2 ** len(support)
        work += (2 ** len(support)) * (sum(map(len, clauses)) + sum(map(len, q)) + sum(forms[i].bit_length() for i in indices))
        if space > LIMITS['max_space_points'] or work > LIMITS['max_verification_work']:
            return False
        for x in points(support):
            # Only quotient coordinates actually used by this block are needed.
            image = sum(parity(x & forms[i]) << i for i in indices)
            if evaluate(clauses, x) != evaluate(q, image):
                return False
    for i, form in enumerate(forms):
        for j, column in enumerate(columns):
            if parity(form & column) != int(i == j):
                return False
    if r * r * n + work > LIMITS['max_verification_work']:
            return False
    return True


def compress_root(formula, **limits):
    limits = dict(LIMITS, **limits)
    if any(type(v) is not int or v < 0 for v in limits.values()):
        raise ValueError('Compression budgets must be nonnegative integers')
    start = time.monotonic()
    ids = sorted({abs(l) for c in formula for l in c})
    n = len(ids)
    def skip(reason):
        return dict(status='skipped', reason=reason, original_variables=n,
                    original_clauses=len(formula), seconds=time.monotonic()-start)
    if n == 0 or n > min(limits['max_variables'], LIMITS['max_variables']):
        return skip('variable_budget_or_trivial')
    if len(formula) > limits['max_clauses']:
        return skip('clause_budget')
    dense = dense_formula(formula, ids)
    blocks = {}
    for clause in dense:
        support = tuple(sorted(map(abs, clause)))
        if len(support) > limits['max_block_width']:
            return skip('block_width_budget')
        z = sum(1 << (abs(l)-1) for l in clause if l < 0)
        blocks.setdefault(support, set()).add(z)
    if sum(2 ** len(s) for s in blocks) > limits['max_space_points']:
        return skip('space_budget')
    frozen = {v for support, z in blocks.items() if len(z) % 2 for v in support}
    if len(frozen) == n:
        return skip('all_variables_in_odd_blocks')
    data = []
    for support, z in sorted(blocks.items()):
        z0 = min(z)
        w = {a ^ z0 for a in z if {b ^ a ^ z0 for b in z} == z}
        wb = basis(w)
        annihilator = {a for a in points(support) if all(parity(a & d) == 0 for d in wb)}
        data.append(dict(support=support, forbidden=z, stabilizer=w, forms=annihilator))
    candidates = set().union(*(d['forms'] for d in data)) - {0}
    candidates = sorted(candidates, key=lambda v: (-sum(v in d['forms'] for d in data), bin(v).count('1'), v))
    chosen = []
    for v in candidates:
        if len(basis(chosen + [v])) > len(chosen):
            chosen.append(v)
    if not 0 < len(chosen) < n:
        return skip('no_dimension_reduction')
    if any(span(v for v in chosen if v in d['forms']) != d['forms'] for d in data):
        return skip('incompatible_greedy_basis')
    rewritten, details, local_work = [], [], 0
    for d in data:
        indices = [i for i, v in enumerate(chosen) if v in d['forms']]
        forbidden = {tuple(parity(z & chosen[i]) for i in indices) for z in d['forbidden']}
        clauses = [tuple(-(i+1) if bit else i+1 for i, bit in zip(indices, t)) for t in sorted(forbidden)]
        rewritten.extend(clauses)
        local_work += (2 ** len(d['support'])) * (len(d['forbidden']) * len(d['support']) +
                      sum(map(len, clauses)) + sum(chosen[i].bit_length() for i in indices))
        details.append(dict(support=list(d['support']), forbidden_points=len(d['forbidden']),
                            stabilizer_size=len(d['stabilizer']), quotient_clauses=len(clauses)))
    if local_work + len(chosen)**2*n > limits['max_verification_work']:
        return skip('verification_work_budget')
    columns = right_inverse(chosen, n)
    if columns is None:
        return skip('no_right_inverse')
    cert = dict(variables=ids, basis_forms=chosen, quotient=[list(c) for c in rewritten], right_inverse=columns,
                block_clause_counts=[d['quotient_clauses'] for d in details])
    if not verify_certificate(formula, cert):
        return skip('certificate_rejected')
    return dict(status='compressed', original_variables=n, original_clauses=len(formula),
                quotient_variables=len(chosen), quotient_clauses=len(rewritten), certificate=cert,
                blocks=details, verification_local_assignments=sum(2 ** len(d['support']) for d in data),
                verification_matrix_entries=len(chosen)**2, verification_work_estimate=local_work+len(chosen)**2*n,
                verification_method='local_block_tables_and_GF2_right_inverse',
                seconds=time.monotonic()-start, certificate_verified=True,
                general_polynomial_sat_proof=False)
