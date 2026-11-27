"""Independent finite checks of the proposed signed-SCC repair and Neon family.

Model prose is data; no model-provided program is executed. This harness does
not prove a universal complexity bound or an asymptotic lower bound.
"""
from pathlib import Path
import datetime
import itertools as it
import json
import random
import sys
import time

HERE = Path(__file__).resolve().parent
from test_elim import elim, variables
from test_mra import canon, restrict, prune, two_sat, models


def signed_scc(formula):
    vs = variables(formula)
    adj = {literal: set() for v in vs for literal in (v, -v)}
    rev = {literal: set() for literal in adj}
    for clause in formula:
        if len(clause) == 2:
            a, b = clause
            for u, v in [(-a, b), (-b, a)]:
                adj[u].add(v)
                rev[v].add(u)
    order, seen = [], set()
    def visit(v):
        if v in seen:
            return
        seen.add(v)
        for w in sorted(adj[v]):
            visit(w)
        order.append(v)
    for v in sorted(adj):
        visit(v)
    component = {}
    def collect(v, group):
        if v in component:
            return
        component[v] = group
        group.add(v)
        for w in rev[v]:
            collect(w, group)
    for v in reversed(order):
        if v not in component:
            collect(v, set())
    if any(-v in component[v] for v in vs):
        return None
    mapping = {}
    for v in adj:
        group = component[v]
        representative = min(map(abs, group))
        mapping[v] = representative if representative in group else -representative
    assert all(mapping[-v] == -mapping[v] for v in vs)
    return mapping


def canon_plus(formula):
    formula = canon(formula)
    history = []
    while formula is not None:
        mapping = signed_scc(formula)
        if mapping is None:
            return None, history
        if all(v == mapped for v, mapped in mapping.items()):
            return formula, history
        history.append(mapping)
        smaller = canon([[mapping[literal] for literal in clause] for clause in formula])
        assert smaller is None or len(variables(smaller)) < len(variables(formula))
        formula = smaller
    return None, history


def elim_plus(formula):
    formula, maps = canon_plus(formula)
    accepted = 0
    while formula is not None:
        result = elim(formula)
        accepted += len(result['steps'])
        if result['status'] != 'STUCK':
            return result['status'], result['formula'], len(maps), accepted
        smaller, newmaps = canon_plus(result['formula'])
        maps += newmaps
        if smaller == result['formula']:
            return 'STUCK', smaller, len(maps), accepted
        formula = smaller
    return 'UNSAT', None, len(maps), accepted


def run_plus(formula, order, partial=False):
    status, root, merges, accepted = elim_plus(formula)
    if status != 'STUCK':
        return {'sat': status == 'SAT', 'peak': 0, 'layers': [], 'scc_rounds': merges, 'accepted_dp': accepted}
    if all(len(clause) <= 2 for clause in root):
        return {'sat': two_sat(root), 'peak': 0, 'layers': [], 'scc_rounds': merges, 'accepted_dp': accepted}
    states, layers, peak = {root}, [], 1
    for variable in order:
        children = set()
        for state in sorted(states):
            for value in (False, True):
                status, residual, nmerge, ndp = elim_plus(restrict(state, variable, value))
                merges += nmerge
                accepted += ndp
                if status == 'UNSAT':
                    continue
                if status == 'SAT' or all(len(clause) <= 2 for clause in residual) and two_sat(residual):
                    return {'sat': True, 'peak': peak, 'layers': layers, 'scc_rounds': merges, 'accepted_dp': accepted}
                if all(len(clause) <= 2 for clause in residual):
                    continue
                children.add(residual)
        states = prune(children)
        peak = max(peak, len(states))
        layers.append({'variable': variable, 'retained': len(states)})
        if not states:
            return {'sat': False, 'peak': peak, 'layers': layers, 'scc_rounds': merges, 'accepted_dp': accepted}
    return {'sat': None if partial else any(not state for state in states), 'peak': peak,
            'layers': layers, 'scc_rounds': merges, 'accepted_dp': accepted,
            'partial_order': partial, 'remaining_states': len(states)}


def satisfies(formula, assignment):
    return formula is not None and all(any(assignment[abs(l)] == (l > 0) for l in c) for c in formula)


def check_projection(formula, vs):
    reduced, history = canon_plus(formula)
    for bits in it.product((False, True), repeat=len(vs)):
        assignment = dict(zip(vs, bits))
        consistent = all(assignment[abs(v)] == (assignment[abs(rep)] if rep > 0 else not assignment[abs(rep)])
                         for mapping in history for v, rep in mapping.items() if v > 0)
        assert satisfies(formula, assignment) == (satisfies(reduced, assignment) and consistent), (formula, reduced, history)


def xor_clauses(vs, parity):
    return [tuple(-v if bit else v for v, bit in zip(vs, bits))
            for bits in it.product((False, True), repeat=len(vs)) if sum(bits) % 2 != parity]


def neon_family(k):
    vertices = 2 * k + 1
    edges = sorted({tuple(sorted((u, (u + shift) % vertices))) for u in range(vertices) for shift in (1, 2)})
    ids = {edge: k + 1 + i for i, edge in enumerate(edges)}
    equations = []
    for vertex in range(vertices):
        incident = [ids[edge] for edge in edges if vertex in edge]
        assert len(incident) == 4
        if vertex:
            incident += [vertex if vertex <= k else vertex - k]
        equations.append((sorted(incident), int(vertex == 0)))
    formula = []
    for vs, rhs in equations:
        clauses = xor_clauses(vs, rhs)
        # Independently check each emitted CNF against its XOR truth table.
        for bits in it.product((False, True), repeat=len(vs)):
            assert satisfies(clauses, dict(zip(vs, bits))) == (sum(bits) % 2 == rhs)
        formula.extend(clauses)
    odd_variables = set()
    rhs = 0
    for vs, bit in equations:
        odd_variables.symmetric_difference_update(vs)
        rhs ^= bit
    assert not odd_variables and rhs == 1  # Explicit finite XOR inconsistency certificate.
    return formula


def main():
    start = time.time()
    randomizer = random.Random(261126)
    edge_cases = [[], [[]], [(1,), (-1,)], [(-1, 2), (1, -2)],
                  [(-1, -2), (1, 2)], [(-1, 2), (-2, 3), (-3, 1)],
                  [(1, 2), (1, -2), (-1, 2), (-1, -2)]]
    for formula in edge_cases:
        check_projection(formula, [1, 2, 3])
    for _ in range(300):
        vs = list(range(1, 6))
        formula = [tuple(randomizer.choice((-1, 1)) * v for v in randomizer.sample(vs, randomizer.randint(1, 4)))
                   for _ in range(randomizer.randint(1, 18))]
        check_projection(formula, vs)
        result = run_plus(formula, vs)
        assert result['sat'] == bool(models(formula, vs)), (formula, result)
    fixtures = []
    for name in ['neon_antigravity_round2', 'neon_antigravity_round3', 'fable_worstcase_round5']:
        data = json.loads((HERE.parent / name / 'structured-output.json').read_text())
        candidate = data['fixture'] if 'fixture' in data else data
        result = run_plus(candidate['formula'], candidate['order'])
        truth = bool(models(candidate['formula'], variables(candidate['formula'])))
        assert result['sat'] == truth
        fixtures.append({'source': name, 'variables': len(variables(candidate['formula'])),
                         'clauses': len(candidate['formula']), 'oracle_sat': truth, 'observed': result})
    family = []
    for k in (2, 3, 4):
        formula = neon_family(k)
        result = run_plus(formula, list(range(1, k + 1)), partial=True)
        row = {'k': k, 'variables': len(variables(formula)), 'clauses': len(formula),
               'xor_unsat_certificate_checked': True, 'observed': result,
               'prediction_matches': [x['retained'] for x in result['layers']] == [2 ** t for t in range(1, k + 1)]}
        if k == 2:
            row['exhaustive_oracle_sat'] = bool(models(formula, variables(formula)))
            assert row['exhaustive_oracle_sat'] is False
        family.append(row)
        print(json.dumps(row), flush=True)
    nonaffine = [(1, 2, 3), (-1, -2, -3), (3, 4, 5), (-3, -4, -5)]
    assignments = models(nonaffine, [1, 2, 3, 4, 5])
    good_renamings = 0
    for bits in it.product((False, True), repeat=5):
        renamed = [tuple(-l if bits[abs(l)-1] else l for l in c) for c in nonaffine]
        good_renamings += all(sum(l > 0 for l in c) <= 1 for c in renamed)
    for bits in it.product((False, True), repeat=5):
        a, b, x, d, e = bits
        represented = (not x and (a or b) and (d or e)) or (x and (not a or not b) and (not d or not e))
        assert represented == (bits in assignments)
    out = {'at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'scc_projection_cases': len(edge_cases) + 300, 'full_solver_random_cases': 300,
           'projection_or_solver_failures': 0, 'old_fixtures': fixtures, 'neon_family': family,
           'fable_union_example': {'model_count': len(assignments), 'renamable_horn_renamings': good_renamings,
                                   'all_32_assignments_match_representation': True},
           'seconds': time.time() - start, 'general_polynomial_sat_proof': False,
           'scope': 'Finite checks of one explicit implementation. Canon+ runs before full ELIM and again after its STUCK return. Growth measured through specified prefix only. XOR cancellation certificates checked, not Lean formalized. No universal or asymptotic claim.'}
    (HERE / 'test-receipt.json').write_text(json.dumps(out, indent=2))
    print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()
