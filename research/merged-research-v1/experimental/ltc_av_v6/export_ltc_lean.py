"""Generate kernel-checkable Lean 4 proofs for Link-Twin Contraction (LTC)
and composed GF(2) compression + LTC chains.
"""
import hashlib
from pathlib import Path

from export_compression_lean import boolean_formula, lean_cnf, render as render_compression
from ltc import _normalize as normalize, verify_ltc_certificate

HERE = Path(__file__).resolve().parent


def _ltc_body():
    text = (HERE / 'LTCSoundness.lean').read_text()
    marker = '-- END_SHARED_PREAMBLE\n'
    idx = text.find(marker)
    if idx < 0:
        raise ValueError('Missing shared preamble marker in LTCSoundness.lean')
    return text[idx + len(marker):]


def _lean_lit(l):
    return '(' + ('true' if l > 0 else 'false') + ', ' + str(abs(l) - 1) + ')'


def _emit_ltc_chain(prefix, initial_cnf_name, start_cnf, ltc_cert):
    """Emit Lean definitions and checkLTCStep_sound theorems for an LTC chain."""
    steps = ltc_cert['steps']
    lines = ['', 'namespace LTCInstances', 'open CompressionSoundness LTCSoundness',
             'set_option maxRecDepth 200000', 'set_option maxHeartbeats 20000000', '']
    lines.append('def ' + prefix + '_f0 : CNF := ' + lean_cnf(start_cnf))
    if initial_cnf_name != prefix + '_f0':
        lines.append('theorem ' + prefix + '_bridge : cnfEquiv ' + initial_cnf_name + ' ' + prefix + '_f0 = true := by')
        lines.append('  decide')
        lines.append('theorem ' + prefix + '_init_equisat : (∃ a, evalCNF ' + initial_cnf_name + ' a = true) ↔ (∃ b, evalCNF ' + prefix + '_f0 b = true) := by')
        lines.append('  constructor')
        lines.append('  · rintro ⟨a, ha⟩; exact ⟨a, (evalCNF_of_cnfEquiv ' + prefix + '_bridge).mp ha⟩')
        lines.append('  · rintro ⟨b, hb⟩; exact ⟨b, (evalCNF_of_cnfEquiv ' + prefix + '_bridge).mpr hb⟩')
        lines.append('')
    cur_name = prefix + '_f0'
    step_theorems = []
    for idx, step in enumerate(steps):
        next_name = prefix + '_f' + str(idx + 1)
        co_name = prefix + '_co' + str(idx)
        neg_name = prefix + '_neg' + str(idx)
        rest_name = prefix + '_rest' + str(idx)
        thm_name = prefix + '_step' + str(idx)
        lines.append('def ' + co_name + ' : CNF := ' + lean_cnf(step['co_remainders']))
        lines.append('def ' + neg_name + ' : CNF := ' + lean_cnf(step['neg_remainders']))
        lines.append('def ' + rest_name + ' : CNF := ' + lean_cnf(step['rest_clauses']))
        lines.append('def ' + next_name + ' : CNF := ' + lean_cnf(step['output']))
        lines.append('theorem ' + thm_name + ' : (∃ a, evalCNF ' + cur_name + ' a = true) ↔ (∃ b, evalCNF ' + next_name + ' b = true) := by')
        lines.append('  apply checkLTCStep_sound ' + _lean_lit(step['l1']) + ' ' + _lean_lit(step['l2']) + ' ' + co_name + ' ' + neg_name + ' ' + rest_name)
        lines.append('  decide')
        lines.append('')
        step_theorems.append(thm_name)
        cur_name = next_name

    # Compose chain equisatisfiability
    lines.append('theorem ' + prefix + '_chain_equisat : (∃ a, evalCNF ' + prefix + '_f0 a = true) ↔ (∃ b, evalCNF ' + cur_name + ' b = true) := by')
    if len(step_theorems) == 1:
        lines.append('  exact ' + step_theorems[0])
    else:
        expr = step_theorems[0]
        for th in step_theorems[1:]:
            expr = expr + '.trans ' + th
        lines.append('  exact ' + expr)
    lines.append('')

    final_q = [list(c) for c in ltc_cert['quotient']]
    q_vars = sorted({abs(l) for c in final_q for l in c})
    if len(q_vars) <= 8:
        v_map = {v - 1: 'y' + str(i) for i, v in enumerate(q_vars)}
        expr = boolean_formula(final_q, lambda idx: v_map[idx])
        args = ' '.join('y' + str(i) for i in range(len(q_vars)))
        applied = ' '.join('(a ' + str(v - 1) + ')' for v in q_vars)
        if args:
            lines.append('theorem ' + prefix + '_qfalse_table (' + args + ' : Bool) : ' + expr + ' = false := by')
            lines.append('  decide +revert')
            lines.append('theorem ' + prefix + '_qfalse (a : Assignment) : evalCNF ' + cur_name + ' a = false := by')
            lines.append('  exact ' + prefix + '_qfalse_table ' + applied)
        else:
            lines.append('theorem ' + prefix + '_qfalse (a : Assignment) : evalCNF ' + cur_name + ' a = false := by')
            lines.append('  decide')
        lines.append('theorem ' + prefix + '_final_unsat : ¬ ∃ b, evalCNF ' + cur_name + ' b = true := by')
        lines.append('  rintro ⟨b, hb⟩')
        lines.append('  have hf := ' + prefix + '_qfalse b')
        lines.append('  rw [hf] at hb')
        lines.append('  contradiction')
        lines.append('')
    lines.append('end LTCInstances')
    return '\n'.join(lines), cur_name, len(q_vars) <= 8


def render_ltc(formula, compression, ltc_result):
    """Render a standalone Lean 4 file verifying LTC (optionally composed with GF(2) root compression)."""
    f = normalize(formula)
    if ltc_result.get('status') != 'compressed':
        raise ValueError('LTC did not compress the input')
    cert = ltc_result['certificate']
    has_outer = isinstance(compression, dict) and compression.get('status') == 'compressed'
    if has_outer:
        start_cnf = normalize(compression['certificate']['quotient'])
        if not verify_ltc_certificate(start_cnf, cert):
            raise ValueError('LTC certificate rejected on outer quotient')
        source = render_compression([('outer', f, compression)])
        source += _ltc_body()
        chain_src, final_name, small_unsat = _emit_ltc_chain('ltc', 'CompressionInstances.outer_quotient', start_cnf, cert)
        source += chain_src
        source += '\nnamespace ComposedLTC\nopen CompressionSoundness CompressionInstances LTCSoundness LTCInstances\n'
        source += ('theorem original_ltc_equisatisfiable : (∃ a, evalCNF outer_original a = true) ↔ (∃ b, evalCNF ' + final_name + ' b = true) :=\n'
                   '  outer_equisatisfiable.trans (ltc_init_equisat.trans ltc_chain_equisat)\n'
                   '#print axioms original_ltc_equisatisfiable\n')
        if small_unsat:
            source += ('theorem original_unsat : ¬ ∃ a, evalCNF outer_original a = true := by\n'
                       '  intro h\n'
                       '  exact ltc_final_unsat (original_ltc_equisatisfiable.mp h)\n'
                       '#print axioms original_unsat\n')
        source += 'end ComposedLTC\n'
    else:
        if not verify_ltc_certificate(f, cert):
            raise ValueError('LTC certificate rejected on input')
        source = (HERE / 'CompressionSoundness.lean').read_text() + _ltc_body()
        chain_src, final_name, small_unsat = _emit_ltc_chain('ltc', 'ltc_f0', f, cert)
        source += chain_src
        source += '\nnamespace StandaloneLTC\nopen CompressionSoundness LTCSoundness LTCInstances\n'
        source += ('theorem original_ltc_equisatisfiable : (∃ a, evalCNF ltc_f0 a = true) ↔ (∃ b, evalCNF ' + final_name + ' b = true) :=\n'
                   '  ltc_chain_equisat\n'
                   '#print axioms original_ltc_equisatisfiable\n')
        if small_unsat:
            source += ('theorem original_unsat : ¬ ∃ a, evalCNF ltc_f0 a = true := by\n'
                       '  intro h\n'
                       '  exact ltc_final_unsat (original_ltc_equisatisfiable.mp h)\n'
                       '#print axioms original_unsat\n')
        source += 'end StandaloneLTC\n'
    if len(source.encode()) > 512 * 1024:
        raise ValueError('Generated LTC proof exceeds finite source budget')
    return source
