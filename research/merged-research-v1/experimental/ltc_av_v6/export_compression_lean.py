"""Generate kernel-checkable concrete compression certificates from trusted data.

The generated file proves local block identities, constructive model lifting,
and satisfiability equivalence. It does not prove discovery or total runtime.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def folded(values, op, empty):
    result = empty
    for value in reversed(values):
        result = '(' + value + ' ' + op + ' ' + result + ')'
    return result


def xor_expr(mask, lookup):
    return folded([lookup(i) for i in range(mask.bit_length()) if mask & (1 << i)], '^^', 'false')


def inverse_proof(form, columns, expression, index):
    # Reorder with the kernel-checked AC tactic once, then cancel adjacent pairs.
    # Repeated permutative simp rewrites can be very expensive on dense inverses.
    terms = sorted(j for k in range(form.bit_length()) if form & (1 << k)
                   for j, c in enumerate(columns) if c & (1 << k))
    canonical = folded(['y'+str(j) for j in terms], '^^', 'false')
    return ('by\n  calc\n    '+expression+' = '+canonical+' := by\n'
            '      simp only [Bool.xor_false, Bool.false_xor] <;> ac_rfl\n'
            '    _ = y'+str(index)+' := by\n'
            '      simp only [xor_cancel, Bool.xor_self, Bool.xor_false, Bool.false_xor]')


def boolean_formula(formula, lookup):
    return folded([folded([lookup(abs(l)-1) if l > 0 else '(!' + lookup(abs(l)-1) + ')' for l in c], '||', 'false')
                   for c in formula], '&&', 'true')


def lean_cnf(formula):
    return '[' + ', '.join('[' + ', '.join('(' + ('true' if l > 0 else 'false') + ', ' + str(abs(l)-1) + ')' for l in c) + ']' for c in formula) + ']'


def function(name, expressions):
    return '\n'.join(['def ' + name + ' (a : Assignment) : Assignment := fun i => match i with'] +
                     ['  | ' + str(i) + ' => ' + value for i, value in enumerate(expressions)] + ['  | _ => false', ''])


def instance(name, formula, compression):
    cert = compression['certificate']
    ids, forms, columns = cert['variables'], cert['basis_forms'], cert['right_inverse']
    mapping = {v:i+1 for i,v in enumerate(ids)}
    dense = [[mapping[abs(l)] if l > 0 else -mapping[abs(l)] for l in c] for c in formula]
    groups = {}
    for c in dense:
        support = tuple(sorted(map(abs,c)))
        groups.setdefault(support,[]).append(c)
    project, lift = name+'_project', name+'_lift'
    project_expressions = [xor_expr(v, lambda i:'(a '+str(i)+')') for v in forms]
    lift_expressions = [folded(['(a '+str(i)+')' for i,v in enumerate(columns) if v & (1 << j)], '^^','false') for j in range(len(ids))]
    lines = [function(project,project_expressions),function(lift,lift_expressions)]
    original_names, quotient_names, correct_names = [],[],[]
    offset=0
    for index, ((support,clauses), detail) in enumerate(zip(sorted(groups.items()),compression['blocks'])):
        assert list(support)==detail['support']
        count=detail['quotient_clauses'];q=cert['quotient'][offset:offset+count];offset+=count
        label=name+'_b'+str(index);qlabel=name+'_q'+str(index)
        original_names.append(label);quotient_names.append(qlabel);correct_names.append(label+'_correct')
        local={v-1:'b'+str(i) for i,v in enumerate(support)}
        original=boolean_formula(clauses,lambda i:local[i])
        reduced=boolean_formula(q,lambda i:xor_expr(forms[i],lambda j:local[j]))
        args=' '.join(local.values());applied=' '.join('(a '+str(v-1)+')' for v in support)
        lines += ['def '+label+' : CNF := '+lean_cnf(clauses),
                  'def '+qlabel+' : CNF := '+lean_cnf(q),
                  'theorem '+label+'_table ('+args+' : Bool) : '+original+' = '+reduced+' := by\n  decide +revert',
                  'theorem '+label+'_correct (a : Assignment) : evalCNF '+label+' a = evalCNF '+qlabel+' ('+project+' a) := by\n  exact '+label+'_table '+applied,'']
    assert offset==len(cert['quotient'])
    original=name+'_original';quotient=name+'_quotient'
    lines += ['def '+original+' : CNF := '+' ++ '.join(original_names+['[]']),
              'def '+quotient+' : CNF := '+' ++ '.join(quotient_names+['[]']),
              'theorem '+name+'_forward (a : Assignment) : evalCNF '+original+' a = evalCNF '+quotient+' ('+project+' a) := by',
              '  simp only ['+original+', '+quotient+', evalCNF_append]',
              '  rw ['+', '.join(correct_names)+']','  rfl','']
    inverse_names=[]
    for i,form in enumerate(forms):
        args=' '.join('y'+str(j) for j in range(len(forms)))
        lifted=[folded(['y'+str(j) for j,c in enumerate(columns) if c&(1<<k)],'^^','false') for k in range(len(ids))]
        expr=xor_expr(form,lambda k:lifted[k]);label=name+'_inverse'+str(i);inverse_names.append(label)
        lines += ['theorem '+label+'_table ('+args+' : Bool) : '+expr+' = y'+str(i)+' := '+inverse_proof(form,columns,expr,i),
                  'theorem '+label+' (a : Assignment) : '+project+' ('+lift+' a) '+str(i)+' = a '+str(i)+' := by\n  exact '+label+'_table '+' '.join('(a '+str(j)+')' for j in range(len(forms))),'']
    lines += ['theorem '+name+'_backward (a : Assignment) : evalCNF '+original+' ('+lift+' a) = evalCNF '+quotient+' a := by',
              '  rw ['+name+'_forward]',
              '  simp only ['+', '.join([quotient]+quotient_names+['evalCNF_append','evalCNF','evalClause','evalLit']+inverse_names)+']',
              'theorem '+name+'_equisatisfiable : (∃ a, evalCNF '+original+' a = true) ↔ (∃ b, evalCNF '+quotient+' b = true) :=',
              '  equisat_of_two_maps (evalCNF '+original+') (evalCNF '+quotient+') '+project+' '+lift+' '+name+'_forward '+name+'_backward',
              '#print axioms '+name+'_forward','#print axioms '+name+'_backward','#print axioms '+name+'_equisatisfiable','']
    return '\n'.join(lines)


def render(cases):
    header=(HERE/'CompressionSoundness.lean').read_text()
    return header+'\nnamespace CompressionInstances\nlocal instance : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩\nlocal instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩\nopen CompressionSoundness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\nset_option linter.unusedVariables false\nset_option linter.unusedSimpArgs false\n\ntheorem xor_cancel (a b : Bool) : (a ^^ (a ^^ b)) = b := by\n  cases a <;> cases b <;> rfl\n\n'+ '\n'.join(instance(name,formula,compression) for name,formula,compression in cases)+'\nend CompressionInstances\n'


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    data=json.loads((HERE/'compression-test-receipt.json').read_text())
    cases=[];manifest=[]
    for name,source in [('case36','neon_worstcase_auto_00006'),('case96','neon_worstcase_auto_00007'),('positive','positive-control')]:
        case=next(r for r in data['fixtures'] if r['source']==source)
        # Production normalization is part of the checked input conversion.
        from solver import normalize
        formula=normalize(case['formula']);compression=case['updated']['compression']
        assert compression['status']=='compressed'
        cases.append((name,formula,compression))
        manifest.append({'name':name,'source':source,'normalized_formula':formula,'certificate':compression['certificate'],
                         'normalized_formula_sha256':hashlib.sha256(json.dumps(formula).encode()).hexdigest()})
    args.output.write_text(render(cases))
    args.output.with_suffix('.manifest.json').write_text(json.dumps(manifest,indent=2))
    print(json.dumps({'file':str(args.output),'cases':len(cases),'sha256':hashlib.sha256(args.output.read_bytes()).hexdigest()}))
