"""Single entry point for the merged solver and its existing evidence."""
from pathlib import Path
import argparse,json,sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'runtime'))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    actions=parser.add_subparsers(dest='action',required=True)
    solve=actions.add_parser('solve',help='Decide an explicit JSON CNF with the merged experimental solver')
    solve.add_argument('input',type=Path,help='JSON list of clauses, or {formula,order}')
    solve.add_argument('--quotient-order',help='Explicit comma-separated order for compressed variables')
    solve.add_argument('--no-counting-cache',action='store_true')
    solve.add_argument('--output',type=Path)
    actions.add_parser('status',help='Show merge and validation status')
    actions.add_parser('evidence',help='List archived research folders and receipt hashes')
    args=parser.parse_args()
    if args.action=='status':result=json.loads((HERE/'merge-manifest.json').read_text())
    elif args.action=='evidence':result=json.loads((HERE/'evidence/index.json').read_text())
    else:
        from solver import run_counting,variables
        data=json.loads(args.input.read_text());formula=data['formula'] if isinstance(data,dict) else data
        order=data.get('order',variables(formula)) if isinstance(data,dict) else variables(formula)
        quotient_order=list(map(int,args.quotient_order.split(','))) if args.quotient_order else None
        result=run_counting(formula,order,quotient_order=quotient_order,cache_counting=not args.no_counting_cache)
        result['implementation_lean_verified']=False
        if args.output:args.output.write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
