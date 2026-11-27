import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'runtime'))
"""Exercise timeout/unknown semantics independently of mathematical claims."""
import sys
import time
import unittest
from unittest.mock import patch
import solver
sys.modules['ialh_target'] = solver
import check_proposal as check


class Limits(unittest.TestCase):
    def test_unknown_oracle_never_confirms_growth(self):
        data={'verdict':'growth_fixture','formula':[[1],[-1]],'order':[1]}
        with patch.object(check,'finite_oracle',return_value={'sat':None,'status':'inconclusive'}), \
             patch.object(check,'bounded',return_value={'status':'completed','result':{'sat':False,'peak':20}}):
            self.assertEqual(check.check(data)['status'],'inconclusive')

    def test_candidate_timeout_retains_independent_oracle(self):
        data={'verdict':'growth_fixture','formula':[[1],[-1]],'order':[1]}
        with patch.object(check,'bounded',return_value={'status':'inconclusive'}):
            result=check.check(data)
        self.assertEqual(result['status'],'inconclusive')
        self.assertIs(result['oracle_sat'],False)

    def test_wrong_answer_is_rejected(self):
        data={'verdict':'correctness_fixture','formula':[[1],[-1]],'order':[1]}
        with patch.object(check,'bounded',return_value={'status':'completed','result':{'sat':True,'peak':0}}):
            self.assertEqual(check.check(data)['status'],'confirmed_correctness_failure')

    def test_kills_only_bounded_test_process(self):
        self.assertEqual(check.bounded(time.sleep,(1,),0.02)['status'],'inconclusive')
        self.assertEqual(check.bounded(sum,([1,2],),1),{'status':'completed','result':3})

    def test_accepts_32_rejects_33(self):
        f=[[v] for v in range(1,33)]
        d={'fixture':{'formula':f,'order':list(range(1,33)),'predicted_sat':True,'predicted_peak':0}}
        self.assertEqual(check.check(d)['status'],'fixture_predictions_match')
        d['fixture']['formula'].append([33]);d['fixture']['order'].append(33)
        with self.assertRaises(AssertionError):check.check(d)


if __name__=='__main__':
    unittest.main()
