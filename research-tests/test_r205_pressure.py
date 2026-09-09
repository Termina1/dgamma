import unittest
from r205_pressure import parse_vm_stat,steady_growth,free_percent,corrected_pressure_stop
class Pressure(unittest.TestCase):
    def test_parse(self):
        s='Mach Virtual Memory Statistics: (page size of 16384 bytes)\nPages occupied by compressor: 10.\nPages stored in compressor: 20.\nSwapouts: 300.\n'
        self.assertEqual(parse_vm_stat(s),dict(pageSizeBytes=16384,compressorPages=10,storedCompressorPages=20,swapouts=300))
    def rows(self,swaps,compressors):return [dict(swapouts=s,compressorPages=c) for s,c in zip(swaps,compressors)]
    def test_baseline_not_pressure(self):self.assertFalse(steady_growth(self.rows([18854177]*4,[51051]*4)))
    def test_swap_growth(self):self.assertTrue(steady_growth(self.rows([1,2,3,4],[0]*4)))
    def test_compressor_growth(self):self.assertTrue(steady_growth(self.rows([0]*4,[1,2,3,4])))
    def test_not_enough_samples(self):self.assertFalse(steady_growth(self.rows([1,2,3],[1,2,3])))
    def test_one_burst_not_steady(self):self.assertFalse(steady_growth(self.rows([0,0,10,10],[0,0,1,1])))
    def test_decrease_resets(self):self.assertFalse(steady_growth(self.rows([0]*4,[10,20,5,6])))
    def test_last_window_only(self):self.assertFalse(steady_growth(self.rows([0]*6,[1,2,3,4,4,4])))
class CorrectedPressure(unittest.TestCase):
    def rows(self,free,swaps,compressors=None):return [dict(freePercent=f,swapouts=s,compressorPages=c) for f,s,c in zip(free,swaps,compressors or [0]*len(free))]
    def test_free_parse(self):self.assertEqual(free_percent('System-wide memory free percentage: 97%'),97)
    def test_compressor_not_stop(self):self.assertFalse(corrected_pressure_stop(self.rows([97]*4,[0]*4,[40069,46529,49243,50942])))
    def test_one_low_not_stop(self):self.assertFalse(corrected_pressure_stop(self.rows([97,14],[0,0])))
    def test_two_low_stop(self):self.assertTrue(corrected_pressure_stop(self.rows([14,14],[0,0])))
    def test_fifteen_not_low(self):self.assertFalse(corrected_pressure_stop(self.rows([15,15],[0,0])))
    def test_three_swap_rises_stop(self):self.assertTrue(corrected_pressure_stop(self.rows([97]*4,[1,2,3,4])))
    def test_two_swap_rises_not_stop(self):self.assertFalse(corrected_pressure_stop(self.rows([97]*3,[1,2,3])))
    def test_swap_plateau_resets(self):self.assertFalse(corrected_pressure_stop(self.rows([97]*4,[1,2,2,3])))
if __name__=='__main__':unittest.main()
