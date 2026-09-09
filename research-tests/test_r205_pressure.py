import unittest
from r205_pressure import parse_vm_stat,steady_growth
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
if __name__=='__main__':unittest.main()
