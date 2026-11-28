import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0952
import ProximityPrize.SubmissionLower.Z6969Pack0960
import ProximityPrize.SubmissionLower.Z6969Pack0953
import ProximityPrize.SubmissionLower.Z6969Pack0950
import ProximityPrize.SubmissionLower.Z6969Pack0961
import ProximityPrize.SubmissionLower.Z6969Pack0955
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0682

set_option Elab.async false

-- Source: Research6969.PairReceipts289
section Z6969Source2886
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5780:PairCell.Row:=⟨59,59,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5780:ThreeRule.check cell5780 (2:Fin 18)=true:=by decide +kernel
def cell5781:PairCell.Row:=⟨59,59,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5781:ThreeRule.check cell5781 (2:Fin 18)=true:=by decide +kernel
def cell5782:PairCell.Row:=⟨59,59,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5782:ThreeRule.check cell5782 (2:Fin 18)=true:=by decide +kernel
def cell5783:PairCell.Row:=⟨59,59,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5783:ThreeRule.check cell5783 (2:Fin 18)=true:=by decide +kernel
private def rows5784 : List StockPairs.Receipt := [
  ⟨⟨60,60,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨60,60,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5784 : StockPairs.checked rows5784 = true := by decide +kernel
theorem route5784 (i : Fin 12) : (rows5784.get i).Done :=
  StockPairs.doneAt paid5784 i

def cell5796:PairCell.Row:=⟨60,60,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5796:ThreeRule.check cell5796 (2:Fin 18)=true:=by decide +kernel
def cell5797:PairCell.Row:=⟨60,60,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5797:ThreeRule.check cell5797 (2:Fin 18)=true:=by decide +kernel
def cell5798:PairCell.Row:=⟨60,60,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5798:ThreeRule.check cell5798 (2:Fin 18)=true:=by decide +kernel
def cell5799:PairCell.Row:=⟨60,60,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5799:ThreeRule.check cell5799 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2886

-- Source: Research6969.PairReceipts290
section Z6969Source2887
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5800:PairCell.Row:=⟨60,60,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5800:ThreeRule.check cell5800 (2:Fin 18)=true:=by decide +kernel
def cell5801:PairCell.Row:=⟨60,60,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5801:ThreeRule.check cell5801 (2:Fin 18)=true:=by decide +kernel
def cell5802:PairCell.Row:=⟨60,60,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5802:ThreeRule.check cell5802 (2:Fin 18)=true:=by decide +kernel
def cell5803:PairCell.Row:=⟨60,60,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5803:ThreeRule.check cell5803 (2:Fin 18)=true:=by decide +kernel
def cell5804:PairCell.Row:=⟨60,60,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5804:ThreeRule.check cell5804 (2:Fin 18)=true:=by decide +kernel
def cell5805:PairCell.Row:=⟨60,60,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5805:ThreeRule.check cell5805 (2:Fin 18)=true:=by decide +kernel
def cell5806:PairCell.Row:=⟨60,60,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5806:ThreeRule.check cell5806 (2:Fin 18)=true:=by decide +kernel
def cell5807:PairCell.Row:=⟨60,60,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5807:ThreeRule.check cell5807 (2:Fin 18)=true:=by decide +kernel
def cell5808:PairCell.Row:=⟨60,60,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5808:ThreeRule.check cell5808 (2:Fin 18)=true:=by decide +kernel
def cell5809:PairCell.Row:=⟨60,60,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5809:ThreeRule.check cell5809 (2:Fin 18)=true:=by decide +kernel
def cell5810:PairCell.Row:=⟨60,60,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5810:ThreeRule.check cell5810 (2:Fin 18)=true:=by decide +kernel
def cell5811:PairCell.Row:=⟨60,60,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5811:ThreeRule.check cell5811 (2:Fin 18)=true:=by decide +kernel
def cell5812:PairCell.Row:=⟨60,60,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5812:ThreeRule.check cell5812 (2:Fin 18)=true:=by decide +kernel
def cell5813:PairCell.Row:=⟨60,60,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5813:ThreeRule.check cell5813 (2:Fin 18)=true:=by decide +kernel
def cell5814:PairCell.Row:=⟨60,60,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5814:ThreeRule.check cell5814 (2:Fin 18)=true:=by decide +kernel
def cell5815:PairCell.Row:=⟨60,60,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5815:ThreeRule.check cell5815 (2:Fin 18)=true:=by decide +kernel
def cell5816:PairCell.Row:=⟨60,60,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5816:ThreeRule.check cell5816 (2:Fin 18)=true:=by decide +kernel
def cell5817:PairCell.Row:=⟨60,60,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5817:ThreeRule.check cell5817 (2:Fin 18)=true:=by decide +kernel
def cell5818:PairCell.Row:=⟨60,60,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5818:ThreeRule.check cell5818 (2:Fin 18)=true:=by decide +kernel
def cell5819:PairCell.Row:=⟨60,60,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5819:ThreeRule.check cell5819 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2887

-- Source: Research6969.PairReceipts291
section Z6969Source2888
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5820:PairCell.Row:=⟨60,60,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5820:ThreeRule.check cell5820 (2:Fin 18)=true:=by decide +kernel
def cell5821:PairCell.Row:=⟨60,60,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5821:ThreeRule.check cell5821 (2:Fin 18)=true:=by decide +kernel
private def rows5822 : List StockPairs.Receipt := [
  ⟨⟨61,61,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨61,61,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5822 : StockPairs.checked rows5822 = true := by decide +kernel
theorem route5822 (i : Fin 12) : (rows5822.get i).Done :=
  StockPairs.doneAt paid5822 i

def cell5834:PairCell.Row:=⟨61,61,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5834:ThreeRule.check cell5834 (2:Fin 18)=true:=by decide +kernel
def cell5835:PairCell.Row:=⟨61,61,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5835:ThreeRule.check cell5835 (2:Fin 18)=true:=by decide +kernel
def cell5836:PairCell.Row:=⟨61,61,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5836:ThreeRule.check cell5836 (2:Fin 18)=true:=by decide +kernel
def cell5837:PairCell.Row:=⟨61,61,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5837:ThreeRule.check cell5837 (2:Fin 18)=true:=by decide +kernel
def cell5838:PairCell.Row:=⟨61,61,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5838:ThreeRule.check cell5838 (2:Fin 18)=true:=by decide +kernel
def cell5839:PairCell.Row:=⟨61,61,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5839:ThreeRule.check cell5839 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2888

-- Source: Research6969.PairReceipts292
section Z6969Source2889
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5840:PairCell.Row:=⟨61,61,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5840:ThreeRule.check cell5840 (2:Fin 18)=true:=by decide +kernel
def cell5841:PairCell.Row:=⟨61,61,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5841:ThreeRule.check cell5841 (2:Fin 18)=true:=by decide +kernel
def cell5842:PairCell.Row:=⟨61,61,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5842:ThreeRule.check cell5842 (2:Fin 18)=true:=by decide +kernel
def cell5843:PairCell.Row:=⟨61,61,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5843:ThreeRule.check cell5843 (2:Fin 18)=true:=by decide +kernel
def cell5844:PairCell.Row:=⟨61,61,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5844:ThreeRule.check cell5844 (2:Fin 18)=true:=by decide +kernel
def cell5845:PairCell.Row:=⟨61,61,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5845:ThreeRule.check cell5845 (2:Fin 18)=true:=by decide +kernel
def cell5846:PairCell.Row:=⟨61,61,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5846:ThreeRule.check cell5846 (2:Fin 18)=true:=by decide +kernel
def cell5847:PairCell.Row:=⟨61,61,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5847:ThreeRule.check cell5847 (2:Fin 18)=true:=by decide +kernel
def cell5848:PairCell.Row:=⟨61,61,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5848:ThreeRule.check cell5848 (2:Fin 18)=true:=by decide +kernel
def cell5849:PairCell.Row:=⟨61,61,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5849:ThreeRule.check cell5849 (2:Fin 18)=true:=by decide +kernel
def cell5850:PairCell.Row:=⟨61,61,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5850:ThreeRule.check cell5850 (2:Fin 18)=true:=by decide +kernel
def cell5851:PairCell.Row:=⟨61,61,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5851:ThreeRule.check cell5851 (2:Fin 18)=true:=by decide +kernel
def cell5852:PairCell.Row:=⟨61,61,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5852:ThreeRule.check cell5852 (2:Fin 18)=true:=by decide +kernel
def cell5853:PairCell.Row:=⟨61,61,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5853:ThreeRule.check cell5853 (2:Fin 18)=true:=by decide +kernel
def cell5854:PairCell.Row:=⟨61,61,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5854:ThreeRule.check cell5854 (2:Fin 18)=true:=by decide +kernel
def cell5855:PairCell.Row:=⟨61,61,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5855:ThreeRule.check cell5855 (2:Fin 18)=true:=by decide +kernel
def cell5856:PairCell.Row:=⟨61,61,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5856:ThreeRule.check cell5856 (2:Fin 18)=true:=by decide +kernel
def cell5857:PairCell.Row:=⟨61,61,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5857:ThreeRule.check cell5857 (2:Fin 18)=true:=by decide +kernel
def cell5858:PairCell.Row:=⟨61,61,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5858:ThreeRule.check cell5858 (2:Fin 18)=true:=by decide +kernel
def cell5859:PairCell.Row:=⟨61,61,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5859:ThreeRule.check cell5859 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2889

-- Source: Research6969.PairReceipts293
section Z6969Source2890
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5860 : List StockPairs.Receipt := [
  ⟨⟨62,62,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨62,62,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5860 : StockPairs.checked rows5860 = true := by decide +kernel
theorem route5860 (i : Fin 12) : (rows5860.get i).Done :=
  StockPairs.doneAt paid5860 i

def cell5872:PairCell.Row:=⟨62,62,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5872:ThreeRule.check cell5872 (2:Fin 18)=true:=by decide +kernel
def cell5873:PairCell.Row:=⟨62,62,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5873:ThreeRule.check cell5873 (2:Fin 18)=true:=by decide +kernel
def cell5874:PairCell.Row:=⟨62,62,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5874:ThreeRule.check cell5874 (2:Fin 18)=true:=by decide +kernel
def cell5875:PairCell.Row:=⟨62,62,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5875:ThreeRule.check cell5875 (2:Fin 18)=true:=by decide +kernel
def cell5876:PairCell.Row:=⟨62,62,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5876:ThreeRule.check cell5876 (2:Fin 18)=true:=by decide +kernel
def cell5877:PairCell.Row:=⟨62,62,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5877:ThreeRule.check cell5877 (2:Fin 18)=true:=by decide +kernel
def cell5878:PairCell.Row:=⟨62,62,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5878:ThreeRule.check cell5878 (2:Fin 18)=true:=by decide +kernel
def cell5879:PairCell.Row:=⟨62,62,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5879:ThreeRule.check cell5879 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2890

-- Source: Research6969.PairReceipts294
section Z6969Source2891
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell5880:PairCell.Row:=⟨62,62,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5880:ThreeRule.check cell5880 (2:Fin 18)=true:=by decide +kernel
def cell5881:PairCell.Row:=⟨62,62,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5881:ThreeRule.check cell5881 (2:Fin 18)=true:=by decide +kernel
def cell5882:PairCell.Row:=⟨62,62,10,3,37,some 37,22,some 22,385979,[MeasuredChoices.test1079],[AxisChoices.test1843]⟩
theorem check5882:ThreeRule.check cell5882 (2:Fin 18)=true:=by decide +kernel
def cell5883:PairCell.Row:=⟨62,62,10,3,37,some 37,23,some 23,385979,[MeasuredChoices.test1079],[AxisChoices.test1844]⟩
theorem check5883:ThreeRule.check cell5883 (2:Fin 18)=true:=by decide +kernel
def cell5884:PairCell.Row:=⟨62,62,10,3,37,some 37,24,some 24,385979,[MeasuredChoices.test1079],[AxisChoices.test1845]⟩
theorem check5884:ThreeRule.check cell5884 (2:Fin 18)=true:=by decide +kernel
def cell5885:PairCell.Row:=⟨62,62,10,3,37,some 37,25,some 25,385979,[MeasuredChoices.test1079],[AxisChoices.test1845,AxisChoices.test1846]⟩
theorem check5885:ThreeRule.check cell5885 (2:Fin 18)=true:=by decide +kernel
def cell5886:PairCell.Row:=⟨62,62,10,3,37,some 37,26,some 26,385979,[MeasuredChoices.test1079],[AxisChoices.test1847]⟩
theorem check5886:ThreeRule.check cell5886 (2:Fin 18)=true:=by decide +kernel
def cell5887:PairCell.Row:=⟨62,62,10,3,37,some 37,27,some 27,385979,[MeasuredChoices.test1079],[AxisChoices.test1848]⟩
theorem check5887:ThreeRule.check cell5887 (2:Fin 18)=true:=by decide +kernel
def cell5888:PairCell.Row:=⟨62,62,10,3,37,some 37,28,some 28,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5888:ThreeRule.check cell5888 (2:Fin 18)=true:=by decide +kernel
def cell5889:PairCell.Row:=⟨62,62,10,3,37,some 37,29,some 29,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1849]⟩
theorem check5889:ThreeRule.check cell5889 (2:Fin 18)=true:=by decide +kernel
def cell5890:PairCell.Row:=⟨62,62,10,3,37,some 37,30,some 30,385979,[MeasuredChoices.test1079],[AxisChoices.test1848,AxisChoices.test1851]⟩
theorem check5890:ThreeRule.check cell5890 (2:Fin 18)=true:=by decide +kernel
def cell5891:PairCell.Row:=⟨62,62,10,3,37,some 37,31,some 31,385979,[MeasuredChoices.test1079],[AxisChoices.test1852]⟩
theorem check5891:ThreeRule.check cell5891 (2:Fin 18)=true:=by decide +kernel
def cell5892:PairCell.Row:=⟨62,62,10,3,37,some 37,32,some 32,385979,[MeasuredChoices.test1079],[AxisChoices.test1853]⟩
theorem check5892:ThreeRule.check cell5892 (2:Fin 18)=true:=by decide +kernel
def cell5893:PairCell.Row:=⟨62,62,10,3,37,some 37,33,some 33,385979,[MeasuredChoices.test1079],[AxisChoices.test1854]⟩
theorem check5893:ThreeRule.check cell5893 (2:Fin 18)=true:=by decide +kernel
def cell5894:PairCell.Row:=⟨62,62,10,3,37,some 37,34,some 34,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1855]⟩
theorem check5894:ThreeRule.check cell5894 (2:Fin 18)=true:=by decide +kernel
def cell5895:PairCell.Row:=⟨62,62,10,3,37,some 37,35,some 35,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1856]⟩
theorem check5895:ThreeRule.check cell5895 (2:Fin 18)=true:=by decide +kernel
def cell5896:PairCell.Row:=⟨62,62,10,3,37,some 37,36,some 36,385979,[MeasuredChoices.test1079],[AxisChoices.test1854,AxisChoices.test1857]⟩
theorem check5896:ThreeRule.check cell5896 (2:Fin 18)=true:=by decide +kernel
def cell5897:PairCell.Row:=⟨62,62,10,3,37,some 37,37,some 37,385979,[MeasuredChoices.test1079],[AxisChoices.test1857,AxisChoices.test1858]⟩
theorem check5897:ThreeRule.check cell5897 (2:Fin 18)=true:=by decide +kernel
private def rows5898 : List StockPairs.Receipt := [
  ⟨⟨63,63,10,3,37,some 37,0,some 0,385979,[MeasuredChoices.test1079],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,1,some 1,385979,[MeasuredChoices.test1079],[AxisChoices.test1822]⟩,2,separateIntersection⟩]
private theorem paid5898 : StockPairs.checked rows5898 = true := by decide +kernel
theorem route5898 (i : Fin 2) : (rows5898.get i).Done :=
  StockPairs.doneAt paid5898 i

end Research6969.PairReceipts
end Z6969Source2891

-- Source: Research6969.PairReceipts295
section Z6969Source2892
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows5900 : List StockPairs.Receipt := [
  ⟨⟨63,63,10,3,37,some 37,2,some 2,385979,[MeasuredChoices.test1079],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,3,some 3,385979,[MeasuredChoices.test1079],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,4,some 4,385979,[MeasuredChoices.test1079],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,5,some 5,385979,[MeasuredChoices.test1079],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,6,some 6,385979,[MeasuredChoices.test1079],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,7,some 7,385979,[MeasuredChoices.test1079],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,8,some 8,385979,[MeasuredChoices.test1079],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,9,some 9,385979,[MeasuredChoices.test1079],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,10,some 10,385979,[MeasuredChoices.test1079],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨63,63,10,3,37,some 37,11,some 11,385979,[MeasuredChoices.test1079],[AxisChoices.test1832]⟩,2,separateIntersection⟩]
private theorem paid5900 : StockPairs.checked rows5900 = true := by decide +kernel
theorem route5900 (i : Fin 10) : (rows5900.get i).Done :=
  StockPairs.doneAt paid5900 i

def cell5910:PairCell.Row:=⟨63,63,10,3,37,some 37,12,some 12,385979,[MeasuredChoices.test1079],[AxisChoices.test1833]⟩
theorem check5910:ThreeRule.check cell5910 (2:Fin 18)=true:=by decide +kernel
def cell5911:PairCell.Row:=⟨63,63,10,3,37,some 37,13,some 13,385979,[MeasuredChoices.test1079],[AxisChoices.test1834]⟩
theorem check5911:ThreeRule.check cell5911 (2:Fin 18)=true:=by decide +kernel
def cell5912:PairCell.Row:=⟨63,63,10,3,37,some 37,14,some 14,385979,[MeasuredChoices.test1079],[AxisChoices.test1835]⟩
theorem check5912:ThreeRule.check cell5912 (2:Fin 18)=true:=by decide +kernel
def cell5913:PairCell.Row:=⟨63,63,10,3,37,some 37,15,some 15,385979,[MeasuredChoices.test1079],[AxisChoices.test1836]⟩
theorem check5913:ThreeRule.check cell5913 (2:Fin 18)=true:=by decide +kernel
def cell5914:PairCell.Row:=⟨63,63,10,3,37,some 37,16,some 16,385979,[MeasuredChoices.test1079],[AxisChoices.test1837]⟩
theorem check5914:ThreeRule.check cell5914 (2:Fin 18)=true:=by decide +kernel
def cell5915:PairCell.Row:=⟨63,63,10,3,37,some 37,17,some 17,385979,[MeasuredChoices.test1079],[AxisChoices.test1838]⟩
theorem check5915:ThreeRule.check cell5915 (2:Fin 18)=true:=by decide +kernel
def cell5916:PairCell.Row:=⟨63,63,10,3,37,some 37,18,some 18,385979,[MeasuredChoices.test1079],[AxisChoices.test1839]⟩
theorem check5916:ThreeRule.check cell5916 (2:Fin 18)=true:=by decide +kernel
def cell5917:PairCell.Row:=⟨63,63,10,3,37,some 37,19,some 19,385979,[MeasuredChoices.test1079],[AxisChoices.test1840]⟩
theorem check5917:ThreeRule.check cell5917 (2:Fin 18)=true:=by decide +kernel
def cell5918:PairCell.Row:=⟨63,63,10,3,37,some 37,20,some 20,385979,[MeasuredChoices.test1079],[AxisChoices.test1841]⟩
theorem check5918:ThreeRule.check cell5918 (2:Fin 18)=true:=by decide +kernel
def cell5919:PairCell.Row:=⟨63,63,10,3,37,some 37,21,some 21,385979,[MeasuredChoices.test1079],[AxisChoices.test1842]⟩
theorem check5919:ThreeRule.check cell5919 (2:Fin 18)=true:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2892

-- Source: Research6969.HardFit3At160
section Z6969Source2893
set_option autoImplicit true
namespace Research6969.HardFit3At160
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3220 0)
theorem case160: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,36,some 36⟩:=PairRoute.start _ leaf0
private theorem allAxes76:PairRoute.Done (2:Fin 18) ⟨⟨50,50,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5404 0),
    (PairReceipts.route5404 1),
    (PairReceipts.route5404 2),
    (PairReceipts.route5404 3),
    (PairReceipts.route5404 4),
    (PairReceipts.route5404 5),
    (PairReceipts.route5404 6),
    (PairReceipts.route5404 7),
    (PairReceipts.route5404 8),
    (PairReceipts.route5404 9),
    PairLeaves.three PairReceipts.cell5414 PairReceipts.check5414 (by decide) (none),
    PairLeaves.three PairReceipts.cell5415 PairReceipts.check5415 (by decide) (none),
    PairLeaves.three PairReceipts.cell5416 PairReceipts.check5416 (by decide) (none),
    PairLeaves.three PairReceipts.cell5417 PairReceipts.check5417 (by decide) (none),
    PairLeaves.three PairReceipts.cell5418 PairReceipts.check5418 (by decide) (none),
    PairLeaves.three PairReceipts.cell5419 PairReceipts.check5419 (by decide) (none),
    PairLeaves.three PairReceipts.cell5420 PairReceipts.check5420 (by decide) (none),
    PairLeaves.three PairReceipts.cell5421 PairReceipts.check5421 (by decide) (none),
    PairLeaves.three PairReceipts.cell5422 PairReceipts.check5422 (by decide) (none),
    PairLeaves.three PairReceipts.cell5423 PairReceipts.check5423 (by decide) (none),
    PairLeaves.three PairReceipts.cell5424 PairReceipts.check5424 (by decide) (none),
    PairLeaves.three PairReceipts.cell5425 PairReceipts.check5425 (by decide) (none),
    PairLeaves.three PairReceipts.cell5426 PairReceipts.check5426 (by decide) (none),
    PairLeaves.three PairReceipts.cell5427 PairReceipts.check5427 (by decide) (none),
    PairLeaves.three PairReceipts.cell5428 PairReceipts.check5428 (by decide) (none),
    PairLeaves.three PairReceipts.cell5429 PairReceipts.check5429 (by decide) (none),
    PairLeaves.three PairReceipts.cell5430 PairReceipts.check5430 (by decide) (none),
    PairLeaves.three PairReceipts.cell5431 PairReceipts.check5431 (by decide) (none),
    PairLeaves.three PairReceipts.cell5432 PairReceipts.check5432 (by decide) (none),
    PairLeaves.three PairReceipts.cell5433 PairReceipts.check5433 (by decide) (none),
    PairLeaves.three PairReceipts.cell5434 PairReceipts.check5434 (by decide) (none),
    PairLeaves.three PairReceipts.cell5435 PairReceipts.check5435 (by decide) (none),
    PairLeaves.three PairReceipts.cell5436 PairReceipts.check5436 (by decide) (none),
    PairLeaves.three PairReceipts.cell5437 PairReceipts.check5437 (by decide) (none),
    PairLeaves.three PairReceipts.cell5438 PairReceipts.check5438 (by decide) (none),
    PairLeaves.three PairReceipts.cell5439 PairReceipts.check5439 (by decide) (none),
    PairLeaves.three PairReceipts.cell5440 PairReceipts.check5440 (by decide) (none),
    PairLeaves.three PairReceipts.cell5441 PairReceipts.check5441 (by decide) (none),
    trivial⟩)
private theorem allAxes152:PairRoute.Done (2:Fin 18) ⟨⟨51,51,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5442 0),
    (PairReceipts.route5442 1),
    (PairReceipts.route5442 2),
    (PairReceipts.route5442 3),
    (PairReceipts.route5442 4),
    (PairReceipts.route5442 5),
    (PairReceipts.route5442 6),
    (PairReceipts.route5442 7),
    (PairReceipts.route5442 8),
    (PairReceipts.route5442 9),
    (PairReceipts.route5442 10),
    PairLeaves.three PairReceipts.cell5453 PairReceipts.check5453 (by decide) (none),
    PairLeaves.three PairReceipts.cell5454 PairReceipts.check5454 (by decide) (none),
    PairLeaves.three PairReceipts.cell5455 PairReceipts.check5455 (by decide) (none),
    PairLeaves.three PairReceipts.cell5456 PairReceipts.check5456 (by decide) (none),
    PairLeaves.three PairReceipts.cell5457 PairReceipts.check5457 (by decide) (none),
    PairLeaves.three PairReceipts.cell5458 PairReceipts.check5458 (by decide) (none),
    PairLeaves.three PairReceipts.cell5459 PairReceipts.check5459 (by decide) (none),
    PairLeaves.three PairReceipts.cell5460 PairReceipts.check5460 (by decide) (none),
    PairLeaves.three PairReceipts.cell5461 PairReceipts.check5461 (by decide) (none),
    PairLeaves.three PairReceipts.cell5462 PairReceipts.check5462 (by decide) (none),
    PairLeaves.three PairReceipts.cell5463 PairReceipts.check5463 (by decide) (none),
    PairLeaves.three PairReceipts.cell5464 PairReceipts.check5464 (by decide) (none),
    PairLeaves.three PairReceipts.cell5465 PairReceipts.check5465 (by decide) (none),
    PairLeaves.three PairReceipts.cell5466 PairReceipts.check5466 (by decide) (none),
    PairLeaves.three PairReceipts.cell5467 PairReceipts.check5467 (by decide) (none),
    PairLeaves.three PairReceipts.cell5468 PairReceipts.check5468 (by decide) (none),
    PairLeaves.three PairReceipts.cell5469 PairReceipts.check5469 (by decide) (none),
    PairLeaves.three PairReceipts.cell5470 PairReceipts.check5470 (by decide) (none),
    PairLeaves.three PairReceipts.cell5471 PairReceipts.check5471 (by decide) (none),
    PairLeaves.three PairReceipts.cell5472 PairReceipts.check5472 (by decide) (none),
    PairLeaves.three PairReceipts.cell5473 PairReceipts.check5473 (by decide) (none),
    PairLeaves.three PairReceipts.cell5474 PairReceipts.check5474 (by decide) (none),
    PairLeaves.three PairReceipts.cell5475 PairReceipts.check5475 (by decide) (none),
    PairLeaves.three PairReceipts.cell5476 PairReceipts.check5476 (by decide) (none),
    PairLeaves.three PairReceipts.cell5477 PairReceipts.check5477 (by decide) (none),
    PairLeaves.three PairReceipts.cell5478 PairReceipts.check5478 (by decide) (none),
    PairLeaves.three PairReceipts.cell5479 PairReceipts.check5479 (by decide) (none),
    trivial⟩)
private theorem allAxes228:PairRoute.Done (2:Fin 18) ⟨⟨52,52,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5480 0),
    (PairReceipts.route5480 1),
    (PairReceipts.route5480 2),
    (PairReceipts.route5480 3),
    (PairReceipts.route5480 4),
    (PairReceipts.route5480 5),
    (PairReceipts.route5480 6),
    (PairReceipts.route5480 7),
    (PairReceipts.route5480 8),
    (PairReceipts.route5480 9),
    (PairReceipts.route5480 10),
    PairLeaves.three PairReceipts.cell5491 PairReceipts.check5491 (by decide) (none),
    PairLeaves.three PairReceipts.cell5492 PairReceipts.check5492 (by decide) (none),
    PairLeaves.three PairReceipts.cell5493 PairReceipts.check5493 (by decide) (none),
    PairLeaves.three PairReceipts.cell5494 PairReceipts.check5494 (by decide) (none),
    PairLeaves.three PairReceipts.cell5495 PairReceipts.check5495 (by decide) (none),
    PairLeaves.three PairReceipts.cell5496 PairReceipts.check5496 (by decide) (none),
    PairLeaves.three PairReceipts.cell5497 PairReceipts.check5497 (by decide) (none),
    PairLeaves.three PairReceipts.cell5498 PairReceipts.check5498 (by decide) (none),
    PairLeaves.three PairReceipts.cell5499 PairReceipts.check5499 (by decide) (none),
    PairLeaves.three PairReceipts.cell5500 PairReceipts.check5500 (by decide) (none),
    PairLeaves.three PairReceipts.cell5501 PairReceipts.check5501 (by decide) (none),
    PairLeaves.three PairReceipts.cell5502 PairReceipts.check5502 (by decide) (none),
    PairLeaves.three PairReceipts.cell5503 PairReceipts.check5503 (by decide) (none),
    PairLeaves.three PairReceipts.cell5504 PairReceipts.check5504 (by decide) (none),
    PairLeaves.three PairReceipts.cell5505 PairReceipts.check5505 (by decide) (none),
    PairLeaves.three PairReceipts.cell5506 PairReceipts.check5506 (by decide) (none),
    PairLeaves.three PairReceipts.cell5507 PairReceipts.check5507 (by decide) (none),
    PairLeaves.three PairReceipts.cell5508 PairReceipts.check5508 (by decide) (none),
    PairLeaves.three PairReceipts.cell5509 PairReceipts.check5509 (by decide) (none),
    PairLeaves.three PairReceipts.cell5510 PairReceipts.check5510 (by decide) (none),
    PairLeaves.three PairReceipts.cell5511 PairReceipts.check5511 (by decide) (none),
    PairLeaves.three PairReceipts.cell5512 PairReceipts.check5512 (by decide) (none),
    PairLeaves.three PairReceipts.cell5513 PairReceipts.check5513 (by decide) (none),
    PairLeaves.three PairReceipts.cell5514 PairReceipts.check5514 (by decide) (none),
    PairLeaves.three PairReceipts.cell5515 PairReceipts.check5515 (by decide) (none),
    PairLeaves.three PairReceipts.cell5516 PairReceipts.check5516 (by decide) (none),
    PairLeaves.three PairReceipts.cell5517 PairReceipts.check5517 (by decide) (none),
    trivial⟩)
private theorem allAxes304:PairRoute.Done (2:Fin 18) ⟨⟨53,53,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5518 0),
    (PairReceipts.route5518 1),
    (PairReceipts.route5520 0),
    (PairReceipts.route5520 1),
    (PairReceipts.route5520 2),
    (PairReceipts.route5520 3),
    (PairReceipts.route5520 4),
    (PairReceipts.route5520 5),
    (PairReceipts.route5520 6),
    (PairReceipts.route5520 7),
    (PairReceipts.route5520 8),
    PairLeaves.three PairReceipts.cell5529 PairReceipts.check5529 (by decide) (none),
    PairLeaves.three PairReceipts.cell5530 PairReceipts.check5530 (by decide) (none),
    PairLeaves.three PairReceipts.cell5531 PairReceipts.check5531 (by decide) (none),
    PairLeaves.three PairReceipts.cell5532 PairReceipts.check5532 (by decide) (none),
    PairLeaves.three PairReceipts.cell5533 PairReceipts.check5533 (by decide) (none),
    PairLeaves.three PairReceipts.cell5534 PairReceipts.check5534 (by decide) (none),
    PairLeaves.three PairReceipts.cell5535 PairReceipts.check5535 (by decide) (none),
    PairLeaves.three PairReceipts.cell5536 PairReceipts.check5536 (by decide) (none),
    PairLeaves.three PairReceipts.cell5537 PairReceipts.check5537 (by decide) (none),
    PairLeaves.three PairReceipts.cell5538 PairReceipts.check5538 (by decide) (none),
    PairLeaves.three PairReceipts.cell5539 PairReceipts.check5539 (by decide) (none),
    PairLeaves.three PairReceipts.cell5540 PairReceipts.check5540 (by decide) (none),
    PairLeaves.three PairReceipts.cell5541 PairReceipts.check5541 (by decide) (none),
    PairLeaves.three PairReceipts.cell5542 PairReceipts.check5542 (by decide) (none),
    PairLeaves.three PairReceipts.cell5543 PairReceipts.check5543 (by decide) (none),
    PairLeaves.three PairReceipts.cell5544 PairReceipts.check5544 (by decide) (none),
    PairLeaves.three PairReceipts.cell5545 PairReceipts.check5545 (by decide) (none),
    PairLeaves.three PairReceipts.cell5546 PairReceipts.check5546 (by decide) (none),
    PairLeaves.three PairReceipts.cell5547 PairReceipts.check5547 (by decide) (none),
    PairLeaves.three PairReceipts.cell5548 PairReceipts.check5548 (by decide) (none),
    PairLeaves.three PairReceipts.cell5549 PairReceipts.check5549 (by decide) (none),
    PairLeaves.three PairReceipts.cell5550 PairReceipts.check5550 (by decide) (none),
    PairLeaves.three PairReceipts.cell5551 PairReceipts.check5551 (by decide) (none),
    PairLeaves.three PairReceipts.cell5552 PairReceipts.check5552 (by decide) (none),
    PairLeaves.three PairReceipts.cell5553 PairReceipts.check5553 (by decide) (none),
    PairLeaves.three PairReceipts.cell5554 PairReceipts.check5554 (by decide) (none),
    PairLeaves.three PairReceipts.cell5555 PairReceipts.check5555 (by decide) (none),
    trivial⟩)
private theorem allAxes380:PairRoute.Done (2:Fin 18) ⟨⟨54,54,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5556 0),
    (PairReceipts.route5556 1),
    (PairReceipts.route5556 2),
    (PairReceipts.route5556 3),
    (PairReceipts.route5560 0),
    (PairReceipts.route5560 1),
    (PairReceipts.route5560 2),
    (PairReceipts.route5560 3),
    (PairReceipts.route5560 4),
    (PairReceipts.route5560 5),
    (PairReceipts.route5560 6),
    PairLeaves.three PairReceipts.cell5567 PairReceipts.check5567 (by decide) (none),
    PairLeaves.three PairReceipts.cell5568 PairReceipts.check5568 (by decide) (none),
    PairLeaves.three PairReceipts.cell5569 PairReceipts.check5569 (by decide) (none),
    PairLeaves.three PairReceipts.cell5570 PairReceipts.check5570 (by decide) (none),
    PairLeaves.three PairReceipts.cell5571 PairReceipts.check5571 (by decide) (none),
    PairLeaves.three PairReceipts.cell5572 PairReceipts.check5572 (by decide) (none),
    PairLeaves.three PairReceipts.cell5573 PairReceipts.check5573 (by decide) (none),
    PairLeaves.three PairReceipts.cell5574 PairReceipts.check5574 (by decide) (none),
    PairLeaves.three PairReceipts.cell5575 PairReceipts.check5575 (by decide) (none),
    PairLeaves.three PairReceipts.cell5576 PairReceipts.check5576 (by decide) (none),
    PairLeaves.three PairReceipts.cell5577 PairReceipts.check5577 (by decide) (none),
    PairLeaves.three PairReceipts.cell5578 PairReceipts.check5578 (by decide) (none),
    PairLeaves.three PairReceipts.cell5579 PairReceipts.check5579 (by decide) (none),
    PairLeaves.three PairReceipts.cell5580 PairReceipts.check5580 (by decide) (none),
    PairLeaves.three PairReceipts.cell5581 PairReceipts.check5581 (by decide) (none),
    PairLeaves.three PairReceipts.cell5582 PairReceipts.check5582 (by decide) (none),
    PairLeaves.three PairReceipts.cell5583 PairReceipts.check5583 (by decide) (none),
    PairLeaves.three PairReceipts.cell5584 PairReceipts.check5584 (by decide) (none),
    PairLeaves.three PairReceipts.cell5585 PairReceipts.check5585 (by decide) (none),
    PairLeaves.three PairReceipts.cell5586 PairReceipts.check5586 (by decide) (none),
    PairLeaves.three PairReceipts.cell5587 PairReceipts.check5587 (by decide) (none),
    PairLeaves.three PairReceipts.cell5588 PairReceipts.check5588 (by decide) (none),
    PairLeaves.three PairReceipts.cell5589 PairReceipts.check5589 (by decide) (none),
    PairLeaves.three PairReceipts.cell5590 PairReceipts.check5590 (by decide) (none),
    PairLeaves.three PairReceipts.cell5591 PairReceipts.check5591 (by decide) (none),
    PairLeaves.three PairReceipts.cell5592 PairReceipts.check5592 (by decide) (none),
    PairLeaves.three PairReceipts.cell5593 PairReceipts.check5593 (by decide) (none),
    trivial⟩)
private theorem allAxes456:PairRoute.Done (2:Fin 18) ⟨⟨55,55,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5594 0),
    (PairReceipts.route5594 1),
    (PairReceipts.route5594 2),
    (PairReceipts.route5594 3),
    (PairReceipts.route5594 4),
    (PairReceipts.route5594 5),
    (PairReceipts.route5600 0),
    (PairReceipts.route5600 1),
    (PairReceipts.route5600 2),
    (PairReceipts.route5600 3),
    (PairReceipts.route5600 4),
    PairLeaves.three PairReceipts.cell5605 PairReceipts.check5605 (by decide) (none),
    PairLeaves.three PairReceipts.cell5606 PairReceipts.check5606 (by decide) (none),
    PairLeaves.three PairReceipts.cell5607 PairReceipts.check5607 (by decide) (none),
    PairLeaves.three PairReceipts.cell5608 PairReceipts.check5608 (by decide) (none),
    PairLeaves.three PairReceipts.cell5609 PairReceipts.check5609 (by decide) (none),
    PairLeaves.three PairReceipts.cell5610 PairReceipts.check5610 (by decide) (none),
    PairLeaves.three PairReceipts.cell5611 PairReceipts.check5611 (by decide) (none),
    PairLeaves.three PairReceipts.cell5612 PairReceipts.check5612 (by decide) (none),
    PairLeaves.three PairReceipts.cell5613 PairReceipts.check5613 (by decide) (none),
    PairLeaves.three PairReceipts.cell5614 PairReceipts.check5614 (by decide) (none),
    PairLeaves.three PairReceipts.cell5615 PairReceipts.check5615 (by decide) (none),
    PairLeaves.three PairReceipts.cell5616 PairReceipts.check5616 (by decide) (none),
    PairLeaves.three PairReceipts.cell5617 PairReceipts.check5617 (by decide) (none),
    PairLeaves.three PairReceipts.cell5618 PairReceipts.check5618 (by decide) (none),
    PairLeaves.three PairReceipts.cell5619 PairReceipts.check5619 (by decide) (none),
    PairLeaves.three PairReceipts.cell5620 PairReceipts.check5620 (by decide) (none),
    PairLeaves.three PairReceipts.cell5621 PairReceipts.check5621 (by decide) (none),
    PairLeaves.three PairReceipts.cell5622 PairReceipts.check5622 (by decide) (none),
    PairLeaves.three PairReceipts.cell5623 PairReceipts.check5623 (by decide) (none),
    PairLeaves.three PairReceipts.cell5624 PairReceipts.check5624 (by decide) (none),
    PairLeaves.three PairReceipts.cell5625 PairReceipts.check5625 (by decide) (none),
    PairLeaves.three PairReceipts.cell5626 PairReceipts.check5626 (by decide) (none),
    PairLeaves.three PairReceipts.cell5627 PairReceipts.check5627 (by decide) (none),
    PairLeaves.three PairReceipts.cell5628 PairReceipts.check5628 (by decide) (none),
    PairLeaves.three PairReceipts.cell5629 PairReceipts.check5629 (by decide) (none),
    PairLeaves.three PairReceipts.cell5630 PairReceipts.check5630 (by decide) (none),
    PairLeaves.three PairReceipts.cell5631 PairReceipts.check5631 (by decide) (none),
    trivial⟩)
private theorem allAxes532:PairRoute.Done (2:Fin 18) ⟨⟨56,56,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5632 0),
    (PairReceipts.route5632 1),
    (PairReceipts.route5632 2),
    (PairReceipts.route5632 3),
    (PairReceipts.route5632 4),
    (PairReceipts.route5632 5),
    (PairReceipts.route5632 6),
    (PairReceipts.route5632 7),
    (PairReceipts.route5640 0),
    (PairReceipts.route5640 1),
    (PairReceipts.route5640 2),
    (PairReceipts.route5640 3),
    PairLeaves.three PairReceipts.cell5644 PairReceipts.check5644 (by decide) (none),
    PairLeaves.three PairReceipts.cell5645 PairReceipts.check5645 (by decide) (none),
    PairLeaves.three PairReceipts.cell5646 PairReceipts.check5646 (by decide) (none),
    PairLeaves.three PairReceipts.cell5647 PairReceipts.check5647 (by decide) (none),
    PairLeaves.three PairReceipts.cell5648 PairReceipts.check5648 (by decide) (none),
    PairLeaves.three PairReceipts.cell5649 PairReceipts.check5649 (by decide) (none),
    PairLeaves.three PairReceipts.cell5650 PairReceipts.check5650 (by decide) (none),
    PairLeaves.three PairReceipts.cell5651 PairReceipts.check5651 (by decide) (none),
    PairLeaves.three PairReceipts.cell5652 PairReceipts.check5652 (by decide) (none),
    PairLeaves.three PairReceipts.cell5653 PairReceipts.check5653 (by decide) (none),
    PairLeaves.three PairReceipts.cell5654 PairReceipts.check5654 (by decide) (none),
    PairLeaves.three PairReceipts.cell5655 PairReceipts.check5655 (by decide) (none),
    PairLeaves.three PairReceipts.cell5656 PairReceipts.check5656 (by decide) (none),
    PairLeaves.three PairReceipts.cell5657 PairReceipts.check5657 (by decide) (none),
    PairLeaves.three PairReceipts.cell5658 PairReceipts.check5658 (by decide) (none),
    PairLeaves.three PairReceipts.cell5659 PairReceipts.check5659 (by decide) (none),
    PairLeaves.three PairReceipts.cell5660 PairReceipts.check5660 (by decide) (none),
    PairLeaves.three PairReceipts.cell5661 PairReceipts.check5661 (by decide) (none),
    PairLeaves.three PairReceipts.cell5662 PairReceipts.check5662 (by decide) (none),
    PairLeaves.three PairReceipts.cell5663 PairReceipts.check5663 (by decide) (none),
    PairLeaves.three PairReceipts.cell5664 PairReceipts.check5664 (by decide) (none),
    PairLeaves.three PairReceipts.cell5665 PairReceipts.check5665 (by decide) (none),
    PairLeaves.three PairReceipts.cell5666 PairReceipts.check5666 (by decide) (none),
    PairLeaves.three PairReceipts.cell5667 PairReceipts.check5667 (by decide) (none),
    PairLeaves.three PairReceipts.cell5668 PairReceipts.check5668 (by decide) (none),
    PairLeaves.three PairReceipts.cell5669 PairReceipts.check5669 (by decide) (none),
    trivial⟩)
private theorem allAxes608:PairRoute.Done (2:Fin 18) ⟨⟨57,57,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5670 0),
    (PairReceipts.route5670 1),
    (PairReceipts.route5670 2),
    (PairReceipts.route5670 3),
    (PairReceipts.route5670 4),
    (PairReceipts.route5670 5),
    (PairReceipts.route5670 6),
    (PairReceipts.route5670 7),
    (PairReceipts.route5670 8),
    (PairReceipts.route5670 9),
    (PairReceipts.route5680 0),
    (PairReceipts.route5680 1),
    PairLeaves.three PairReceipts.cell5682 PairReceipts.check5682 (by decide) (none),
    PairLeaves.three PairReceipts.cell5683 PairReceipts.check5683 (by decide) (none),
    PairLeaves.three PairReceipts.cell5684 PairReceipts.check5684 (by decide) (none),
    PairLeaves.three PairReceipts.cell5685 PairReceipts.check5685 (by decide) (none),
    PairLeaves.three PairReceipts.cell5686 PairReceipts.check5686 (by decide) (none),
    PairLeaves.three PairReceipts.cell5687 PairReceipts.check5687 (by decide) (none),
    PairLeaves.three PairReceipts.cell5688 PairReceipts.check5688 (by decide) (none),
    PairLeaves.three PairReceipts.cell5689 PairReceipts.check5689 (by decide) (none),
    PairLeaves.three PairReceipts.cell5690 PairReceipts.check5690 (by decide) (none),
    PairLeaves.three PairReceipts.cell5691 PairReceipts.check5691 (by decide) (none),
    PairLeaves.three PairReceipts.cell5692 PairReceipts.check5692 (by decide) (none),
    PairLeaves.three PairReceipts.cell5693 PairReceipts.check5693 (by decide) (none),
    PairLeaves.three PairReceipts.cell5694 PairReceipts.check5694 (by decide) (none),
    PairLeaves.three PairReceipts.cell5695 PairReceipts.check5695 (by decide) (none),
    PairLeaves.three PairReceipts.cell5696 PairReceipts.check5696 (by decide) (none),
    PairLeaves.three PairReceipts.cell5697 PairReceipts.check5697 (by decide) (none),
    PairLeaves.three PairReceipts.cell5698 PairReceipts.check5698 (by decide) (none),
    PairLeaves.three PairReceipts.cell5699 PairReceipts.check5699 (by decide) (none),
    PairLeaves.three PairReceipts.cell5700 PairReceipts.check5700 (by decide) (none),
    PairLeaves.three PairReceipts.cell5701 PairReceipts.check5701 (by decide) (none),
    PairLeaves.three PairReceipts.cell5702 PairReceipts.check5702 (by decide) (none),
    PairLeaves.three PairReceipts.cell5703 PairReceipts.check5703 (by decide) (none),
    PairLeaves.three PairReceipts.cell5704 PairReceipts.check5704 (by decide) (none),
    PairLeaves.three PairReceipts.cell5705 PairReceipts.check5705 (by decide) (none),
    PairLeaves.three PairReceipts.cell5706 PairReceipts.check5706 (by decide) (none),
    PairLeaves.three PairReceipts.cell5707 PairReceipts.check5707 (by decide) (none),
    trivial⟩)
private theorem allAxes684:PairRoute.Done (2:Fin 18) ⟨⟨58,58,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5708 0),
    (PairReceipts.route5708 1),
    (PairReceipts.route5708 2),
    (PairReceipts.route5708 3),
    (PairReceipts.route5708 4),
    (PairReceipts.route5708 5),
    (PairReceipts.route5708 6),
    (PairReceipts.route5708 7),
    (PairReceipts.route5708 8),
    (PairReceipts.route5708 9),
    (PairReceipts.route5708 10),
    (PairReceipts.route5708 11),
    PairLeaves.three PairReceipts.cell5720 PairReceipts.check5720 (by decide) (none),
    PairLeaves.three PairReceipts.cell5721 PairReceipts.check5721 (by decide) (none),
    PairLeaves.three PairReceipts.cell5722 PairReceipts.check5722 (by decide) (none),
    PairLeaves.three PairReceipts.cell5723 PairReceipts.check5723 (by decide) (none),
    PairLeaves.three PairReceipts.cell5724 PairReceipts.check5724 (by decide) (none),
    PairLeaves.three PairReceipts.cell5725 PairReceipts.check5725 (by decide) (none),
    PairLeaves.three PairReceipts.cell5726 PairReceipts.check5726 (by decide) (none),
    PairLeaves.three PairReceipts.cell5727 PairReceipts.check5727 (by decide) (none),
    PairLeaves.three PairReceipts.cell5728 PairReceipts.check5728 (by decide) (none),
    PairLeaves.three PairReceipts.cell5729 PairReceipts.check5729 (by decide) (none),
    PairLeaves.three PairReceipts.cell5730 PairReceipts.check5730 (by decide) (none),
    PairLeaves.three PairReceipts.cell5731 PairReceipts.check5731 (by decide) (none),
    PairLeaves.three PairReceipts.cell5732 PairReceipts.check5732 (by decide) (none),
    PairLeaves.three PairReceipts.cell5733 PairReceipts.check5733 (by decide) (none),
    PairLeaves.three PairReceipts.cell5734 PairReceipts.check5734 (by decide) (none),
    PairLeaves.three PairReceipts.cell5735 PairReceipts.check5735 (by decide) (none),
    PairLeaves.three PairReceipts.cell5736 PairReceipts.check5736 (by decide) (none),
    PairLeaves.three PairReceipts.cell5737 PairReceipts.check5737 (by decide) (none),
    PairLeaves.three PairReceipts.cell5738 PairReceipts.check5738 (by decide) (none),
    PairLeaves.three PairReceipts.cell5739 PairReceipts.check5739 (by decide) (none),
    PairLeaves.three PairReceipts.cell5740 PairReceipts.check5740 (by decide) (none),
    PairLeaves.three PairReceipts.cell5741 PairReceipts.check5741 (by decide) (none),
    PairLeaves.three PairReceipts.cell5742 PairReceipts.check5742 (by decide) (none),
    PairLeaves.three PairReceipts.cell5743 PairReceipts.check5743 (by decide) (none),
    PairLeaves.three PairReceipts.cell5744 PairReceipts.check5744 (by decide) (none),
    PairLeaves.three PairReceipts.cell5745 PairReceipts.check5745 (by decide) (none),
    trivial⟩)
private theorem allAxes760:PairRoute.Done (2:Fin 18) ⟨⟨59,59,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5746 0),
    (PairReceipts.route5746 1),
    (PairReceipts.route5746 2),
    (PairReceipts.route5746 3),
    (PairReceipts.route5746 4),
    (PairReceipts.route5746 5),
    (PairReceipts.route5746 6),
    (PairReceipts.route5746 7),
    (PairReceipts.route5746 8),
    (PairReceipts.route5746 9),
    (PairReceipts.route5746 10),
    (PairReceipts.route5746 11),
    PairLeaves.three PairReceipts.cell5758 PairReceipts.check5758 (by decide) (none),
    PairLeaves.three PairReceipts.cell5759 PairReceipts.check5759 (by decide) (none),
    PairLeaves.three PairReceipts.cell5760 PairReceipts.check5760 (by decide) (none),
    PairLeaves.three PairReceipts.cell5761 PairReceipts.check5761 (by decide) (none),
    PairLeaves.three PairReceipts.cell5762 PairReceipts.check5762 (by decide) (none),
    PairLeaves.three PairReceipts.cell5763 PairReceipts.check5763 (by decide) (none),
    PairLeaves.three PairReceipts.cell5764 PairReceipts.check5764 (by decide) (none),
    PairLeaves.three PairReceipts.cell5765 PairReceipts.check5765 (by decide) (none),
    PairLeaves.three PairReceipts.cell5766 PairReceipts.check5766 (by decide) (none),
    PairLeaves.three PairReceipts.cell5767 PairReceipts.check5767 (by decide) (none),
    PairLeaves.three PairReceipts.cell5768 PairReceipts.check5768 (by decide) (none),
    PairLeaves.three PairReceipts.cell5769 PairReceipts.check5769 (by decide) (none),
    PairLeaves.three PairReceipts.cell5770 PairReceipts.check5770 (by decide) (none),
    PairLeaves.three PairReceipts.cell5771 PairReceipts.check5771 (by decide) (none),
    PairLeaves.three PairReceipts.cell5772 PairReceipts.check5772 (by decide) (none),
    PairLeaves.three PairReceipts.cell5773 PairReceipts.check5773 (by decide) (none),
    PairLeaves.three PairReceipts.cell5774 PairReceipts.check5774 (by decide) (none),
    PairLeaves.three PairReceipts.cell5775 PairReceipts.check5775 (by decide) (none),
    PairLeaves.three PairReceipts.cell5776 PairReceipts.check5776 (by decide) (none),
    PairLeaves.three PairReceipts.cell5777 PairReceipts.check5777 (by decide) (none),
    PairLeaves.three PairReceipts.cell5778 PairReceipts.check5778 (by decide) (none),
    PairLeaves.three PairReceipts.cell5779 PairReceipts.check5779 (by decide) (none),
    PairLeaves.three PairReceipts.cell5780 PairReceipts.check5780 (by decide) (none),
    PairLeaves.three PairReceipts.cell5781 PairReceipts.check5781 (by decide) (none),
    PairLeaves.three PairReceipts.cell5782 PairReceipts.check5782 (by decide) (none),
    PairLeaves.three PairReceipts.cell5783 PairReceipts.check5783 (by decide) (none),
    trivial⟩)
private theorem allAxes836:PairRoute.Done (2:Fin 18) ⟨⟨60,60,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5784 0),
    (PairReceipts.route5784 1),
    (PairReceipts.route5784 2),
    (PairReceipts.route5784 3),
    (PairReceipts.route5784 4),
    (PairReceipts.route5784 5),
    (PairReceipts.route5784 6),
    (PairReceipts.route5784 7),
    (PairReceipts.route5784 8),
    (PairReceipts.route5784 9),
    (PairReceipts.route5784 10),
    (PairReceipts.route5784 11),
    PairLeaves.three PairReceipts.cell5796 PairReceipts.check5796 (by decide) (none),
    PairLeaves.three PairReceipts.cell5797 PairReceipts.check5797 (by decide) (none),
    PairLeaves.three PairReceipts.cell5798 PairReceipts.check5798 (by decide) (none),
    PairLeaves.three PairReceipts.cell5799 PairReceipts.check5799 (by decide) (none),
    PairLeaves.three PairReceipts.cell5800 PairReceipts.check5800 (by decide) (none),
    PairLeaves.three PairReceipts.cell5801 PairReceipts.check5801 (by decide) (none),
    PairLeaves.three PairReceipts.cell5802 PairReceipts.check5802 (by decide) (none),
    PairLeaves.three PairReceipts.cell5803 PairReceipts.check5803 (by decide) (none),
    PairLeaves.three PairReceipts.cell5804 PairReceipts.check5804 (by decide) (none),
    PairLeaves.three PairReceipts.cell5805 PairReceipts.check5805 (by decide) (none),
    PairLeaves.three PairReceipts.cell5806 PairReceipts.check5806 (by decide) (none),
    PairLeaves.three PairReceipts.cell5807 PairReceipts.check5807 (by decide) (none),
    PairLeaves.three PairReceipts.cell5808 PairReceipts.check5808 (by decide) (none),
    PairLeaves.three PairReceipts.cell5809 PairReceipts.check5809 (by decide) (none),
    PairLeaves.three PairReceipts.cell5810 PairReceipts.check5810 (by decide) (none),
    PairLeaves.three PairReceipts.cell5811 PairReceipts.check5811 (by decide) (none),
    PairLeaves.three PairReceipts.cell5812 PairReceipts.check5812 (by decide) (none),
    PairLeaves.three PairReceipts.cell5813 PairReceipts.check5813 (by decide) (none),
    PairLeaves.three PairReceipts.cell5814 PairReceipts.check5814 (by decide) (none),
    PairLeaves.three PairReceipts.cell5815 PairReceipts.check5815 (by decide) (none),
    PairLeaves.three PairReceipts.cell5816 PairReceipts.check5816 (by decide) (none),
    PairLeaves.three PairReceipts.cell5817 PairReceipts.check5817 (by decide) (none),
    PairLeaves.three PairReceipts.cell5818 PairReceipts.check5818 (by decide) (none),
    PairLeaves.three PairReceipts.cell5819 PairReceipts.check5819 (by decide) (none),
    PairLeaves.three PairReceipts.cell5820 PairReceipts.check5820 (by decide) (none),
    PairLeaves.three PairReceipts.cell5821 PairReceipts.check5821 (by decide) (none),
    trivial⟩)
private theorem allAxes912:PairRoute.Done (2:Fin 18) ⟨⟨61,61,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5822 0),
    (PairReceipts.route5822 1),
    (PairReceipts.route5822 2),
    (PairReceipts.route5822 3),
    (PairReceipts.route5822 4),
    (PairReceipts.route5822 5),
    (PairReceipts.route5822 6),
    (PairReceipts.route5822 7),
    (PairReceipts.route5822 8),
    (PairReceipts.route5822 9),
    (PairReceipts.route5822 10),
    (PairReceipts.route5822 11),
    PairLeaves.three PairReceipts.cell5834 PairReceipts.check5834 (by decide) (none),
    PairLeaves.three PairReceipts.cell5835 PairReceipts.check5835 (by decide) (none),
    PairLeaves.three PairReceipts.cell5836 PairReceipts.check5836 (by decide) (none),
    PairLeaves.three PairReceipts.cell5837 PairReceipts.check5837 (by decide) (none),
    PairLeaves.three PairReceipts.cell5838 PairReceipts.check5838 (by decide) (none),
    PairLeaves.three PairReceipts.cell5839 PairReceipts.check5839 (by decide) (none),
    PairLeaves.three PairReceipts.cell5840 PairReceipts.check5840 (by decide) (none),
    PairLeaves.three PairReceipts.cell5841 PairReceipts.check5841 (by decide) (none),
    PairLeaves.three PairReceipts.cell5842 PairReceipts.check5842 (by decide) (none),
    PairLeaves.three PairReceipts.cell5843 PairReceipts.check5843 (by decide) (none),
    PairLeaves.three PairReceipts.cell5844 PairReceipts.check5844 (by decide) (none),
    PairLeaves.three PairReceipts.cell5845 PairReceipts.check5845 (by decide) (none),
    PairLeaves.three PairReceipts.cell5846 PairReceipts.check5846 (by decide) (none),
    PairLeaves.three PairReceipts.cell5847 PairReceipts.check5847 (by decide) (none),
    PairLeaves.three PairReceipts.cell5848 PairReceipts.check5848 (by decide) (none),
    PairLeaves.three PairReceipts.cell5849 PairReceipts.check5849 (by decide) (none),
    PairLeaves.three PairReceipts.cell5850 PairReceipts.check5850 (by decide) (none),
    PairLeaves.three PairReceipts.cell5851 PairReceipts.check5851 (by decide) (none),
    PairLeaves.three PairReceipts.cell5852 PairReceipts.check5852 (by decide) (none),
    PairLeaves.three PairReceipts.cell5853 PairReceipts.check5853 (by decide) (none),
    PairLeaves.three PairReceipts.cell5854 PairReceipts.check5854 (by decide) (none),
    PairLeaves.three PairReceipts.cell5855 PairReceipts.check5855 (by decide) (none),
    PairLeaves.three PairReceipts.cell5856 PairReceipts.check5856 (by decide) (none),
    PairLeaves.three PairReceipts.cell5857 PairReceipts.check5857 (by decide) (none),
    PairLeaves.three PairReceipts.cell5858 PairReceipts.check5858 (by decide) (none),
    PairLeaves.three PairReceipts.cell5859 PairReceipts.check5859 (by decide) (none),
    trivial⟩)
private theorem allAxes988:PairRoute.Done (2:Fin 18) ⟨⟨62,62,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5860 0),
    (PairReceipts.route5860 1),
    (PairReceipts.route5860 2),
    (PairReceipts.route5860 3),
    (PairReceipts.route5860 4),
    (PairReceipts.route5860 5),
    (PairReceipts.route5860 6),
    (PairReceipts.route5860 7),
    (PairReceipts.route5860 8),
    (PairReceipts.route5860 9),
    (PairReceipts.route5860 10),
    (PairReceipts.route5860 11),
    PairLeaves.three PairReceipts.cell5872 PairReceipts.check5872 (by decide) (none),
    PairLeaves.three PairReceipts.cell5873 PairReceipts.check5873 (by decide) (none),
    PairLeaves.three PairReceipts.cell5874 PairReceipts.check5874 (by decide) (none),
    PairLeaves.three PairReceipts.cell5875 PairReceipts.check5875 (by decide) (none),
    PairLeaves.three PairReceipts.cell5876 PairReceipts.check5876 (by decide) (none),
    PairLeaves.three PairReceipts.cell5877 PairReceipts.check5877 (by decide) (none),
    PairLeaves.three PairReceipts.cell5878 PairReceipts.check5878 (by decide) (none),
    PairLeaves.three PairReceipts.cell5879 PairReceipts.check5879 (by decide) (none),
    PairLeaves.three PairReceipts.cell5880 PairReceipts.check5880 (by decide) (none),
    PairLeaves.three PairReceipts.cell5881 PairReceipts.check5881 (by decide) (none),
    PairLeaves.three PairReceipts.cell5882 PairReceipts.check5882 (by decide) (none),
    PairLeaves.three PairReceipts.cell5883 PairReceipts.check5883 (by decide) (none),
    PairLeaves.three PairReceipts.cell5884 PairReceipts.check5884 (by decide) (none),
    PairLeaves.three PairReceipts.cell5885 PairReceipts.check5885 (by decide) (none),
    PairLeaves.three PairReceipts.cell5886 PairReceipts.check5886 (by decide) (none),
    PairLeaves.three PairReceipts.cell5887 PairReceipts.check5887 (by decide) (none),
    PairLeaves.three PairReceipts.cell5888 PairReceipts.check5888 (by decide) (none),
    PairLeaves.three PairReceipts.cell5889 PairReceipts.check5889 (by decide) (none),
    PairLeaves.three PairReceipts.cell5890 PairReceipts.check5890 (by decide) (none),
    PairLeaves.three PairReceipts.cell5891 PairReceipts.check5891 (by decide) (none),
    PairLeaves.three PairReceipts.cell5892 PairReceipts.check5892 (by decide) (none),
    PairLeaves.three PairReceipts.cell5893 PairReceipts.check5893 (by decide) (none),
    PairLeaves.three PairReceipts.cell5894 PairReceipts.check5894 (by decide) (none),
    PairLeaves.three PairReceipts.cell5895 PairReceipts.check5895 (by decide) (none),
    PairLeaves.three PairReceipts.cell5896 PairReceipts.check5896 (by decide) (none),
    PairLeaves.three PairReceipts.cell5897 PairReceipts.check5897 (by decide) (none),
    trivial⟩)
private theorem allAxes1064:PairRoute.Done (2:Fin 18) ⟨⟨63,63,10,3,37,some 37⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 37 ⟨
    (PairReceipts.route5898 0),
    (PairReceipts.route5898 1),
    (PairReceipts.route5900 0),
    (PairReceipts.route5900 1),
    (PairReceipts.route5900 2),
    (PairReceipts.route5900 3),
    (PairReceipts.route5900 4),
    (PairReceipts.route5900 5),
    (PairReceipts.route5900 6),
    (PairReceipts.route5900 7),
    (PairReceipts.route5900 8),
    (PairReceipts.route5900 9),
    PairLeaves.three PairReceipts.cell5910 PairReceipts.check5910 (by decide) (none),
    PairLeaves.three PairReceipts.cell5911 PairReceipts.check5911 (by decide) (none),
    PairLeaves.three PairReceipts.cell5912 PairReceipts.check5912 (by decide) (none),
    PairLeaves.three PairReceipts.cell5913 PairReceipts.check5913 (by decide) (none),
    PairLeaves.three PairReceipts.cell5914 PairReceipts.check5914 (by decide) (none),
    PairLeaves.three PairReceipts.cell5915 PairReceipts.check5915 (by decide) (none),
    PairLeaves.three PairReceipts.cell5916 PairReceipts.check5916 (by decide) (none),
    PairLeaves.three PairReceipts.cell5917 PairReceipts.check5917 (by decide) (none),
    PairLeaves.three PairReceipts.cell5918 PairReceipts.check5918 (by decide) (none),
    PairLeaves.three PairReceipts.cell5919 PairReceipts.check5919 (by decide) (none),
    PairLeaves.three PairReceipts.cell5920 PairReceipts.check5920 (by decide) (none),
    PairLeaves.three PairReceipts.cell5921 PairReceipts.check5921 (by decide) (none),
    PairLeaves.three PairReceipts.cell5922 PairReceipts.check5922 (by decide) (none),
    PairLeaves.three PairReceipts.cell5923 PairReceipts.check5923 (by decide) (none),
    PairLeaves.three PairReceipts.cell5924 PairReceipts.check5924 (by decide) (none),
    PairLeaves.three PairReceipts.cell5925 PairReceipts.check5925 (by decide) (none),
    PairLeaves.three PairReceipts.cell5926 PairReceipts.check5926 (by decide) (none),
    PairLeaves.three PairReceipts.cell5927 PairReceipts.check5927 (by decide) (none),
    PairLeaves.three PairReceipts.cell5928 PairReceipts.check5928 (by decide) (none),
    PairLeaves.three PairReceipts.cell5929 PairReceipts.check5929 (by decide) (none),
    PairLeaves.three PairReceipts.cell5930 PairReceipts.check5930 (by decide) (none),
    PairLeaves.three PairReceipts.cell5931 PairReceipts.check5931 (by decide) (none),
    PairLeaves.three PairReceipts.cell5932 PairReceipts.check5932 (by decide) (none),
    PairLeaves.three PairReceipts.cell5933 PairReceipts.check5933 (by decide) (none),
    PairLeaves.three PairReceipts.cell5934 PairReceipts.check5934 (by decide) (none),
    PairLeaves.three PairReceipts.cell5935 PairReceipts.check5935 (by decide) (none),
    trivial⟩)
private def grade1065 := PairRoute.grade 62 allAxes988 allAxes1064
private def grade1066 := PairRoute.grade 61 allAxes912 grade1065
private def grade1067 := PairRoute.grade 60 allAxes836 grade1066
private def grade1068 := PairRoute.grade 59 allAxes760 grade1067
private def grade1069 := PairRoute.grade 58 allAxes684 grade1068
private def grade1070 := PairRoute.grade 57 allAxes608 grade1069
private def grade1071 := PairRoute.grade 56 allAxes532 grade1070
private def grade1072 := PairRoute.grade 55 allAxes456 grade1071
private def grade1073 := PairRoute.grade 54 allAxes380 grade1072
private def grade1074 := PairRoute.grade 53 allAxes304 grade1073
private def grade1075 := PairRoute.grade 52 allAxes228 grade1074
private def grade1076 := PairRoute.grade 51 allAxes152 grade1075
private def grade1077 := PairRoute.grade 50 allAxes76 grade1076
theorem case161: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,37,some 37⟩:=PairRoute.start _ grade1077
private theorem allAxes1155:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,38,some 38⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 38 ⟨
    (PairReceipts.route3181 0),
    (PairReceipts.route3181 1),
    (PairReceipts.route3181 2),
    (PairReceipts.route3181 3),
    (PairReceipts.route3181 4),
    (PairReceipts.route3181 5),
    (PairReceipts.route3181 6),
    (PairReceipts.route3181 7),
    (PairReceipts.route3181 8),
    (PairReceipts.route3181 9),
    (PairReceipts.route3181 10),
    (PairReceipts.route3181 11),
    (PairReceipts.route3181 12),
    (PairReceipts.route3181 13),
    (PairReceipts.route3181 14),
    (PairReceipts.route3181 15),
    (PairReceipts.route3181 16),
    (PairReceipts.route3181 17),
    (PairReceipts.route3181 18),
    (PairReceipts.route3200 0),
    (PairReceipts.route3200 1),
    (PairReceipts.route3200 2),
    (PairReceipts.route3200 3),
    (PairReceipts.route3200 4),
    (PairReceipts.route3200 5),
    (PairReceipts.route3200 6),
    (PairReceipts.route3200 7),
    (PairReceipts.route3200 8),
    (PairReceipts.route3200 9),
    (PairReceipts.route3200 10),
    (PairReceipts.route3200 11),
    PairLeaves.excluded PairReceipts.cell3212 PairReceipts.check3212 (none),
    PairLeaves.excluded PairReceipts.cell3213 PairReceipts.check3213 (none),
    PairLeaves.excluded PairReceipts.cell3214 PairReceipts.check3214 (none),
    PairLeaves.excluded PairReceipts.cell3215 PairReceipts.check3215 (none),
    PairLeaves.excluded PairReceipts.cell3216 PairReceipts.check3216 (none),
    PairLeaves.excluded PairReceipts.cell3217 PairReceipts.check3217 (none),
    PairLeaves.excluded PairReceipts.cell3218 PairReceipts.check3218 (none),
    PairLeaves.excluded PairReceipts.cell3219 PairReceipts.check3219 (none),
    trivial⟩)
theorem case162: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,38,some 38⟩:=PairRoute.start _ allAxes1155
private theorem allAxes1235:PairRoute.Done (2:Fin 18) ⟨⟨50,63,10,3,39,some 39⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 39 ⟨
    (PairReceipts.route3140 1),
    (PairReceipts.route3140 2),
    (PairReceipts.route3140 3),
    (PairReceipts.route3140 4),
    (PairReceipts.route3140 5),
    (PairReceipts.route3140 6),
    (PairReceipts.route3140 7),
    (PairReceipts.route3140 8),
    (PairReceipts.route3140 9),
    (PairReceipts.route3140 10),
    (PairReceipts.route3140 11),
    (PairReceipts.route3140 12),
    (PairReceipts.route3140 13),
    (PairReceipts.route3140 14),
    (PairReceipts.route3140 15),
    (PairReceipts.route3140 16),
    (PairReceipts.route3140 17),
    (PairReceipts.route3140 18),
    (PairReceipts.route3140 19),
    (PairReceipts.route3160 0),
    (PairReceipts.route3160 1),
    (PairReceipts.route3160 2),
    (PairReceipts.route3160 3),
    (PairReceipts.route3160 4),
    (PairReceipts.route3160 5),
    (PairReceipts.route3160 6),
    (PairReceipts.route3160 7),
    (PairReceipts.route3160 8),
    (PairReceipts.route3160 9),
    (PairReceipts.route3160 10),
    (PairReceipts.route3160 11),
    PairLeaves.excluded PairReceipts.cell3172 PairReceipts.check3172 (none),
    PairLeaves.excluded PairReceipts.cell3173 PairReceipts.check3173 (none),
    PairLeaves.excluded PairReceipts.cell3174 PairReceipts.check3174 (none),
    PairLeaves.excluded PairReceipts.cell3175 PairReceipts.check3175 (none),
    PairLeaves.excluded PairReceipts.cell3176 PairReceipts.check3176 (none),
    PairLeaves.excluded PairReceipts.cell3177 PairReceipts.check3177 (none),
    PairLeaves.excluded PairReceipts.cell3178 PairReceipts.check3178 (none),
    PairLeaves.excluded PairReceipts.cell3179 PairReceipts.check3179 (none),
    PairLeaves.excluded PairReceipts.cell3180 PairReceipts.check3180 (none),
    trivial⟩)
theorem case163: NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,39,some 39⟩:=PairRoute.start _ allAxes1235
private def leaf1236 := (PairReceipts.route3400 1)
theorem case164: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,0,some 0⟩:=PairRoute.start _ leaf1236
private def leaf1237 := (PairReceipts.route3400 0)
theorem case165: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,1,some 1⟩:=PairRoute.start _ leaf1237
private def leaf1238 := (PairReceipts.route3380 19)
theorem case166: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,2,some 3⟩:=PairRoute.start _ leaf1238
private def leaf1239 := (PairReceipts.route3380 18)
theorem case167: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,4,some 8⟩:=PairRoute.start _ leaf1239
private def leaf1240 := (PairReceipts.route3380 17)
theorem case168: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,9,some 12⟩:=PairRoute.start _ leaf1240
private def leaf1241 := (PairReceipts.route3380 16)
theorem case169: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,13,some 16⟩:=PairRoute.start _ leaf1241
end Research6969.HardFit3At160
end Z6969Source2893

-- Source: Research6969.PairReceipts171
section Z6969Source2894
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3420 : List StockPairs.Receipt := [
  ⟨⟨64,722,12,2,13,some 16,0,none,257319,[],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,9,some 12,0,none,257319,[],[]⟩,2,surfaceWhole⟩,
  ⟨⟨64,722,12,2,4,some 8,0,none,257319,[],[]⟩,2,surfaceWhole⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,3,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨23,24,9,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,17,some 20,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,13,some 16,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,9,some 12,0,none,257319,[],[]⟩,3,surfaceIntersection⟩,
  ⟨⟨23,24,9,2,4,some 8,0,none,257319,[],[]⟩,3,⟨.surface,.intersection,.surface,0⟩⟩,
  ⟨⟨23,24,9,3,17,some 20,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,3,markedAxisIntersection⟩,
  ⟨⟨23,24,9,3,17,some 20,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,3,markedAxisIntersection⟩]
private theorem paid3420 : StockPairs.checked rows3420 = true := by decide +kernel
theorem route3420 (i : Fin 20) : (rows3420.get i).Done :=
  StockPairs.doneAt paid3420 i

end Research6969.PairReceipts
end Z6969Source2894

-- Source: Research6969.HardFit3At170
section Z6969Source2895
set_option autoImplicit true
namespace Research6969.HardFit3At170
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route3380 15)
theorem case170: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,17,some 20⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route3380 14)
theorem case171: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,21,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route3380 13)
theorem case172: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,25,some 28⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route3380 12)
theorem case173: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,29,some 32⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route3380 11)
theorem case174: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,33,some 40⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route3380 10)
theorem case175: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,41,some 48⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route3380 9)
theorem case176: NormalRoute.Done (2:Fin 18) ⟨64,722,12,1,49,some 64⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route3420 2)
theorem case177: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,4,some 8⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route3420 1)
theorem case178: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,9,some 12⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route3420 0)
theorem case179: NormalRoute.Done (2:Fin 18) ⟨64,722,12,2,13,some 16⟩:=PairRoute.start _ leaf9
end Research6969.HardFit3At170
end Z6969Source2895
