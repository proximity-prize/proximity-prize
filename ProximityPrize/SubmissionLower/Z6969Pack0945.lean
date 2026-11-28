import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0944

set_option Elab.async false

-- Source: Research6969.PairReceipts087
section Z6969Source2699
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1740 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,57,some 64,16,some 16,257319,[MeasuredChoices.test79],[AxisChoices.test1779]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,17,some 17,257319,[MeasuredChoices.test79],[AxisChoices.test1780]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,18,some 18,257319,[MeasuredChoices.test79],[AxisChoices.test1781]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,19,some 19,257319,[MeasuredChoices.test79],[AxisChoices.test1782]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,20,some 20,257319,[MeasuredChoices.test79],[AxisChoices.test1783]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,21,some 21,257319,[MeasuredChoices.test79],[AxisChoices.test1784]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,22,some 22,257319,[MeasuredChoices.test79],[AxisChoices.test1785]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,23,some 23,257319,[MeasuredChoices.test79],[AxisChoices.test1786]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,24,some 24,257319,[MeasuredChoices.test79],[AxisChoices.test1787]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,25,some 25,257319,[MeasuredChoices.test79],[AxisChoices.test1788]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,26,some 26,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1789]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,27,some 27,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1790]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,28,some 28,257319,[MeasuredChoices.test79],[AxisChoices.test1791]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,29,some 29,257319,[MeasuredChoices.test79],[AxisChoices.test1791,AxisChoices.test1792]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,30,some 30,257319,[MeasuredChoices.test79],[AxisChoices.test1792,AxisChoices.test1793]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,57,some 64,31,some 31,257319,[MeasuredChoices.test79],[AxisChoices.test1793,AxisChoices.test1794]⟩,1,markedAxisWhole⟩]
private theorem paid1740 : StockPairs.checked rows1740 = true := by decide +kernel
theorem route1740 (i : Fin 16) : (rows1740.get i).Done :=
  StockPairs.doneAt paid1740 i

def cell1756:PairCell.Row:=⟨41,49,9,2,57,some 64,32,some 32,257319,[MeasuredChoices.test79],[AxisChoices.test1795]⟩
theorem check1756:(cell1756.cap (1:Fin 18)).grade<cell1756.lowerGrade-cell1756.off:=by decide +kernel
def cell1757:PairCell.Row:=⟨41,49,9,2,57,some 64,33,some 33,257319,[MeasuredChoices.test79],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check1757:(cell1757.cap (1:Fin 18)).grade<cell1757.lowerGrade-cell1757.off:=by decide +kernel
def cell1758:PairCell.Row:=⟨41,49,9,2,57,some 64,34,some 34,257319,[MeasuredChoices.test79],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check1758:(cell1758.cap (1:Fin 18)).grade<cell1758.lowerGrade-cell1758.off:=by decide +kernel
def cell1759:PairCell.Row:=⟨41,49,9,2,57,some 64,35,some 35,257319,[MeasuredChoices.test79],[AxisChoices.test1798]⟩
theorem check1759:(cell1759.cap (1:Fin 18)).grade<cell1759.lowerGrade-cell1759.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2699

-- Source: Research6969.PairReceipts088
section Z6969Source2700
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell1760:PairCell.Row:=⟨41,49,9,2,57,some 64,36,some 36,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check1760:(cell1760.cap (1:Fin 18)).grade<cell1760.lowerGrade-cell1760.off:=by decide +kernel
def cell1761:PairCell.Row:=⟨41,49,9,2,57,some 64,37,some 37,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check1761:(cell1761.cap (1:Fin 18)).grade<cell1761.lowerGrade-cell1761.off:=by decide +kernel
def cell1762:PairCell.Row:=⟨41,49,9,2,57,some 64,38,some 38,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check1762:(cell1762.cap (1:Fin 18)).grade<cell1762.lowerGrade-cell1762.off:=by decide +kernel
def cell1763:PairCell.Row:=⟨41,49,9,2,57,some 64,39,some 39,257319,[MeasuredChoices.test79],[AxisChoices.test1802]⟩
theorem check1763:(cell1763.cap (1:Fin 18)).grade<cell1763.lowerGrade-cell1763.off:=by decide +kernel
def cell1764:PairCell.Row:=⟨41,49,9,2,57,some 64,40,some 40,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check1764:(cell1764.cap (1:Fin 18)).grade<cell1764.lowerGrade-cell1764.off:=by decide +kernel
def cell1765:PairCell.Row:=⟨41,49,9,2,57,some 64,41,some 41,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check1765:(cell1765.cap (1:Fin 18)).grade<cell1765.lowerGrade-cell1765.off:=by decide +kernel
def cell1766:PairCell.Row:=⟨41,49,9,2,57,some 64,42,some 42,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check1766:(cell1766.cap (1:Fin 18)).grade<cell1766.lowerGrade-cell1766.off:=by decide +kernel
def cell1767:PairCell.Row:=⟨41,49,9,2,57,some 64,43,some 43,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check1767:(cell1767.cap (1:Fin 18)).grade<cell1767.lowerGrade-cell1767.off:=by decide +kernel
def cell1768:PairCell.Row:=⟨41,49,9,2,57,some 64,44,some 44,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check1768:(cell1768.cap (1:Fin 18)).grade<cell1768.lowerGrade-cell1768.off:=by decide +kernel
def cell1769:PairCell.Row:=⟨41,49,9,2,57,some 64,45,some 45,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check1769:(cell1769.cap (1:Fin 18)).grade<cell1769.lowerGrade-cell1769.off:=by decide +kernel
def cell1770:PairCell.Row:=⟨41,49,9,2,57,some 64,46,some 46,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check1770:(cell1770.cap (1:Fin 18)).grade<cell1770.lowerGrade-cell1770.off:=by decide +kernel
def cell1771:PairCell.Row:=⟨41,49,9,2,57,some 64,47,some 47,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check1771:(cell1771.cap (1:Fin 18)).grade<cell1771.lowerGrade-cell1771.off:=by decide +kernel
def cell1772:PairCell.Row:=⟨41,49,9,2,57,some 64,48,some 48,257319,[MeasuredChoices.test79],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check1772:(cell1772.cap (1:Fin 18)).grade<cell1772.lowerGrade-cell1772.off:=by decide +kernel
def cell1773:PairCell.Row:=⟨41,49,9,2,57,some 64,49,some 49,257319,[MeasuredChoices.test79],[AxisChoices.test1812]⟩
theorem check1773:(cell1773.cap (1:Fin 18)).grade<cell1773.lowerGrade-cell1773.off:=by decide +kernel
def cell1774:PairCell.Row:=⟨41,49,9,2,57,some 64,50,some 50,257319,[MeasuredChoices.test79],[AxisChoices.test1813]⟩
theorem check1774:(cell1774.cap (1:Fin 18)).grade<cell1774.lowerGrade-cell1774.off:=by decide +kernel
def cell1775:PairCell.Row:=⟨41,49,9,2,57,some 64,51,some 51,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check1775:(cell1775.cap (1:Fin 18)).grade<cell1775.lowerGrade-cell1775.off:=by decide +kernel
def cell1776:PairCell.Row:=⟨41,49,9,2,57,some 64,52,some 52,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check1776:(cell1776.cap (1:Fin 18)).grade<cell1776.lowerGrade-cell1776.off:=by decide +kernel
def cell1777:PairCell.Row:=⟨41,49,9,2,57,some 64,53,some 53,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check1777:(cell1777.cap (1:Fin 18)).grade<cell1777.lowerGrade-cell1777.off:=by decide +kernel
def cell1778:PairCell.Row:=⟨41,49,9,2,57,some 64,54,some 54,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check1778:(cell1778.cap (1:Fin 18)).grade<cell1778.lowerGrade-cell1778.off:=by decide +kernel
def cell1779:PairCell.Row:=⟨41,49,9,2,57,some 64,55,some 55,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check1779:(cell1779.cap (1:Fin 18)).grade<cell1779.lowerGrade-cell1779.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2700

-- Source: Research6969.PairReceipts089
section Z6969Source2701
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell1780:PairCell.Row:=⟨41,49,9,2,57,some 64,56,some 56,257319,[MeasuredChoices.test79],[AxisChoices.test1819]⟩
theorem check1780:(cell1780.cap (1:Fin 18)).grade<cell1780.lowerGrade-cell1780.off:=by decide +kernel
def cell1781:PairCell.Row:=⟨41,49,9,2,57,some 64,57,some 57,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1781:(cell1781.cap (1:Fin 18)).grade<cell1781.lowerGrade-cell1781.off:=by decide +kernel
def cell1782:PairCell.Row:=⟨41,49,9,2,57,some 64,58,some 58,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1782:(cell1782.cap (1:Fin 18)).grade<cell1782.lowerGrade-cell1782.off:=by decide +kernel
def cell1783:PairCell.Row:=⟨41,49,9,2,57,some 64,59,some 59,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1783:(cell1783.cap (1:Fin 18)).grade<cell1783.lowerGrade-cell1783.off:=by decide +kernel
def cell1784:PairCell.Row:=⟨41,49,9,2,57,some 64,60,some 60,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1784:(cell1784.cap (1:Fin 18)).grade<cell1784.lowerGrade-cell1784.off:=by decide +kernel
def cell1785:PairCell.Row:=⟨41,49,9,2,57,some 64,61,some 61,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1785:(cell1785.cap (1:Fin 18)).grade<cell1785.lowerGrade-cell1785.off:=by decide +kernel
def cell1786:PairCell.Row:=⟨41,49,9,2,57,some 64,62,some 62,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1786:(cell1786.cap (1:Fin 18)).grade<cell1786.lowerGrade-cell1786.off:=by decide +kernel
def cell1787:PairCell.Row:=⟨41,49,9,2,57,some 64,63,some 63,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1787:(cell1787.cap (1:Fin 18)).grade<cell1787.lowerGrade-cell1787.off:=by decide +kernel
def cell1788:PairCell.Row:=⟨41,49,9,2,57,some 64,64,some 64,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check1788:(cell1788.cap (1:Fin 18)).grade<cell1788.lowerGrade-cell1788.off:=by decide +kernel
private def rows1789 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 56,0,some 0,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,1,some 1,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,2,some 2,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,3,some 3,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,4,some 4,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,5,some 5,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,6,some 6,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,7,some 7,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,8,some 8,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,9,some 9,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,10,some 10,257319,[MeasuredChoices.test62],[]⟩,1,separateWhole⟩]
private theorem paid1789 : StockPairs.checked rows1789 = true := by decide +kernel
theorem route1789 (i : Fin 11) : (rows1789.get i).Done :=
  StockPairs.doneAt paid1789 i

end Research6969.PairReceipts
end Z6969Source2701

-- Source: Research6969.PairReceipts090
section Z6969Source2702
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1800 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 56,11,some 11,257319,[MeasuredChoices.test62],[AxisChoices.test1774]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,12,some 12,257319,[MeasuredChoices.test62],[AxisChoices.test1775]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,13,some 13,257319,[MeasuredChoices.test62],[AxisChoices.test1776]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,14,some 14,257319,[MeasuredChoices.test62],[AxisChoices.test1777]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,15,some 15,257319,[MeasuredChoices.test62],[AxisChoices.test1778]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,16,some 16,257319,[MeasuredChoices.test62],[AxisChoices.test1779]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,17,some 17,257319,[MeasuredChoices.test62],[AxisChoices.test1780]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,18,some 18,257319,[MeasuredChoices.test62],[AxisChoices.test1781]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,19,some 19,257319,[MeasuredChoices.test62],[AxisChoices.test1782]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,20,some 20,257319,[MeasuredChoices.test62],[AxisChoices.test1783]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,21,some 21,257319,[MeasuredChoices.test62],[AxisChoices.test1784]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,22,some 22,257319,[MeasuredChoices.test62],[AxisChoices.test1785]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,23,some 23,257319,[MeasuredChoices.test62],[AxisChoices.test1786]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,24,some 24,257319,[MeasuredChoices.test62],[AxisChoices.test1787]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,25,some 25,257319,[MeasuredChoices.test62],[AxisChoices.test1788]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,26,some 26,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1789]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,27,some 27,257319,[MeasuredChoices.test62],[AxisChoices.test1788,AxisChoices.test1790]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,28,some 28,257319,[MeasuredChoices.test62],[AxisChoices.test1791]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,29,some 29,257319,[MeasuredChoices.test62],[AxisChoices.test1791,AxisChoices.test1792]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,2,49,some 56,30,some 30,257319,[MeasuredChoices.test62],[AxisChoices.test1792,AxisChoices.test1793]⟩,1,markedAxisWhole⟩]
private theorem paid1800 : StockPairs.checked rows1800 = true := by decide +kernel
theorem route1800 (i : Fin 20) : (rows1800.get i).Done :=
  StockPairs.doneAt paid1800 i

end Research6969.PairReceipts
end Z6969Source2702

-- Source: Research6969.PairReceipts091
section Z6969Source2703
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1820 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,2,49,some 56,31,some 31,257319,[MeasuredChoices.test62],[AxisChoices.test1793,AxisChoices.test1794]⟩,1,markedAxisWhole⟩]
private theorem paid1820 : StockPairs.checked rows1820 = true := by decide +kernel
theorem route1820 (i : Fin 1) : (rows1820.get i).Done :=
  StockPairs.doneAt paid1820 i
def cell1821:PairCell.Row:=⟨41,49,9,2,49,some 56,32,some 32,257319,[MeasuredChoices.test62],[AxisChoices.test1795]⟩
theorem check1821:(cell1821.cap (1:Fin 18)).grade<cell1821.lowerGrade-cell1821.off:=by decide +kernel
def cell1822:PairCell.Row:=⟨41,49,9,2,49,some 56,33,some 33,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check1822:(cell1822.cap (1:Fin 18)).grade<cell1822.lowerGrade-cell1822.off:=by decide +kernel
def cell1823:PairCell.Row:=⟨41,49,9,2,49,some 56,34,some 34,257319,[MeasuredChoices.test62],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check1823:(cell1823.cap (1:Fin 18)).grade<cell1823.lowerGrade-cell1823.off:=by decide +kernel
def cell1824:PairCell.Row:=⟨41,49,9,2,49,some 56,35,some 35,257319,[MeasuredChoices.test62],[AxisChoices.test1798]⟩
theorem check1824:(cell1824.cap (1:Fin 18)).grade<cell1824.lowerGrade-cell1824.off:=by decide +kernel
def cell1825:PairCell.Row:=⟨41,49,9,2,49,some 56,36,some 36,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check1825:(cell1825.cap (1:Fin 18)).grade<cell1825.lowerGrade-cell1825.off:=by decide +kernel
def cell1826:PairCell.Row:=⟨41,49,9,2,49,some 56,37,some 37,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check1826:(cell1826.cap (1:Fin 18)).grade<cell1826.lowerGrade-cell1826.off:=by decide +kernel
def cell1827:PairCell.Row:=⟨41,49,9,2,49,some 56,38,some 38,257319,[MeasuredChoices.test62],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check1827:(cell1827.cap (1:Fin 18)).grade<cell1827.lowerGrade-cell1827.off:=by decide +kernel
def cell1828:PairCell.Row:=⟨41,49,9,2,49,some 56,39,some 39,257319,[MeasuredChoices.test62],[AxisChoices.test1802]⟩
theorem check1828:(cell1828.cap (1:Fin 18)).grade<cell1828.lowerGrade-cell1828.off:=by decide +kernel
def cell1829:PairCell.Row:=⟨41,49,9,2,49,some 56,40,some 40,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check1829:(cell1829.cap (1:Fin 18)).grade<cell1829.lowerGrade-cell1829.off:=by decide +kernel
def cell1830:PairCell.Row:=⟨41,49,9,2,49,some 56,41,some 41,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check1830:(cell1830.cap (1:Fin 18)).grade<cell1830.lowerGrade-cell1830.off:=by decide +kernel
def cell1831:PairCell.Row:=⟨41,49,9,2,49,some 56,42,some 42,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check1831:(cell1831.cap (1:Fin 18)).grade<cell1831.lowerGrade-cell1831.off:=by decide +kernel
def cell1832:PairCell.Row:=⟨41,49,9,2,49,some 56,43,some 43,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check1832:(cell1832.cap (1:Fin 18)).grade<cell1832.lowerGrade-cell1832.off:=by decide +kernel
def cell1833:PairCell.Row:=⟨41,49,9,2,49,some 56,44,some 44,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check1833:(cell1833.cap (1:Fin 18)).grade<cell1833.lowerGrade-cell1833.off:=by decide +kernel
def cell1834:PairCell.Row:=⟨41,49,9,2,49,some 56,45,some 45,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check1834:(cell1834.cap (1:Fin 18)).grade<cell1834.lowerGrade-cell1834.off:=by decide +kernel
def cell1835:PairCell.Row:=⟨41,49,9,2,49,some 56,46,some 46,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check1835:(cell1835.cap (1:Fin 18)).grade<cell1835.lowerGrade-cell1835.off:=by decide +kernel
def cell1836:PairCell.Row:=⟨41,49,9,2,49,some 56,47,some 47,257319,[MeasuredChoices.test62],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check1836:(cell1836.cap (1:Fin 18)).grade<cell1836.lowerGrade-cell1836.off:=by decide +kernel
def cell1837:PairCell.Row:=⟨41,49,9,2,49,some 56,48,some 48,257319,[MeasuredChoices.test62],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check1837:(cell1837.cap (1:Fin 18)).grade<cell1837.lowerGrade-cell1837.off:=by decide +kernel
def cell1838:PairCell.Row:=⟨41,49,9,2,49,some 56,49,some 49,257319,[MeasuredChoices.test62],[AxisChoices.test1812]⟩
theorem check1838:(cell1838.cap (1:Fin 18)).grade<cell1838.lowerGrade-cell1838.off:=by decide +kernel
def cell1839:PairCell.Row:=⟨41,49,9,2,49,some 56,50,some 50,257319,[MeasuredChoices.test62],[AxisChoices.test1813]⟩
theorem check1839:(cell1839.cap (1:Fin 18)).grade<cell1839.lowerGrade-cell1839.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2703

-- Source: Research6969.PairReceipts101
section Z6969Source2704
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2020 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,15,some 15,13,some 13,385979,[MeasuredChoices.test797],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,14,some 14,385979,[MeasuredChoices.test797],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,15,some 15,385979,[MeasuredChoices.test797],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,14,some 14,0,none,385979,[MeasuredChoices.test785],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,13,some 13,0,none,385979,[MeasuredChoices.test770],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,9,some 12,0,none,385979,[MeasuredChoices.test724],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,4,some 8,0,none,385979,[MeasuredChoices.test671],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,61,some 64,0,none,257319,[MeasuredChoices.test82,MeasuredChoices.test85],[]⟩,1,markedWhole⟩,
  ⟨⟨50,63,10,2,59,some 60,0,none,257319,[MeasuredChoices.test82],[]⟩,1,markedWhole⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test81],[]⟩,1,⟨(.node 8025893007439878),.intersection,.impossible,283522⟩⟩,
  ⟨⟨50,63,10,2,58,some 58,0,none,283522,[MeasuredChoices.test106,MeasuredChoices.test107],[]⟩,1,markedWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,0,some 0,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,1,some 1,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,2,some 2,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,3,some 3,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,4,some 4,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,5,some 5,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,6,some 6,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,7,some 7,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,8,some 8,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩]
private theorem paid2020 : StockPairs.checked rows2020 = true := by decide +kernel
theorem route2020 (i : Fin 20) : (rows2020.get i).Done :=
  StockPairs.doneAt paid2020 i

end Research6969.PairReceipts
end Z6969Source2704

-- Source: Research6969.HardFit2At100
section Z6969Source2705
set_option autoImplicit true
namespace Research6969.HardFit2At100
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1846 5)
theorem case100: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,21,some 24⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1846 3)
private def leaf2 := (PairReceipts.route1846 4)
private def weight3 := PairRoute.weight 302619 leaf1 leaf2
theorem case101: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,25,some 28⟩:=PairRoute.start _ weight3
private def leaf4 := (PairReceipts.route1846 2)
theorem case102: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,29,some 32⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1846 1)
theorem case103: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,33,some 40⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1846 0)
theorem case104: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,41,some 48⟩:=PairRoute.start _ leaf6
private theorem allAxes120:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,49,some 56⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 56 ⟨
    (PairReceipts.route1789 0),
    (PairReceipts.route1789 1),
    (PairReceipts.route1789 2),
    (PairReceipts.route1789 3),
    (PairReceipts.route1789 4),
    (PairReceipts.route1789 5),
    (PairReceipts.route1789 6),
    (PairReceipts.route1789 7),
    (PairReceipts.route1789 8),
    (PairReceipts.route1789 9),
    (PairReceipts.route1789 10),
    (PairReceipts.route1800 0),
    (PairReceipts.route1800 1),
    (PairReceipts.route1800 2),
    (PairReceipts.route1800 3),
    (PairReceipts.route1800 4),
    (PairReceipts.route1800 5),
    (PairReceipts.route1800 6),
    (PairReceipts.route1800 7),
    (PairReceipts.route1800 8),
    (PairReceipts.route1800 9),
    (PairReceipts.route1800 10),
    (PairReceipts.route1800 11),
    (PairReceipts.route1800 12),
    (PairReceipts.route1800 13),
    (PairReceipts.route1800 14),
    (PairReceipts.route1800 15),
    (PairReceipts.route1800 16),
    (PairReceipts.route1800 17),
    (PairReceipts.route1800 18),
    (PairReceipts.route1800 19),
    (PairReceipts.route1820 0),
    PairLeaves.excluded PairReceipts.cell1821 PairReceipts.check1821 (none),
    PairLeaves.excluded PairReceipts.cell1822 PairReceipts.check1822 (none),
    PairLeaves.excluded PairReceipts.cell1823 PairReceipts.check1823 (none),
    PairLeaves.excluded PairReceipts.cell1824 PairReceipts.check1824 (none),
    PairLeaves.excluded PairReceipts.cell1825 PairReceipts.check1825 (none),
    PairLeaves.excluded PairReceipts.cell1826 PairReceipts.check1826 (none),
    PairLeaves.excluded PairReceipts.cell1827 PairReceipts.check1827 (none),
    PairLeaves.excluded PairReceipts.cell1828 PairReceipts.check1828 (none),
    PairLeaves.excluded PairReceipts.cell1829 PairReceipts.check1829 (none),
    PairLeaves.excluded PairReceipts.cell1830 PairReceipts.check1830 (none),
    PairLeaves.excluded PairReceipts.cell1831 PairReceipts.check1831 (none),
    PairLeaves.excluded PairReceipts.cell1832 PairReceipts.check1832 (none),
    PairLeaves.excluded PairReceipts.cell1833 PairReceipts.check1833 (none),
    PairLeaves.excluded PairReceipts.cell1834 PairReceipts.check1834 (none),
    PairLeaves.excluded PairReceipts.cell1835 PairReceipts.check1835 (none),
    PairLeaves.excluded PairReceipts.cell1836 PairReceipts.check1836 (none),
    PairLeaves.excluded PairReceipts.cell1837 PairReceipts.check1837 (none),
    PairLeaves.excluded PairReceipts.cell1838 PairReceipts.check1838 (none),
    PairLeaves.excluded PairReceipts.cell1839 PairReceipts.check1839 (none),
    PairLeaves.excluded PairReceipts.cell1840 PairReceipts.check1840 (none),
    PairLeaves.excluded PairReceipts.cell1841 PairReceipts.check1841 (none),
    PairLeaves.excluded PairReceipts.cell1842 PairReceipts.check1842 (none),
    PairLeaves.excluded PairReceipts.cell1843 PairReceipts.check1843 (none),
    PairLeaves.excluded PairReceipts.cell1844 PairReceipts.check1844 (none),
    PairLeaves.excluded PairReceipts.cell1845 PairReceipts.check1845 (none),
    trivial⟩)
theorem case105: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,49,some 56⟩:=PairRoute.start _ allAxes120
private theorem allAxes250:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,2,57,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route1720 4),
    (PairReceipts.route1720 5),
    (PairReceipts.route1720 6),
    (PairReceipts.route1720 7),
    (PairReceipts.route1720 8),
    (PairReceipts.route1720 9),
    (PairReceipts.route1720 10),
    (PairReceipts.route1720 11),
    (PairReceipts.route1720 12),
    (PairReceipts.route1720 13),
    (PairReceipts.route1720 14),
    (PairReceipts.route1720 15),
    (PairReceipts.route1720 16),
    (PairReceipts.route1720 17),
    (PairReceipts.route1720 18),
    (PairReceipts.route1720 19),
    (PairReceipts.route1740 0),
    (PairReceipts.route1740 1),
    (PairReceipts.route1740 2),
    (PairReceipts.route1740 3),
    (PairReceipts.route1740 4),
    (PairReceipts.route1740 5),
    (PairReceipts.route1740 6),
    (PairReceipts.route1740 7),
    (PairReceipts.route1740 8),
    (PairReceipts.route1740 9),
    (PairReceipts.route1740 10),
    (PairReceipts.route1740 11),
    (PairReceipts.route1740 12),
    (PairReceipts.route1740 13),
    (PairReceipts.route1740 14),
    (PairReceipts.route1740 15),
    PairLeaves.excluded PairReceipts.cell1756 PairReceipts.check1756 (none),
    PairLeaves.excluded PairReceipts.cell1757 PairReceipts.check1757 (none),
    PairLeaves.excluded PairReceipts.cell1758 PairReceipts.check1758 (none),
    PairLeaves.excluded PairReceipts.cell1759 PairReceipts.check1759 (none),
    PairLeaves.excluded PairReceipts.cell1760 PairReceipts.check1760 (none),
    PairLeaves.excluded PairReceipts.cell1761 PairReceipts.check1761 (none),
    PairLeaves.excluded PairReceipts.cell1762 PairReceipts.check1762 (none),
    PairLeaves.excluded PairReceipts.cell1763 PairReceipts.check1763 (none),
    PairLeaves.excluded PairReceipts.cell1764 PairReceipts.check1764 (none),
    PairLeaves.excluded PairReceipts.cell1765 PairReceipts.check1765 (none),
    PairLeaves.excluded PairReceipts.cell1766 PairReceipts.check1766 (none),
    PairLeaves.excluded PairReceipts.cell1767 PairReceipts.check1767 (none),
    PairLeaves.excluded PairReceipts.cell1768 PairReceipts.check1768 (none),
    PairLeaves.excluded PairReceipts.cell1769 PairReceipts.check1769 (none),
    PairLeaves.excluded PairReceipts.cell1770 PairReceipts.check1770 (none),
    PairLeaves.excluded PairReceipts.cell1771 PairReceipts.check1771 (none),
    PairLeaves.excluded PairReceipts.cell1772 PairReceipts.check1772 (none),
    PairLeaves.excluded PairReceipts.cell1773 PairReceipts.check1773 (none),
    PairLeaves.excluded PairReceipts.cell1774 PairReceipts.check1774 (none),
    PairLeaves.excluded PairReceipts.cell1775 PairReceipts.check1775 (none),
    PairLeaves.excluded PairReceipts.cell1776 PairReceipts.check1776 (none),
    PairLeaves.excluded PairReceipts.cell1777 PairReceipts.check1777 (none),
    PairLeaves.excluded PairReceipts.cell1778 PairReceipts.check1778 (none),
    PairLeaves.excluded PairReceipts.cell1779 PairReceipts.check1779 (none),
    PairLeaves.excluded PairReceipts.cell1780 PairReceipts.check1780 (none),
    PairLeaves.excluded PairReceipts.cell1781 PairReceipts.check1781 (none),
    PairLeaves.excluded PairReceipts.cell1782 PairReceipts.check1782 (none),
    PairLeaves.excluded PairReceipts.cell1783 PairReceipts.check1783 (none),
    PairLeaves.excluded PairReceipts.cell1784 PairReceipts.check1784 (none),
    PairLeaves.excluded PairReceipts.cell1785 PairReceipts.check1785 (none),
    PairLeaves.excluded PairReceipts.cell1786 PairReceipts.check1786 (none),
    PairLeaves.excluded PairReceipts.cell1787 PairReceipts.check1787 (none),
    PairLeaves.excluded PairReceipts.cell1788 PairReceipts.check1788 (none),
    trivial⟩)
theorem case106: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,57,some 64⟩:=PairRoute.start _ allAxes250
private def leaf251 := (PairReceipts.route1720 3)
theorem case107: NormalRoute.Done (1:Fin 18) ⟨41,49,9,2,65,some 96⟩:=PairRoute.start _ leaf251
private def leaf252 := (PairReceipts.route2020 6)
theorem case108: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,4,some 8⟩:=PairRoute.start _ leaf252
private def leaf253 := (PairReceipts.route2020 5)
theorem case109: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf253
end Research6969.HardFit2At100
end Z6969Source2705

-- Source: Research6969.PairReceipts093
section Z6969Source2706
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1860 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,26,some 26,0,none,385979,[MeasuredChoices.test939],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,25,some 25,0,none,385979,[MeasuredChoices.test924],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,24,some 24,0,none,385979,[MeasuredChoices.test910],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,23,some 23,0,none,385979,[MeasuredChoices.test896],[]⟩,1,surfaceWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,0,some 0,385979,[MeasuredChoices.test882],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,1,some 1,385979,[MeasuredChoices.test882],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,2,some 2,385979,[MeasuredChoices.test882],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,3,some 3,385979,[MeasuredChoices.test882],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,4,some 4,385979,[MeasuredChoices.test882],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,5,some 5,385979,[MeasuredChoices.test882],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,6,some 6,385979,[MeasuredChoices.test882],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,7,some 7,385979,[MeasuredChoices.test882],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,8,some 8,385979,[MeasuredChoices.test882],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,9,some 9,385979,[MeasuredChoices.test882],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,10,some 10,385979,[MeasuredChoices.test882],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,11,some 11,385979,[MeasuredChoices.test882],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,12,some 12,385979,[MeasuredChoices.test882],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩]
private theorem paid1860 : StockPairs.checked rows1860 = true := by decide +kernel
theorem route1860 (i : Fin 20) : (rows1860.get i).Done :=
  StockPairs.doneAt paid1860 i

end Research6969.PairReceipts
end Z6969Source2706

-- Source: Research6969.PairReceipts094
section Z6969Source2707
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1880 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,22,some 22,13,some 13,385979,[MeasuredChoices.test882],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,14,some 14,385979,[MeasuredChoices.test882],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,15,some 15,385979,[MeasuredChoices.test882],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,16,some 16,385979,[MeasuredChoices.test882],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,17,some 17,385979,[MeasuredChoices.test882],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,18,some 18,385979,[MeasuredChoices.test882],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,19,some 19,385979,[MeasuredChoices.test882],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,20,some 20,385979,[MeasuredChoices.test882],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,21,some 21,385979,[MeasuredChoices.test882],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,22,some 22,22,some 22,385979,[MeasuredChoices.test882],[AxisChoices.test1843]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,0,some 0,385979,[MeasuredChoices.test869],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,1,some 1,385979,[MeasuredChoices.test869],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,2,some 2,385979,[MeasuredChoices.test869],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,3,some 3,385979,[MeasuredChoices.test869],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,4,some 4,385979,[MeasuredChoices.test869],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,5,some 5,385979,[MeasuredChoices.test869],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,6,some 6,385979,[MeasuredChoices.test869],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,7,some 7,385979,[MeasuredChoices.test869],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,8,some 8,385979,[MeasuredChoices.test869],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,9,some 9,385979,[MeasuredChoices.test869],[AxisChoices.test1830]⟩,1,separateWhole⟩]
private theorem paid1880 : StockPairs.checked rows1880 = true := by decide +kernel
theorem route1880 (i : Fin 20) : (rows1880.get i).Done :=
  StockPairs.doneAt paid1880 i

end Research6969.PairReceipts
end Z6969Source2707

-- Source: Research6969.PairReceipts095
section Z6969Source2708
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1900 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,21,some 21,10,some 10,385979,[MeasuredChoices.test869],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,11,some 11,385979,[MeasuredChoices.test869],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,12,some 12,385979,[MeasuredChoices.test869],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,13,some 13,385979,[MeasuredChoices.test869],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,14,some 14,385979,[MeasuredChoices.test869],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,15,some 15,385979,[MeasuredChoices.test869],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,16,some 16,385979,[MeasuredChoices.test869],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,17,some 17,385979,[MeasuredChoices.test869],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,18,some 18,385979,[MeasuredChoices.test869],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,19,some 19,385979,[MeasuredChoices.test869],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,20,some 20,385979,[MeasuredChoices.test869],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,21,some 21,21,some 21,385979,[MeasuredChoices.test869],[AxisChoices.test1842]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,0,some 0,385979,[MeasuredChoices.test856],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,1,some 1,385979,[MeasuredChoices.test856],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,2,some 2,385979,[MeasuredChoices.test856],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,3,some 3,385979,[MeasuredChoices.test856],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,4,some 4,385979,[MeasuredChoices.test856],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,5,some 5,385979,[MeasuredChoices.test856],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,6,some 6,385979,[MeasuredChoices.test856],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,7,some 7,385979,[MeasuredChoices.test856],[AxisChoices.test1828]⟩,1,separateWhole⟩]
private theorem paid1900 : StockPairs.checked rows1900 = true := by decide +kernel
theorem route1900 (i : Fin 20) : (rows1900.get i).Done :=
  StockPairs.doneAt paid1900 i

end Research6969.PairReceipts
end Z6969Source2708

-- Source: Research6969.PairReceipts096
section Z6969Source2709
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1920 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,20,some 20,8,some 8,385979,[MeasuredChoices.test856],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,9,some 9,385979,[MeasuredChoices.test856],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,10,some 10,385979,[MeasuredChoices.test856],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,11,some 11,385979,[MeasuredChoices.test856],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,12,some 12,385979,[MeasuredChoices.test856],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,13,some 13,385979,[MeasuredChoices.test856],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,14,some 14,385979,[MeasuredChoices.test856],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,15,some 15,385979,[MeasuredChoices.test856],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,16,some 16,385979,[MeasuredChoices.test856],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,17,some 17,385979,[MeasuredChoices.test856],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,18,some 18,385979,[MeasuredChoices.test856],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,19,some 19,385979,[MeasuredChoices.test856],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,20,some 20,20,some 20,385979,[MeasuredChoices.test856],[AxisChoices.test1841]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,0,some 0,385979,[MeasuredChoices.test843],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,1,some 1,385979,[MeasuredChoices.test843],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,2,some 2,385979,[MeasuredChoices.test843],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,3,some 3,385979,[MeasuredChoices.test843],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,4,some 4,385979,[MeasuredChoices.test843],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,5,some 5,385979,[MeasuredChoices.test843],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,6,some 6,385979,[MeasuredChoices.test843],[AxisChoices.test1827]⟩,1,separateWhole⟩]
private theorem paid1920 : StockPairs.checked rows1920 = true := by decide +kernel
theorem route1920 (i : Fin 20) : (rows1920.get i).Done :=
  StockPairs.doneAt paid1920 i

end Research6969.PairReceipts
end Z6969Source2709

-- Source: Research6969.PairReceipts097
section Z6969Source2710
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1940 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,19,some 19,7,some 7,385979,[MeasuredChoices.test843],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,8,some 8,385979,[MeasuredChoices.test843],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,9,some 9,385979,[MeasuredChoices.test843],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,10,some 10,385979,[MeasuredChoices.test843],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,11,some 11,385979,[MeasuredChoices.test843],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,12,some 12,385979,[MeasuredChoices.test843],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,13,some 13,385979,[MeasuredChoices.test843],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,14,some 14,385979,[MeasuredChoices.test843],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,15,some 15,385979,[MeasuredChoices.test843],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,16,some 16,385979,[MeasuredChoices.test843],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,17,some 17,385979,[MeasuredChoices.test843],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,18,some 18,385979,[MeasuredChoices.test843],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,19,some 19,19,some 19,385979,[MeasuredChoices.test843],[AxisChoices.test1840]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,0,some 0,385979,[MeasuredChoices.test831],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,1,some 1,385979,[MeasuredChoices.test831],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,2,some 2,385979,[MeasuredChoices.test831],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,3,some 3,385979,[MeasuredChoices.test831],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,4,some 4,385979,[MeasuredChoices.test831],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,5,some 5,385979,[MeasuredChoices.test831],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,6,some 6,385979,[MeasuredChoices.test831],[AxisChoices.test1827]⟩,1,separateWhole⟩]
private theorem paid1940 : StockPairs.checked rows1940 = true := by decide +kernel
theorem route1940 (i : Fin 20) : (rows1940.get i).Done :=
  StockPairs.doneAt paid1940 i

end Research6969.PairReceipts
end Z6969Source2710
