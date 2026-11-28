import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0671
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0951
import ProximityPrize.SubmissionLower.Z6969Pack0939
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0950

set_option Elab.async false

-- Source: Research6969.HardFit3At090
section Z6969Source2783
set_option autoImplicit true
namespace Research6969.HardFit3At090
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2768 0)
theorem case90: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,41,some 48⟩:=PairRoute.start _ leaf0
private theorem allAxes130:PairRoute.Done (2:Fin 18) ⟨⟨41,49,9,2,49,some 64⟩,0,none,257319,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 64 ⟨
    (PairReceipts.route2700 3),
    (PairReceipts.route2700 4),
    (PairReceipts.route2700 5),
    (PairReceipts.route2700 6),
    (PairReceipts.route2700 7),
    (PairReceipts.route2700 8),
    (PairReceipts.route2700 9),
    (PairReceipts.route2700 10),
    (PairReceipts.route2700 11),
    (PairReceipts.route2700 12),
    (PairReceipts.route2700 13),
    (PairReceipts.route2700 14),
    (PairReceipts.route2700 15),
    (PairReceipts.route2700 16),
    (PairReceipts.route2700 17),
    (PairReceipts.route2700 18),
    (PairReceipts.route2700 19),
    (PairReceipts.route2720 0),
    (PairReceipts.route2720 1),
    (PairReceipts.route2720 2),
    (PairReceipts.route2720 3),
    (PairReceipts.route2720 4),
    (PairReceipts.route2720 5),
    (PairReceipts.route2720 6),
    (PairReceipts.route2720 7),
    (PairReceipts.route2720 8),
    (PairReceipts.route2720 9),
    (PairReceipts.route2720 10),
    (PairReceipts.route2720 11),
    (PairReceipts.route2720 12),
    (PairReceipts.route2720 13),
    (PairReceipts.route2720 14),
    PairLeaves.excluded PairReceipts.cell2735 PairReceipts.check2735 (none),
    PairLeaves.excluded PairReceipts.cell2736 PairReceipts.check2736 (none),
    PairLeaves.excluded PairReceipts.cell2737 PairReceipts.check2737 (none),
    PairLeaves.excluded PairReceipts.cell2738 PairReceipts.check2738 (none),
    PairLeaves.excluded PairReceipts.cell2739 PairReceipts.check2739 (none),
    PairLeaves.excluded PairReceipts.cell2740 PairReceipts.check2740 (none),
    PairLeaves.excluded PairReceipts.cell2741 PairReceipts.check2741 (none),
    PairLeaves.excluded PairReceipts.cell2742 PairReceipts.check2742 (none),
    PairLeaves.excluded PairReceipts.cell2743 PairReceipts.check2743 (none),
    PairLeaves.excluded PairReceipts.cell2744 PairReceipts.check2744 (none),
    PairLeaves.excluded PairReceipts.cell2745 PairReceipts.check2745 (none),
    PairLeaves.excluded PairReceipts.cell2746 PairReceipts.check2746 (none),
    PairLeaves.excluded PairReceipts.cell2747 PairReceipts.check2747 (none),
    PairLeaves.excluded PairReceipts.cell2748 PairReceipts.check2748 (none),
    PairLeaves.excluded PairReceipts.cell2749 PairReceipts.check2749 (none),
    PairLeaves.excluded PairReceipts.cell2750 PairReceipts.check2750 (none),
    PairLeaves.excluded PairReceipts.cell2751 PairReceipts.check2751 (none),
    PairLeaves.excluded PairReceipts.cell2752 PairReceipts.check2752 (none),
    PairLeaves.excluded PairReceipts.cell2753 PairReceipts.check2753 (none),
    PairLeaves.excluded PairReceipts.cell2754 PairReceipts.check2754 (none),
    PairLeaves.excluded PairReceipts.cell2755 PairReceipts.check2755 (none),
    PairLeaves.excluded PairReceipts.cell2756 PairReceipts.check2756 (none),
    PairLeaves.excluded PairReceipts.cell2757 PairReceipts.check2757 (none),
    PairLeaves.excluded PairReceipts.cell2758 PairReceipts.check2758 (none),
    PairLeaves.excluded PairReceipts.cell2759 PairReceipts.check2759 (none),
    PairLeaves.excluded PairReceipts.cell2760 PairReceipts.check2760 (none),
    PairLeaves.excluded PairReceipts.cell2761 PairReceipts.check2761 (none),
    PairLeaves.excluded PairReceipts.cell2762 PairReceipts.check2762 (none),
    PairLeaves.excluded PairReceipts.cell2763 PairReceipts.check2763 (none),
    PairLeaves.excluded PairReceipts.cell2764 PairReceipts.check2764 (none),
    PairLeaves.excluded PairReceipts.cell2765 PairReceipts.check2765 (none),
    PairLeaves.excluded PairReceipts.cell2766 PairReceipts.check2766 (none),
    PairLeaves.excluded PairReceipts.cell2767 PairReceipts.check2767 (none),
    trivial⟩)
theorem case91: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,49,some 64⟩:=PairRoute.start _ allAxes130
private def leaf131 := (PairReceipts.route2700 2)
theorem case92: NormalRoute.Done (2:Fin 18) ⟨41,49,9,2,65,some 96⟩:=PairRoute.start _ leaf131
private def leaf132 := (PairReceipts.route2880 10)
theorem case93: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,4,some 8⟩:=PairRoute.start _ leaf132
private def leaf133 := (PairReceipts.route2880 9)
theorem case94: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,9,some 12⟩:=PairRoute.start _ leaf133
private def leaf134 := (PairReceipts.route2880 8)
theorem case95: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,13,some 14⟩:=PairRoute.start _ leaf134
private def leaf135 := (PairReceipts.route2880 7)
theorem case96: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,15,some 15⟩:=PairRoute.start _ leaf135
private def leaf136 := (PairReceipts.route2880 6)
theorem case97: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,16,some 16⟩:=PairRoute.start _ leaf136
private def leaf137 := (PairReceipts.route2880 5)
theorem case98: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,17,some 17⟩:=PairRoute.start _ leaf137
private def leaf138 := (PairReceipts.route2880 4)
theorem case99: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,18,some 18⟩:=PairRoute.start _ leaf138
end Research6969.HardFit3At090
end Z6969Source2783

-- Source: Research6969.PairReceipts143
section Z6969Source2784
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2860 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,41,some 44,31,some 31,385979,[MeasuredChoices.test1133],[AxisChoices.test1852]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,32,some 32,385979,[MeasuredChoices.test1133],[AxisChoices.test1853]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,33,some 33,385979,[MeasuredChoices.test1133],[AxisChoices.test1854]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,34,some 34,385979,[MeasuredChoices.test1133],[AxisChoices.test1854,AxisChoices.test1855]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,35,some 35,385979,[MeasuredChoices.test1133],[AxisChoices.test1854,AxisChoices.test1856]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,36,some 36,385979,[MeasuredChoices.test1133],[AxisChoices.test1854,AxisChoices.test1857]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,37,some 37,385979,[MeasuredChoices.test1133],[AxisChoices.test1857,AxisChoices.test1858]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,37,some 40,0,none,385979,[MeasuredChoices.test1079],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,33,some 36,0,none,385979,[MeasuredChoices.test1029],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,29,some 32,0,none,385979,[MeasuredChoices.test977],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,25,some 26,0,none,385979,[MeasuredChoices.test924],[]⟩,2,surfaceIntersection⟩,
  ⟨⟨41,49,9,3,23,some 24,0,none,385979,[MeasuredChoices.test896],[]⟩,2,surfaceIntersection⟩]
private theorem paid2860 : StockPairs.checked rows2860 = true := by decide +kernel
theorem route2860 (i : Fin 13) : (rows2860.get i).Done :=
  StockPairs.doneAt paid2860 i

def cell2867:PairCell.Row:=⟨41,49,9,3,41,some 44,38,some 38,385979,[MeasuredChoices.test1133],[AxisChoices.test1859]⟩
theorem check2867:(cell2867.cap (2:Fin 18)).grade<cell2867.lowerGrade-cell2867.off:=by decide +kernel
def cell2868:PairCell.Row:=⟨41,49,9,3,41,some 44,39,some 39,385979,[MeasuredChoices.test1133],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2868:(cell2868.cap (2:Fin 18)).grade<cell2868.lowerGrade-cell2868.off:=by decide +kernel
def cell2869:PairCell.Row:=⟨41,49,9,3,41,some 44,40,some 40,385979,[MeasuredChoices.test1133],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2869:(cell2869.cap (2:Fin 18)).grade<cell2869.lowerGrade-cell2869.off:=by decide +kernel
def cell2870:PairCell.Row:=⟨41,49,9,3,41,some 44,41,some 41,385979,[MeasuredChoices.test1133],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2870:(cell2870.cap (2:Fin 18)).grade<cell2870.lowerGrade-cell2870.off:=by decide +kernel
def cell2871:PairCell.Row:=⟨41,49,9,3,41,some 44,42,some 42,385979,[MeasuredChoices.test1133],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2871:(cell2871.cap (2:Fin 18)).grade<cell2871.lowerGrade-cell2871.off:=by decide +kernel
def cell2872:PairCell.Row:=⟨41,49,9,3,41,some 44,43,some 43,385979,[MeasuredChoices.test1133],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2872:(cell2872.cap (2:Fin 18)).grade<cell2872.lowerGrade-cell2872.off:=by decide +kernel
def cell2873:PairCell.Row:=⟨41,49,9,3,41,some 44,44,some 44,385979,[MeasuredChoices.test1133],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2873:(cell2873.cap (2:Fin 18)).grade<cell2873.lowerGrade-cell2873.off:=by decide +kernel

end Research6969.PairReceipts
end Z6969Source2784

-- Source: Research6969.HardFit3At100
section Z6969Source2785
set_option autoImplicit true
namespace Research6969.HardFit3At100
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2880 3)
theorem case100: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,19,some 19⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2880 2)
theorem case101: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,20,some 20⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route2880 1)
theorem case102: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,21,some 21⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route2880 0)
theorem case103: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,22,some 22⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route2860 12)
theorem case104: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,23,some 24⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2860 11)
theorem case105: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,25,some 26⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route2860 10)
theorem case106: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,27,some 28⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route2860 9)
theorem case107: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,29,some 32⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route2860 8)
theorem case108: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,33,some 36⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route2860 7)
theorem case109: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,37,some 40⟩:=PairRoute.start _ leaf9
end Research6969.HardFit3At100
end Z6969Source2785

-- Source: Research6969.PairReceipts139
section Z6969Source2786
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2780 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,45,some 48,0,some 0,385979,[MeasuredChoices.test1139],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,1,some 1,385979,[MeasuredChoices.test1139],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,2,some 2,385979,[MeasuredChoices.test1139],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,3,some 3,385979,[MeasuredChoices.test1139],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,4,some 4,385979,[MeasuredChoices.test1139],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,5,some 5,385979,[MeasuredChoices.test1139],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,6,some 6,385979,[MeasuredChoices.test1139],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,7,some 7,385979,[MeasuredChoices.test1139],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,8,some 8,385979,[MeasuredChoices.test1139],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,9,some 9,385979,[MeasuredChoices.test1139],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,10,some 10,385979,[MeasuredChoices.test1139],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,11,some 11,385979,[MeasuredChoices.test1139],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,12,some 12,385979,[MeasuredChoices.test1139],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,13,some 13,385979,[MeasuredChoices.test1139],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,14,some 14,385979,[MeasuredChoices.test1139],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,15,some 15,385979,[MeasuredChoices.test1139],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,16,some 16,385979,[MeasuredChoices.test1139],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,17,some 17,385979,[MeasuredChoices.test1139],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,18,some 18,385979,[MeasuredChoices.test1139],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,19,some 19,385979,[MeasuredChoices.test1139],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩]
private theorem paid2780 : StockPairs.checked rows2780 = true := by decide +kernel
theorem route2780 (i : Fin 20) : (rows2780.get i).Done :=
  StockPairs.doneAt paid2780 i

end Research6969.PairReceipts
end Z6969Source2786

-- Source: Research6969.PairReceipts140
section Z6969Source2787
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2800 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,45,some 48,20,some 20,385979,[MeasuredChoices.test1139],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,21,some 21,385979,[MeasuredChoices.test1139],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,22,some 22,385979,[MeasuredChoices.test1139],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,23,some 23,385979,[MeasuredChoices.test1139],[AxisChoices.test1844]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,24,some 24,385979,[MeasuredChoices.test1139],[AxisChoices.test1845]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,25,some 25,385979,[MeasuredChoices.test1139],[AxisChoices.test1845,AxisChoices.test1846]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,26,some 26,385979,[MeasuredChoices.test1139],[AxisChoices.test1847]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,27,some 27,385979,[MeasuredChoices.test1139],[AxisChoices.test1848]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,28,some 28,385979,[MeasuredChoices.test1139],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,29,some 29,385979,[MeasuredChoices.test1139],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,30,some 30,385979,[MeasuredChoices.test1139],[AxisChoices.test1848,AxisChoices.test1851]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,31,some 31,385979,[MeasuredChoices.test1139],[AxisChoices.test1852]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,32,some 32,385979,[MeasuredChoices.test1139],[AxisChoices.test1853]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,33,some 33,385979,[MeasuredChoices.test1139],[AxisChoices.test1854]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,34,some 34,385979,[MeasuredChoices.test1139],[AxisChoices.test1854,AxisChoices.test1855]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,35,some 35,385979,[MeasuredChoices.test1139],[AxisChoices.test1854,AxisChoices.test1856]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,36,some 36,385979,[MeasuredChoices.test1139],[AxisChoices.test1854,AxisChoices.test1857]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,45,some 48,37,some 37,385979,[MeasuredChoices.test1139],[AxisChoices.test1857,AxisChoices.test1858]⟩,2,markedAxisIntersection⟩]
private theorem paid2800 : StockPairs.checked rows2800 = true := by decide +kernel
theorem route2800 (i : Fin 18) : (rows2800.get i).Done :=
  StockPairs.doneAt paid2800 i

def cell2818:PairCell.Row:=⟨41,49,9,3,45,some 48,38,some 38,385979,[MeasuredChoices.test1139],[AxisChoices.test1859]⟩
theorem check2818:(cell2818.cap (2:Fin 18)).grade<cell2818.lowerGrade-cell2818.off:=by decide +kernel
def cell2819:PairCell.Row:=⟨41,49,9,3,45,some 48,39,some 39,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2819:(cell2819.cap (2:Fin 18)).grade<cell2819.lowerGrade-cell2819.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2787

-- Source: Research6969.PairReceipts141
section Z6969Source2788
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell2820:PairCell.Row:=⟨41,49,9,3,45,some 48,40,some 40,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2820:(cell2820.cap (2:Fin 18)).grade<cell2820.lowerGrade-cell2820.off:=by decide +kernel
def cell2821:PairCell.Row:=⟨41,49,9,3,45,some 48,41,some 41,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2821:(cell2821.cap (2:Fin 18)).grade<cell2821.lowerGrade-cell2821.off:=by decide +kernel
def cell2822:PairCell.Row:=⟨41,49,9,3,45,some 48,42,some 42,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2822:(cell2822.cap (2:Fin 18)).grade<cell2822.lowerGrade-cell2822.off:=by decide +kernel
def cell2823:PairCell.Row:=⟨41,49,9,3,45,some 48,43,some 43,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2823:(cell2823.cap (2:Fin 18)).grade<cell2823.lowerGrade-cell2823.off:=by decide +kernel
def cell2824:PairCell.Row:=⟨41,49,9,3,45,some 48,44,some 44,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2824:(cell2824.cap (2:Fin 18)).grade<cell2824.lowerGrade-cell2824.off:=by decide +kernel
def cell2825:PairCell.Row:=⟨41,49,9,3,45,some 48,45,some 45,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2825:(cell2825.cap (2:Fin 18)).grade<cell2825.lowerGrade-cell2825.off:=by decide +kernel
def cell2826:PairCell.Row:=⟨41,49,9,3,45,some 48,46,some 46,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2826:(cell2826.cap (2:Fin 18)).grade<cell2826.lowerGrade-cell2826.off:=by decide +kernel
def cell2827:PairCell.Row:=⟨41,49,9,3,45,some 48,47,some 47,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2827:(cell2827.cap (2:Fin 18)).grade<cell2827.lowerGrade-cell2827.off:=by decide +kernel
def cell2828:PairCell.Row:=⟨41,49,9,3,45,some 48,48,some 48,385979,[MeasuredChoices.test1139],[AxisChoices.test1859,AxisChoices.test1860]⟩
theorem check2828:(cell2828.cap (2:Fin 18)).grade<cell2828.lowerGrade-cell2828.off:=by decide +kernel
private def rows2829 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,41,some 44,0,some 0,385979,[MeasuredChoices.test1133],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,1,some 1,385979,[MeasuredChoices.test1133],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,2,some 2,385979,[MeasuredChoices.test1133],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,3,some 3,385979,[MeasuredChoices.test1133],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,4,some 4,385979,[MeasuredChoices.test1133],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,5,some 5,385979,[MeasuredChoices.test1133],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,6,some 6,385979,[MeasuredChoices.test1133],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,7,some 7,385979,[MeasuredChoices.test1133],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,8,some 8,385979,[MeasuredChoices.test1133],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,9,some 9,385979,[MeasuredChoices.test1133],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,10,some 10,385979,[MeasuredChoices.test1133],[AxisChoices.test1831]⟩,2,separateIntersection⟩]
private theorem paid2829 : StockPairs.checked rows2829 = true := by decide +kernel
theorem route2829 (i : Fin 11) : (rows2829.get i).Done :=
  StockPairs.doneAt paid2829 i

end Research6969.PairReceipts
end Z6969Source2788

-- Source: Research6969.PairReceipts142
section Z6969Source2789
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2840 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,41,some 44,11,some 11,385979,[MeasuredChoices.test1133],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,12,some 12,385979,[MeasuredChoices.test1133],[AxisChoices.test1833]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,13,some 13,385979,[MeasuredChoices.test1133],[AxisChoices.test1834]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,14,some 14,385979,[MeasuredChoices.test1133],[AxisChoices.test1835]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,15,some 15,385979,[MeasuredChoices.test1133],[AxisChoices.test1836]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,16,some 16,385979,[MeasuredChoices.test1133],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,17,some 17,385979,[MeasuredChoices.test1133],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,18,some 18,385979,[MeasuredChoices.test1133],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,19,some 19,385979,[MeasuredChoices.test1133],[AxisChoices.test1840]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,20,some 20,385979,[MeasuredChoices.test1133],[AxisChoices.test1841]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,21,some 21,385979,[MeasuredChoices.test1133],[AxisChoices.test1842]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,22,some 22,385979,[MeasuredChoices.test1133],[AxisChoices.test1843]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,23,some 23,385979,[MeasuredChoices.test1133],[AxisChoices.test1844]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,24,some 24,385979,[MeasuredChoices.test1133],[AxisChoices.test1845]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,25,some 25,385979,[MeasuredChoices.test1133],[AxisChoices.test1845,AxisChoices.test1846]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,26,some 26,385979,[MeasuredChoices.test1133],[AxisChoices.test1847]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,27,some 27,385979,[MeasuredChoices.test1133],[AxisChoices.test1848]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,28,some 28,385979,[MeasuredChoices.test1133],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,29,some 29,385979,[MeasuredChoices.test1133],[AxisChoices.test1848,AxisChoices.test1849]⟩,2,markedAxisIntersection⟩,
  ⟨⟨41,49,9,3,41,some 44,30,some 30,385979,[MeasuredChoices.test1133],[AxisChoices.test1848,AxisChoices.test1851]⟩,2,markedAxisIntersection⟩]
private theorem paid2840 : StockPairs.checked rows2840 = true := by decide +kernel
theorem route2840 (i : Fin 20) : (rows2840.get i).Done :=
  StockPairs.doneAt paid2840 i

end Research6969.PairReceipts
end Z6969Source2789

-- Source: Research6969.PairReceipts156
section Z6969Source2790
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3120:PairCell.Row:=⟨50,63,10,2,54,some 54,54,some 54,257319,[MeasuredChoices.test73],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check3120:(cell3120.cap (2:Fin 18)).grade<cell3120.lowerGrade-cell3120.off:=by decide +kernel
private def rows3121 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,53,some 53,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test71],[]⟩,2,⟨(.node 8027880449706932),.intersection,.impossible,287630⟩⟩,
  ⟨⟨50,63,10,2,53,some 53,0,none,287630,[MeasuredChoices.test70,MeasuredChoices.test113],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,52,some 52,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test69],[]⟩,2,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨50,63,10,2,52,some 52,0,none,288407,[MeasuredChoices.test116,MeasuredChoices.test117],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,51,some 51,0,none,257319,[MeasuredChoices.test64,MeasuredChoices.test66],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,49,some 50,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,2,⟨(.node 8029306683929914),.intersection,.impossible,289917⟩⟩,
  ⟨⟨50,63,10,2,49,some 50,0,none,289917,[MeasuredChoices.test104,MeasuredChoices.test118],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,45,some 48,0,none,257319,[MeasuredChoices.test56],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,41,some 44,0,none,257319,[MeasuredChoices.test50],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,2,⟨(.node 12122407664504094),.intersection,.impossible,304553⟩⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,304553,[MeasuredChoices.test230],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,23,some 24,0,none,257319,[MeasuredChoices.test29],[]⟩,2,⟨(.node 12156969814651320),.intersection,.impossible,305579⟩⟩,
  ⟨⟨50,63,10,2,23,some 24,0,none,305579,[MeasuredChoices.test299],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,21,some 22,0,none,257319,[MeasuredChoices.test25],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,2,surfaceWhole⟩]
private theorem paid3121 : StockPairs.checked rows3121 = true := by decide +kernel
theorem route3121 (i : Fin 19) : (rows3121.get i).Done :=
  StockPairs.doneAt paid3121 i

end Research6969.PairReceipts
end Z6969Source2790

-- Source: Research6969.PairReceipts157
section Z6969Source2791
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3140 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,4,some 8,0,none,257319,[],[]⟩,2,surfaceWhole⟩,
  ⟨⟨50,63,10,3,39,some 39,0,some 0,385979,[MeasuredChoices.test1105],[AxisChoices.test1821]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,1,some 1,385979,[MeasuredChoices.test1105],[AxisChoices.test1822]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,2,some 2,385979,[MeasuredChoices.test1105],[AxisChoices.test1823]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,3,some 3,385979,[MeasuredChoices.test1105],[AxisChoices.test1824]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,4,some 4,385979,[MeasuredChoices.test1105],[AxisChoices.test1825]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,5,some 5,385979,[MeasuredChoices.test1105],[AxisChoices.test1826]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,6,some 6,385979,[MeasuredChoices.test1105],[AxisChoices.test1827]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,7,some 7,385979,[MeasuredChoices.test1105],[AxisChoices.test1828]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,8,some 8,385979,[MeasuredChoices.test1105],[AxisChoices.test1829]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,9,some 9,385979,[MeasuredChoices.test1105],[AxisChoices.test1830]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,10,some 10,385979,[MeasuredChoices.test1105],[AxisChoices.test1831]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,11,some 11,385979,[MeasuredChoices.test1105],[AxisChoices.test1832]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,12,some 12,385979,[MeasuredChoices.test1105],[AxisChoices.test1833]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,13,some 13,385979,[MeasuredChoices.test1105],[AxisChoices.test1834]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,14,some 14,385979,[MeasuredChoices.test1105],[AxisChoices.test1835]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,15,some 15,385979,[MeasuredChoices.test1105],[AxisChoices.test1836]⟩,2,separateIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,16,some 16,385979,[MeasuredChoices.test1105],[AxisChoices.test1837]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,17,some 17,385979,[MeasuredChoices.test1105],[AxisChoices.test1838]⟩,2,markedAxisIntersection⟩,
  ⟨⟨50,63,10,3,39,some 39,18,some 18,385979,[MeasuredChoices.test1105],[AxisChoices.test1839]⟩,2,markedAxisIntersection⟩]
private theorem paid3140 : StockPairs.checked rows3140 = true := by decide +kernel
theorem route3140 (i : Fin 20) : (rows3140.get i).Done :=
  StockPairs.doneAt paid3140 i

end Research6969.PairReceipts
end Z6969Source2791

-- Source: Research6969.HardFit3At110
section Z6969Source2792
set_option autoImplicit true
namespace Research6969.HardFit3At110
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private theorem allAxes89:PairRoute.Done (2:Fin 18) ⟨⟨41,49,9,3,41,some 44⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 44 ⟨
    (PairReceipts.route2829 0),
    (PairReceipts.route2829 1),
    (PairReceipts.route2829 2),
    (PairReceipts.route2829 3),
    (PairReceipts.route2829 4),
    (PairReceipts.route2829 5),
    (PairReceipts.route2829 6),
    (PairReceipts.route2829 7),
    (PairReceipts.route2829 8),
    (PairReceipts.route2829 9),
    (PairReceipts.route2829 10),
    (PairReceipts.route2840 0),
    (PairReceipts.route2840 1),
    (PairReceipts.route2840 2),
    (PairReceipts.route2840 3),
    (PairReceipts.route2840 4),
    (PairReceipts.route2840 5),
    (PairReceipts.route2840 6),
    (PairReceipts.route2840 7),
    (PairReceipts.route2840 8),
    (PairReceipts.route2840 9),
    (PairReceipts.route2840 10),
    (PairReceipts.route2840 11),
    (PairReceipts.route2840 12),
    (PairReceipts.route2840 13),
    (PairReceipts.route2840 14),
    (PairReceipts.route2840 15),
    (PairReceipts.route2840 16),
    (PairReceipts.route2840 17),
    (PairReceipts.route2840 18),
    (PairReceipts.route2840 19),
    (PairReceipts.route2860 0),
    (PairReceipts.route2860 1),
    (PairReceipts.route2860 2),
    (PairReceipts.route2860 3),
    (PairReceipts.route2860 4),
    (PairReceipts.route2860 5),
    (PairReceipts.route2860 6),
    PairLeaves.excluded PairReceipts.cell2867 PairReceipts.check2867 (none),
    PairLeaves.excluded PairReceipts.cell2868 PairReceipts.check2868 (none),
    PairLeaves.excluded PairReceipts.cell2869 PairReceipts.check2869 (none),
    PairLeaves.excluded PairReceipts.cell2870 PairReceipts.check2870 (none),
    PairLeaves.excluded PairReceipts.cell2871 PairReceipts.check2871 (none),
    PairLeaves.excluded PairReceipts.cell2872 PairReceipts.check2872 (none),
    PairLeaves.excluded PairReceipts.cell2873 PairReceipts.check2873 (none),
    trivial⟩)
theorem case110: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,41,some 44⟩:=PairRoute.start _ allAxes89
private theorem allAxes187:PairRoute.Done (2:Fin 18) ⟨⟨41,49,9,3,45,some 48⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 48 ⟨
    (PairReceipts.route2780 0),
    (PairReceipts.route2780 1),
    (PairReceipts.route2780 2),
    (PairReceipts.route2780 3),
    (PairReceipts.route2780 4),
    (PairReceipts.route2780 5),
    (PairReceipts.route2780 6),
    (PairReceipts.route2780 7),
    (PairReceipts.route2780 8),
    (PairReceipts.route2780 9),
    (PairReceipts.route2780 10),
    (PairReceipts.route2780 11),
    (PairReceipts.route2780 12),
    (PairReceipts.route2780 13),
    (PairReceipts.route2780 14),
    (PairReceipts.route2780 15),
    (PairReceipts.route2780 16),
    (PairReceipts.route2780 17),
    (PairReceipts.route2780 18),
    (PairReceipts.route2780 19),
    (PairReceipts.route2800 0),
    (PairReceipts.route2800 1),
    (PairReceipts.route2800 2),
    (PairReceipts.route2800 3),
    (PairReceipts.route2800 4),
    (PairReceipts.route2800 5),
    (PairReceipts.route2800 6),
    (PairReceipts.route2800 7),
    (PairReceipts.route2800 8),
    (PairReceipts.route2800 9),
    (PairReceipts.route2800 10),
    (PairReceipts.route2800 11),
    (PairReceipts.route2800 12),
    (PairReceipts.route2800 13),
    (PairReceipts.route2800 14),
    (PairReceipts.route2800 15),
    (PairReceipts.route2800 16),
    (PairReceipts.route2800 17),
    PairLeaves.excluded PairReceipts.cell2818 PairReceipts.check2818 (none),
    PairLeaves.excluded PairReceipts.cell2819 PairReceipts.check2819 (none),
    PairLeaves.excluded PairReceipts.cell2820 PairReceipts.check2820 (none),
    PairLeaves.excluded PairReceipts.cell2821 PairReceipts.check2821 (none),
    PairLeaves.excluded PairReceipts.cell2822 PairReceipts.check2822 (none),
    PairLeaves.excluded PairReceipts.cell2823 PairReceipts.check2823 (none),
    PairLeaves.excluded PairReceipts.cell2824 PairReceipts.check2824 (none),
    PairLeaves.excluded PairReceipts.cell2825 PairReceipts.check2825 (none),
    PairLeaves.excluded PairReceipts.cell2826 PairReceipts.check2826 (none),
    PairLeaves.excluded PairReceipts.cell2827 PairReceipts.check2827 (none),
    PairLeaves.excluded PairReceipts.cell2828 PairReceipts.check2828 (none),
    trivial⟩)
theorem case111: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,45,some 48⟩:=PairRoute.start _ allAxes187
private theorem leaf188:PairRoute.Done (2:Fin 18) ⟨⟨41,49,9,3,49,some 64⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5403 PairReceipts.check5403 (by decide) (none)
theorem case112: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,49,some 64⟩:=PairRoute.start _ leaf188
private theorem leaf189:PairRoute.Done (2:Fin 18) ⟨⟨41,49,9,3,65,some 96⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5402 PairReceipts.check5402 (by decide) (none)
theorem case113: NormalRoute.Done (2:Fin 18) ⟨41,49,9,3,65,some 96⟩:=PairRoute.start _ leaf189
private def leaf190 := (PairReceipts.route3140 0)
theorem case114: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,4,some 8⟩:=PairRoute.start _ leaf190
private def leaf191 := (PairReceipts.route3121 18)
theorem case115: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf191
private def leaf192 := (PairReceipts.route3121 17)
theorem case116: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf192
private def leaf193 := (PairReceipts.route3121 16)
theorem case117: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf193
private def leaf194 := (PairReceipts.route3121 15)
theorem case118: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,21,some 22⟩:=PairRoute.start _ leaf194
private def leaf195 := (PairReceipts.route3121 13)
private def leaf196 := (PairReceipts.route3121 14)
private def weight197 := PairRoute.weight 305579 leaf195 leaf196
theorem case119: NormalRoute.Done (2:Fin 18) ⟨50,63,10,2,23,some 24⟩:=PairRoute.start _ weight197
end Research6969.HardFit3At110
end Z6969Source2792

-- Source: Research6969.PairReceipts153
section Z6969Source2793
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell3060:PairCell.Row:=⟨50,63,10,2,55,some 55,50,some 50,257319,[MeasuredChoices.test74],[AxisChoices.test1813]⟩
theorem check3060:(cell3060.cap (2:Fin 18)).grade<cell3060.lowerGrade-cell3060.off:=by decide +kernel
def cell3061:PairCell.Row:=⟨50,63,10,2,55,some 55,51,some 51,257319,[MeasuredChoices.test74],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3061:(cell3061.cap (2:Fin 18)).grade<cell3061.lowerGrade-cell3061.off:=by decide +kernel
def cell3062:PairCell.Row:=⟨50,63,10,2,55,some 55,52,some 52,257319,[MeasuredChoices.test74],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check3062:(cell3062.cap (2:Fin 18)).grade<cell3062.lowerGrade-cell3062.off:=by decide +kernel
def cell3063:PairCell.Row:=⟨50,63,10,2,55,some 55,53,some 53,257319,[MeasuredChoices.test74],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check3063:(cell3063.cap (2:Fin 18)).grade<cell3063.lowerGrade-cell3063.off:=by decide +kernel
def cell3064:PairCell.Row:=⟨50,63,10,2,55,some 55,54,some 54,257319,[MeasuredChoices.test74],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check3064:(cell3064.cap (2:Fin 18)).grade<cell3064.lowerGrade-cell3064.off:=by decide +kernel
def cell3065:PairCell.Row:=⟨50,63,10,2,55,some 55,55,some 55,257319,[MeasuredChoices.test74],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check3065:(cell3065.cap (2:Fin 18)).grade<cell3065.lowerGrade-cell3065.off:=by decide +kernel
private def rows3066 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,54,some 54,0,some 0,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,1,some 1,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,2,some 2,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,3,some 3,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,4,some 4,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,5,some 5,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,6,some 6,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,7,some 7,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,8,some 8,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,9,some 9,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,10,some 10,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,11,some 11,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1774]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,12,some 12,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1775]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,13,some 13,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1776]⟩,2,separateWhole⟩]
private theorem paid3066 : StockPairs.checked rows3066 = true := by decide +kernel
theorem route3066 (i : Fin 14) : (rows3066.get i).Done :=
  StockPairs.doneAt paid3066 i

end Research6969.PairReceipts
end Z6969Source2793

-- Source: Research6969.PairReceipts154
section Z6969Source2794
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows3080 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,54,some 54,14,some 14,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1777]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,15,some 15,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1778]⟩,2,separateWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,16,some 16,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1779]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,17,some 17,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1780]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,18,some 18,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1781]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,19,some 19,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1782]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,20,some 20,257319,[MeasuredChoices.test70,MeasuredChoices.test73],[AxisChoices.test1783]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,21,some 21,257319,[MeasuredChoices.test73],[AxisChoices.test1784]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,22,some 22,257319,[MeasuredChoices.test73],[AxisChoices.test1784,AxisChoices.test1785]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,23,some 23,257319,[MeasuredChoices.test73],[AxisChoices.test1784,AxisChoices.test1786]⟩,2,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,54,some 54,24,some 24,257319,[MeasuredChoices.test73],[AxisChoices.test1787]⟩,2,markedAxisWhole⟩]
private theorem paid3080 : StockPairs.checked rows3080 = true := by decide +kernel
theorem route3080 (i : Fin 11) : (rows3080.get i).Done :=
  StockPairs.doneAt paid3080 i

def cell3091:PairCell.Row:=⟨50,63,10,2,54,some 54,25,some 25,257319,[MeasuredChoices.test73],[AxisChoices.test1788]⟩
theorem check3091:(cell3091.cap (2:Fin 18)).grade<cell3091.lowerGrade-cell3091.off:=by decide +kernel
def cell3092:PairCell.Row:=⟨50,63,10,2,54,some 54,26,some 26,257319,[MeasuredChoices.test73],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check3092:(cell3092.cap (2:Fin 18)).grade<cell3092.lowerGrade-cell3092.off:=by decide +kernel
def cell3093:PairCell.Row:=⟨50,63,10,2,54,some 54,27,some 27,257319,[MeasuredChoices.test73],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check3093:(cell3093.cap (2:Fin 18)).grade<cell3093.lowerGrade-cell3093.off:=by decide +kernel
def cell3094:PairCell.Row:=⟨50,63,10,2,54,some 54,28,some 28,257319,[MeasuredChoices.test73],[AxisChoices.test1791]⟩
theorem check3094:(cell3094.cap (2:Fin 18)).grade<cell3094.lowerGrade-cell3094.off:=by decide +kernel
def cell3095:PairCell.Row:=⟨50,63,10,2,54,some 54,29,some 29,257319,[MeasuredChoices.test73],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check3095:(cell3095.cap (2:Fin 18)).grade<cell3095.lowerGrade-cell3095.off:=by decide +kernel
def cell3096:PairCell.Row:=⟨50,63,10,2,54,some 54,30,some 30,257319,[MeasuredChoices.test73],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check3096:(cell3096.cap (2:Fin 18)).grade<cell3096.lowerGrade-cell3096.off:=by decide +kernel
def cell3097:PairCell.Row:=⟨50,63,10,2,54,some 54,31,some 31,257319,[MeasuredChoices.test73],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check3097:(cell3097.cap (2:Fin 18)).grade<cell3097.lowerGrade-cell3097.off:=by decide +kernel
def cell3098:PairCell.Row:=⟨50,63,10,2,54,some 54,32,some 32,257319,[MeasuredChoices.test73],[AxisChoices.test1795]⟩
theorem check3098:(cell3098.cap (2:Fin 18)).grade<cell3098.lowerGrade-cell3098.off:=by decide +kernel
def cell3099:PairCell.Row:=⟨50,63,10,2,54,some 54,33,some 33,257319,[MeasuredChoices.test73],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check3099:(cell3099.cap (2:Fin 18)).grade<cell3099.lowerGrade-cell3099.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2794
