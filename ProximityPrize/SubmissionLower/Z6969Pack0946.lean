import ProximityPrize.SubmissionLower.Z6970StockReceiptIndex
import ProximityPrize.SubmissionLower.Z6970StockPairRoutes
import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0669
import ProximityPrize.SubmissionLower.Z6969Pack0945
import ProximityPrize.SubmissionLower.Z6969Pack0944
import ProximityPrize.SubmissionLower.Z6969Pack0682
import ProximityPrize.SubmissionLower.Z6969Pack0668
import ProximityPrize.SubmissionLower.Z6969Pack0938
import ProximityPrize.SubmissionLower.Z6969Pack0939

set_option Elab.async false

-- Source: Research6969.PairReceipts098
section Z6969Source2711
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1960 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,18,some 18,7,some 7,385979,[MeasuredChoices.test831],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,8,some 8,385979,[MeasuredChoices.test831],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,9,some 9,385979,[MeasuredChoices.test831],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,10,some 10,385979,[MeasuredChoices.test831],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,11,some 11,385979,[MeasuredChoices.test831],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,12,some 12,385979,[MeasuredChoices.test831],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,13,some 13,385979,[MeasuredChoices.test831],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,14,some 14,385979,[MeasuredChoices.test831],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,15,some 15,385979,[MeasuredChoices.test831],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,16,some 16,385979,[MeasuredChoices.test831],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,17,some 17,385979,[MeasuredChoices.test831],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,18,some 18,18,some 18,385979,[MeasuredChoices.test831],[AxisChoices.test1839]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,0,some 0,385979,[MeasuredChoices.test821],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,1,some 1,385979,[MeasuredChoices.test821],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,2,some 2,385979,[MeasuredChoices.test821],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,3,some 3,385979,[MeasuredChoices.test821],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,4,some 4,385979,[MeasuredChoices.test821],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,5,some 5,385979,[MeasuredChoices.test821],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,6,some 6,385979,[MeasuredChoices.test821],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,7,some 7,385979,[MeasuredChoices.test821],[AxisChoices.test1828]⟩,1,separateWhole⟩]
private theorem paid1960 : StockPairs.checked rows1960 = true := by decide +kernel
theorem route1960 (i : Fin 20) : (rows1960.get i).Done :=
  StockPairs.doneAt paid1960 i

end Research6969.PairReceipts
end Z6969Source2711

-- Source: Research6969.PairReceipts099
section Z6969Source2712
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows1980 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,17,some 17,8,some 8,385979,[MeasuredChoices.test821],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,9,some 9,385979,[MeasuredChoices.test821],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,10,some 10,385979,[MeasuredChoices.test821],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,11,some 11,385979,[MeasuredChoices.test821],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,12,some 12,385979,[MeasuredChoices.test821],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,13,some 13,385979,[MeasuredChoices.test821],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,14,some 14,385979,[MeasuredChoices.test821],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,15,some 15,385979,[MeasuredChoices.test821],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,16,some 16,385979,[MeasuredChoices.test821],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,17,some 17,17,some 17,385979,[MeasuredChoices.test821],[AxisChoices.test1838]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,0,some 0,385979,[MeasuredChoices.test807],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,1,some 1,385979,[MeasuredChoices.test807],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,2,some 2,385979,[MeasuredChoices.test807],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,3,some 3,385979,[MeasuredChoices.test807],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,4,some 4,385979,[MeasuredChoices.test807],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,5,some 5,385979,[MeasuredChoices.test807],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,6,some 6,385979,[MeasuredChoices.test807],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,7,some 7,385979,[MeasuredChoices.test807],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,8,some 8,385979,[MeasuredChoices.test807],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,9,some 9,385979,[MeasuredChoices.test807],[AxisChoices.test1830]⟩,1,separateWhole⟩]
private theorem paid1980 : StockPairs.checked rows1980 = true := by decide +kernel
theorem route1980 (i : Fin 20) : (rows1980.get i).Done :=
  StockPairs.doneAt paid1980 i

end Research6969.PairReceipts
end Z6969Source2712

-- Source: Research6969.PairReceipts100
section Z6969Source2713
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2000 : List StockPairs.Receipt := [
  ⟨⟨41,49,9,3,16,some 16,10,some 10,385979,[MeasuredChoices.test807],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,11,some 11,385979,[MeasuredChoices.test807],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,12,some 12,385979,[MeasuredChoices.test807],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,13,some 13,385979,[MeasuredChoices.test807],[AxisChoices.test1834]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,14,some 14,385979,[MeasuredChoices.test807],[AxisChoices.test1835]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,15,some 15,385979,[MeasuredChoices.test807],[AxisChoices.test1836]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,16,some 16,16,some 16,385979,[MeasuredChoices.test807],[AxisChoices.test1837]⟩,1,markedAxisWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,0,some 0,385979,[MeasuredChoices.test797],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,1,some 1,385979,[MeasuredChoices.test797],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,2,some 2,385979,[MeasuredChoices.test797],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,3,some 3,385979,[MeasuredChoices.test797],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,4,some 4,385979,[MeasuredChoices.test797],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,5,some 5,385979,[MeasuredChoices.test797],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,6,some 6,385979,[MeasuredChoices.test797],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,7,some 7,385979,[MeasuredChoices.test797],[AxisChoices.test1828]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,8,some 8,385979,[MeasuredChoices.test797],[AxisChoices.test1829]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,9,some 9,385979,[MeasuredChoices.test797],[AxisChoices.test1830]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,10,some 10,385979,[MeasuredChoices.test797],[AxisChoices.test1831]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,11,some 11,385979,[MeasuredChoices.test797],[AxisChoices.test1832]⟩,1,separateWhole⟩,
  ⟨⟨41,49,9,3,15,some 15,12,some 12,385979,[MeasuredChoices.test797],[AxisChoices.test1833]⟩,1,markedAxisWhole⟩]
private theorem paid2000 : StockPairs.checked rows2000 = true := by decide +kernel
theorem route2000 (i : Fin 20) : (rows2000.get i).Done :=
  StockPairs.doneAt paid2000 i

end Research6969.PairReceipts
end Z6969Source2713

-- Source: Research6969.HardFit2At110
section Z6969Source2714
set_option autoImplicit true
namespace Research6969.HardFit2At110
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route2020 4)
theorem case110: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,13,some 13⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route2020 3)
theorem case111: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,14,some 14⟩:=PairRoute.start _ leaf1
private theorem allAxes33:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,15,some 15⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 15 ⟨
    (PairReceipts.route2000 7),
    (PairReceipts.route2000 8),
    (PairReceipts.route2000 9),
    (PairReceipts.route2000 10),
    (PairReceipts.route2000 11),
    (PairReceipts.route2000 12),
    (PairReceipts.route2000 13),
    (PairReceipts.route2000 14),
    (PairReceipts.route2000 15),
    (PairReceipts.route2000 16),
    (PairReceipts.route2000 17),
    (PairReceipts.route2000 18),
    (PairReceipts.route2000 19),
    (PairReceipts.route2020 0),
    (PairReceipts.route2020 1),
    (PairReceipts.route2020 2),
    trivial⟩)
theorem case112: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,15,some 15⟩:=PairRoute.start _ allAxes33
private theorem allAxes67:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,16,some 16⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 16 ⟨
    (PairReceipts.route1980 10),
    (PairReceipts.route1980 11),
    (PairReceipts.route1980 12),
    (PairReceipts.route1980 13),
    (PairReceipts.route1980 14),
    (PairReceipts.route1980 15),
    (PairReceipts.route1980 16),
    (PairReceipts.route1980 17),
    (PairReceipts.route1980 18),
    (PairReceipts.route1980 19),
    (PairReceipts.route2000 0),
    (PairReceipts.route2000 1),
    (PairReceipts.route2000 2),
    (PairReceipts.route2000 3),
    (PairReceipts.route2000 4),
    (PairReceipts.route2000 5),
    (PairReceipts.route2000 6),
    trivial⟩)
theorem case113: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,16,some 16⟩:=PairRoute.start _ allAxes67
private theorem allAxes103:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,17,some 17⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 17 ⟨
    (PairReceipts.route1960 12),
    (PairReceipts.route1960 13),
    (PairReceipts.route1960 14),
    (PairReceipts.route1960 15),
    (PairReceipts.route1960 16),
    (PairReceipts.route1960 17),
    (PairReceipts.route1960 18),
    (PairReceipts.route1960 19),
    (PairReceipts.route1980 0),
    (PairReceipts.route1980 1),
    (PairReceipts.route1980 2),
    (PairReceipts.route1980 3),
    (PairReceipts.route1980 4),
    (PairReceipts.route1980 5),
    (PairReceipts.route1980 6),
    (PairReceipts.route1980 7),
    (PairReceipts.route1980 8),
    (PairReceipts.route1980 9),
    trivial⟩)
theorem case114: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,17,some 17⟩:=PairRoute.start _ allAxes103
private theorem allAxes141:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,18,some 18⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 18 ⟨
    (PairReceipts.route1940 13),
    (PairReceipts.route1940 14),
    (PairReceipts.route1940 15),
    (PairReceipts.route1940 16),
    (PairReceipts.route1940 17),
    (PairReceipts.route1940 18),
    (PairReceipts.route1940 19),
    (PairReceipts.route1960 0),
    (PairReceipts.route1960 1),
    (PairReceipts.route1960 2),
    (PairReceipts.route1960 3),
    (PairReceipts.route1960 4),
    (PairReceipts.route1960 5),
    (PairReceipts.route1960 6),
    (PairReceipts.route1960 7),
    (PairReceipts.route1960 8),
    (PairReceipts.route1960 9),
    (PairReceipts.route1960 10),
    (PairReceipts.route1960 11),
    trivial⟩)
theorem case115: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,18,some 18⟩:=PairRoute.start _ allAxes141
private theorem allAxes181:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,19,some 19⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 19 ⟨
    (PairReceipts.route1920 13),
    (PairReceipts.route1920 14),
    (PairReceipts.route1920 15),
    (PairReceipts.route1920 16),
    (PairReceipts.route1920 17),
    (PairReceipts.route1920 18),
    (PairReceipts.route1920 19),
    (PairReceipts.route1940 0),
    (PairReceipts.route1940 1),
    (PairReceipts.route1940 2),
    (PairReceipts.route1940 3),
    (PairReceipts.route1940 4),
    (PairReceipts.route1940 5),
    (PairReceipts.route1940 6),
    (PairReceipts.route1940 7),
    (PairReceipts.route1940 8),
    (PairReceipts.route1940 9),
    (PairReceipts.route1940 10),
    (PairReceipts.route1940 11),
    (PairReceipts.route1940 12),
    trivial⟩)
theorem case116: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,19,some 19⟩:=PairRoute.start _ allAxes181
private theorem allAxes223:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,20,some 20⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 20 ⟨
    (PairReceipts.route1900 12),
    (PairReceipts.route1900 13),
    (PairReceipts.route1900 14),
    (PairReceipts.route1900 15),
    (PairReceipts.route1900 16),
    (PairReceipts.route1900 17),
    (PairReceipts.route1900 18),
    (PairReceipts.route1900 19),
    (PairReceipts.route1920 0),
    (PairReceipts.route1920 1),
    (PairReceipts.route1920 2),
    (PairReceipts.route1920 3),
    (PairReceipts.route1920 4),
    (PairReceipts.route1920 5),
    (PairReceipts.route1920 6),
    (PairReceipts.route1920 7),
    (PairReceipts.route1920 8),
    (PairReceipts.route1920 9),
    (PairReceipts.route1920 10),
    (PairReceipts.route1920 11),
    (PairReceipts.route1920 12),
    trivial⟩)
theorem case117: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,20,some 20⟩:=PairRoute.start _ allAxes223
private theorem allAxes267:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,21,some 21⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 21 ⟨
    (PairReceipts.route1880 10),
    (PairReceipts.route1880 11),
    (PairReceipts.route1880 12),
    (PairReceipts.route1880 13),
    (PairReceipts.route1880 14),
    (PairReceipts.route1880 15),
    (PairReceipts.route1880 16),
    (PairReceipts.route1880 17),
    (PairReceipts.route1880 18),
    (PairReceipts.route1880 19),
    (PairReceipts.route1900 0),
    (PairReceipts.route1900 1),
    (PairReceipts.route1900 2),
    (PairReceipts.route1900 3),
    (PairReceipts.route1900 4),
    (PairReceipts.route1900 5),
    (PairReceipts.route1900 6),
    (PairReceipts.route1900 7),
    (PairReceipts.route1900 8),
    (PairReceipts.route1900 9),
    (PairReceipts.route1900 10),
    (PairReceipts.route1900 11),
    trivial⟩)
theorem case118: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,21,some 21⟩:=PairRoute.start _ allAxes267
private theorem allAxes313:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,22,some 22⟩,0,none,385979,none⟩:=
  PairRoute.axes_of_total (PairRoute.axesOfRun 0 22 ⟨
    (PairReceipts.route1860 7),
    (PairReceipts.route1860 8),
    (PairReceipts.route1860 9),
    (PairReceipts.route1860 10),
    (PairReceipts.route1860 11),
    (PairReceipts.route1860 12),
    (PairReceipts.route1860 13),
    (PairReceipts.route1860 14),
    (PairReceipts.route1860 15),
    (PairReceipts.route1860 16),
    (PairReceipts.route1860 17),
    (PairReceipts.route1860 18),
    (PairReceipts.route1860 19),
    (PairReceipts.route1880 0),
    (PairReceipts.route1880 1),
    (PairReceipts.route1880 2),
    (PairReceipts.route1880 3),
    (PairReceipts.route1880 4),
    (PairReceipts.route1880 5),
    (PairReceipts.route1880 6),
    (PairReceipts.route1880 7),
    (PairReceipts.route1880 8),
    (PairReceipts.route1880 9),
    trivial⟩)
theorem case119: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,22,some 22⟩:=PairRoute.start _ allAxes313
end Research6969.HardFit2At110
end Z6969Source2714

-- Source: Research6969.HardFit2At120
section Z6969Source2715
set_option autoImplicit true
namespace Research6969.HardFit2At120
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1860 6)
theorem case120: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,23,some 23⟩:=PairRoute.start _ leaf0
private def leaf1 := (PairReceipts.route1860 5)
theorem case121: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,24,some 24⟩:=PairRoute.start _ leaf1
private def leaf2 := (PairReceipts.route1860 4)
theorem case122: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,25,some 25⟩:=PairRoute.start _ leaf2
private def leaf3 := (PairReceipts.route1860 3)
theorem case123: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,26,some 26⟩:=PairRoute.start _ leaf3
private def leaf4 := (PairReceipts.route1860 2)
theorem case124: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,27,some 28⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route1860 1)
theorem case125: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,29,some 30⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route1860 0)
theorem case126: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,31,some 32⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route1846 13)
theorem case127: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,33,some 34⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route1846 12)
theorem case128: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,35,some 36⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route1846 11)
theorem case129: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,37,some 38⟩:=PairRoute.start _ leaf9
end Research6969.HardFit2At120
end Z6969Source2715

-- Source: Research6969.PairReceipts107
section Z6969Source2716
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell2140:PairCell.Row:=⟨50,63,10,2,56,some 56,51,some 51,257319,[MeasuredChoices.test77],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check2140:(cell2140.cap (1:Fin 18)).grade<cell2140.lowerGrade-cell2140.off:=by decide +kernel
def cell2141:PairCell.Row:=⟨50,63,10,2,56,some 56,52,some 52,257319,[MeasuredChoices.test77],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check2141:(cell2141.cap (1:Fin 18)).grade<cell2141.lowerGrade-cell2141.off:=by decide +kernel
def cell2142:PairCell.Row:=⟨50,63,10,2,56,some 56,53,some 53,257319,[MeasuredChoices.test77],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check2142:(cell2142.cap (1:Fin 18)).grade<cell2142.lowerGrade-cell2142.off:=by decide +kernel
def cell2143:PairCell.Row:=⟨50,63,10,2,56,some 56,54,some 54,257319,[MeasuredChoices.test77],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check2143:(cell2143.cap (1:Fin 18)).grade<cell2143.lowerGrade-cell2143.off:=by decide +kernel
def cell2144:PairCell.Row:=⟨50,63,10,2,56,some 56,55,some 55,257319,[MeasuredChoices.test77],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check2144:(cell2144.cap (1:Fin 18)).grade<cell2144.lowerGrade-cell2144.off:=by decide +kernel
def cell2145:PairCell.Row:=⟨50,63,10,2,56,some 56,56,some 56,257319,[MeasuredChoices.test77],[AxisChoices.test1819]⟩
theorem check2145:(cell2145.cap (1:Fin 18)).grade<cell2145.lowerGrade-cell2145.off:=by decide +kernel
private def rows2146 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,55,some 55,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test74],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,53,some 54,0,none,257319,[MeasuredChoices.test70,MeasuredChoices.test71],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,49,some 52,0,none,257319,[MeasuredChoices.test58,MeasuredChoices.test62],[]⟩,1,⟨(.node 8028273500198129),.intersection,.impossible,288407⟩⟩,
  ⟨⟨50,63,10,2,49,some 52,0,none,288407,[MeasuredChoices.test104,MeasuredChoices.test114],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,41,some 48,0,none,257319,[MeasuredChoices.test50],[]⟩,1,⟨(.node 8030575396047635),.intersection,.impossible,291368⟩⟩,
  ⟨⟨50,63,10,2,41,some 48,0,none,291368,[MeasuredChoices.test125],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,33,some 40,0,none,257319,[MeasuredChoices.test44],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,29,some 32,0,none,257319,[MeasuredChoices.test39],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,257319,[MeasuredChoices.test36],[]⟩,1,⟨(.node 8059959167344767),.intersection,.impossible,302619⟩⟩,
  ⟨⟨50,63,10,2,25,some 28,0,none,302619,[MeasuredChoices.test166],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,21,some 24,0,none,257319,[MeasuredChoices.test25],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,17,some 20,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,13,some 16,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,2,9,some 12,0,none,257319,[],[]⟩,1,surfaceWhole⟩]
private theorem paid2146 : StockPairs.checked rows2146 = true := by decide +kernel
theorem route2146 (i : Fin 14) : (rows2146.get i).Done :=
  StockPairs.doneAt paid2146 i

end Research6969.PairReceipts
end Z6969Source2716

-- Source: Research6969.PairReceipts108
section Z6969Source2717
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2160 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,4,some 8,0,none,257319,[],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,39,some 39,0,none,385979,[MeasuredChoices.test1105],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,37,some 37,0,none,385979,[MeasuredChoices.test1080],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,38,some 38,0,none,385979,[MeasuredChoices.test1093],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,35,some 36,0,none,385979,[MeasuredChoices.test1055],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,33,some 34,0,none,385979,[MeasuredChoices.test1029],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,31,some 32,0,none,385979,[MeasuredChoices.test1005],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,29,some 30,0,none,385979,[MeasuredChoices.test977],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,27,some 28,0,none,385979,[MeasuredChoices.test952],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,26,some 26,0,none,385979,[MeasuredChoices.test939],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,25,some 25,0,none,385979,[MeasuredChoices.test924],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,24,some 24,0,none,385979,[MeasuredChoices.test910],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,23,some 23,0,none,385979,[MeasuredChoices.test896],[]⟩,1,surfaceWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,0,some 0,385979,[MeasuredChoices.test882],[AxisChoices.test1821]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,1,some 1,385979,[MeasuredChoices.test882],[AxisChoices.test1822]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,2,some 2,385979,[MeasuredChoices.test882],[AxisChoices.test1823]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,3,some 3,385979,[MeasuredChoices.test882],[AxisChoices.test1824]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,4,some 4,385979,[MeasuredChoices.test882],[AxisChoices.test1825]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,5,some 5,385979,[MeasuredChoices.test882],[AxisChoices.test1826]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,6,some 6,385979,[MeasuredChoices.test882],[AxisChoices.test1827]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,3,22,some 22,7,some 7,385979,[MeasuredChoices.test882],[AxisChoices.test1828]⟩,1,separateWhole⟩]
private theorem paid2160 : StockPairs.checked rows2160 = true := by decide +kernel
theorem route2160 (i : Fin 21) : (rows2160.get i).Done :=
  StockPairs.doneAt paid2160 i

end Research6969.PairReceipts
end Z6969Source2717

-- Source: Research6969.HardFit2At130
section Z6969Source2718
set_option autoImplicit true
namespace Research6969.HardFit2At130
set_option maxRecDepth 18000
set_option maxHeartbeats 1200000
private def leaf0 := (PairReceipts.route1846 10)
theorem case130: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,39,some 40⟩:=PairRoute.start _ leaf0
private theorem leaf1:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,41,some 44⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5175 PairReceipts.check5175 (by decide) (none)
theorem case131: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,41,some 44⟩:=PairRoute.start _ leaf1
private theorem leaf2:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,45,some 48⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5174 PairReceipts.check5174 (by decide) (none)
theorem case132: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,45,some 48⟩:=PairRoute.start _ leaf2
private theorem leaf3:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,49,some 64⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5173 PairReceipts.check5173 (by decide) (none)
theorem case133: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,49,some 64⟩:=PairRoute.start _ leaf3
private theorem leaf4:PairRoute.Done (1:Fin 18) ⟨⟨41,49,9,3,65,some 96⟩,0,none,385979,none⟩:=PairLeaves.three PairReceipts.cell5172 PairReceipts.check5172 (by decide) (none)
theorem case134: NormalRoute.Done (1:Fin 18) ⟨41,49,9,3,65,some 96⟩:=PairRoute.start _ leaf4
private def leaf5 := (PairReceipts.route2160 0)
theorem case135: NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,4,some 8⟩:=PairRoute.start _ leaf5
private def leaf6 := (PairReceipts.route2146 13)
theorem case136: NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,9,some 12⟩:=PairRoute.start _ leaf6
private def leaf7 := (PairReceipts.route2146 12)
theorem case137: NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,13,some 16⟩:=PairRoute.start _ leaf7
private def leaf8 := (PairReceipts.route2146 11)
theorem case138: NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,17,some 20⟩:=PairRoute.start _ leaf8
private def leaf9 := (PairReceipts.route2146 10)
theorem case139: NormalRoute.Done (1:Fin 18) ⟨50,63,10,2,21,some 24⟩:=PairRoute.start _ leaf9
end Research6969.HardFit2At130
end Z6969Source2718

-- Source: Research6969.PairReceipts102
section Z6969Source2719
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2040 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,57,some 57,9,some 9,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,10,some 10,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,11,some 11,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1774]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,12,some 12,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1775]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,13,some 13,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1776]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,14,some 14,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1777]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,15,some 15,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1778]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,16,some 16,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1779]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,17,some 17,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1780]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,18,some 18,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1781]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,19,some 19,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1782]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,20,some 20,257319,[MeasuredChoices.test70,MeasuredChoices.test79],[AxisChoices.test1783]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,21,some 21,257319,[MeasuredChoices.test79],[AxisChoices.test1784]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,22,some 22,257319,[MeasuredChoices.test79],[AxisChoices.test1784,AxisChoices.test1785]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,23,some 23,257319,[MeasuredChoices.test79],[AxisChoices.test1784,AxisChoices.test1786]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,57,some 57,24,some 24,257319,[MeasuredChoices.test79],[AxisChoices.test1787]⟩,1,markedAxisWhole⟩]
private theorem paid2040 : StockPairs.checked rows2040 = true := by decide +kernel
theorem route2040 (i : Fin 16) : (rows2040.get i).Done :=
  StockPairs.doneAt paid2040 i

def cell2056:PairCell.Row:=⟨50,63,10,2,57,some 57,25,some 25,257319,[MeasuredChoices.test79],[AxisChoices.test1788]⟩
theorem check2056:(cell2056.cap (1:Fin 18)).grade<cell2056.lowerGrade-cell2056.off:=by decide +kernel
def cell2057:PairCell.Row:=⟨50,63,10,2,57,some 57,26,some 26,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check2057:(cell2057.cap (1:Fin 18)).grade<cell2057.lowerGrade-cell2057.off:=by decide +kernel
def cell2058:PairCell.Row:=⟨50,63,10,2,57,some 57,27,some 27,257319,[MeasuredChoices.test79],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check2058:(cell2058.cap (1:Fin 18)).grade<cell2058.lowerGrade-cell2058.off:=by decide +kernel
def cell2059:PairCell.Row:=⟨50,63,10,2,57,some 57,28,some 28,257319,[MeasuredChoices.test79],[AxisChoices.test1791]⟩
theorem check2059:(cell2059.cap (1:Fin 18)).grade<cell2059.lowerGrade-cell2059.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2719

-- Source: Research6969.PairReceipts103
section Z6969Source2720
set_option autoImplicit true
namespace Research6969.PairReceipts
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell2060:PairCell.Row:=⟨50,63,10,2,57,some 57,29,some 29,257319,[MeasuredChoices.test79],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check2060:(cell2060.cap (1:Fin 18)).grade<cell2060.lowerGrade-cell2060.off:=by decide +kernel
def cell2061:PairCell.Row:=⟨50,63,10,2,57,some 57,30,some 30,257319,[MeasuredChoices.test79],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check2061:(cell2061.cap (1:Fin 18)).grade<cell2061.lowerGrade-cell2061.off:=by decide +kernel
def cell2062:PairCell.Row:=⟨50,63,10,2,57,some 57,31,some 31,257319,[MeasuredChoices.test79],[AxisChoices.test1793,AxisChoices.test1794]⟩
theorem check2062:(cell2062.cap (1:Fin 18)).grade<cell2062.lowerGrade-cell2062.off:=by decide +kernel
def cell2063:PairCell.Row:=⟨50,63,10,2,57,some 57,32,some 32,257319,[MeasuredChoices.test79],[AxisChoices.test1795]⟩
theorem check2063:(cell2063.cap (1:Fin 18)).grade<cell2063.lowerGrade-cell2063.off:=by decide +kernel
def cell2064:PairCell.Row:=⟨50,63,10,2,57,some 57,33,some 33,257319,[MeasuredChoices.test79],[AxisChoices.test1795,AxisChoices.test1796]⟩
theorem check2064:(cell2064.cap (1:Fin 18)).grade<cell2064.lowerGrade-cell2064.off:=by decide +kernel
def cell2065:PairCell.Row:=⟨50,63,10,2,57,some 57,34,some 34,257319,[MeasuredChoices.test79],[AxisChoices.test1795,AxisChoices.test1797]⟩
theorem check2065:(cell2065.cap (1:Fin 18)).grade<cell2065.lowerGrade-cell2065.off:=by decide +kernel
def cell2066:PairCell.Row:=⟨50,63,10,2,57,some 57,35,some 35,257319,[MeasuredChoices.test79],[AxisChoices.test1798]⟩
theorem check2066:(cell2066.cap (1:Fin 18)).grade<cell2066.lowerGrade-cell2066.off:=by decide +kernel
def cell2067:PairCell.Row:=⟨50,63,10,2,57,some 57,36,some 36,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1799]⟩
theorem check2067:(cell2067.cap (1:Fin 18)).grade<cell2067.lowerGrade-cell2067.off:=by decide +kernel
def cell2068:PairCell.Row:=⟨50,63,10,2,57,some 57,37,some 37,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check2068:(cell2068.cap (1:Fin 18)).grade<cell2068.lowerGrade-cell2068.off:=by decide +kernel
def cell2069:PairCell.Row:=⟨50,63,10,2,57,some 57,38,some 38,257319,[MeasuredChoices.test79],[AxisChoices.test1798,AxisChoices.test1800]⟩
theorem check2069:(cell2069.cap (1:Fin 18)).grade<cell2069.lowerGrade-cell2069.off:=by decide +kernel
def cell2070:PairCell.Row:=⟨50,63,10,2,57,some 57,39,some 39,257319,[MeasuredChoices.test79],[AxisChoices.test1802]⟩
theorem check2070:(cell2070.cap (1:Fin 18)).grade<cell2070.lowerGrade-cell2070.off:=by decide +kernel
def cell2071:PairCell.Row:=⟨50,63,10,2,57,some 57,40,some 40,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1803]⟩
theorem check2071:(cell2071.cap (1:Fin 18)).grade<cell2071.lowerGrade-cell2071.off:=by decide +kernel
def cell2072:PairCell.Row:=⟨50,63,10,2,57,some 57,41,some 41,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check2072:(cell2072.cap (1:Fin 18)).grade<cell2072.lowerGrade-cell2072.off:=by decide +kernel
def cell2073:PairCell.Row:=⟨50,63,10,2,57,some 57,42,some 42,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1804]⟩
theorem check2073:(cell2073.cap (1:Fin 18)).grade<cell2073.lowerGrade-cell2073.off:=by decide +kernel
def cell2074:PairCell.Row:=⟨50,63,10,2,57,some 57,43,some 43,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1806]⟩
theorem check2074:(cell2074.cap (1:Fin 18)).grade<cell2074.lowerGrade-cell2074.off:=by decide +kernel
def cell2075:PairCell.Row:=⟨50,63,10,2,57,some 57,44,some 44,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1807]⟩
theorem check2075:(cell2075.cap (1:Fin 18)).grade<cell2075.lowerGrade-cell2075.off:=by decide +kernel
def cell2076:PairCell.Row:=⟨50,63,10,2,57,some 57,45,some 45,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1808]⟩
theorem check2076:(cell2076.cap (1:Fin 18)).grade<cell2076.lowerGrade-cell2076.off:=by decide +kernel
def cell2077:PairCell.Row:=⟨50,63,10,2,57,some 57,46,some 46,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check2077:(cell2077.cap (1:Fin 18)).grade<cell2077.lowerGrade-cell2077.off:=by decide +kernel
def cell2078:PairCell.Row:=⟨50,63,10,2,57,some 57,47,some 47,257319,[MeasuredChoices.test79],[AxisChoices.test1802,AxisChoices.test1809]⟩
theorem check2078:(cell2078.cap (1:Fin 18)).grade<cell2078.lowerGrade-cell2078.off:=by decide +kernel
def cell2079:PairCell.Row:=⟨50,63,10,2,57,some 57,48,some 48,257319,[MeasuredChoices.test79],[AxisChoices.test1809,AxisChoices.test1811]⟩
theorem check2079:(cell2079.cap (1:Fin 18)).grade<cell2079.lowerGrade-cell2079.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2720

-- Source: Research6969.PairReceipts104
section Z6969Source2721
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
def cell2080:PairCell.Row:=⟨50,63,10,2,57,some 57,49,some 49,257319,[MeasuredChoices.test79],[AxisChoices.test1812]⟩
theorem check2080:(cell2080.cap (1:Fin 18)).grade<cell2080.lowerGrade-cell2080.off:=by decide +kernel
def cell2081:PairCell.Row:=⟨50,63,10,2,57,some 57,50,some 50,257319,[MeasuredChoices.test79],[AxisChoices.test1813]⟩
theorem check2081:(cell2081.cap (1:Fin 18)).grade<cell2081.lowerGrade-cell2081.off:=by decide +kernel
def cell2082:PairCell.Row:=⟨50,63,10,2,57,some 57,51,some 51,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check2082:(cell2082.cap (1:Fin 18)).grade<cell2082.lowerGrade-cell2082.off:=by decide +kernel
def cell2083:PairCell.Row:=⟨50,63,10,2,57,some 57,52,some 52,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1814]⟩
theorem check2083:(cell2083.cap (1:Fin 18)).grade<cell2083.lowerGrade-cell2083.off:=by decide +kernel
def cell2084:PairCell.Row:=⟨50,63,10,2,57,some 57,53,some 53,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1816]⟩
theorem check2084:(cell2084.cap (1:Fin 18)).grade<cell2084.lowerGrade-cell2084.off:=by decide +kernel
def cell2085:PairCell.Row:=⟨50,63,10,2,57,some 57,54,some 54,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check2085:(cell2085.cap (1:Fin 18)).grade<cell2085.lowerGrade-cell2085.off:=by decide +kernel
def cell2086:PairCell.Row:=⟨50,63,10,2,57,some 57,55,some 55,257319,[MeasuredChoices.test79],[AxisChoices.test1813,AxisChoices.test1817]⟩
theorem check2086:(cell2086.cap (1:Fin 18)).grade<cell2086.lowerGrade-cell2086.off:=by decide +kernel
def cell2087:PairCell.Row:=⟨50,63,10,2,57,some 57,56,some 56,257319,[MeasuredChoices.test79],[AxisChoices.test1819]⟩
theorem check2087:(cell2087.cap (1:Fin 18)).grade<cell2087.lowerGrade-cell2087.off:=by decide +kernel
def cell2088:PairCell.Row:=⟨50,63,10,2,57,some 57,57,some 57,257319,[MeasuredChoices.test79],[AxisChoices.test1819,AxisChoices.test1820]⟩
theorem check2088:(cell2088.cap (1:Fin 18)).grade<cell2088.lowerGrade-cell2088.off:=by decide +kernel
private def rows2089 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,56,some 56,0,some 0,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,1,some 1,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,2,some 2,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,3,some 3,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,4,some 4,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,5,some 5,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,6,some 6,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,7,some 7,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,8,some 8,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,9,some 9,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,10,some 10,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[]⟩,1,separateWhole⟩]
private theorem paid2089 : StockPairs.checked rows2089 = true := by decide +kernel
theorem route2089 (i : Fin 11) : (rows2089.get i).Done :=
  StockPairs.doneAt paid2089 i

end Research6969.PairReceipts
end Z6969Source2721

-- Source: Research6969.PairReceipts105
section Z6969Source2722
set_option autoImplicit true
namespace Research6969.PairReceipts
open StockPairs
set_option maxHeartbeats 0
set_option maxRecDepth 15000
private def rows2100 : List StockPairs.Receipt := [
  ⟨⟨50,63,10,2,56,some 56,11,some 11,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1774]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,12,some 12,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1775]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,13,some 13,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1776]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,14,some 14,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1777]⟩,1,separateWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,15,some 15,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1778]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,16,some 16,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1779]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,17,some 17,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1780]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,18,some 18,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1781]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,19,some 19,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1782]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,20,some 20,257319,[MeasuredChoices.test70,MeasuredChoices.test77],[AxisChoices.test1783]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,21,some 21,257319,[MeasuredChoices.test77],[AxisChoices.test1784]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,22,some 22,257319,[MeasuredChoices.test77],[AxisChoices.test1784,AxisChoices.test1785]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,23,some 23,257319,[MeasuredChoices.test77],[AxisChoices.test1784,AxisChoices.test1786]⟩,1,markedAxisWhole⟩,
  ⟨⟨50,63,10,2,56,some 56,24,some 24,257319,[MeasuredChoices.test77],[AxisChoices.test1787]⟩,1,markedAxisWhole⟩]
private theorem paid2100 : StockPairs.checked rows2100 = true := by decide +kernel
theorem route2100 (i : Fin 14) : (rows2100.get i).Done :=
  StockPairs.doneAt paid2100 i

def cell2114:PairCell.Row:=⟨50,63,10,2,56,some 56,25,some 25,257319,[MeasuredChoices.test77],[AxisChoices.test1788]⟩
theorem check2114:(cell2114.cap (1:Fin 18)).grade<cell2114.lowerGrade-cell2114.off:=by decide +kernel
def cell2115:PairCell.Row:=⟨50,63,10,2,56,some 56,26,some 26,257319,[MeasuredChoices.test77],[AxisChoices.test1788,AxisChoices.test1789]⟩
theorem check2115:(cell2115.cap (1:Fin 18)).grade<cell2115.lowerGrade-cell2115.off:=by decide +kernel
def cell2116:PairCell.Row:=⟨50,63,10,2,56,some 56,27,some 27,257319,[MeasuredChoices.test77],[AxisChoices.test1788,AxisChoices.test1790]⟩
theorem check2116:(cell2116.cap (1:Fin 18)).grade<cell2116.lowerGrade-cell2116.off:=by decide +kernel
def cell2117:PairCell.Row:=⟨50,63,10,2,56,some 56,28,some 28,257319,[MeasuredChoices.test77],[AxisChoices.test1791]⟩
theorem check2117:(cell2117.cap (1:Fin 18)).grade<cell2117.lowerGrade-cell2117.off:=by decide +kernel
def cell2118:PairCell.Row:=⟨50,63,10,2,56,some 56,29,some 29,257319,[MeasuredChoices.test77],[AxisChoices.test1791,AxisChoices.test1792]⟩
theorem check2118:(cell2118.cap (1:Fin 18)).grade<cell2118.lowerGrade-cell2118.off:=by decide +kernel
def cell2119:PairCell.Row:=⟨50,63,10,2,56,some 56,30,some 30,257319,[MeasuredChoices.test77],[AxisChoices.test1792,AxisChoices.test1793]⟩
theorem check2119:(cell2119.cap (1:Fin 18)).grade<cell2119.lowerGrade-cell2119.off:=by decide +kernel
end Research6969.PairReceipts
end Z6969Source2722
