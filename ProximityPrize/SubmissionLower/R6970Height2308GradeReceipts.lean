import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.R6970Height2313MeasuredTests03
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e

set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.BandGradeReceipts

open _root_.Research6970.Height2313.Research6969

private theorem beginAt {i} (r : NormalRoute.Region)
    (all : PairRoute.Done i ⟨r,0,none,r.graph*(131071-2313)-1,none⟩) :
    NormalRoute.Done i r := by
  intro s h
  have w := NormalGeometry.base s
  rw [h.2.2.2.1] at w
  exact all s ⟨h,Nat.zero_le _,by simp,w,by simp⟩

private def row_5_1_0_0 : PairCell.Row := ⟨24,24,9,1,0,some 159,0,none,128757,[],[]⟩
private def price_5_1_0_0 : PairPrices.Decision := ⟨.affine,.intersection,.impossible,0⟩
private theorem leaf_5_1_0_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,1,0,some 159⟩,0,none,128757,none⟩ :=
  PairLeaves.paired row_5_1_0_0 price_5_1_0_0 (by decide +kernel) (none) (by decide)

private theorem seed5graph1cell0 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,1,0,some 159⟩ :=
  beginAt _ leaf_5_1_0_0

private def row_5_1_1_0 : PairCell.Row := ⟨24,24,9,1,160,none,0,none,128757,[MeasuredChoices.test0,MeasuredChoices.test11],[]⟩
private theorem leaf_5_1_1_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,1,160,none⟩,0,none,128757,none⟩ :=
  PairLeaves.three row_5_1_1_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph1cell1 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,1,160,none⟩ :=
  beginAt _ leaf_5_1_1_0

private theorem seed5graph1 : NormalRoute.Tail (4:Fin 18) 24 24 9 1 0 :=
  (NormalRoute.join seed5graph1cell0 seed5graph1cell1)

private def row_5_2_0_0 : PairCell.Row := ⟨24,24,9,2,0,some 26,0,none,257515,[],[]⟩
private def price_5_2_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.surface,0⟩
private theorem leaf_5_2_0_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,2,0,some 26⟩,0,none,257515,none⟩ :=
  PairLeaves.paired row_5_2_0_0 price_5_2_0_0 (by decide +kernel) (none) (by decide)

private theorem seed5graph2cell0 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,2,0,some 26⟩ :=
  beginAt _ leaf_5_2_0_0

private def row_5_2_1_0 : PairCell.Row := ⟨24,24,9,2,27,some 47,0,none,257515,[MeasuredChoices.test37],[]⟩
private def price_5_2_1_0 : PairPrices.Decision := ⟨(.node 22203381721308985),.intersection,.impossible,302619⟩
private theorem leaf_5_2_1_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,2,27,some 47⟩,0,none,257515,some 302619⟩ :=
  PairLeaves.paired row_5_2_1_0 price_5_2_1_0 (by decide +kernel) (some 302619) (by decide)

private def row_5_2_1_1 : PairCell.Row := ⟨24,24,9,2,27,some 47,0,none,302619,[MeasuredChoices.test168,MeasuredChoices.test169],[]⟩
private def price_5_2_1_1 : PairPrices.Decision := ⟨.marked,.intersection,.impossible,0⟩
private theorem leaf_5_2_1_1 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,2,27,some 47⟩,0,none,302619,none⟩ :=
  PairLeaves.paired row_5_2_1_1 price_5_2_1_1 (by decide +kernel) (none) (by decide)

private theorem seed5graph2cell1 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,2,27,some 47⟩ :=
  beginAt _ (PairRoute.weight 302619 leaf_5_2_1_0 leaf_5_2_1_1)

private def row_5_2_2_0 : PairCell.Row := ⟨24,24,9,2,48,some 305,0,none,257515,[MeasuredChoices.test60],[]⟩
private def price_5_2_2_0 : PairPrices.Decision := ⟨.marked,.intersection,.impossible,0⟩
private theorem leaf_5_2_2_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,2,48,some 305⟩,0,none,257515,none⟩ :=
  PairLeaves.paired row_5_2_2_0 price_5_2_2_0 (by decide +kernel) (none) (by decide)

private theorem seed5graph2cell2 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,2,48,some 305⟩ :=
  beginAt _ leaf_5_2_2_0

private def row_5_2_3_0 : PairCell.Row := ⟨24,24,9,2,306,some 5225,0,none,257515,[MeasuredChoices.test92,MeasuredChoices.test93],[]⟩
private def price_5_2_3_0 : PairPrices.Decision := ⟨.marked,.intersection,.impossible,0⟩
private theorem leaf_5_2_3_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,2,306,some 5225⟩,0,none,257515,none⟩ :=
  PairLeaves.paired row_5_2_3_0 price_5_2_3_0 (by decide +kernel) (none) (by decide)

private theorem seed5graph2cell3 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,2,306,some 5225⟩ :=
  beginAt _ leaf_5_2_3_0

private def row_5_2_4_0 : PairCell.Row := ⟨24,24,9,2,5226,none,0,none,257515,[MeasuredChoices.test27,MeasuredChoices.test98],[]⟩
private theorem leaf_5_2_4_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,2,5226,none⟩,0,none,257515,none⟩ :=
  PairLeaves.excluded row_5_2_4_0 (by decide +kernel) none

private theorem seed5graph2cell4 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,2,5226,none⟩ :=
  beginAt _ leaf_5_2_4_0

private theorem seed5graph2 : NormalRoute.Tail (4:Fin 18) 24 24 9 2 0 :=
  (NormalRoute.join seed5graph2cell0 (NormalRoute.join seed5graph2cell1 (NormalRoute.join seed5graph2cell2 (NormalRoute.join seed5graph2cell3 seed5graph2cell4))))

private def row_5_3_0_0 : PairCell.Row := ⟨24,24,9,3,0,some 14,0,none,386273,[],[]⟩
private def price_5_3_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_5_3_0_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,3,0,some 14⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_5_3_0_0 price_5_3_0_0 (by decide +kernel) (none) (by decide)

private theorem seed5graph3cell0 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,3,0,some 14⟩ :=
  beginAt _ leaf_5_3_0_0

private def row_5_3_1_0 : PairCell.Row := ⟨24,24,9,3,15,some 24,0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test797],[]⟩
private theorem leaf_5_3_1_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,3,15,some 24⟩,0,none,386273,none⟩ :=
  PairLeaves.three row_5_3_1_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph3cell1 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,3,15,some 24⟩ :=
  beginAt _ leaf_5_3_1_0

private def row_5_3_2_0 : PairCell.Row := ⟨24,24,9,3,25,some 146,0,none,386273,[MeasuredChoices.test924,MeasuredChoices.test925],[]⟩
private theorem leaf_5_3_2_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,3,25,some 146⟩,0,none,386273,none⟩ :=
  PairLeaves.three row_5_3_2_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph3cell2 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,3,25,some 146⟩ :=
  beginAt _ leaf_5_3_2_0

private def row_5_3_3_0 : PairCell.Row := ⟨24,24,9,3,147,some 1094,0,none,386273,[MeasuredChoices.test1151],[]⟩
private theorem leaf_5_3_3_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,3,147,some 1094⟩,0,none,386273,none⟩ :=
  PairLeaves.three row_5_3_3_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph3cell3 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,3,147,some 1094⟩ :=
  beginAt _ leaf_5_3_3_0

private def row_5_3_4_0 : PairCell.Row := ⟨24,24,9,3,1095,none,0,none,386273,[MeasuredChoices.test649,MeasuredChoices.test1156],[]⟩
private theorem leaf_5_3_4_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,3,1095,none⟩,0,none,386273,none⟩ :=
  PairLeaves.three row_5_3_4_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph3cell4 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,3,1095,none⟩ :=
  beginAt _ leaf_5_3_4_0

private theorem seed5graph3 : NormalRoute.Tail (4:Fin 18) 24 24 9 3 0 :=
  (NormalRoute.join seed5graph3cell0 (NormalRoute.join seed5graph3cell1 (NormalRoute.join seed5graph3cell2 (NormalRoute.join seed5graph3cell3 seed5graph3cell4))))

private def row_5_4_0_0 : PairCell.Row := ⟨24,24,9,4,0,some 10,0,none,515031,[],[]⟩
private def price_5_4_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_5_4_0_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,4,0,some 10⟩,0,none,515031,none⟩ :=
  PairLeaves.paired row_5_4_0_0 price_5_4_0_0 (by decide +kernel) (none) (by decide)

private theorem seed5graph4cell0 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,4,0,some 10⟩ :=
  beginAt _ leaf_5_4_0_0

private def row_5_4_1_0 : PairCell.Row := ⟨24,24,9,4,11,some 173,0,none,515031,[MeasuredChoices.test1239,MeasuredChoices.test1251],[]⟩
private theorem leaf_5_4_1_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,4,11,some 173⟩,0,none,515031,none⟩ :=
  PairLeaves.three row_5_4_1_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph4cell1 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,4,11,some 173⟩ :=
  beginAt _ leaf_5_4_1_0

private def row_5_4_2_0 : PairCell.Row := ⟨24,24,9,4,174,some 1116,0,none,515031,[MeasuredChoices.test1374],[]⟩
private theorem leaf_5_4_2_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,4,174,some 1116⟩,0,none,515031,none⟩ :=
  PairLeaves.three row_5_4_2_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph4cell2 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,4,174,some 1116⟩ :=
  beginAt _ leaf_5_4_2_0

private def row_5_4_3_0 : PairCell.Row := ⟨24,24,9,4,1117,none,0,none,515031,[MeasuredChoices.test1372,MeasuredChoices.test1379],[]⟩
private theorem leaf_5_4_3_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,4,1117,none⟩,0,none,515031,none⟩ :=
  PairLeaves.three row_5_4_3_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph4cell3 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,4,1117,none⟩ :=
  beginAt _ leaf_5_4_3_0

private theorem seed5graph4 : NormalRoute.Tail (4:Fin 18) 24 24 9 4 0 :=
  (NormalRoute.join seed5graph4cell0 (NormalRoute.join seed5graph4cell1 (NormalRoute.join seed5graph4cell2 seed5graph4cell3)))

private def row_5_5_0_0 : PairCell.Row := ⟨24,24,9,5,0,some 8,0,none,643789,[],[]⟩
private def price_5_5_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_5_5_0_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,5,0,some 8⟩,0,none,643789,none⟩ :=
  PairLeaves.paired row_5_5_0_0 price_5_5_0_0 (by decide +kernel) (none) (by decide)

private theorem seed5graph5cell0 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,5,0,some 8⟩ :=
  beginAt _ leaf_5_5_0_0

private def row_5_5_1_0 : PairCell.Row := ⟨24,24,9,5,9,some 336,0,none,643789,[MeasuredChoices.test1461,MeasuredChoices.test1471],[]⟩
private theorem leaf_5_5_1_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,5,9,some 336⟩,0,none,643789,none⟩ :=
  PairLeaves.three row_5_5_1_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph5cell1 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,5,9,some 336⟩ :=
  beginAt _ leaf_5_5_1_0

private def row_5_5_2_0 : PairCell.Row := ⟨24,24,9,5,337,some 1429,0,none,643789,[MeasuredChoices.test1531],[]⟩
private theorem leaf_5_5_2_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,5,337,some 1429⟩,0,none,643789,none⟩ :=
  PairLeaves.three row_5_5_2_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph5cell2 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,5,337,some 1429⟩ :=
  beginAt _ leaf_5_5_2_0

private def row_5_5_3_0 : PairCell.Row := ⟨24,24,9,5,1430,none,0,none,643789,[MeasuredChoices.test1436,MeasuredChoices.test1534],[]⟩
private theorem leaf_5_5_3_0 : PairRoute.Done (4:Fin 18) ⟨⟨24,24,9,5,1430,none⟩,0,none,643789,none⟩ :=
  PairLeaves.three row_5_5_3_0 (by decide +kernel) (by decide) (none)

private theorem seed5graph5cell3 : NormalRoute.Done (4:Fin 18) ⟨24,24,9,5,1430,none⟩ :=
  beginAt _ leaf_5_5_3_0

private theorem seed5graph5 : NormalRoute.Tail (4:Fin 18) 24 24 9 5 0 :=
  (NormalRoute.join seed5graph5cell0 (NormalRoute.join seed5graph5cell1 (NormalRoute.join seed5graph5cell2 seed5graph5cell3)))

private def row_9_1_0_0 : PairCell.Row := ⟨27,27,9,1,0,some 194,0,none,128757,[],[]⟩
private def price_9_1_0_0 : PairPrices.Decision := ⟨.affine,.intersection,.impossible,0⟩
private theorem leaf_9_1_0_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,1,0,some 194⟩,0,none,128757,none⟩ :=
  PairLeaves.paired row_9_1_0_0 price_9_1_0_0 (by decide +kernel) (none) (by decide)

private theorem seed9graph1cell0 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,1,0,some 194⟩ :=
  beginAt _ leaf_9_1_0_0

private def row_9_1_1_0 : PairCell.Row := ⟨27,27,9,1,195,none,0,none,128757,[MeasuredChoices.test0,MeasuredChoices.test11],[]⟩
private theorem leaf_9_1_1_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,1,195,none⟩,0,none,128757,none⟩ :=
  PairLeaves.three row_9_1_1_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph1cell1 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,1,195,none⟩ :=
  beginAt _ leaf_9_1_1_0

private theorem seed9graph1 : NormalRoute.Tail (8:Fin 18) 27 27 9 1 0 :=
  (NormalRoute.join seed9graph1cell0 seed9graph1cell1)

private def row_9_2_0_0 : PairCell.Row := ⟨27,27,9,2,0,some 34,0,none,257515,[],[]⟩
private def price_9_2_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.surface,0⟩
private theorem leaf_9_2_0_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,2,0,some 34⟩,0,none,257515,none⟩ :=
  PairLeaves.paired row_9_2_0_0 price_9_2_0_0 (by decide +kernel) (none) (by decide)

private theorem seed9graph2cell0 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,2,0,some 34⟩ :=
  beginAt _ leaf_9_2_0_0

private def row_9_2_1_0 : PairCell.Row := ⟨27,27,9,2,35,some 123,0,none,257515,[MeasuredChoices.test43],[]⟩
private def price_9_2_1_0 : PairPrices.Decision := ⟨.marked,.intersection,.impossible,0⟩
private theorem leaf_9_2_1_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,2,35,some 123⟩,0,none,257515,none⟩ :=
  PairLeaves.paired row_9_2_1_0 price_9_2_1_0 (by decide +kernel) (none) (by decide)

private theorem seed9graph2cell1 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,2,35,some 123⟩ :=
  beginAt _ leaf_9_2_1_0

private def row_9_2_2_0 : PairCell.Row := ⟨27,27,9,2,124,some 658,0,none,257515,[MeasuredChoices.test88],[]⟩
private def price_9_2_2_0 : PairPrices.Decision := ⟨.marked,.intersection,.impossible,0⟩
private theorem leaf_9_2_2_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,2,124,some 658⟩,0,none,257515,none⟩ :=
  PairLeaves.paired row_9_2_2_0 price_9_2_2_0 (by decide +kernel) (none) (by decide)

private theorem seed9graph2cell2 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,2,124,some 658⟩ :=
  beginAt _ leaf_9_2_2_0

private def row_9_2_3_0 : PairCell.Row := ⟨27,27,9,2,659,none,0,none,257515,[MeasuredChoices.test27,MeasuredChoices.test94],[]⟩
private theorem leaf_9_2_3_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,2,659,none⟩,0,none,257515,none⟩ :=
  PairLeaves.excluded row_9_2_3_0 (by decide +kernel) none

private theorem seed9graph2cell3 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,2,659,none⟩ :=
  beginAt _ leaf_9_2_3_0

private theorem seed9graph2 : NormalRoute.Tail (8:Fin 18) 27 27 9 2 0 :=
  (NormalRoute.join seed9graph2cell0 (NormalRoute.join seed9graph2cell1 (NormalRoute.join seed9graph2cell2 seed9graph2cell3)))

private def row_9_3_0_0 : PairCell.Row := ⟨27,27,9,3,0,some 19,0,none,386273,[],[]⟩
private def price_9_3_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_9_3_0_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,3,0,some 19⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_9_3_0_0 price_9_3_0_0 (by decide +kernel) (none) (by decide)

private theorem seed9graph3cell0 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,3,0,some 19⟩ :=
  beginAt _ leaf_9_3_0_0

private def row_9_3_1_0 : PairCell.Row := ⟨27,27,9,3,20,some 67,0,none,386273,[MeasuredChoices.test773,MeasuredChoices.test856],[]⟩
private theorem leaf_9_3_1_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,3,20,some 67⟩,0,none,386273,none⟩ :=
  PairLeaves.three row_9_3_1_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph3cell1 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,3,20,some 67⟩ :=
  beginAt _ leaf_9_3_1_0

private def row_9_3_2_0 : PairCell.Row := ⟨27,27,9,3,68,some 653,0,none,386273,[MeasuredChoices.test1146,MeasuredChoices.test1147],[]⟩
private theorem leaf_9_3_2_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,3,68,some 653⟩,0,none,386273,none⟩ :=
  PairLeaves.three row_9_3_2_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph3cell2 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,3,68,some 653⟩ :=
  beginAt _ leaf_9_3_2_0

private def row_9_3_3_0 : PairCell.Row := ⟨27,27,9,3,654,none,0,none,386273,[MeasuredChoices.test649,MeasuredChoices.test1154],[]⟩
private theorem leaf_9_3_3_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,3,654,none⟩,0,none,386273,none⟩ :=
  PairLeaves.excluded row_9_3_3_0 (by decide +kernel) none

private theorem seed9graph3cell3 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,3,654,none⟩ :=
  beginAt _ leaf_9_3_3_0

private theorem seed9graph3 : NormalRoute.Tail (8:Fin 18) 27 27 9 3 0 :=
  (NormalRoute.join seed9graph3cell0 (NormalRoute.join seed9graph3cell1 (NormalRoute.join seed9graph3cell2 seed9graph3cell3)))

private def row_9_4_0_0 : PairCell.Row := ⟨27,27,9,4,0,some 13,0,none,515031,[],[]⟩
private def price_9_4_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_9_4_0_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,4,0,some 13⟩,0,none,515031,none⟩ :=
  PairLeaves.paired row_9_4_0_0 price_9_4_0_0 (by decide +kernel) (none) (by decide)

private theorem seed9graph4cell0 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,4,0,some 13⟩ :=
  beginAt _ leaf_9_4_0_0

private def row_9_4_1_0 : PairCell.Row := ⟨27,27,9,4,14,some 174,0,none,515031,[MeasuredChoices.test1256,MeasuredChoices.test1257],[]⟩
private theorem leaf_9_4_1_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,4,14,some 174⟩,0,none,515031,none⟩ :=
  PairLeaves.three row_9_4_1_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph4cell1 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,4,14,some 174⟩ :=
  beginAt _ leaf_9_4_1_0

private def row_9_4_2_0 : PairCell.Row := ⟨27,27,9,4,175,some 1063,0,none,515031,[MeasuredChoices.test1374],[]⟩
private theorem leaf_9_4_2_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,4,175,some 1063⟩,0,none,515031,none⟩ :=
  PairLeaves.three row_9_4_2_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph4cell2 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,4,175,some 1063⟩ :=
  beginAt _ leaf_9_4_2_0

private def row_9_4_3_0 : PairCell.Row := ⟨27,27,9,4,1064,none,0,none,515031,[MeasuredChoices.test1372,MeasuredChoices.test1379],[]⟩
private theorem leaf_9_4_3_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,4,1064,none⟩,0,none,515031,none⟩ :=
  PairLeaves.excluded row_9_4_3_0 (by decide +kernel) none

private theorem seed9graph4cell3 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,4,1064,none⟩ :=
  beginAt _ leaf_9_4_3_0

private theorem seed9graph4 : NormalRoute.Tail (8:Fin 18) 27 27 9 4 0 :=
  (NormalRoute.join seed9graph4cell0 (NormalRoute.join seed9graph4cell1 (NormalRoute.join seed9graph4cell2 seed9graph4cell3)))

private def row_9_5_0_0 : PairCell.Row := ⟨27,27,9,5,0,some 10,0,none,643789,[],[]⟩
private def price_9_5_0_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_9_5_0_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,5,0,some 10⟩,0,none,643789,none⟩ :=
  PairLeaves.paired row_9_5_0_0 price_9_5_0_0 (by decide +kernel) (none) (by decide)

private theorem seed9graph5cell0 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,5,0,some 10⟩ :=
  beginAt _ leaf_9_5_0_0

private def row_9_5_1_0 : PairCell.Row := ⟨27,27,9,5,11,some 317,0,none,643789,[MeasuredChoices.test1461,MeasuredChoices.test1471],[]⟩
private theorem leaf_9_5_1_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,5,11,some 317⟩,0,none,643789,none⟩ :=
  PairLeaves.three row_9_5_1_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph5cell1 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,5,11,some 317⟩ :=
  beginAt _ leaf_9_5_1_0

private def row_9_5_2_0 : PairCell.Row := ⟨27,27,9,5,318,some 1362,0,none,643789,[MeasuredChoices.test1531],[]⟩
private theorem leaf_9_5_2_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,5,318,some 1362⟩,0,none,643789,none⟩ :=
  PairLeaves.three row_9_5_2_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph5cell2 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,5,318,some 1362⟩ :=
  beginAt _ leaf_9_5_2_0

private def row_9_5_3_0 : PairCell.Row := ⟨27,27,9,5,1363,none,0,none,643789,[MeasuredChoices.test1436,MeasuredChoices.test1534],[]⟩
private theorem leaf_9_5_3_0 : PairRoute.Done (8:Fin 18) ⟨⟨27,27,9,5,1363,none⟩,0,none,643789,none⟩ :=
  PairLeaves.three row_9_5_3_0 (by decide +kernel) (by decide) (none)

private theorem seed9graph5cell3 : NormalRoute.Done (8:Fin 18) ⟨27,27,9,5,1363,none⟩ :=
  beginAt _ leaf_9_5_3_0

private theorem seed9graph5 : NormalRoute.Tail (8:Fin 18) 27 27 9 5 0 :=
  (NormalRoute.join seed9graph5cell0 (NormalRoute.join seed9graph5cell1 (NormalRoute.join seed9graph5cell2 seed9graph5cell3)))

theorem count5 (a : ℕ) (positive : 0 < a) (bound : a ≤ 5) :
    NormalRoute.Tail (4:Fin 18) 24 24 9 a 0 := by
  interval_cases a
  · exact seed5graph1
  · exact seed5graph2
  · exact seed5graph3
  · exact seed5graph4
  · exact seed5graph5

theorem count9 (a : ℕ) (positive : 0 < a) (bound : a ≤ 5) :
    NormalRoute.Tail (8:Fin 18) 27 27 9 a 0 := by
  interval_cases a
  · exact seed9graph1
  · exact seed9graph2
  · exact seed9graph3
  · exact seed9graph4
  · exact seed9graph5

end Research6970.Height2313.Research6969.BandGradeReceipts
