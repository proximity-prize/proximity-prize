import ProximityPrize.SubmissionLower.R6970Height2308ContentAdapter
import ProximityPrize.SubmissionLower.R6970Height2308PowerBounds
import ProximityPrize.SubmissionLower.R6970Height2313AlternateTests
import ProximityPrize.SubmissionLower.Bundle6970_7a0ead0a3fc2768d
import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.R6970Height2313MeasuredTests03
import ProximityPrize.SubmissionLower.Bundle6970_fb46f5d61219415e

set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 25000

namespace Research6970.Height2313.Research6969.BandPowerReceipts

open _root_.Research6970.Height2313.Research6969

private theorem beginAt {i} (r : NormalRoute.Region)
    (all : PairRoute.Done i ⟨r,0,none,r.graph*(131071-2313)-1,none⟩) :
    NormalRoute.Done i r := by
  intro s h
  have w := NormalGeometry.base s
  rw [h.2.2.2.1] at w
  exact all s ⟨h,Nat.zero_le _,by simp,w,by simp⟩

private theorem rect43 :
    _root_.Research6969.PhysicalWindow.Cover
      (_root_.Research6969.PowerExclusion.Positive (PowerSheets.entry 50 3 6 43 386273))
      2313 2308 [2309, 2313] :=
  ⟨by decide, by decide, (show _root_.Research6969.PowerExclusion.Positive (PowerSheets.entry 50 3 6 43 386273) 2308 2309 by decide +kernel), ⟨by decide, by decide, (show _root_.Research6969.PowerExclusion.Positive (PowerSheets.entry 50 3 6 43 386273) 2310 2313 by decide +kernel), rfl⟩⟩

private theorem above43 {i} : NormalRoute.Done i ⟨50,63,9,3,43,some 48⟩ :=
  NormalRoute.power_at_base _ 386273 (by decide) rect43 (by decide) (by decide) (by decide)

private theorem rect1701 :
    _root_.Research6969.PhysicalWindow.Cover
      (_root_.Research6969.PowerExclusion.Positive (PowerSheets.entry 22 6 3 1701 772547))
      2313 2308 [2313] :=
  ⟨by decide, by decide, by decide +kernel, rfl⟩

private theorem above1701 : NormalRoute.Done (0:Fin 18) ⟨22,22,9,6,1701,some 2048⟩ :=
  NormalRoute.power_at_base _ 772547 (by decide) rect1701 (by decide) (by decide) (by decide)

private def row_seed1_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 41,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed1_41_0 : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩
private theorem leaf_seed1_41_0 : PairRoute.Done (0:Fin 18) ⟨⟨50,63,9,3,41,some 41⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed1_41_0 price_seed1_41_0 (by decide +kernel) (none) (by decide)

private def row_seed1_41_1 : PairCell.Row := ⟨50,63,9,3,42,some 42,0,some 10,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1821,AlternateBanks.test26221]⟩
private def price_seed1_41_1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed1_41_1 : PairRoute.Done (0:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,0,some 10,386273,none⟩ :=
  PairLeaves.paired row_seed1_41_1 price_seed1_41_1 (by decide +kernel) (none) (by decide)

private def row_seed1_41_2 : PairCell.Row := ⟨50,63,9,3,42,some 42,11,some 13,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AlternateBanks.test26225]⟩
private def price_seed1_41_2 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed1_41_2 : PairRoute.Done (0:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,11,some 13,386273,none⟩ :=
  PairLeaves.paired row_seed1_41_2 price_seed1_41_2 (by decide +kernel) (none) (by decide)

private def row_seed1_41_3 : PairCell.Row := ⟨50,63,9,3,42,some 42,14,some 16,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1835]⟩
private theorem leaf_seed1_41_3 : PairRoute.Done (0:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,14,some 16,386273,none⟩ :=
  PairLeaves.three row_seed1_41_3 (by decide +kernel) (by decide) (none)

private def row_seed1_41_4 : PairCell.Row := ⟨50,63,9,3,42,some 42,17,some 21,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1838]⟩
private theorem leaf_seed1_41_4 : PairRoute.Done (0:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,17,some 21,386273,none⟩ :=
  PairLeaves.three row_seed1_41_4 (by decide +kernel) (by decide) (none)

private def row_seed1_41_5 : PairCell.Row := ⟨50,63,9,3,42,some 42,22,some 42,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1843]⟩
private theorem leaf_seed1_41_5 : PairRoute.Done (0:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,22,some 42,386273,none⟩ :=
  PairLeaves.three row_seed1_41_5 (by decide +kernel) (by decide) (none)

theorem cover1_41 : NormalRoute.Done (0:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ (PairRoute.splitSeed 41 leaf_seed1_41_0 (PairRoute.axes_of_total (PairRoute.axis 21 (PairRoute.axis 10 leaf_seed1_41_1 (PairRoute.axis 16 (PairRoute.axis 13 leaf_seed1_41_2 leaf_seed1_41_3) leaf_seed1_41_4)) leaf_seed1_41_5)))) above43)

private def row_seed2_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 41,0,some 10,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1821,AlternateBanks.test26221]⟩
private def price_seed2_41_0 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_41_0 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,41,some 41⟩,0,some 10,386273,none⟩ :=
  PairLeaves.paired row_seed2_41_0 price_seed2_41_0 (by decide +kernel) (none) (by decide)

private def row_seed2_41_1 : PairCell.Row := ⟨50,63,9,3,41,some 41,11,some 13,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AlternateBanks.test26225]⟩
private def price_seed2_41_1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_41_1 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,41,some 41⟩,11,some 13,386273,none⟩ :=
  PairLeaves.paired row_seed2_41_1 price_seed2_41_1 (by decide +kernel) (none) (by decide)

private def row_seed2_41_2 : PairCell.Row := ⟨50,63,9,3,41,some 41,14,some 15,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1835]⟩
private theorem leaf_seed2_41_2 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,41,some 41⟩,14,some 15,386273,none⟩ :=
  PairLeaves.three row_seed2_41_2 (by decide +kernel) (by decide) (none)

private def row_seed2_41_3 : PairCell.Row := ⟨50,63,9,3,41,some 41,16,some 20,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1837]⟩
private theorem leaf_seed2_41_3 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,41,some 41⟩,16,some 20,386273,none⟩ :=
  PairLeaves.three row_seed2_41_3 (by decide +kernel) (by decide) (none)

private def row_seed2_41_4 : PairCell.Row := ⟨50,63,9,3,41,some 41,21,some 41,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1842]⟩
private theorem leaf_seed2_41_4 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,41,some 41⟩,21,some 41,386273,none⟩ :=
  PairLeaves.three row_seed2_41_4 (by decide +kernel) (by decide) (none)

private def row_seed2_41_5 : PairCell.Row := ⟨50,63,9,3,42,some 42,0,some 5,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1821,AlternateBanks.test26221]⟩
private def price_seed2_41_5 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_41_5 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,0,some 5,386273,none⟩ :=
  PairLeaves.paired row_seed2_41_5 price_seed2_41_5 (by decide +kernel) (none) (by decide)

private def row_seed2_41_6 : PairCell.Row := ⟨50,63,9,3,42,some 42,6,some 8,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1826,AxisChoices.test1827]⟩
private def price_seed2_41_6 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_41_6 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,6,some 8,386273,none⟩ :=
  PairLeaves.paired row_seed2_41_6 price_seed2_41_6 (by decide +kernel) (none) (by decide)

private def row_seed2_41_7 : PairCell.Row := ⟨50,63,9,3,42,some 42,9,some 9,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1830]⟩
private def price_seed2_41_7 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_41_7 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,9,some 9,386273,none⟩ :=
  PairLeaves.paired row_seed2_41_7 price_seed2_41_7 (by decide +kernel) (none) (by decide)

private def row_seed2_41_8 : PairCell.Row := ⟨50,63,9,3,42,some 42,10,some 10,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AlternateBanks.test26219]⟩
private def price_seed2_41_8 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_41_8 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,10,some 10,386273,none⟩ :=
  PairLeaves.paired row_seed2_41_8 price_seed2_41_8 (by decide +kernel) (none) (by decide)

private def row_seed2_41_9 : PairCell.Row := ⟨50,63,9,3,42,some 42,11,some 12,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AlternateBanks.test26225]⟩
private def price_seed2_41_9 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_41_9 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,11,some 12,386273,none⟩ :=
  PairLeaves.paired row_seed2_41_9 price_seed2_41_9 (by decide +kernel) (none) (by decide)

private def row_seed2_41_10 : PairCell.Row := ⟨50,63,9,3,42,some 42,13,some 13,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1834]⟩
private theorem leaf_seed2_41_10 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,13,some 13,386273,none⟩ :=
  PairLeaves.three row_seed2_41_10 (by decide +kernel) (by decide) (none)

private def row_seed2_41_11 : PairCell.Row := ⟨50,63,9,3,42,some 42,14,some 16,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1835]⟩
private theorem leaf_seed2_41_11 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,14,some 16,386273,none⟩ :=
  PairLeaves.three row_seed2_41_11 (by decide +kernel) (by decide) (none)

private def row_seed2_41_12 : PairCell.Row := ⟨50,63,9,3,42,some 42,17,some 21,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1838]⟩
private theorem leaf_seed2_41_12 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,17,some 21,386273,none⟩ :=
  PairLeaves.three row_seed2_41_12 (by decide +kernel) (by decide) (none)

private def row_seed2_41_13 : PairCell.Row := ⟨50,63,9,3,42,some 42,22,some 42,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[AxisChoices.test1843]⟩
private theorem leaf_seed2_41_13 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,42,some 42⟩,22,some 42,386273,none⟩ :=
  PairLeaves.three row_seed2_41_13 (by decide +kernel) (by decide) (none)

theorem cover2_41 : NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ (PairRoute.splitSeed 41 (PairRoute.axes_of_total (PairRoute.axis 20 (PairRoute.axis 10 leaf_seed2_41_0 (PairRoute.axis 15 (PairRoute.axis 13 leaf_seed2_41_1 leaf_seed2_41_2) leaf_seed2_41_3)) leaf_seed2_41_4)) (PairRoute.axes_of_total (PairRoute.axis 21 (PairRoute.axis 10 (PairRoute.axis 5 leaf_seed2_41_5 (PairRoute.axis 8 leaf_seed2_41_6 (PairRoute.axis 9 leaf_seed2_41_7 leaf_seed2_41_8))) (PairRoute.axis 16 (PairRoute.axis 13 (PairRoute.axis 12 leaf_seed2_41_9 leaf_seed2_41_10) leaf_seed2_41_11) leaf_seed2_41_12)) leaf_seed2_41_13)))) above43)

private def row_seed2_40_0 : PairCell.Row := ⟨50,63,9,3,40,some 40,0,some 10,386273,[MeasuredChoices.test1119,AlternateBanks.test26216],[AxisChoices.test1821,AlternateBanks.test26221]⟩
private def price_seed2_40_0 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_40_0 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,40,some 40⟩,0,some 10,386273,none⟩ :=
  PairLeaves.paired row_seed2_40_0 price_seed2_40_0 (by decide +kernel) (none) (by decide)

private def row_seed2_40_1 : PairCell.Row := ⟨50,63,9,3,40,some 40,11,some 13,386273,[MeasuredChoices.test1119,AlternateBanks.test26216],[AlternateBanks.test26225]⟩
private def price_seed2_40_1 : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
private theorem leaf_seed2_40_1 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,40,some 40⟩,11,some 13,386273,none⟩ :=
  PairLeaves.paired row_seed2_40_1 price_seed2_40_1 (by decide +kernel) (none) (by decide)

private def row_seed2_40_2 : PairCell.Row := ⟨50,63,9,3,40,some 40,14,some 15,386273,[MeasuredChoices.test1119,AlternateBanks.test26216],[AxisChoices.test1835]⟩
private theorem leaf_seed2_40_2 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,40,some 40⟩,14,some 15,386273,none⟩ :=
  PairLeaves.three row_seed2_40_2 (by decide +kernel) (by decide) (none)

private def row_seed2_40_3 : PairCell.Row := ⟨50,63,9,3,40,some 40,16,some 20,386273,[MeasuredChoices.test1119,AlternateBanks.test26216],[AxisChoices.test1837]⟩
private theorem leaf_seed2_40_3 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,40,some 40⟩,16,some 20,386273,none⟩ :=
  PairLeaves.three row_seed2_40_3 (by decide +kernel) (by decide) (none)

private def row_seed2_40_4 : PairCell.Row := ⟨50,63,9,3,40,some 40,21,some 40,386273,[MeasuredChoices.test1119,AlternateBanks.test26216],[AxisChoices.test1842]⟩
private theorem leaf_seed2_40_4 : PairRoute.Done (1:Fin 18) ⟨⟨50,63,9,3,40,some 40⟩,21,some 40,386273,none⟩ :=
  PairLeaves.three row_seed2_40_4 (by decide +kernel) (by decide) (none)

theorem cover2_40 : NormalRoute.Done (1:Fin 18) ⟨50,63,10,3,40,some 40⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (beginAt _ (PairRoute.axes_of_total (PairRoute.axis 20 (PairRoute.axis 10 leaf_seed2_40_0 (PairRoute.axis 15 (PairRoute.axis 13 leaf_seed2_40_1 leaf_seed2_40_2) leaf_seed2_40_3)) leaf_seed2_40_4)))

private def row_seed3_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 42,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed3_41_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed3_41_0 : PairRoute.Done (2:Fin 18) ⟨⟨50,63,9,3,41,some 42⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed3_41_0 price_seed3_41_0 (by decide +kernel) (none) (by decide)

theorem cover3_41 : NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ leaf_seed3_41_0) above43)

private def row_seed3_40_0 : PairCell.Row := ⟨50,63,9,3,40,some 40,0,none,386273,[MeasuredChoices.test1119,AlternateBanks.test26216],[]⟩
private def price_seed3_40_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed3_40_0 : PairRoute.Done (2:Fin 18) ⟨⟨50,63,9,3,40,some 40⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed3_40_0 price_seed3_40_0 (by decide +kernel) (none) (by decide)

theorem cover3_40 : NormalRoute.Done (2:Fin 18) ⟨50,63,10,3,40,some 40⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (beginAt _ leaf_seed3_40_0)

private def row_seed4_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 42,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed4_41_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed4_41_0 : PairRoute.Done (3:Fin 18) ⟨⟨50,63,9,3,41,some 42⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed4_41_0 price_seed4_41_0 (by decide +kernel) (none) (by decide)

theorem cover4_41 : NormalRoute.Done (3:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ leaf_seed4_41_0) above43)

private def row_seed5_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 42,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed5_41_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed5_41_0 : PairRoute.Done (4:Fin 18) ⟨⟨50,63,9,3,41,some 42⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed5_41_0 price_seed5_41_0 (by decide +kernel) (none) (by decide)

theorem cover5_41 : NormalRoute.Done (4:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ leaf_seed5_41_0) above43)

private def row_seed6_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 42,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed6_41_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed6_41_0 : PairRoute.Done (5:Fin 18) ⟨⟨50,63,9,3,41,some 42⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed6_41_0 price_seed6_41_0 (by decide +kernel) (none) (by decide)

theorem cover6_41 : NormalRoute.Done (5:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ leaf_seed6_41_0) above43)

private def row_seed7_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 42,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed7_41_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed7_41_0 : PairRoute.Done (6:Fin 18) ⟨⟨50,63,9,3,41,some 42⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed7_41_0 price_seed7_41_0 (by decide +kernel) (none) (by decide)

theorem cover7_41 : NormalRoute.Done (6:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ leaf_seed7_41_0) above43)

private def row_seed8_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 42,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed8_41_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed8_41_0 : PairRoute.Done (7:Fin 18) ⟨⟨50,63,9,3,41,some 42⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed8_41_0 price_seed8_41_0 (by decide +kernel) (none) (by decide)

theorem cover8_41 : NormalRoute.Done (7:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ leaf_seed8_41_0) above43)

private def row_seed9_41_0 : PairCell.Row := ⟨50,63,9,3,41,some 42,0,none,386273,[MeasuredChoices.test1133,AlternateBanks.test21134],[]⟩
private def price_seed9_41_0 : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
private theorem leaf_seed9_41_0 : PairRoute.Done (8:Fin 18) ⟨⟨50,63,9,3,41,some 42⟩,0,none,386273,none⟩ :=
  PairLeaves.paired row_seed9_41_0 price_seed9_41_0 (by decide +kernel) (none) (by decide)

theorem cover9_41 : NormalRoute.Done (8:Fin 18) ⟨50,63,10,3,41,some 48⟩ :=
  NormalRoute.withNineBelow (by decide) (by decide) (by decide) (NormalRoute.splitSeed 42 (beginAt _ leaf_seed9_41_0) above43)

private def row_graph6_0 : PairCell.Row := ⟨22,22,9,6,1537,some 1700,0,none,772547,[MeasuredChoices.test1671],[]⟩
private theorem leaf_graph6_0 : PairRoute.Done (0:Fin 18) ⟨⟨22,22,9,6,1537,some 1700⟩,0,none,772547,none⟩ :=
  PairLeaves.three row_graph6_0 (by decide +kernel) (by decide) (none)

theorem cover1Graph6 : NormalRoute.Done (0:Fin 18) ⟨22,22,9,6,1537,some 2048⟩ :=
  NormalRoute.splitSeed 1700 (beginAt _ leaf_graph6_0) above1701

end Research6970.Height2313.Research6969.BandPowerReceipts
