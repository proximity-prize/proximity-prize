import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research

 








namespace ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research

open scoped BigOperators
open ContactAnchoredOneFamilySelector6750Research

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

 

def hardMinT (y r : Nat) : Nat :=
  match y, r with
  | 38, 14 => 1647
  | 39, 14 => 1596
  | 40, 13 => 1647 | 40, 14 => 1549
  | 41, 13 => 1600 | 41, 14 => 1504
  | 42, 12 => 1666 | 42, 13 => 1555 | 42, 14 => 1462
  | 43, 12 => 1622 | 43, 13 => 1514 | 43, 14 => 1422
  | 44, 12 => 1580 | 44, 13 => 1474 | 44, 14 => 1384
  | 45, 11 => 1665 | 45, 12 => 1540 | 45, 13 => 1437 | 45, 14 => 1349
  | 46, 11 => 1625 | 46, 12 => 1503 | 46, 13 => 1401 | 46, 14 => 1315
  | 47, 11 => 1586 | 47, 12 => 1467 | 47, 13 => 1367 | 47, 14 => 1283
  | 48, 11 => 1550 | 48, 12 => 1433 | 48, 13 => 1335 | 48, 14 => 1253
  | 49, 10 => 1655 | 49, 11 => 1515 | 49, 12 => 1400 | 49, 13 => 1305 | 49, 14 => 1224
  | 50, 10 => 1619 | 50, 11 => 1482 | 50, 12 => 1369 | 50, 13 => 1276 | 50, 14 => 1196
  | 51, 10 => 1585 | 51, 11 => 1450 | 51, 12 => 1340 | 51, 13 => 1248 | 51, 14 => 1170
  | 52, 10 => 1552 | 52, 11 => 1420 | 52, 12 => 1312 | 52, 13 => 1221 | 52, 14 => 1145
  | 53, 9 => 1681 | 53, 10 => 1520 | 53, 11 => 1391 | 53, 12 => 1285 | 53, 13 => 1196 | 53, 14 => 1121
  | 54, 9 => 1648 | 54, 10 => 1490 | 54, 11 => 1363 | 54, 12 => 1259 | 54, 13 => 1172 | 54, 14 => 1098
  | 55, 9 => 1616 | 55, 10 => 1461 | 55, 11 => 1336 | 55, 12 => 1234 | 55, 13 => 1149 | 55, 14 => 1076
  | 56, 9 => 1586 | 56, 10 => 1433 | 56, 11 => 1311 | 56, 12 => 1210 | 56, 13 => 1126 | 56, 14 => 1055
  | 57, 9 => 1556 | 57, 10 => 1407 | 57, 11 => 1286 | 57, 12 => 1188 | 57, 13 => 1105 | 57, 14 => 1035
  | 58, 9 => 1528 | 58, 10 => 1381 | 58, 11 => 1263 | 58, 12 => 1166 | 58, 13 => 1085 | 58, 14 => 1016
  | 59, 8 => 1686 | 59, 9 => 1501 | 59, 10 => 1356 | 59, 11 => 1240 | 59, 12 => 1145 | 59, 13 => 1065 | 59, 14 => 997
  | 60, 8 => 1656 | 60, 9 => 1475 | 60, 10 => 1333 | 60, 11 => 1218 | 60, 12 => 1124 | 60, 13 => 1046 | 60, 14 => 980
  | 61, 8 => 1628 | 61, 9 => 1450 | 61, 10 => 1310 | 61, 11 => 1197 | 61, 12 => 1105 | 61, 13 => 1028 | 61, 14 => 963
  | 62, 8 => 1601 | 62, 9 => 1425 | 62, 10 => 1288 | 62, 11 => 1177 | 62, 12 => 1086 | 62, 13 => 1010 | 62, 14 => 946
  | 63, 8 => 1575 | 63, 9 => 1402 | 63, 10 => 1266 | 63, 11 => 1158 | 63, 12 => 1068 | 63, 13 => 994 | 63, 14 => 930
  | 64, 8 => 1549 | 64, 9 => 1379 | 64, 10 => 1246 | 64, 11 => 1139 | 64, 12 => 1051 | 64, 13 => 977 | 64, 14 => 915
  | 65, 8 => 1525 | 65, 9 => 1357 | 65, 10 => 1226 | 65, 11 => 1121 | 65, 12 => 1034 | 65, 13 => 962 | 65, 14 => 900
  | 66, 8 => 1501 | 66, 9 => 1336 | 66, 10 => 1207 | 66, 11 => 1103 | 66, 12 => 1018 | 66, 13 => 946 | 66, 14 => 886
  | _, _ => 0

 

def hardLastR1658 (y : Nat) : Nat :=
  if y ≤ 40 then 14 else
  if y ≤ 43 then 13 else
  if y ≤ 45 then 12 else
  if y ≤ 49 then 11 else
  if y ≤ 54 then 10 else
  if y ≤ 60 then 9 else 8

def hardMaxT (y r : Nat) : Nat :=
  if r ≤ hardLastR1658 y then 1698 else 1699

 

def HardCell (t y r : Nat) : Prop :=
  38 ≤ y ∧ y ≤ 66 ∧
  hostileMinR y ≤ r ∧ r ≤ 14 ∧
  hardMinT y r ≤ t ∧ t ≤ hardMaxT y r

theorem HardCell.y_lower {t y r : Nat} (h : HardCell t y r) : 38 ≤ y := h.1
theorem HardCell.y_upper {t y r : Nat} (h : HardCell t y r) : y ≤ 66 := h.2.1
theorem HardCell.r_lower {t y r : Nat} (h : HardCell t y r) :
    hostileMinR y ≤ r := h.2.2.1
theorem HardCell.r_upper {t y r : Nat} (h : HardCell t y r) : r ≤ 14 :=
  h.2.2.2.1
theorem HardCell.t_lower {t y r : Nat} (h : HardCell t y r) :
    hardMinT y r ≤ t := h.2.2.2.2.1
theorem HardCell.t_upper {t y r : Nat} (h : HardCell t y r) :
    t ≤ hardMaxT y r := h.2.2.2.2.2

theorem hardMaxT_le_1659 (y r : Nat) : hardMaxT y r ≤ 1699 := by
  unfold hardMaxT
  split <;> omega

theorem HardCell.t_le_1659 {t y r : Nat} (h : HardCell t y r) : t ≤ 1699 :=
  h.t_upper.trans (hardMaxT_le_1659 y r)

 

theorem channelCount_mono_total_of_ys_le
    {T₁ T₂ ys slope : Nat} (hys : ys ≤ T₁) (hT : T₁ ≤ T₂) :
    channelCount T₁ ys slope ≤ channelCount T₂ ys slope := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  rw [channelCount_add_of_Y_le_T hys]
  exact Nat.le_add_right _ _

 
theorem selectorDeficit_antitone_t
    {t₁ t₂ y r : Nat}
    (ht : t₁ ≤ t₂) (htbase : t₂ ≤ familyBaseTotal)
    (hface : familyYSCap - y ≤ familyBaseTotal - t₂) :
    selectorDeficit t₂ y r ≤ selectorDeficit t₁ y r := by
  have hT : familyBaseTotal - t₂ ≤ familyBaseTotal - t₁ := by omega
  have hchannels :
      residualChannels t₂ y r familyBaseTotal ≤
        residualChannels t₁ y r familyBaseTotal := by
    unfold residualChannels
    exact channelCount_mono_total_of_ys_le hface hT
  unfold selectorDeficit
  exact Nat.sub_le_sub_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left cutWidth hchannels) 1)
    (affineNullity familyBaseTotal)

theorem selectedTotal_mono_of_deficit
    {t₁ t₂ y r : Nat} (hslope : 0 < selectorSlope y r)
    (hdeficit : selectorDeficit t₂ y r ≤ selectorDeficit t₁ y r) :
    selectedTotal t₂ y r ≤ selectedTotal t₁ y r := by
  have hceil := (gc_smul_ceilDiv hslope).monotone_l hdeficit
  unfold selectedTotal
  omega

 

theorem hard_boundary_numeric
    {y r : Nat} (hylo : 38 ≤ y) (hyhi : y ≤ 66)
    (hrlo : hostileMinR y ≤ r) (hrhi : r ≤ 14) :
    selectorDeficit (hardMinT y r) y r ≤
        selectorSlope y r * (familyMaxTotal - familyBaseTotal) ∧
      selectedTotal (hardMinT y r) y r - hardMinT y r ≤ 2650 := by
  interval_cases y <;> interval_cases r <;>
    norm_num [hardMinT, hostileMinR, selectorDeficit, selectorSlope,
      selectedTotal, residualChannels, channelCount, channelSlope,
      affineNullity, nullitySlope, nullityConstant, cutWidth,
      familyBaseTotal, familyMaxTotal, familyYSCap, familySlopeCap,
      Nat.ceilDiv_eq_add_pred_div, Finset.sum_range_succ] at *

 

theorem HardCell.selector_inputs {t y r : Nat} (h : HardCell t y r) :
    t ≤ familyBaseTotal ∧
    familyYSCap - y ≤ familyBaseTotal - t ∧
    0 < selectorSlope y r := by
  refine ⟨?_, ?_, selectorSlope_pos_of_hostile_band
    h.y_lower h.y_upper h.r_lower⟩
  · exact h.t_le_1659.trans (by norm_num [familyBaseTotal])
  · have ht := h.t_le_1659
    have hy := h.y_lower
    norm_num [familyYSCap, familyBaseTotal] at *
    omega

theorem HardCell.selectorDeficit_le_max {t y r : Nat}
    (h : HardCell t y r) :
    selectorDeficit t y r ≤
      selectorSlope y r * (familyMaxTotal - familyBaseTotal) := by
  have hinputs := h.selector_inputs
  have hmono :
      selectorDeficit t y r ≤ selectorDeficit (hardMinT y r) y r :=
    selectorDeficit_antitone_t (t₁ := hardMinT y r) (t₂ := t)
      (y := y) (r := r) h.t_lower hinputs.1 hinputs.2.1
  exact hmono.trans
    (hard_boundary_numeric h.y_lower h.y_upper h.r_lower h.r_upper).1

 
theorem HardCell.selectedTotal_le_4186 {t y r : Nat}
    (h : HardCell t y r) : selectedTotal t y r ≤ familyMaxTotal :=
  selectedTotal_le_familyMaxTotal h.selector_inputs.2.2
    h.selectorDeficit_le_max

 



def quotientWeightedCut (y r : Nat) : Nat :=
  familyMultiplicity * agreements - (contactSlope * y - r) - cutWidth

 

theorem HardCell.quotient_caps {t y r : Nat} (h : HardCell t y r) :
    selectedTotal t y r - t ≤ 2650 ∧
    familyYSCap - y ≤ 49 ∧
    familySlopeCap - r ≤ 10 ∧
    2756580 ≤ quotientWeightedCut y r := by
  have hslope := h.selector_inputs.2.2
  have hdef :
      selectorDeficit t y r ≤ selectorDeficit (hardMinT y r) y r :=
    selectorDeficit_antitone_t (t₁ := hardMinT y r) (t₂ := t)
      (y := y) (r := r) h.t_lower h.selector_inputs.1
        h.selector_inputs.2.1
  have hselected := selectedTotal_mono_of_deficit hslope hdef
  have hboundary :=
    (hard_boundary_numeric h.y_lower h.y_upper h.r_lower h.r_upper).2
  have hr : 8 ≤ r := by
    apply (show 8 ≤ hostileMinR y from ?_).trans h.r_lower
    unfold hostileMinR
    split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      ((Nat.sub_le_sub_right hselected t).trans
        (Nat.sub_le_sub_left h.t_lower
          (selectedTotal (hardMinT y r) y r))).trans hboundary
  · norm_num [familyYSCap]
    have hy := h.y_lower
    omega
  ·
    norm_num [familySlopeCap]
    omega
  · unfold quotientWeightedCut
    norm_num [familyMultiplicity, agreements, contactSlope, cutWidth]
    have hy := h.y_upper
    omega

 


theorem HardCell.closes_actual_rank_gap
    {t y r : Nat} (h : HardCell t y r)
    (hnullity : affineNullity (selectedTotal t y r) ≤
      actualNullity (selectedTotal t y r)) :
    actualRankGapHolds t y r (selectedTotal t y r) :=
  selectedTotal_closes_actual_rank_gap h.selector_inputs.1
    h.selector_inputs.2.1 h.selector_inputs.2.2 hnullity

theorem HardCell.actualNullity_pos
    {t y r : Nat} (h : HardCell t y r)
    (hnullity : affineNullity (selectedTotal t y r) ≤
      actualNullity (selectedTotal t y r)) :
    0 < actualNullity (selectedTotal t y r) := by
  have hgap := h.closes_actual_rank_gap hnullity
  unfold actualRankGapHolds at hgap
  omega

end ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research.hard_boundary_numeric
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research.HardCell.selectedTotal_le_4186
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research.HardCell.quotient_caps
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research.HardCell.closes_actual_rank_gap
