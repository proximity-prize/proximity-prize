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
  | 38, 14 => 1641
  | 39, 14 => 1590
  | 40, 13 => 1639 | 40, 14 => 1543
  | 41, 13 => 1593 | 41, 14 => 1498
  | 42, 12 => 1658 | 42, 13 => 1548 | 42, 14 => 1456
  | 43, 12 => 1614 | 43, 13 => 1507 | 43, 14 => 1416
  | 44, 12 => 1572 | 44, 13 => 1467 | 44, 14 => 1379
  | 45, 11 => 1656 | 45, 12 => 1533 | 45, 13 => 1430 | 45, 14 => 1344
  | 46, 11 => 1616 | 46, 12 => 1495 | 46, 13 => 1395 | 46, 14 => 1310
  | 47, 11 => 1578 | 47, 12 => 1460 | 47, 13 => 1361 | 47, 14 => 1278
  | 48, 11 => 1541 | 48, 12 => 1426 | 48, 13 => 1329 | 48, 14 => 1248
  | 49, 10 => 1645 | 49, 11 => 1507 | 49, 12 => 1394
  | 49, 13 => 1299 | 49, 14 => 1219
  | 50, 10 => 1609 | 50, 11 => 1474 | 50, 12 => 1363
  | 50, 13 => 1270 | 50, 14 => 1192
  | 51, 10 => 1575 | 51, 11 => 1442 | 51, 12 => 1333
  | 51, 13 => 1243 | 51, 14 => 1166
  | 52, 10 => 1543 | 52, 11 => 1412 | 52, 12 => 1305
  | 52, 13 => 1216 | 52, 14 => 1141
  | 53, 9 => 1684 | 53, 10 => 1511 | 53, 11 => 1383 | 53, 12 => 1279
  | 53, 13 => 1191 | 53, 14 => 1117
  | 54, 9 => 1638 | 54, 10 => 1481 | 54, 11 => 1356
  | 54, 12 => 1253 | 54, 13 => 1167 | 54, 14 => 1094
  | 55, 9 => 1606 | 55, 10 => 1453 | 55, 11 => 1329
  | 55, 12 => 1228 | 55, 13 => 1144 | 55, 14 => 1072
  | 56, 9 => 1576 | 56, 10 => 1425 | 56, 11 => 1304
  | 56, 12 => 1205 | 56, 13 => 1122 | 56, 14 => 1051
  | 57, 9 => 1547 | 57, 10 => 1399 | 57, 11 => 1280
  | 57, 12 => 1182 | 57, 13 => 1100 | 57, 14 => 1031
  | 58, 9 => 1519 | 58, 10 => 1373 | 58, 11 => 1256
  | 58, 12 => 1160 | 58, 13 => 1080 | 58, 14 => 1012
  | 59, 8 => 1689 | 59, 9 => 1492 | 59, 10 => 1349 | 59, 11 => 1234
  | 59, 12 => 1139 | 59, 13 => 1061 | 59, 14 => 994
  | 60, 8 => 1645 | 60, 9 => 1466 | 60, 10 => 1325
  | 60, 11 => 1212 | 60, 12 => 1119 | 60, 13 => 1042 | 60, 14 => 976
  | 61, 8 => 1617 | 61, 9 => 1441 | 61, 10 => 1302
  | 61, 11 => 1191 | 61, 12 => 1100 | 61, 13 => 1024 | 61, 14 => 959
  | 62, 8 => 1590 | 62, 9 => 1417 | 62, 10 => 1281
  | 62, 11 => 1171 | 62, 12 => 1081 | 62, 13 => 1006 | 62, 14 => 943
  | 63, 8 => 1564 | 63, 9 => 1393 | 63, 10 => 1259
  | 63, 11 => 1152 | 63, 12 => 1063 | 63, 13 => 989 | 63, 14 => 927
  | 64, 8 => 1539 | 64, 9 => 1371 | 64, 10 => 1239
  | 64, 11 => 1133 | 64, 12 => 1046 | 64, 13 => 973 | 64, 14 => 912
  | 65, 8 => 1515 | 65, 9 => 1349 | 65, 10 => 1219
  | 65, 11 => 1115 | 65, 12 => 1029 | 65, 13 => 958 | 65, 14 => 897
  | _, _ => 0

 

def hardLastR1658 (y : Nat) : Nat :=
  if y ≤ 40 then 14 else
  if y ≤ 43 then 13 else
  if y ≤ 45 then 12 else
  if y ≤ 49 then 11 else
  if y ≤ 54 then 10 else
  if y ≤ 60 then 9 else 8

def hardMaxT (_y _r : Nat) : Nat := 1692

 

def HardCell (t y r : Nat) : Prop :=
  38 ≤ y ∧ y ≤ 65 ∧
  hostileMinR y ≤ r ∧ r ≤ 14 ∧
  hardMinT y r ≤ t ∧ t ≤ hardMaxT y r

theorem HardCell.y_lower {t y r : Nat} (h : HardCell t y r) : 38 ≤ y := h.1
theorem HardCell.y_upper {t y r : Nat} (h : HardCell t y r) : y ≤ 65 := h.2.1
theorem HardCell.r_lower {t y r : Nat} (h : HardCell t y r) :
    hostileMinR y ≤ r := h.2.2.1
theorem HardCell.r_upper {t y r : Nat} (h : HardCell t y r) : r ≤ 14 :=
  h.2.2.2.1
theorem HardCell.t_lower {t y r : Nat} (h : HardCell t y r) :
    hardMinT y r ≤ t := h.2.2.2.2.1
theorem HardCell.t_upper {t y r : Nat} (h : HardCell t y r) :
    t ≤ hardMaxT y r := h.2.2.2.2.2

theorem hardMaxT_le_1692 (y r : Nat) : hardMaxT y r ≤ 1692 := by
  simp [hardMaxT]

theorem HardCell.t_le_1692 {t y r : Nat} (h : HardCell t y r) : t ≤ 1692 :=
  h.t_upper.trans (hardMaxT_le_1692 y r)

 

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

 

private theorem hard_boundary_numeric_compressed :
    ∀ y : Fin 66, ∀ r : Fin 15,
      38 ≤ y.1 → hostileMinR y.1 ≤ r.1 →
      selectorDeficit (hardMinT y.1 r.1) y.1 r.1 ≤
          selectorSlope y.1 r.1 * (familyMaxTotal - familyBaseTotal) ∧
        selectedTotal (hardMinT y.1 r.1) y.1 r.1 -
          hardMinT y.1 r.1 ≤ 1218 := by
  decide

theorem hard_boundary_numeric
    {y r : Nat} (hylo : 38 ≤ y) (hyhi : y ≤ 65)
    (hrlo : hostileMinR y ≤ r) (hrhi : r ≤ 14) :
    selectorDeficit (hardMinT y r) y r ≤
        selectorSlope y r * (familyMaxTotal - familyBaseTotal) ∧
      selectedTotal (hardMinT y r) y r - hardMinT y r ≤ 1218 := by
  simpa using hard_boundary_numeric_compressed
    ⟨y, by omega⟩ ⟨r, by omega⟩ hylo hrlo

 

theorem HardCell.selector_inputs {t y r : Nat} (h : HardCell t y r) :
    t ≤ familyBaseTotal ∧
    familyYSCap - y ≤ familyBaseTotal - t ∧
    0 < selectorSlope y r := by
  refine ⟨?_, ?_, selectorSlope_pos_of_hostile_band
    h.y_lower h.y_upper h.r_lower⟩
  · exact h.t_le_1692.trans (by norm_num [familyBaseTotal])
  · have ht := h.t_le_1692
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
    selectedTotal t y r - t ≤ 1218 ∧
    familyYSCap - y ≤ 71 ∧
    familySlopeCap - r ≤ 16 ∧
    5797635 ≤ quotientWeightedCut y r := by
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
