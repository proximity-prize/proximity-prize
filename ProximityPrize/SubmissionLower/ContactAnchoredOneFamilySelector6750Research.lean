import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research
import Mathlib.Algebra.Order.Floor.Div

 














namespace ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research

open scoped BigOperators
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 400000

def agreements : Nat := 181874
def domainSize : Nat := 262144
def contactSlope : Nat := 131071
def cutWidth : Nat := 50804

def familyMultiplicity : Nat := 63
def familySlopeCap : Nat := 18
def familyYSCap : Nat := 87
def familyBaseTotal : Nat := 2423
def familyMaxTotal : Nat := 4340

def nullitySlope : Nat := 22567668
def nullityConstant : Nat := 54663495311

 
def channelCount (total ys slope : Nat) : Nat :=
  ∑ u ∈ Finset.range (min total ys + 1),
    (min slope u + 1) * (total - u + 1)

 
def channelSlope (ys slope : Nat) : Nat :=
  ∑ u ∈ Finset.range (ys + 1), (min slope u + 1)

theorem channelSlope_mono_slope {ys slope₁ slope₂ : Nat}
    (h : slope₁ ≤ slope₂) :
    channelSlope ys slope₁ ≤ channelSlope ys slope₂ := by
  unfold channelSlope
  apply Finset.sum_le_sum
  intro u hu
  exact Nat.add_le_add_right (min_le_min_right u h) 1

 

theorem channelCount_add_of_Y_le_T
    {total ys slope k : Nat} (hYT : ys ≤ total) :
    channelCount (total + k) ys slope =
      channelCount total ys slope + k * channelSlope ys slope := by
  have hYT' : ys ≤ total + k := hYT.trans (Nat.le_add_right total k)
  unfold channelCount channelSlope
  rw [Nat.min_eq_right hYT, Nat.min_eq_right hYT']
  calc
    (∑ u ∈ Finset.range (ys + 1),
        (min slope u + 1) * (total + k - u + 1)) =
        ∑ u ∈ Finset.range (ys + 1),
          ((min slope u + 1) * (total - u + 1) +
            k * (min slope u + 1)) := by
      apply Finset.sum_congr rfl
      intro u hu
      have huY : u ≤ ys := by
        have := Finset.mem_range.mp hu
        omega
      have huT : u ≤ total := huY.trans hYT
      have hsub : total + k - u + 1 = (total - u + 1) + k := by omega
      rw [hsub, Nat.mul_add]
      rw [Nat.mul_comm (min slope u + 1) k]
    _ = (∑ u ∈ Finset.range (ys + 1),
          (min slope u + 1) * (total - u + 1)) +
        ∑ u ∈ Finset.range (ys + 1), k * (min slope u + 1) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ u ∈ Finset.range (ys + 1),
          (min slope u + 1) * (total - u + 1)) +
        k * ∑ u ∈ Finset.range (ys + 1), (min slope u + 1) := by
      rw [Finset.mul_sum]

 
def actualNullity (L : Nat) : Nat :=
  coefficientCount (familyMultiplicity * agreements) contactSlope L
      familySlopeCap -
    domainSize * localRankBound familyMultiplicity L familySlopeCap

 
def affineNullity (L : Nat) : Nat :=
  nullitySlope * L - nullityConstant

theorem affineNullity_base : affineNullity familyBaseTotal = 17964253 := by
  norm_num [affineNullity, nullitySlope, familyBaseTotal, nullityConstant]

theorem affineNullity_base_add (k : Nat) :
    affineNullity (familyBaseTotal + k) =
      affineNullity familyBaseTotal + nullitySlope * k := by
  rw [affineNullity_base]
  simp only [affineNullity, familyBaseTotal, nullitySlope, nullityConstant]
  omega

 
def residualChannels (t y r L : Nat) : Nat :=
  channelCount (L - t) (familyYSCap - y) (familySlopeCap - r)

 
def affineRankGapHolds (t y r L : Nat) : Prop :=
  cutWidth * residualChannels t y r L + 1 ≤ affineNullity L

 
def actualRankGapHolds (t y r L : Nat) : Prop :=
  cutWidth * residualChannels t y r L + 1 ≤ actualNullity L

 
def selectorSlope (y r : Nat) : Nat :=
  nullitySlope - cutWidth *
    channelSlope (familyYSCap - y) (familySlopeCap - r)

 
def selectorDeficit (t y r : Nat) : Nat :=
  cutWidth * residualChannels t y r familyBaseTotal + 1 -
    affineNullity familyBaseTotal

 
def selectedTotal (t y r : Nat) : Nat :=
  familyBaseTotal + selectorDeficit t y r ⌈/⌉ selectorSlope y r

theorem selectedTotal_eq_formula (t y r : Nat) :
    selectedTotal t y r =
      2423 +
        (50804 * channelCount (2423 - t) (87 - y) (18 - r) + 1 -
            17964253) ⌈/⌉
          (22567668 - 50804 * channelSlope (87 - y) (18 - r)) := by
  unfold selectedTotal selectorDeficit selectorSlope residualChannels
  rw [affineNullity_base]
  rfl

 


theorem selectedTotal_closes_rank_gap
    {t y r : Nat}
    (ht : t ≤ familyBaseTotal)
    (hface : familyYSCap - y ≤ familyBaseTotal - t)
    (hslope : 0 < selectorSlope y r) :
    affineRankGapHolds t y r (selectedTotal t y r) := by
  let ys := familyYSCap - y
  let slope := familySlopeCap - r
  let channels := residualChannels t y r familyBaseTotal
  let increment := channelSlope ys slope
  let d := selectorDeficit t y r
  let s := selectorSlope y r
  let k := d ⌈/⌉ s
  have hselected : selectedTotal t y r = familyBaseTotal + k := rfl
  have hspos : 0 < s := hslope
  have hcut_lt : cutWidth * increment < nullitySlope := by
    change 0 < nullitySlope - cutWidth * increment at hspos
    exact Nat.sub_pos_iff_lt.mp hspos
  have hsadd : s + cutWidth * increment = nullitySlope := by
    change (nullitySlope - cutWidth * increment) +
      cutWidth * increment = nullitySlope
    exact Nat.sub_add_cancel hcut_lt.le
  have hceil : d ≤ s * k := by
    simpa [nsmul_eq_mul] using
      (le_smul_ceilDiv (a := s) (b := d) hspos)
  have hchannel :
      residualChannels t y r (familyBaseTotal + k) =
        channels + k * increment := by
    change channelCount (familyBaseTotal + k - t) ys slope =
      channels + k * increment
    have hsub : familyBaseTotal + k - t =
        (familyBaseTotal - t) + k := by omega
    rw [hsub, channelCount_add_of_Y_le_T hface]
    rfl
  have hdeficit :
      cutWidth * channels + 1 ≤ affineNullity familyBaseTotal + d := by
    change cutWidth * channels + 1 ≤ affineNullity familyBaseTotal +
      (cutWidth * channels + 1 - affineNullity familyBaseTotal)
    omega
  rw [affineRankGapHolds, hselected, hchannel,
    affineNullity_base_add]
  calc
    cutWidth * (channels + k * increment) + 1 =
        (cutWidth * channels + 1) + cutWidth * (k * increment) := by ring
    _ ≤ (affineNullity familyBaseTotal + d) +
        cutWidth * (k * increment) := Nat.add_le_add_right hdeficit _
    _ ≤ (affineNullity familyBaseTotal + s * k) +
        cutWidth * (k * increment) := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left hceil (affineNullity familyBaseTotal)) _
    _ = affineNullity familyBaseTotal + nullitySlope * k := by
      rw [← hsadd]
      ring

 

theorem selectorSlope_ge_4819535_of_channelSlope_le
    {y r : Nat}
    (hchannels :
      channelSlope (familyYSCap - y) (familySlopeCap - r) ≤ 316) :
    6513604 ≤ selectorSlope y r := by
  unfold selectorSlope nullitySlope cutWidth
  omega

theorem selectorSlope_pos_of_channelSlope_le_316
    {y r : Nat}
    (hchannels :
      channelSlope (familyYSCap - y) (familySlopeCap - r) ≤ 316) :
    0 < selectorSlope y r :=
  (by omega : 0 < 6513604).trans_le
    (selectorSlope_ge_4819535_of_channelSlope_le hchannels)

 
def hostileMinR (y : Nat) : Nat :=
  if y <= 39 then 14 else
  if y <= 41 then 13 else
  if y <= 44 then 12 else
  if y <= 48 then 11 else
  if y <= 52 then 10 else
  if y <= 58 then 9 else 8

 
theorem hostile_boundary_channelSlope_le_316
    {y : Nat} (hylo : 38 ≤ y) (hyhi : y ≤ 66) :
    channelSlope (familyYSCap - y)
      (familySlopeCap - hostileMinR y) ≤ 316 := by
  interval_cases y <;>
    norm_num [hostileMinR, channelSlope, familyYSCap, familySlopeCap,
      Finset.sum_range_succ]

theorem channelSlope_le_316_of_hostile_band
    {y r : Nat} (hylo : 38 ≤ y) (hyhi : y ≤ 66)
    (hr : hostileMinR y ≤ r) :
    channelSlope (familyYSCap - y) (familySlopeCap - r) ≤ 316 := by
  have hs : familySlopeCap - r ≤ familySlopeCap - hostileMinR y := by
    omega
  exact (channelSlope_mono_slope hs).trans
    (hostile_boundary_channelSlope_le_316 hylo hyhi)

theorem selectorSlope_pos_of_hostile_band
    {y r : Nat} (hylo : 38 ≤ y) (hyhi : y ≤ 66)
    (hr : hostileMinR y ≤ r) :
    0 < selectorSlope y r :=
  selectorSlope_pos_of_channelSlope_le_316
    (channelSlope_le_316_of_hostile_band hylo hyhi hr)

 

theorem selectedTotal_le_familyMaxTotal
    {t y r : Nat} (hslope : 0 < selectorSlope y r)
    (hdeficit : selectorDeficit t y r ≤
      selectorSlope y r * (familyMaxTotal - familyBaseTotal)) :
    selectedTotal t y r ≤ familyMaxTotal := by
  have hceil : selectorDeficit t y r ⌈/⌉ selectorSlope y r ≤
      familyMaxTotal - familyBaseTotal :=
    (ceilDiv_le_iff_le_mul hslope).2 hdeficit
  unfold selectedTotal
  norm_num [familyMaxTotal, familyBaseTotal] at hceil ⊢
  omega

 


theorem selectedTotal_closes_actual_rank_gap
    {t y r : Nat}
    (ht : t ≤ familyBaseTotal)
    (hface : familyYSCap - y ≤ familyBaseTotal - t)
    (hslope : 0 < selectorSlope y r)
    (hnullity : affineNullity (selectedTotal t y r) ≤
      actualNullity (selectedTotal t y r)) :
    actualRankGapHolds t y r (selectedTotal t y r) := by
  exact (selectedTotal_closes_rank_gap ht hface hslope).trans hnullity

 
theorem one_family_numeric_caps :
    familyMultiplicity * agreements = 11458062 ∧
    (familyMultiplicity * agreements - 1) / contactSlope = familyYSCap ∧
    familyMaxTotal ≤ 60877326 ∧
    familyBaseTotal ≤ familyMaxTotal := by
  norm_num [familyMultiplicity, agreements, contactSlope, familyYSCap,
    familyMaxTotal, familyBaseTotal]

end ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research.channelCount_add_of_Y_le_T
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research.selectedTotal_closes_rank_gap
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research.selectedTotal_closes_actual_rank_gap
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredOneFamilySelector6750Research.one_family_numeric_caps
