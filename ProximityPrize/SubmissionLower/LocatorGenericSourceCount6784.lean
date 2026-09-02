import ProximityPrize.SubmissionLower.LocatorGenericSourceCountEngine
import ProximityPrize.SubmissionLower.LocatorHelperFactorSwitchGeneric

namespace ProximityPrize.SubmissionLower.LocatorGenericSourceCount6784

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorGenericSourceCount LocatorGenericSourceCountEngine
  LocatorReplacementGridData

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem helper_count
    (D L s m Ysrc delta k : ℕ) (src : Source)
    (hsrcLength : src.length = L) (hsrcY : src.y = Ysrc)
    (hsrcR : src.r = s) (hdelta : delta = 50470)
    (hD : 0 < D) (hDa : D = m * 181540)
    (hshape : D + s ≤ 131071 * (Ysrc + 1))
    (hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      D - j * delta ≤ (m - j) * 181540 + j * (131071 - 1))
    (hlowpos : ∀ j, 1 ≤ j → j ≤ k → 0 < D - j * delta)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hgap : src.gap ≤ Module.finrank K (SourceKernel D L s m u0 u1))
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits src k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost src (box c) k)
        (LocatorReplacementGridData.helperPair src (box c)).regularCountCap := by
  obtain ⟨hr, _hylo, hyhi, _htlo, hthi⟩ :=
    factor_bounds_of_cell H F c hcell
  have hFY : F.1.degreeOf 1 ≤ (box c).factorY :=
    (degreeY_le_ysWeight F.1).trans hyhi
  have hFR : F.1.degreeOf 2 ≤ (box c).r := by
    simpa only [LocatorContact.slope_weight_eq_degreeR] using hr.le
  have hFZ : F.1.degreeOf 3 ≤ (box c).thi :=
    (degreeZ_le_totalWeight F.1).trans hthi
  have hhelperShape : D + s ≤ 131071 * (src.y + 1) := by
    simpa only [hsrcY] using hshape
  have hhelperGates : LocatorHelperFactorSwitchGeneric.HelperPairGates
      src.y s L (box c).factorY (box c).r (box c).thi := by
    simpa only [LocatorHelperFactorSwitchGeneric.HelperPairGates,
      LocatorHelperFactorSwitchGeneric.helperPair,
      LocatorReplacementGridData.helperPair, PairGates, hsrcR, hsrcLength]
      using hfit.2.1
  rcases LocatorHelperFactorSwitchGeneric.divisor_or_helper_count
      D L s m src.y hD hDa hhelperShape selected Gamma hdegree hagreement hno
      F (box c).factorY (box c).r (box c).thi hFY hFR hFZ hhelperGates with
    hdiv | hhelper
  · exact (source_count_of_divisor D L s m Ysrc delta k src
      hsrcLength hsrcY hsrcR hdelta hD hshape hcapacity hlowpos
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdiv hgap
      c hcell hfit.1).trans (Nat.le_max_left _ _)
  · have hhelper' : (regularSeeds H selected Gamma F).card ≤
        (LocatorReplacementGridData.helperPair src (box c)).regularCountCap := by
      simpa only [LocatorHelperFactorSwitchGeneric.helperPair,
        LocatorReplacementGridData.helperPair, hsrcR, hsrcLength] using hhelper
    exact hhelper'.trans (Nat.le_max_right _ _)

theorem sourceH1_count
    (k : ℕ) (hk13 : k ≤ 13)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH1 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH1 (box c) k)
        (helperPair sourceH1 (box c)).regularCountCap := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      64446700 - j * 50470 ≤ (355 - j) * 181540 + j * 131070 := by
    intro j _ hjk
    exact (LocatorHelperArithmetic6784.sourceS1_stage_capacity j
      (hjk.trans hk13)).le
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 64446700 - j * 50470 := by
    intro j _ hjk
    exact LocatorHelperArithmetic6784.sourceS1_low_positive j (hjk.trans hk13)
  have hgap : sourceH1.gap ≤ Module.finrank K
      (SourceKernel 64446700 350000 105 355 u0 u1) := by
    simpa only [sourceH1, SourceKernel] using
      LocatorHelperArithmetic6784.sourceS1_finrank_lower_bound u0 u1
  exact helper_count 64446700 350000 105 355 491 50470 k sourceH1
    rfl rfl rfl rfl (by decide) (by decide)
    LocatorHelperArithmetic6784.sourceS1_shape hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hgap c hcell hfit

theorem sourceH2_count
    (k : ℕ) (hk18 : k ≤ 18)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH2 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH2 (box c) k)
        (helperPair sourceH2 (box c)).regularCountCap := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      90770000 - j * 50470 ≤ (500 - j) * 181540 + j * 131070 := by
    intro j _ hjk
    exact (LocatorHelperArithmetic6784.sourceS2_stage_capacity j
      (hjk.trans hk18)).le
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 90770000 - j * 50470 := by
    intro j _ hjk
    exact LocatorHelperArithmetic6784.sourceS2_low_positive j (hjk.trans hk18)
  have hgap : sourceH2.gap ≤ Module.finrank K
      (SourceKernel 90770000 1000000 150 500 u0 u1) := by
    simpa only [sourceH2, SourceKernel] using
      LocatorHelperArithmetic6784.sourceS2_finrank_lower_bound u0 u1
  exact helper_count 90770000 1000000 150 500 692 50470 k sourceH2
    rfl rfl rfl rfl (by decide) (by decide)
    LocatorHelperArithmetic6784.sourceS2_shape hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hgap c hcell hfit

theorem sourceH3_count
    (k : ℕ) (hk30 : k ≤ 30)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH3 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH3 (box c) k)
        (helperPair sourceH3 (box c)).regularCountCap := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      147047400 - j * 50470 ≤ (810 - j) * 181540 + j * 131070 := by
    intro j _ hjk
    exact (LocatorHelperArithmetic6784.sourceS3_stage_capacity j
      (hjk.trans hk30)).le
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 147047400 - j * 50470 := by
    intro j _ hjk
    exact LocatorHelperArithmetic6784.sourceS3_low_positive j (hjk.trans hk30)
  have hgap : sourceH3.gap ≤ Module.finrank K
      (SourceKernel 147047400 350000 243 810 u0 u1) := by
    simpa only [sourceH3, SourceKernel] using
      LocatorHelperArithmetic6784.sourceS3_finrank_lower_bound u0 u1
  exact helper_count 147047400 350000 243 810 1121 50470 k sourceH3
    rfl rfl rfl rfl (by decide) (by decide)
    LocatorHelperArithmetic6784.sourceS3_shape hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hgap c hcell hfit

theorem sourceH4_count
    (k : ℕ) (hk45 : k ≤ 45)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH4 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH4 (box c) k)
        (helperPair sourceH4 (box c)).regularCountCap := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      221478800 - j * 50470 ≤ (1220 - j) * 181540 + j * 131070 := by
    intro j _ hjk
    exact (LocatorHelperArithmetic6784.sourceS4_stage_capacity j
      (hjk.trans hk45)).le
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 221478800 - j * 50470 := by
    intro j _ hjk
    exact LocatorHelperArithmetic6784.sourceS4_low_positive j (hjk.trans hk45)
  have hgap : sourceH4.gap ≤ Module.finrank K
      (SourceKernel 221478800 675716 365 1220 u0 u1) := by
    simpa only [sourceH4, SourceKernel] using
      LocatorHelperArithmetic6784.sourceS4_finrank_lower_bound u0 u1
  exact helper_count 221478800 675716 365 1220 1689 50470 k sourceH4
    rfl rfl rfl rfl (by decide) (by decide)
    LocatorHelperArithmetic6784.sourceS4_shape hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hgap c hcell hfit

theorem sourceH5_count
    (k : ℕ) (hk28 : k ≤ 28)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH5 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH5 (box c) k)
        (helperPair sourceH5 (box c)).regularCountCap := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      136155000 - j * 50470 ≤ (750 - j) * 181540 + j * 131070 := by
    intro j _ hjk
    exact (LocatorHelperArithmetic6784.sourceS5_stage_capacity j
      (hjk.trans hk28)).le
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 136155000 - j * 50470 := by
    intro j _ hjk
    exact LocatorHelperArithmetic6784.sourceS5_low_positive j (hjk.trans hk28)
  have hgap : sourceH5.gap ≤ Module.finrank K
      (SourceKernel 136155000 669072 225 750 u0 u1) := by
    simpa only [sourceH5, SourceKernel] using
      LocatorHelperArithmetic6784.sourceS5_finrank_lower_bound u0 u1
  exact helper_count 136155000 669072 225 750 1038 50470 k sourceH5
    rfl rfl rfl rfl (by decide) (by decide)
    LocatorHelperArithmetic6784.sourceS5_shape hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hgap c hcell hfit

theorem sourceH6_count
    (k : ℕ) (hk27 : k ≤ 27)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH6 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH6 (box c) k)
        (helperPair sourceH6 (box c)).regularCountCap := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      136155000 - j * 50470 ≤ (750 - j) * 181540 + j * 131070 := by
    intro j _ hjk
    exact (LocatorHelperArithmetic6784.sourceS6_stage_capacity j
      (hjk.trans hk27)).le
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k →
      0 < 136155000 - j * 50470 := by
    intro j _ hjk
    exact LocatorHelperArithmetic6784.sourceS6_low_positive j (hjk.trans hk27)
  have hgap : sourceH6.gap ≤ Module.finrank K
      (SourceKernel 136155000 219707 225 750 u0 u1) := by
    simpa only [sourceH6, SourceKernel] using
      LocatorHelperArithmetic6784.sourceS6_finrank_lower_bound u0 u1
  exact helper_count 136155000 219707 225 750 1038 50470 k sourceH6
    rfl rfl rfl rfl (by decide) (by decide)
    LocatorHelperArithmetic6784.sourceS6_shape hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF hgap c hcell hfit

end

end ProximityPrize.SubmissionLower.LocatorGenericSourceCount6784
