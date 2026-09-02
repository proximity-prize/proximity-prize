/-
Generic source counts, row 6786.  `helper_count` is jieyilong's (PR #471,
commit db5c259, score 6784); `source_count` packages its per-source arithmetic
so that every route source (A, Aux, C and the seven helpers) is one instance.
Row constants come from LocatorReplacementGridData and the kernel constants from
LocatorHelperArithmeticGeneric, so no literal of either kind appears here.
-/
import ProximityPrize.SubmissionLower.LocatorGenericSourceCountEngine
import ProximityPrize.SubmissionLower.LocatorHelperFactorSwitchGenericC2

namespace ProximityPrize.SubmissionLower.LocatorGenericSourceCountC2

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
    (hpair : ∀ b j, (stagePair src b j).a = agreements)
    (hpairE : ∀ b j, (stagePair src b j).errors = 262144 - agreements)
    (hsrcLength : src.length = L) (hsrcY : src.y = Ysrc)
    (hsrcR : src.r = s) (hdelta : delta = LocatorReplacementGridData.delta)
    (hD : 0 < D) (hDa : D = m * agreements)
    (hshape : D + s ≤ selectedDegree * (Ysrc + 1))
    (hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      D - j * delta ≤ (m - j) * agreements + j * (selectedDegree - 1))
    (hlowpos : ∀ j, 1 ≤ j → j ≤ k → 0 < D - j * delta)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
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
  have hhelperGates : LocatorHelperFactorSwitchGenericC2.HelperPairGates
      src.y s L (box c).factorY (box c).r (box c).thi := by
    simpa only [LocatorHelperFactorSwitchGenericC2.HelperPairGates,
      LocatorHelperFactorSwitchGenericC2.helperPair,
      LocatorReplacementGridData.helperPair, PairGates, hsrcR, hsrcLength]
      using hfit.2.1
  rcases LocatorHelperFactorSwitchGenericC2.divisor_or_helper_count
      D L s m src.y hD hDa hhelperShape selected Gamma hdegree hagreement hno
      F (box c).factorY (box c).r (box c).thi hFY hFR hFZ hhelperGates with
    hdiv | hhelper
  · exact (source_count_of_divisor D L s m Ysrc delta k agreements src
      hpair hpairE
      hsrcLength hsrcY hsrcR hdelta hD hshape hcapacity hlowpos
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdiv hgap
      c hcell hfit.1).trans (Nat.le_max_left _ _)
  · have hhelper' : (regularSeeds H selected Gamma F).card ≤
        (LocatorReplacementGridData.helperPair src (box c)).regularCountCap := by
      simpa only [LocatorHelperFactorSwitchGenericC2.helperPair,
        LocatorReplacementGridData.helperPair, hsrcR, hsrcLength] using hhelper
    exact hhelper'.trans (Nat.le_max_right _ _)


/-- One route source: the per-source arithmetic of `LocatorHelperArithmeticGeneric`
feeds `helper_count` at any depth up to the source's window. -/
theorem source_count
    (D L s m Ysrc depth : ℕ) (src : Source)
    (hsrcLength : src.length = L) (hsrcY : src.y = Ysrc) (hsrcR : src.r = s)
    (hD : 0 < D) (hDa : D = m * agreements)
    (hshape : D + s ≤ selectedDegree * (Ysrc + 1))
    (hcap : ∀ j, j ≤ depth →
      D - j * delta = (m - j) * agreements + j * (selectedDegree - 1))
    (hlow : ∀ j, j ≤ depth → 0 < D - j * delta)
    (hfin : ∀ u0 u1 : I → K,
      src.gap ≤ Module.finrank K (SourceKernel D L s m u0 u1))
    (k : ℕ) (hk : k ≤ depth)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits src k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost src (box c) k) (helperPair src (box c)).regularCountCap := by
  have hcapacity : ∀ j, 1 ≤ j → j ≤ k →
      D - j * delta ≤ (m - j) * agreements + j * (selectedDegree - 1) :=
    fun j _ hjk => (hcap j (hjk.trans hk)).le
  have hlowpos : ∀ j, 1 ≤ j → j ≤ k → 0 < D - j * delta :=
    fun j _ hjk => hlow j (hjk.trans hk)
  exact helper_count D L s m Ysrc delta k src (fun _ _ => rfl) (fun _ _ => rfl)
    hsrcLength hsrcY hsrcR rfl hD hDa hshape hcapacity hlowpos
    u0 u1 H selected Gamma hdegree hagreement hno F hF (hfin u0 u1) c hcell hfit

theorem sourceA_count
    (k : ℕ) (hk : k ≤ 1)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceA k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceA (box c) k)
        (helperPair sourceA (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DA LocatorHelperArithmeticGeneric.LA LocatorHelperArithmeticGeneric.sA LocatorHelperArithmeticGeneric.mA LocatorHelperArithmeticGeneric.yA LocatorHelperArithmeticGeneric.depthA
    sourceA rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceA_shape
    LocatorHelperArithmeticGeneric.sourceA_stage_capacity LocatorHelperArithmeticGeneric.sourceA_low_positive
    (fun u0 u1 => by
      simpa only [sourceA, SourceKernel] using LocatorHelperArithmeticGeneric.sourceA_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceAux_count
    (k : ℕ) (hk : k ≤ 1)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceAux k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceAux (box c) k)
        (helperPair sourceAux (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DAux LocatorHelperArithmeticGeneric.LAux LocatorHelperArithmeticGeneric.sAux LocatorHelperArithmeticGeneric.mAux LocatorHelperArithmeticGeneric.yAux LocatorHelperArithmeticGeneric.depthAux
    sourceAux rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceAux_shape
    LocatorHelperArithmeticGeneric.sourceAux_stage_capacity LocatorHelperArithmeticGeneric.sourceAux_low_positive
    (fun u0 u1 => by
      simpa only [sourceAux, SourceKernel] using LocatorHelperArithmeticGeneric.sourceAux_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceC_count
    (k : ℕ) (hk : k ≤ 14)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceC k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceC (box c) k)
        (helperPair sourceC (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DC LocatorHelperArithmeticGeneric.LC LocatorHelperArithmeticGeneric.sC LocatorHelperArithmeticGeneric.mC LocatorHelperArithmeticGeneric.yC LocatorHelperArithmeticGeneric.depthC
    sourceC rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceC_shape
    LocatorHelperArithmeticGeneric.sourceC_stage_capacity LocatorHelperArithmeticGeneric.sourceC_low_positive
    (fun u0 u1 => by
      simpa only [sourceC, SourceKernel] using LocatorHelperArithmeticGeneric.sourceC_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceH1_count
    (k : ℕ) (hk : k ≤ 13)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH1 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH1 (box c) k)
        (helperPair sourceH1 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS1 LocatorHelperArithmeticGeneric.LS1 LocatorHelperArithmeticGeneric.sS1 LocatorHelperArithmeticGeneric.mS1 LocatorHelperArithmeticGeneric.yS1 LocatorHelperArithmeticGeneric.depthS1
    sourceH1 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS1_shape
    LocatorHelperArithmeticGeneric.sourceS1_stage_capacity LocatorHelperArithmeticGeneric.sourceS1_low_positive
    (fun u0 u1 => by
      simpa only [sourceH1, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS1_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceH2_count
    (k : ℕ) (hk : k ≤ 18)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH2 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH2 (box c) k)
        (helperPair sourceH2 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS2 LocatorHelperArithmeticGeneric.LS2 LocatorHelperArithmeticGeneric.sS2 LocatorHelperArithmeticGeneric.mS2 LocatorHelperArithmeticGeneric.yS2 LocatorHelperArithmeticGeneric.depthS2
    sourceH2 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS2_shape
    LocatorHelperArithmeticGeneric.sourceS2_stage_capacity LocatorHelperArithmeticGeneric.sourceS2_low_positive
    (fun u0 u1 => by
      simpa only [sourceH2, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS2_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceH3_count
    (k : ℕ) (hk : k ≤ 30)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH3 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH3 (box c) k)
        (helperPair sourceH3 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS3 LocatorHelperArithmeticGeneric.LS3 LocatorHelperArithmeticGeneric.sS3 LocatorHelperArithmeticGeneric.mS3 LocatorHelperArithmeticGeneric.yS3 LocatorHelperArithmeticGeneric.depthS3
    sourceH3 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS3_shape
    LocatorHelperArithmeticGeneric.sourceS3_stage_capacity LocatorHelperArithmeticGeneric.sourceS3_low_positive
    (fun u0 u1 => by
      simpa only [sourceH3, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS3_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceH3X_count
    (k : ℕ) (hk : k ≤ 33)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceH3X k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH3X (box c) k)
        (helperPair sourceH3X (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS4 LocatorHelperArithmeticGeneric.LS4 LocatorHelperArithmeticGeneric.sS4 LocatorHelperArithmeticGeneric.mS4 LocatorHelperArithmeticGeneric.yS4 LocatorHelperArithmeticGeneric.depthS4
    sourceH3X rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS4_shape
    LocatorHelperArithmeticGeneric.sourceS4_stage_capacity LocatorHelperArithmeticGeneric.sourceS4_low_positive
    (fun u0 u1 => by
      simpa only [sourceH3X, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS4_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceCbig_count
    (k : ℕ) (hk : k ≤ 17)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceCbig k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceCbig (box c) k)
        (helperPair sourceCbig (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS5 LocatorHelperArithmeticGeneric.LS5 LocatorHelperArithmeticGeneric.sS5 LocatorHelperArithmeticGeneric.mS5 LocatorHelperArithmeticGeneric.yS5 LocatorHelperArithmeticGeneric.depthS5
    sourceCbig rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS5_shape
    LocatorHelperArithmeticGeneric.sourceS5_stage_capacity LocatorHelperArithmeticGeneric.sourceS5_low_positive
    (fun u0 u1 => by
      simpa only [sourceCbig, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS5_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceT20k_count
    (k : ℕ) (hk : k ≤ 10)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceT20k k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceT20k (box c) k)
        (helperPair sourceT20k (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS6 LocatorHelperArithmeticGeneric.LS6 LocatorHelperArithmeticGeneric.sS6 LocatorHelperArithmeticGeneric.mS6 LocatorHelperArithmeticGeneric.yS6 LocatorHelperArithmeticGeneric.depthS6
    sourceT20k rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS6_shape
    LocatorHelperArithmeticGeneric.sourceS6_stage_capacity LocatorHelperArithmeticGeneric.sourceS6_low_positive
    (fun u0 u1 => by
      simpa only [sourceT20k, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS6_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceT30k_count
    (k : ℕ) (hk : k ≤ 12)
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (hF : F.1 ≠ 0) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c)
    (hfit : HelperFits sourceT30k k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceT30k (box c) k)
        (helperPair sourceT30k (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS7 LocatorHelperArithmeticGeneric.LS7 LocatorHelperArithmeticGeneric.sS7 LocatorHelperArithmeticGeneric.mS7 LocatorHelperArithmeticGeneric.yS7 LocatorHelperArithmeticGeneric.depthS7
    sourceT30k rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS7_shape
    LocatorHelperArithmeticGeneric.sourceS7_stage_capacity LocatorHelperArithmeticGeneric.sourceS7_low_positive
    (fun u0 u1 => by
      simpa only [sourceT30k, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS7_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

end

end ProximityPrize.SubmissionLower.LocatorGenericSourceCountC2
