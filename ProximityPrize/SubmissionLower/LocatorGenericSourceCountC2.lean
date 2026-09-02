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

theorem sourceS2_count
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
    (hfit : HelperFits sourceS2 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceS2 (box c) k)
        (helperPair sourceS2 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS2 LocatorHelperArithmeticGeneric.LS2 LocatorHelperArithmeticGeneric.sS2 LocatorHelperArithmeticGeneric.mS2 LocatorHelperArithmeticGeneric.yS2 LocatorHelperArithmeticGeneric.depthS2
    sourceS2 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS2_shape
    LocatorHelperArithmeticGeneric.sourceS2_stage_capacity LocatorHelperArithmeticGeneric.sourceS2_low_positive
    (fun u0 u1 => by
      simpa only [sourceS2, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS2_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceS3_count
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
    (hfit : HelperFits sourceS3 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceS3 (box c) k)
        (helperPair sourceS3 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DS3 LocatorHelperArithmeticGeneric.LS3 LocatorHelperArithmeticGeneric.sS3 LocatorHelperArithmeticGeneric.mS3 LocatorHelperArithmeticGeneric.yS3 LocatorHelperArithmeticGeneric.depthS3
    sourceS3 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceS3_shape
    LocatorHelperArithmeticGeneric.sourceS3_stage_capacity LocatorHelperArithmeticGeneric.sourceS3_low_positive
    (fun u0 u1 => by
      simpa only [sourceS3, SourceKernel] using LocatorHelperArithmeticGeneric.sourceS3_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceH3X_count
    (k : ℕ) (hk : k ≤ 32)
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
  source_count LocatorHelperArithmeticGeneric.DH3X LocatorHelperArithmeticGeneric.LH3X LocatorHelperArithmeticGeneric.sH3X LocatorHelperArithmeticGeneric.mH3X LocatorHelperArithmeticGeneric.yH3X LocatorHelperArithmeticGeneric.depthH3X
    sourceH3X rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceH3X_shape
    LocatorHelperArithmeticGeneric.sourceH3X_stage_capacity LocatorHelperArithmeticGeneric.sourceH3X_low_positive
    (fun u0 u1 => by
      simpa only [sourceH3X, SourceKernel] using LocatorHelperArithmeticGeneric.sourceH3X_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceH4_count
    (k : ℕ) (hk : k ≤ 36)
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
    (hfit : HelperFits sourceH4 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceH4 (box c) k)
        (helperPair sourceH4 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DH4 LocatorHelperArithmeticGeneric.LH4 LocatorHelperArithmeticGeneric.sH4 LocatorHelperArithmeticGeneric.mH4 LocatorHelperArithmeticGeneric.yH4 LocatorHelperArithmeticGeneric.depthH4
    sourceH4 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceH4_shape
    LocatorHelperArithmeticGeneric.sourceH4_stage_capacity LocatorHelperArithmeticGeneric.sourceH4_low_positive
    (fun u0 u1 => by
      simpa only [sourceH4, SourceKernel] using LocatorHelperArithmeticGeneric.sourceH4_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceT10k_count
    (k : ℕ) (hk : k ≤ 8)
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
    (hfit : HelperFits sourceT10k k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceT10k (box c) k)
        (helperPair sourceT10k (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DT10k LocatorHelperArithmeticGeneric.LT10k LocatorHelperArithmeticGeneric.sT10k LocatorHelperArithmeticGeneric.mT10k LocatorHelperArithmeticGeneric.yT10k LocatorHelperArithmeticGeneric.depthT10k
    sourceT10k rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceT10k_shape
    LocatorHelperArithmeticGeneric.sourceT10k_stage_capacity LocatorHelperArithmeticGeneric.sourceT10k_low_positive
    (fun u0 u1 => by
      simpa only [sourceT10k, SourceKernel] using LocatorHelperArithmeticGeneric.sourceT10k_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceT15k_count
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
    (hfit : HelperFits sourceT15k k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceT15k (box c) k)
        (helperPair sourceT15k (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DT15k LocatorHelperArithmeticGeneric.LT15k LocatorHelperArithmeticGeneric.sT15k LocatorHelperArithmeticGeneric.mT15k LocatorHelperArithmeticGeneric.yT15k LocatorHelperArithmeticGeneric.depthT15k
    sourceT15k rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceT15k_shape
    LocatorHelperArithmeticGeneric.sourceT15k_stage_capacity LocatorHelperArithmeticGeneric.sourceT15k_low_positive
    (fun u0 u1 => by
      simpa only [sourceT15k, SourceKernel] using LocatorHelperArithmeticGeneric.sourceT15k_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceT20k_count
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
    (hfit : HelperFits sourceT20k k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceT20k (box c) k)
        (helperPair sourceT20k (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DT20k LocatorHelperArithmeticGeneric.LT20k LocatorHelperArithmeticGeneric.sT20k LocatorHelperArithmeticGeneric.mT20k LocatorHelperArithmeticGeneric.yT20k LocatorHelperArithmeticGeneric.depthT20k
    sourceT20k rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceT20k_shape
    LocatorHelperArithmeticGeneric.sourceT20k_stage_capacity LocatorHelperArithmeticGeneric.sourceT20k_low_positive
    (fun u0 u1 => by
      simpa only [sourceT20k, SourceKernel] using LocatorHelperArithmeticGeneric.sourceT20k_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceT30k_count
    (k : ℕ) (hk : k ≤ 22)
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
  source_count LocatorHelperArithmeticGeneric.DT30k LocatorHelperArithmeticGeneric.LT30k LocatorHelperArithmeticGeneric.sT30k LocatorHelperArithmeticGeneric.mT30k LocatorHelperArithmeticGeneric.yT30k LocatorHelperArithmeticGeneric.depthT30k
    sourceT30k rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceT30k_shape
    LocatorHelperArithmeticGeneric.sourceT30k_stage_capacity LocatorHelperArithmeticGeneric.sourceT30k_low_positive
    (fun u0 u1 => by
      simpa only [sourceT30k, SourceKernel] using LocatorHelperArithmeticGeneric.sourceT30k_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceL1_count
    (k : ℕ) (hk : k ≤ 50)
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
    (hfit : HelperFits sourceL1 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceL1 (box c) k)
        (helperPair sourceL1 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DL1 LocatorHelperArithmeticGeneric.LL1 LocatorHelperArithmeticGeneric.sL1 LocatorHelperArithmeticGeneric.mL1 LocatorHelperArithmeticGeneric.yL1 LocatorHelperArithmeticGeneric.depthL1
    sourceL1 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceL1_shape
    LocatorHelperArithmeticGeneric.sourceL1_stage_capacity LocatorHelperArithmeticGeneric.sourceL1_low_positive
    (fun u0 u1 => by
      simpa only [sourceL1, SourceKernel] using LocatorHelperArithmeticGeneric.sourceL1_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceL2_count
    (k : ℕ) (hk : k ≤ 72)
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
    (hfit : HelperFits sourceL2 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceL2 (box c) k)
        (helperPair sourceL2 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DL2 LocatorHelperArithmeticGeneric.LL2 LocatorHelperArithmeticGeneric.sL2 LocatorHelperArithmeticGeneric.mL2 LocatorHelperArithmeticGeneric.yL2 LocatorHelperArithmeticGeneric.depthL2
    sourceL2 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceL2_shape
    LocatorHelperArithmeticGeneric.sourceL2_stage_capacity LocatorHelperArithmeticGeneric.sourceL2_low_positive
    (fun u0 u1 => by
      simpa only [sourceL2, SourceKernel] using LocatorHelperArithmeticGeneric.sourceL2_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceL3_count
    (k : ℕ) (hk : k ≤ 80)
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
    (hfit : HelperFits sourceL3 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceL3 (box c) k)
        (helperPair sourceL3 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DL3 LocatorHelperArithmeticGeneric.LL3 LocatorHelperArithmeticGeneric.sL3 LocatorHelperArithmeticGeneric.mL3 LocatorHelperArithmeticGeneric.yL3 LocatorHelperArithmeticGeneric.depthL3
    sourceL3 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceL3_shape
    LocatorHelperArithmeticGeneric.sourceL3_stage_capacity LocatorHelperArithmeticGeneric.sourceL3_low_positive
    (fun u0 u1 => by
      simpa only [sourceL3, SourceKernel] using LocatorHelperArithmeticGeneric.sourceL3_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceL4_count
    (k : ℕ) (hk : k ≤ 56)
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
    (hfit : HelperFits sourceL4 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceL4 (box c) k)
        (helperPair sourceL4 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DL4 LocatorHelperArithmeticGeneric.LL4 LocatorHelperArithmeticGeneric.sL4 LocatorHelperArithmeticGeneric.mL4 LocatorHelperArithmeticGeneric.yL4 LocatorHelperArithmeticGeneric.depthL4
    sourceL4 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceL4_shape
    LocatorHelperArithmeticGeneric.sourceL4_stage_capacity LocatorHelperArithmeticGeneric.sourceL4_low_positive
    (fun u0 u1 => by
      simpa only [sourceL4, SourceKernel] using LocatorHelperArithmeticGeneric.sourceL4_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceL5_count
    (k : ℕ) (hk : k ≤ 128)
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
    (hfit : HelperFits sourceL5 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceL5 (box c) k)
        (helperPair sourceL5 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DL5 LocatorHelperArithmeticGeneric.LL5 LocatorHelperArithmeticGeneric.sL5 LocatorHelperArithmeticGeneric.mL5 LocatorHelperArithmeticGeneric.yL5 LocatorHelperArithmeticGeneric.depthL5
    sourceL5 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceL5_shape
    LocatorHelperArithmeticGeneric.sourceL5_stage_capacity LocatorHelperArithmeticGeneric.sourceL5_low_positive
    (fun u0 u1 => by
      simpa only [sourceL5, SourceKernel] using LocatorHelperArithmeticGeneric.sourceL5_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceL6_count
    (k : ℕ) (hk : k ≤ 150)
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
    (hfit : HelperFits sourceL6 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceL6 (box c) k)
        (helperPair sourceL6 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DL6 LocatorHelperArithmeticGeneric.LL6 LocatorHelperArithmeticGeneric.sL6 LocatorHelperArithmeticGeneric.mL6 LocatorHelperArithmeticGeneric.yL6 LocatorHelperArithmeticGeneric.depthL6
    sourceL6 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceL6_shape
    LocatorHelperArithmeticGeneric.sourceL6_stage_capacity LocatorHelperArithmeticGeneric.sourceL6_low_positive
    (fun u0 u1 => by
      simpa only [sourceL6, SourceKernel] using LocatorHelperArithmeticGeneric.sourceL6_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceM1_count
    (k : ℕ) (hk : k ≤ 102)
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
    (hfit : HelperFits sourceM1 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceM1 (box c) k)
        (helperPair sourceM1 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DM1 LocatorHelperArithmeticGeneric.LM1 LocatorHelperArithmeticGeneric.sM1 LocatorHelperArithmeticGeneric.mM1 LocatorHelperArithmeticGeneric.yM1 LocatorHelperArithmeticGeneric.depthM1
    sourceM1 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceM1_shape
    LocatorHelperArithmeticGeneric.sourceM1_stage_capacity LocatorHelperArithmeticGeneric.sourceM1_low_positive
    (fun u0 u1 => by
      simpa only [sourceM1, SourceKernel] using LocatorHelperArithmeticGeneric.sourceM1_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceM3_count
    (k : ℕ) (hk : k ≤ 124)
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
    (hfit : HelperFits sourceM3 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceM3 (box c) k)
        (helperPair sourceM3 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DM3 LocatorHelperArithmeticGeneric.LM3 LocatorHelperArithmeticGeneric.sM3 LocatorHelperArithmeticGeneric.mM3 LocatorHelperArithmeticGeneric.yM3 LocatorHelperArithmeticGeneric.depthM3
    sourceM3 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceM3_shape
    LocatorHelperArithmeticGeneric.sourceM3_stage_capacity LocatorHelperArithmeticGeneric.sourceM3_low_positive
    (fun u0 u1 => by
      simpa only [sourceM3, SourceKernel] using LocatorHelperArithmeticGeneric.sourceM3_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceN1_count
    (k : ℕ) (hk : k ≤ 104)
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
    (hfit : HelperFits sourceN1 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceN1 (box c) k)
        (helperPair sourceN1 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DN1 LocatorHelperArithmeticGeneric.LN1 LocatorHelperArithmeticGeneric.sN1 LocatorHelperArithmeticGeneric.mN1 LocatorHelperArithmeticGeneric.yN1 LocatorHelperArithmeticGeneric.depthN1
    sourceN1 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceN1_shape
    LocatorHelperArithmeticGeneric.sourceN1_stage_capacity LocatorHelperArithmeticGeneric.sourceN1_low_positive
    (fun u0 u1 => by
      simpa only [sourceN1, SourceKernel] using LocatorHelperArithmeticGeneric.sourceN1_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceN3_count
    (k : ℕ) (hk : k ≤ 180)
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
    (hfit : HelperFits sourceN3 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceN3 (box c) k)
        (helperPair sourceN3 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DN3 LocatorHelperArithmeticGeneric.LN3 LocatorHelperArithmeticGeneric.sN3 LocatorHelperArithmeticGeneric.mN3 LocatorHelperArithmeticGeneric.yN3 LocatorHelperArithmeticGeneric.depthN3
    sourceN3 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceN3_shape
    LocatorHelperArithmeticGeneric.sourceN3_stage_capacity LocatorHelperArithmeticGeneric.sourceN3_low_positive
    (fun u0 u1 => by
      simpa only [sourceN3, SourceKernel] using LocatorHelperArithmeticGeneric.sourceN3_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

theorem sourceN4_count
    (k : ℕ) (hk : k ≤ 200)
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
    (hfit : HelperFits sourceN4 k (box c)) :
    (regularSeeds H selected Gamma F).card ≤
      max (routeCost sourceN4 (box c) k)
        (helperPair sourceN4 (box c)).regularCountCap :=
  source_count LocatorHelperArithmeticGeneric.DN4 LocatorHelperArithmeticGeneric.LN4 LocatorHelperArithmeticGeneric.sN4 LocatorHelperArithmeticGeneric.mN4 LocatorHelperArithmeticGeneric.yN4 LocatorHelperArithmeticGeneric.depthN4
    sourceN4 rfl rfl rfl (by decide) (by decide) LocatorHelperArithmeticGeneric.sourceN4_shape
    LocatorHelperArithmeticGeneric.sourceN4_stage_capacity LocatorHelperArithmeticGeneric.sourceN4_low_positive
    (fun u0 u1 => by
      simpa only [sourceN4, SourceKernel] using LocatorHelperArithmeticGeneric.sourceN4_finrank_lower_bound u0 u1)
    k hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hfit

end

end ProximityPrize.SubmissionLower.LocatorGenericSourceCountC2
