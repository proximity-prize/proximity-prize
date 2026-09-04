import ProximityPrize.SubmissionLower.LocatorFixedHybridC26803
import ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2

/-!
# Realization of the C2 hybrid provider for the 68.03 row
-/

namespace ProximityPrize.SubmissionLower.LocatorHybridRealizeC26803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN001 RCN002 RCN003 RCN027 RCN029 RCN030 RCN037 RCN038 RCN042 RCN046
  RCN066 RCN074 RCN085 RCN086 RCN093 RCN095 RCN135 RCN136 RCN156 RCN159
  RCN174 RCN198 RCN199 RCN203 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243
  RCN244 RCN263 RCN264 RCN271 RCN275 RCN277 RCN287 RCN312 RCN313 RCN314
  RCN315 RCN319 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339
  RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
  LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1
  LocatorHybridCostC2 LocatorHybridTailProviderC1 LocatorHybridTailProviderC2
  LocatorHybridTailRealizationC2 LocatorFixed
  LocatorFixedHybridC26803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (GenericField K) := Classical.decEq _
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem realizationC2 : RealizationC2 17773574 := by
  intro p hS hY hT hS3 hhyb
  letI : CharP (GenericField K) 2130706433 :=
    genericField_charP K 2130706433
  unfold ProviderHypC2
  intro Gamma flag S hnodes hagreement hbox hflag hTail
  have hpb := pad_bounds p
  have hps := pad_sums p
  have hyt : padY p ≤ padT p := hpb.2.2
  have hS' : padSlope p + 2 ≤ 29 := by
    rw [hps.1]
    exact hS
  have hY' : padB p + padSlope p + 3 ≤ 135 := by
    rw [hps.2.1]
    exact hY
  have hT' : padA p + padB p + padSlope p + 3 ≤ 6676 := by
    rw [hps.2.2]
    exact hT
  have hfS : flag.all ≤ padSlope p + 2 := by
    rw [hps.1]
    exact hflag.1
  have hfY : flag.yz + flag.all ≤ padB p + padSlope p + 3 := by
    rw [hps.2.1]
    exact hflag.2.1
  have hfT : flag.zOnly + flag.yz + flag.all ≤
      padA p + padB p + padSlope p + 3 := by
    rw [hps.2.2]
    exact hflag.2.2
  have hflagChar : flag.yz + flag.all < 2130706433 ∧
      flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by
    exact LocatorHybridGatesC26803.flag_characteristic
      (padA p) (padB p) (padSlope p) flag hS' hY' hT'
        ⟨hfS, hfY, hfT⟩
  have hmixedRed := LocatorHybridGatesC26803.reduced_mixed_gate
    (padB p) (padSlope p) flag
    hS' hY' hfS hfY
  have hmix := LocatorHybridGatesC26803.product_gate
    (padA p) (padB p) (padSlope p) flag hT' hfT
  have hrat := LocatorHybridGatesC26803.rational_gate
    (padT p) (padY p) (padS p) hhyb
  have htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (RCN327.w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (80781 + 1) *
            (reducedBudgetFamily S hTail hflagChar hmixedRed).yzCost C := by
    intro C hall
    exact tangent_component_card_le S C hTail
      (reducedBaseOrd S hTail hflagChar hmixedRed C)
      181363 17773574 (padT p) (padS p) hnodes hagreement
      (by norm_num [RCN327.w]) (by norm_num [RCN327.w])
      (by norm_num [RCN327.w]) (by norm_num)
      hbox (reducedBudgetFamily S hTail hflagChar hmixedRed)
      (reducedBudgetFamily_yzPositive S hTail hflagChar hmixedRed C) hall
      (reducedBudgetFamily_yzPole S hTail hflagChar hmixedRed C)
  exact exists_hybridTailMultiplicityProviderC2_realized hS3 hhyb hyt
    S hTail hflagChar hmixedRed hmix hrat htangent

end

end ProximityPrize.SubmissionLower.LocatorHybridRealizeC26803
