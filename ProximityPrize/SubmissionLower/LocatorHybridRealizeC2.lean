/-
THE C2 HYBRID PROVIDER EXISTS ON EVERY ADMISSIBLE CELL — 6802 ROW.

`RealizationC2 17411808`: the weighted cap of the 6802 A-kernel is
`A.m * agreements = 96 * 181373 = 17411808`.

Gates come from `LocatorHybridGatesC2` (caps 29 / 132 / 6403, errors 80771).  The
tangent count is `tangent_component_card_le` against the REDUCED budget family,
exactly as `RCN335` does it for the delayed provider.
-/
import ProximityPrize.SubmissionLower.LocatorFixedHybridC2

namespace ProximityPrize.SubmissionLower.LocatorHybridRealizeC2
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCostC1 LocatorHybridCostC2
open LocatorHybridTailProviderC1 LocatorHybridTailProviderC2
open LocatorHybridTailRealizationC2 LocatorHybridGatesC2
open LocatorFixed LocatorFixedHybridC2
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

theorem realizationC2 : RealizationC2 17411808 := by
  intro p hS hY hT hS3 hhyb
  letI : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
  unfold ProviderHypC2
  intro Gamma flag S hnodes hagreement hbox hflag hTail
  have hps := pad_sums p
  have hpb := pad_bounds p
  have hyt : padY p ≤ padT p := hpb.2.2
  have hflagChar : flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433 := by
    refine ⟨?_, ?_, ?_⟩ <;> omega
  have hmixedRed := reduced_mixed_gateC2 (padB p) (padSlope p) flag
    (by omega) (by omega) (by omega) (by omega)
  have hmix := product_gateC2 (padA p) (padB p) (padSlope p) flag
    (by omega) (by omega)
  have hrat := rational_gateC2 (padT p) (padY p) (padS p) hhyb
  have htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (RCN327.w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (80771 + 1) *
            (reducedBudgetFamily S hTail hflagChar hmixedRed).yzCost C := by
    intro C hall
    exact tangent_component_card_le S C hTail
      (reducedBaseOrd S hTail hflagChar hmixedRed C)
      181373 17411808 (padT p) (padS p) hnodes hagreement
      (by norm_num [RCN327.w]) (by norm_num [RCN327.w])
      (by norm_num [RCN327.w]) (by norm_num)
      hbox (reducedBudgetFamily S hTail hflagChar hmixedRed)
      (reducedBudgetFamily_yzPositive S hTail hflagChar hmixedRed C) hall
      (reducedBudgetFamily_yzPole S hTail hflagChar hmixedRed C)
  exact exists_hybridTailMultiplicityProviderC2_realized hS3 hhyb hyt S hTail
    hflagChar hmixedRed hmix hrat htangent

end
end ProximityPrize.SubmissionLower.LocatorHybridRealizeC2
