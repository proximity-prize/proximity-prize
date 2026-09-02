import ProximityPrize.SubmissionLower.LocatorFixedHybrid
import ProximityPrize.SubmissionLower.LocatorHybridTailRealization
import ProximityPrize.SubmissionLower.LocatorHybridGates

/-! The hybrid provider exists on every admissible cell of the fixed stage. -/

namespace ProximityPrize.SubmissionLower.LocatorHybridRealize
open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridTailProvider
open LocatorFactorAggregate LocatorHybridCost LocatorHybridCells LocatorHybridTailProvider
  LocatorHybridTailRealization LocatorHybridGates LocatorFixed LocatorFixedHybrid
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
local instance:DecidableEq (GenericField K):=Classical.decEq _
local instance:CharP K 2130706433:=by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

theorem realization:Realization 13071600:=by
  intro p hS hY hT hhyb
  letI:CharP (GenericField K) 2130706433:=genericField_charP K 2130706433
  unfold ProviderHyp
  intro Gamma flag S hnodes hagreement hbox hflag hTail
  have hps:=pad_sums p
  have hpb:=pad_bounds p
  have hr2:2 ≤ padS p:=hpb.1
  have hyt:padY p ≤ padT p:=hpb.2.2
  have hflagChar:flag.yz + flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly + flag.yz + flag.all < 2130706433:=by
    refine ⟨?_,?_,?_⟩ <;> omega
  have hmixedSharp:=sharp_mixed_gate (padB p) (padSlope p) flag
    (by omega) (by omega) (by omega) (by omega)
  have hmix:=product_gate (padA p) (padB p) (padSlope p) flag (by omega) (by omega)
  have hrat:=rational_gate (padT p) (padY p) (padS p) hhyb
  have htangent:∀ C:FirstTailComponent S,
      (∀ delay,globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (RCN327.w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (80594 + 1) * (sharpBudgetFamily S hTail hflagChar hmixedSharp).yzCost C:=by
    intro C hall
    exact tangent_component_card_le S C hTail
      ((sharpActiveGeometry S hTail hflagChar hmixedSharp).base C)
      181550 13071600 (padT p) (padS p) hnodes hagreement
      (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) (by norm_num)
      hbox (sharpBudgetFamily S hTail hflagChar hmixedSharp)
      (sharpUnitFamily_one_le_yzCost S hTail hflagChar hmixedSharp C) hall
      ((sharpUnitFamily S hTail hflagChar hmixedSharp).toAdaptiveUnitPoleBudget.yzPole C)
  exact exists_hybridTailMultiplicityProvider_realized hr2 hhyb hyt S hTail hflagChar
    hmixedSharp hmix hrat htangent
end
end ProximityPrize.SubmissionLower.LocatorHybridRealize
