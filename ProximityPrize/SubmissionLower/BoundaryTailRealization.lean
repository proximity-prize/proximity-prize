import ProximityPrize.SubmissionLower.BoundaryTailProvider
import ProximityPrize.SubmissionLower.BoundaryTailReduced

namespace ProximityPrize.SubmissionLower.BoundaryTailRealization
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTailProviderC2 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 800000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap : ℕ}
variable {t y r : Nat}

theorem exists_provider
    (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t) (hchar : 2*(w-1) < p)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (BoundaryTailProvider.cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (BoundaryTailReduced.reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := cellFirstTail t y r)
      (tailFlag2 := BoundaryTailProvider.cellNormal t y r) S
      (flagMixed flag (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r) +
        65539 *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  haveI : CharP (AlgebraicClosure (RatFunc (GenericField K))) p :=
    charP_of_injective_algebraMap
      (algebraMap (GenericField K)
        (AlgebraicClosure (RatFunc (GenericField K)))).injective p
  obtain ⟨budget, hcost, hmov⟩ :=
    exists_firstTail_moving_budgets
      (E := AlgebraicClosure (RatFunc (GenericField K)))
      (polynomialEmbedding K) S.F S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (cellA t y) (cellB y r) (cellS r) w (by norm_num [RCN327.w])
      rfl
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      flag S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
      (BoundaryTailReduced.reducedBaseOrd S hfirstProper hflagChar hmixedRed)
      (cellFirstTail t y r)
      (unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
        (BoundaryTailReduced.reducedUnitFamily S hfirstProper hflagChar hmixedRed)
        (BoundaryTailReduced.reducedBaseOrd S hfirstProper hflagChar hmixedRed))
      p hmix
  have hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    have hcut := cellMovingCut_eq_center_add t y r
    have hfib : cellMovingFiber t y r =
        RCN206.fiberFlag (cellA t y) (cellB y r) (cellS r) := rfl
    rw [hfib, hcut]
    exact hmov
  -- route the cost equalities through `unitFamilyOfCongruentCut_costs` rather
  -- than through a single large defeq check, which overruns `maxRecDepth`
  have hcost' : ∀ C : FirstTailComponent S,
      (budget C).zCost =
        (BoundaryTailReduced.reducedBudgetFamily S hfirstProper hflagChar hmixedRed).zCost C ∧
      (budget C).yzCost =
        (BoundaryTailReduced.reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C ∧
      (budget C).allCost =
        (BoundaryTailReduced.reducedBudgetFamily S hfirstProper hflagChar hmixedRed).allCost C := by
    intro C
    obtain ⟨hz, hy, ha⟩ := hcost C
    obtain ⟨ez, ey, ea⟩ := unitFamilyOfCongruentCut_costs
      (ordinary_sub_reducedFirstCut_dvd S)
      (BoundaryTailReduced.reducedUnitFamily S hfirstProper hflagChar hmixedRed)
      (BoundaryTailReduced.reducedBaseOrd S hfirstProper hflagChar hmixedRed) C
    refine ⟨hz.trans ez, hy.trans ey, ha.trans ea⟩
  exact BoundaryTailProvider.exists_provider_on_active_components
    t y r hr3 hb hyt hchar S hfirstProper (cellFirstTail t y r)
    (BoundaryTailReduced.reducedBudgetFamily S hfirstProper hflagChar hmixedRed)
    (BoundaryTailReduced.reducedBaseOrd S hfirstProper hflagChar hmixedRed)
    budget hcost' Finset.univ
    (flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))
    (by intro C hC; exact False.elim (hC (Finset.mem_univ C)))
    (by simpa using hmovingSum)
    hrationalGate htangent
    (BoundaryTailReduced.transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixedRed)

end
end ProximityPrize.SubmissionLower.BoundaryTailRealization
