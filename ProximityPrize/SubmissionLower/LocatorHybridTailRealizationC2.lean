/-
LOCATOR HYBRID TAIL REALIZATION — C2 VARIANT.

C2 runs the hybrid provider on the REDUCED first tail
`cellFirstTail t y r = reducedResidualAgreementFlag (cellSupport t y r) (w+1)`
instead of the sharp one.  Three pieces come from `RCN332` unchanged:

  reducedBudgetFamily                  the budget family over the T1-components
  reducedBaseOrd                       the separable base, transported
  transportedWeightedResultantsGeneral the certificate at the reduced flag

and the missing fourth — a `MovingPoleBudget` whose costs agree with that budget
family — is built here from `LocatorHybridTransportC2`: the reduced unit family
is transported to the T1-components, and `exists_firstTail_moving_budgets`
consumes it at the reduced first-tail flag.

The provider itself is `exists_hybridTailMultiplicityProviderGen_of_localDVR`,
the C1 proof with the first-tail flag left free.
-/
import ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
namespace ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
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
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
variable {t y r : Nat}

theorem exists_hybridTailMultiplicityProviderC2_realized
    (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedRed : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 2) * (w + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := cellFirstTail t y r)
      (tailFlag2 := cellHybridCoordinateC1 t y r) S
      (flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r) +
        (w + 5) *
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
      (reducedBaseOrd S hfirstProper hflagChar hmixedRed)
      (cellFirstTail t y r)
      (unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
        (reducedUnitFamily S hfirstProper hflagChar hmixedRed)
        (reducedBaseOrd S hfirstProper hflagChar hmixedRed))
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
        (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).zCost C ∧
      (budget C).yzCost =
        (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C ∧
      (budget C).allCost =
        (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).allCost C := by
    intro C
    obtain ⟨hz, hy, ha⟩ := hcost C
    obtain ⟨ez, ey, ea⟩ := unitFamilyOfCongruentCut_costs
      (ordinary_sub_reducedFirstCut_dvd S)
      (reducedUnitFamily S hfirstProper hflagChar hmixedRed)
      (reducedBaseOrd S hfirstProper hflagChar hmixedRed) C
    refine ⟨hz.trans ez, hy.trans ey, ha.trans ea⟩
  exact exists_hybridTailMultiplicityProviderGen_of_localDVR
    t y r hr3 hb hyt S hfirstProper (cellFirstTail t y r)
    (reducedBudgetFamily S hfirstProper hflagChar hmixedRed)
    (reducedBaseOrd S hfirstProper hflagChar hmixedRed)
    budget hcost' hmovingSum hrationalGate htangent
    (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixedRed)

/-- The C2 hybrid fixed-stage seed bound. -/
theorem hybridC2_stage_card_le
    (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
      flag.zOnly + flag.yz + flag.all < p)
    (hmixedRed : (1 + (w + 1) *
        (2 * (cellB y r + cellS r + 3) - 2)) * flag.all +
      (flag.yz + flag.all) *
        ((2 * (cellS r + 2) - 2) * (w + 1)) < p)
    (hmix : 2 * (flag.zOnly + flag.yz + flag.all) *
      (cellA t y + cellB y r + cellS r + 4) < p)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) *
            (reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C) :
    Gamma.card ≤
      flagMixed flag (cellFirstTail t y r) (cellHybridCoordinateC1 t y r) +
        (w + 5) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) :=
  stage_card_le_divisorBound S
    (exists_hybridTailMultiplicityProviderC2_realized hr3 hb hyt S hfirstProper
      hflagChar hmixedRed hmix hrationalGate htangent).some

end
end ProximityPrize.SubmissionLower.LocatorHybridTailRealizationC2
