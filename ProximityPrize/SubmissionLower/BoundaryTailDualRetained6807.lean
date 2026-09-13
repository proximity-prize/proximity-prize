/-
UNCOMPILED. Actual retained proper-first-tail Stage adapter. The joint budget is
built inside the body from actual-source pointwise budgets and three actual
common linear channels. Neither hcut nor hjoint is a theorem premise.
This is not an unconditional ProtocolClaim or a full mixed-branch regular bound.
-/
import ProximityPrize.SubmissionLower.BoundaryTailProvider
import ProximityPrize.SubmissionLower.ThreeChannelJoint6807
import ProximityPrize.SubmissionLower.ReducedCommonLinear6807
import ProximityPrize.SubmissionLower.SecondJetPointwiseBudgets6807
import ProximityPrize.SubmissionLower.BoundaryTailJointBudget6807

namespace ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
open RCN057 (WeightBound)
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
open BoundaryTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap : ℕ}

theorem stage_card_le_dual
    (t y r : ℕ) (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧
      flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p)
    (hlinear : 2*(flag.zOnly+flag.yz+flag.all) < p)
    (hchar : 2*(w-1) < p)
    (hgate : stageErrorCap+1 ≤ (cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap+1)*(BoundaryTailReduced.reducedBudgetFamily S hfirstProper hflagChar hmixedRed).yzCost C)
    (P : SecondJetSupport.Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0) (hB : 2*(n0-(k+1)) ≤ B)
    (hn : n0 ≤ (SecondJetCoefficients.asS P).natDegree)
    (hdiv : ∀ d ≤ k, S.F ∣ SecondJetClearedHelper.helper P S.F (s-d) d)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : (k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff) ≠ 0) :
    Gamma.card ≤ flagMixed flag
      ((k+1) • ActualFirstCutPole6807.firstBaseFlag (w-1) r (y-r) (t-y) +
        w • SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)
      ((k+1) • cellNormal t y r +
        65539 • SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) / (k+1)^2 := by
  classical
  let E := AlgebraicClosure (RatFunc (GenericField K))
  haveI : CharP E p := charP_of_injective_algebraMap
    (algebraMap (GenericField K) E).injective p
  have h2E : (2 : E) ≠ 0 := by
    intro hh
    apply h2
    apply (algebraMap (GenericField K) E).injective
    simpa only [map_ofNat,map_zero] using hh
  have hfactE : (k.factorial : E) ≠ 0 := by
    intro hh
    apply hfact
    apply (algebraMap (GenericField K) E).injective
    simpa only [map_natCast,map_zero] using hh
  let base := BoundaryTailReduced.reducedBaseOrd S hfirstProper hflagChar hmixedRed
  let Uold := BoundaryTailReduced.reducedUnitFamily S hfirstProper hflagChar hmixedRed
  let unit := unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S) Uold base
  let Bfam := BoundaryTailReduced.reducedBudgetFamily S hfirstProper hflagChar hmixedRed
  let V := SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0
  let D1 := (k+1) • ActualFirstCutPole6807.firstBaseFlag (w-1) r (y-r) (t-y) + w • V
  let D2 := (k+1) • cellNormal t y r + 65539 • V
  let bound := flagMixed flag D1 D2 / (k+1)^2
  obtain ⟨budget,hcost,hpoint,hmov⟩ := SecondJetRetainedBudgets6807.exists_retained_budgets
    (polynomialEmbedding K) S.F S.G
    (globalTailCut (polynomialEmbedding K) S.F (w+1)) S.G_dvd_surface
    P B U L s k n0 hS hP hBU hUL hdn hB hn hdiv h2 hfact
    base flag (cellFirstTail t y r) unit
  let active := Finset.univ.filter (fun C : FirstTailComponent S =>
    surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff ∉ C.1)
  have hcost' : ∀ C : FirstTailComponent S,
      (budget C).zCost = Bfam.zCost C ∧ (budget C).yzCost = Bfam.yzCost C ∧
        (budget C).allCost = Bfam.allCost C := by
    intro C
    obtain ⟨hz,hy,ha⟩ := hcost C
    obtain ⟨ez,ey,ea⟩ := unitFamilyOfCongruentCut_costs
      (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    exact ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  have heq (f : FlagDegree) (C : FirstTailComponent S) :
      unit.toPrimeFlagBudgetFamily.weightedCost f C = Bfam.weightedCost f C := by
    obtain ⟨ez,ey,ea⟩ := unitFamilyOfCongruentCut_costs
      (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    change unit.toPrimeFlagBudgetFamily.zCost C = Bfam.zCost C at ez
    change unit.toPrimeFlagBudgetFamily.yzCost C = Bfam.yzCost C at ey
    change unit.toPrimeFlagBudgetFamily.allCost C = Bfam.allCost C at ea
    unfold PrimeFlagBudgetFamily.weightedCost
    rw [ez, ey, ea]
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hys : cellB y r + cellS r + 3 = r+(y-r) := by dsimp [cellB,cellS]; omega
  have htot : cellA t y + cellB y r + cellS r + 3 = r+(y-r)+(t-y) := by
    dsimp [cellA,cellB,cellS]; omega
  have hR : WeightBound residualSWeights S.F (r : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualSWeights S.F ≤ r by
      simpa only [cellSupport,RCN198.support,hs] using Hsupport.s_weight)
  have hYR : WeightBound residualYSWeights S.F ((r+(y-r) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualYSWeights S.F ≤ r+(y-r) by
      simpa only [cellSupport,RCN198.support,hys] using Hsupport.ys_weight)
  have hAll : WeightBound residualTotalWeights S.F ((r+(y-r)+(t-y) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualTotalWeights S.F ≤ r+(y-r)+(t-y) by
      simpa only [cellSupport,RCN198.support,htot] using Hsupport.total_weight)
  have hjoint0 := ThreeChannelJoint6807.joint_for_actual_unit_family (E := E)
    (loosenStageGeneral S) hfirstProper base (cellFirstTail t y r) unit
    (ReducedCommonLinear6807.original_common S hfirstProper hflagChar hmixedRed)
    active (fun C => (budget C).movingCost) P B U L s k n0
    hS hP hBU hUL hdn hB hn
    (fun C hc => (Finset.mem_filter.mp hc).2) hdiv h2E hfactE
    r (y-r) (t-y) hr3 (by omega) hR hYR hAll hflagChar.2.2 hlinear
    (fun C hc => hpoint C (Finset.mem_filter.mp hc).2) (cellNormal t y r) 65539
  have hjoint : (∑ C ∈ active,
      (localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C *
        Bfam.weightedCost (cellNormal t y r) C + 65539*(budget C).movingCost)) ≤ bound := by
    calc
      _ = ∑ C ∈ active,
          (localMultiplicity (loosenStageGeneral S)
            (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C *
            unit.toPrimeFlagBudgetFamily.weightedCost (cellNormal t y r) C +
              65539*(budget C).movingCost) := by
        apply Finset.sum_congr rfl
        intro C _
        rw [heq]
      _ ≤ bound := hjoint0
  have hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0 := by
    intro C hC
    apply SecondJetExceptionalComponents.component_empty_of_nonvanishing _ _ _
      (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS P).leadingCoeff)
      Gamma _ C ?_ hgood
    simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hC
  obtain ⟨provider⟩ := BoundaryTailJointBudget6807.exists_provider_of_joint_curve_budget
    t y r hr3 hb hyt hchar S hfirstProper (cellFirstTail t y r) Bfam base budget hcost'
    active bound hinactive hjoint hgate htangent
  exact stage_card_le_divisorBound S provider

end
end ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
