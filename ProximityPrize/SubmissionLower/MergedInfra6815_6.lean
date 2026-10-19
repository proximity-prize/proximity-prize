import ProximityPrize.SubmissionLower.MergedInfra6815_2
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.LowerFoundation
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.BoundaryTailComponent
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open BoundaryTailAlgebra RCN057
set_option Elab.async false
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable [CharP K p]
variable {stageErrorCap : ℕ}

set_option maxHeartbeats 1000000 in
theorem component_moving_card_le_delay
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (hchar : 2 * (w - 1) < p)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (delay : ℕ) (hdelay : 1 ≤ delay) (factor : ℕ)
    (hfactor : w + 1 + delay ≤ 2 * factor)
    (htail : globalTailCut (polynomialEmbedding K) S.F
      (w + 1 + delay) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (BoundaryTailAlgebra.normalFlag (w - 1 + delay) r (y-r) (t-y)) +
        factor * budget.movingCost := by
  classical
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hs : cellS r + 2 = r := by dsimp [cellS]; omega
  have hys : cellB y r + cellS r + 3 = r + (y-r) := by
    dsimp [cellB, cellS]; omega
  have htot : cellA t y + cellB y r + cellS r + 3 = r + (y-r) + (t-y) := by
    dsimp [cellA, cellB, cellS]; omega
  have hR : WeightBound residualSWeights S.F (r : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualSWeights S.F ≤ r by
      simpa only [cellSupport, RCN198.support, hs] using Hsupport.s_weight)
  have hYR : WeightBound residualYSWeights S.F ((r + (y-r) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualYSWeights S.F ≤ r + (y-r) by
      simpa only [cellSupport, RCN198.support, hys] using Hsupport.ys_weight)
  have hAll : WeightBound residualTotalWeights S.F ((r + (y-r) + (t-y) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualTotalWeights S.F ≤ r + (y-r) + (t-y) by
      simpa only [cellSupport, RCN198.support, htot] using Hsupport.total_weight)
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hfirst : globalTailCut (polynomialEmbedding K) S.F (w + 1) ∈ C.1 :=
    regularComponent_T_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay))
      (budget.weightedCost (BoundaryTailAlgebra.normalFlag (w - 1 + delay) r (y-r) (t-y)) +
        factor * budget.movingCost) := by
    have hlevel : w - 1 + delay + 2 = w + 1 + delay := by norm_num [w]; omega
    have hfirstlevel : w - 1 + 2 = w + 1 := by norm_num [w]
    have hf : w - 1 + delay + 2 ≤ 2 * factor := by omega
    have hfirst0 : globalTailCut (polynomialEmbedding K) S.F (w-1+2) ∈ C.1 := by
      rw [hfirstlevel]
      exact hfirst
    have hlater0 : globalTailCut (polynomialEmbedding K) S.F (w-1+delay+2) ∉ C.1 := by
      rw [hlevel]
      exact htail
    have hz := BoundaryTailAlgebra.global_tail_zero_count C.1
      (polynomialEmbedding K) (polynomialEmbedding_injective K) S.F
      (w-1) (w-1+delay) r (y-r) (t-y) p factor
      (by norm_num [w]) (by norm_num [w]; omega) hchar hr3 (by omega)
      hf hR hYR hAll budget base hHnot hfirst0 hlater0
    rwa [hlevel] at hz
  let seeds := componentSeeds (GenericField K) S.G
    (globalTailCut (polynomialEmbedding K) S.F (w + 1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C
  let pts : Finset (Fin 3 → GenericField K) :=
    seeds.image (selectedPoint (polynomialEmbedding K) S.selected)
  have hprime : ∀ v ∈ pts,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
  have hHne : ∀ v ∈ pts, MvPolynomial.aeval v
      (regularitySurface (polynomialEmbedding K) S.F) ≠ 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    show MvPolynomial.eval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (regularitySurface (polynomialEmbedding K) S.F) ≠ 0
    exact (selectedPoint_evaluation (polynomialEmbedding K) S.selected gamma
      (MvPolynomial.pderiv (2 : Fin 4) S.F)).symm ▸ S.regular gamma hGamma
  have hAzero : ∀ v ∈ pts, MvPolynomial.aeval v
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0 := by
    intro v hv
    obtain ⟨gamma, hgamma, rfl⟩ := Finset.mem_image.mp hv
    have hGamma : gamma ∈ Gamma := componentSeeds_subset (GenericField K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w + 1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
    have hz : MvPolynomial.aeval
        (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (globalTailCut (polynomialEmbedding K) S.F
          (w + 1 + delay)) = 0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
        S.selected gamma w (w + 1 + delay)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact hz
  have hbound : pts.card ≤
      budget.weightedCost (BoundaryTailAlgebra.normalFlag (w - 1 + delay) r (y-r) (t-y)) +
        factor * budget.movingCost :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega

end
end ProximityPrize.SubmissionLower.BoundaryTailComponent
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
open RCN095 RCN237 RCN206 RCN327 LocatorHybridCells LocatorHybridCellsC1

theorem normalFlag_yz_eq (m v : ℕ) (hv : 1 ≤ v) :
    (m + 3) * v - (m + 1) = (m + 3) * (v - 1) + 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hv
  simp only [Nat.add_sub_cancel_left, Nat.mul_add, Nat.mul_one]
  omega

theorem normalFlag_eq_cell (t y r : ℕ) (hr : 3 ≤ r)
    (hy : r + 2 ≤ y) :
    normalFlag w r (y - r) (t - y) =
      cellHybridCoordinateC1 t y r + w • unitAllFlag := by
  unfold normalFlag cellHybridCoordinateC1 cellRational
  apply congrArg₃ (f := FlagDegree.mk)
  all_goals simp only [normalFlag, cellHybridCoordinateC1, cellRational,
    cellDirection, directionFlag, cellA, cellB, cellS, add_zOnly, add_yz,
    add_all, nsmul_zOnly, nsmul_yz, nsmul_all, unitAllFlag, w]
  all_goals omega

theorem normalFlag_delay_le_smul (w m d r v z : ℕ)
    (hw : 1 ≤ w) (hm : 1 ≤ m) (hd : d ≤ m) (hv : 1 ≤ v) :
    (normalFlag (w - 1 + d) r v z).zOnly ≤ (m • normalFlag w r v z).zOnly ∧
    (normalFlag (w - 1 + d) r v z).yz ≤ (m • normalFlag w r v z).yz ∧
    (normalFlag (w - 1 + d) r v z).all ≤ (m • normalFlag w r v z).all := by
  have hwsub : w - 1 + 1 = w := Nat.sub_add_cancel hw
  have hscale : w - 1 + d + 3 ≤ m * (w + 3) := by nlinarith [Nat.mul_le_mul_right w hm]
  simp only [normalFlag, nsmul_zOnly, nsmul_yz, nsmul_all]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [Nat.mul_le_mul_right z hscale]
  · rw [normalFlag_yz_eq _ _ hv, normalFlag_yz_eq _ _ hv]
    nlinarith [Nat.mul_le_mul_right (v - 1) hscale]
  · nlinarith [Nat.mul_le_mul_right (r - 1) hscale]

theorem low_delay_factor (d m : ℕ) (hd : d ≤ m) (hm : m ≤ 5) :
    w + 1 + d ≤ 2 * 65539 := by
  simp only [w]
  omega

end ProximityPrize.SubmissionLower.BoundaryTailAlgebra
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.BoundaryTailProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
open BoundaryTailAlgebra
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

def cellNormal (t y r : ℕ) : FlagDegree :=
  BoundaryTailAlgebra.normalFlag w r (y-r) (t-y)

theorem exists_provider_on_active_components
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (hchar : 2 * (w - 1) < p)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (tail1 : FlagDegree)
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag tail1)
    (base : ∀ C : FirstTailComponent S, SeparableLiteralCoordinate C.1)
    (budget : ∀ C : FirstTailComponent S,
      MovingPoleBudget C.1
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (hcost : ∀ C : FirstTailComponent S,
      (budget C).zCost = B.zCost C ∧ (budget C).yzCost = B.yzCost C ∧
        (budget C).allCost = B.allCost C)
    (active : Finset (FirstTailComponent S)) (movingTotal : ℕ)
    (hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0)
    (hmovingSum : (∑ C ∈ active, (budget C).movingCost) ≤ movingTotal)
    (hgate : stageErrorCap + 1 ≤ (cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F
        (w + 1 + delay) ∈ C.1) →
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (stageErrorCap + 1) * B.yzCost C)
    (hresultants : RegularComponentWeightedInertiaResultantCertificate B
      (fun C => localMultiplicity (loosenStageGeneral S)
        (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C)) :
    Nonempty (HybridTailMultiplicityProvider
      (tailFlag1 := tail1)
      (tailFlag2 := cellNormal t y r) S
      (flagMixed flag tail1 (cellNormal t y r) +
        65539 * movingTotal)) := by
  classical
  have hry : r < y := by omega
  have hr2 : 2 ≤ r := by omega
  let S0 := loosenStageGeneral S
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C :=
    loosenStageGeneral_one_le_localMultiplicity S hfirstProper
  have hwcEq : ∀ (C : FirstTailComponent S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [MovingPoleBudget.weightedCost,
      PrimeFlagBudgetFamily.weightedCost, hz, hy', ha]
  have hscale : ∀ (m : ℕ) (f : FlagDegree) (C : FirstTailComponent S),
      B.weightedCost (m • f) C = m * B.weightedCost f C := by
    intro m f C
    simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
      nsmul_all]
    ring
  have hnormal : ∀ C : FirstTailComponent S,
      B.weightedCost (cellHybridCoordinateC1 t y r) C ≤
        B.weightedCost (cellNormal t y r) C := by
    intro C
    unfold cellNormal
    rw [normalFlag_eq_cell t y r hr3 hb]
    apply weightedCost_mono B C
    all_goals simp only [add_zOnly, add_yz, add_all, nsmul_zOnly,
      nsmul_yz, nsmul_all, unitAllFlag]
    all_goals omega
  let cost : FirstTailComponent S → ℕ := fun C =>
    multiplicity C * B.weightedCost (cellNormal t y r) C +
      65539 * (budget C).movingCost
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellNormal t y r) C +
        65539 * (budget C).movingCost := fun _ => le_rfl
  have hbound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤ cost C := by
    intro C
    have dichotomy := local_order_tail_dichotomy S0
      (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
    rcases dichotomy.2 with hproper | htangentBranch
    · obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
      by_cases hm : 6 ≤ multiplicity C
      · have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C,
            MvPolynomial.aeval
              (selectedPoint (polynomialEmbedding K) S.selected gamma)
              (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0 := by
          intro gamma hgamma
          have hGamma := componentSeeds_subset (GenericField K) S.G
            (globalTailCut (polynomialEmbedding K) S.F (w + 1))
            (regularitySurface (polynomialEmbedding K) S.F) Gamma
            (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
          exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K)
            S.F S.selected gamma w (w + 1 + delay)
            (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
        have hflagMod : PolynomialInFlagMod C.1
            (multiplicity C • cellHybridCoordinateC1 t y r)
            (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay),
            laterTail_in_hybridFlagC1 t y r hr3 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simp
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        rw [hscale] at hcount
        exact hcount.trans ((Nat.mul_le_mul_left _ (hnormal C)).trans
          (Nat.le_add_right _ _))
      · have hdm : delay ≤ multiplicity C := hdelayMu
        have hcount := BoundaryTailComponent.component_moving_card_le_delay
          t y r hr3 hb hyt hchar S C (budget C) (base C) delay hdelay
          65539 (low_delay_factor delay (multiplicity C) hdm (by omega)) htail
        simp only [hwcEq] at hcount
        have hmono := normalFlag_delay_le_smul w (multiplicity C) delay r
          (y-r) (t-y) (by norm_num [w]) (hone C) hdm (by omega)
        have hcostle := weightedCost_mono B C hmono.1 hmono.2.1 hmono.2.2
        rw [hscale] at hcostle
        exact hcount.trans (Nat.add_le_add_right hcostle _)
    · have hcount := htangent C htangentBranch
      calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
        _ ≤ B.weightedCost (cellNormal t y r) C :=
          yzCost_mul_le_weightedCost B (cellNormal t y r) C
            (stageErrorCap + 1) hgate
        _ ≤ multiplicity C * B.weightedCost (cellNormal t y r) C := by
          simpa only [one_mul] using Nat.mul_le_mul_right
            (B.weightedCost (cellNormal t y r) C) (hone C)
        _ ≤ cost C := Nat.le_add_right _ _
  let activeCost : FirstTailComponent S → ℕ := fun C => if C ∈ active then cost C else 0
  have hactiveBound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤ activeCost C := by
    intro C
    by_cases hC : C ∈ active
    · simpa only [activeCost,if_pos hC] using hbound C
    · simp only [activeCost,if_neg hC,hinactive C hC,le_refl]
  have hsum : (∑ C, activeCost C) ≤
      flagMixed flag tail1 (cellNormal t y r) + 65539*movingTotal := by
    have ha : (∑ C, activeCost C) = ∑ C ∈ active, cost C := by simp only [activeCost,Finset.sum_ite_mem,Finset.univ_inter]
    rw [ha]
    calc
      (∑ C ∈ active, cost C) ≤
          ∑ C ∈ active, (multiplicity C *
            B.weightedCost (cellNormal t y r) C +
            65539*(budget C).movingCost) :=
        Finset.sum_le_sum (fun C _ => hcost_pointwise C)
      _ = (∑ C ∈ active, multiplicity C *
            B.weightedCost (cellNormal t y r) C) +
          65539*(∑ C ∈ active, (budget C).movingCost) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
      _ ≤ (∑ C, multiplicity C *
            B.weightedCost (cellNormal t y r) C) +
          65539*movingTotal :=
        Nat.add_le_add (Finset.sum_le_sum_of_subset (Finset.subset_univ active))
          (Nat.mul_le_mul_left _ hmovingSum)
      _ ≤ _ := Nat.add_le_add (hresultants.divisor_le B multiplicity) (le_refl _)
  have providerDichotomy := loosenStageGeneral_dichotomy_with_tangent S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := activeCost
    one_le_multiplicity := hone
    tangentYZGate := hgate
    cost_sum_le := hsum
    componentBound := hactiveBound
    dichotomy := providerDichotomy }⟩

end
end ProximityPrize.SubmissionLower.BoundaryTailProvider
end MergedPart2
section MergedPart3
namespace ProximityPrize.SubmissionLower.BoundaryTailSharpGate
set_option maxHeartbeats 1000000
open RCN002 RCN004 RCN005 RCN095 RCN125 RCN371
open scoped BigOperators

theorem finite_separable_z_of_flag_gate {Omega : Type} [Field Omega]
    (P : Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
    (hZ : Transcendental Omega (coordinate Omega P 2))
    (prime : Nat) [CharP Omega prime]
    (G T : MvPolynomial (Fin 3) Omega)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P)
    (hproper : ¬ G ∣ T)
    (hR : MvPolynomial.pderiv (1 : Fin 3) G ≠ 0)
    (pG pT : FlagDegree)
    (hGflag : RCN095.PolynomialInFlag pG G)
    (hTflag : RCN095.PolynomialInFlag pT T)
    (hsmall : flagMixed pG pT unitZFlag < prime) :
    letI := rationalBaseAlgebra Omega P 2 hZ
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) ∧
      Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P) := by
  let Q : Unit → Ideal (MvPolynomial (Fin 3) Omega) := fun _ => P
  have hinj : Function.Injective Q := by
    intro i j _
    exact Subsingleton.elim i j
  letI : Algebra (RatFunc Omega) (CoordinateField Omega P) :=
    rationalBaseAlgebra Omega P 2 hZ
  have htZ : ∀ i : Unit, Transcendental Omega
      (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0))) := by
    intro i
    simpa [Q, zOrder, Equiv.swap_apply_def] using hZ
  have hembZ (i : Unit) :
      RCN022.elementEmbedding Omega (CoordinateField Omega (Q i))
        (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0))) (htZ i) =
      RCN022.elementEmbedding Omega (CoordinateField Omega P) (coordinate Omega P 2) hZ :=
    by
      have hx : RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0)) =
          coordinate Omega P 2 := by simp [Q, zOrder]
      simp only [hx]
      rfl
  have hgenZ : ∀ i : Unit,
      letI : Algebra (RatFunc Omega) (CoordinateField Omega (Q i)) :=
        (RCN022.elementEmbedding Omega (CoordinateField Omega (Q i))
          (RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 0)))
          (htZ i)).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc Omega)
        ({RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 2)),
          RCN093.flagEvaluation Omega (Q i) 0 0 0 (MvPolynomial.X (zOrder 1))} :
            Set (CoordinateField Omega (Q i))) = ⊤ := by
    intro i
    rw [hembZ i]
    simpa [Q, zOrder, Equiv.swap_apply_def] using RCN093.flag_generators_z Omega P 0 0 0 hZ
  have hfamily := RCN093.finite_sum_flag_finrank_trapezoid
    (K := Omega) (Q := Q) hinj 0 0 0 zOrder htZ hgenZ
      G T hG (fun _ => hGmem) (fun _ => hTmem) hproper
      (by simpa using (RCN117.flag_u_z_outer_positive_of_pderiv 0 0 G hR).2)
      pG.all pT.all (pG.yz + pG.all) (pT.yz + pT.all)
      (flagMixed pG pT unitZFlag) (by
        intro hzero
        apply hproper
        rw [hzero]
        exact dvd_zero G)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pG G 0 0 0
          ((support_subset_flagSupport_iff pG G).2 hGflag)).zOuter)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pT T 0 0 0
          ((support_subset_flagSupport_iff pT T).2 hTflag)).zOuter)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pG G 0 0 0
          ((support_subset_flagSupport_iff pG G).2 hGflag)).zTotal)
      (by
        simpa using (RCN123.flagTrapezoidCaps_flagAlgHom pT T 0 0 0
          ((support_subset_flagSupport_iff pT T).2 hTflag)).zTotal)
      (RCN121.z_flag_trapezoid_budget pG pT)
  have hfd : FiniteDimensional (RatFunc Omega) (CoordinateField Omega P) := by
    convert hfamily.1 () using 1
    congr 1
    exact congrArg (fun e : RatFunc Omega →ₐ[Omega] CoordinateField Omega P => e.toRingHom.toAlgebra) (hembZ ()).symm
  have hrank : Module.finrank (RatFunc Omega) (CoordinateField Omega P) ≤
      flagMixed pG pT unitZFlag := by
    have hs := hfamily.2
    simp only [Fintype.sum_unique] at hs
    convert hs using 1
    congr 2
    exact congrArg (fun e : RatFunc Omega →ₐ[Omega] CoordinateField Omega P => e.toRingHom.toAlgebra) (hembZ ()).symm
  letI := hfd
  refine ⟨hfd, ⟨fun x => ?_⟩⟩
  have hint : IsIntegral (RatFunc Omega) x := Algebra.IsIntegral.isIntegral x
  exact (RCN364.integral_and_separable_of_small_annihilator prime
    (minpoly (RatFunc Omega) x) x (minpoly.ne_zero hint) (minpoly.aeval _ _)
    ((minpoly.natDegree_le (A := RatFunc Omega) x).trans_lt (hrank.trans_lt hsmall))).2
end ProximityPrize.SubmissionLower.BoundaryTailSharpGate
end MergedPart3
section MergedPart4
namespace ProximityPrize.SubmissionLower.BoundaryTailProjection
open scoped Classical BigOperators
open BoundaryTailSharpGate
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN198 RCN086 RCN263 RCN089
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+* Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem exists_reduced_firstTail_activeNestedData_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < pchar) :
   ∃ (base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F), SeparableLiteralCoordinate C.1),
     ∃ (hactive:∀ C:RegularComponent Omega S.G
         (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
         (regularitySurface phi S.F),
         KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 0) ≠ 0 ∨
           KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃ (hZ:∀ C:RegularComponent Omega S.G
           (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
           (regularitySurface phi S.F), LiteralProjectionGate C 2),
         Nonempty (AdaptiveNestedProjectionDataActive base hactive
           (RCN315.residualStage_pderiv_one_ne_zero_of_support S)):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T, Tred, sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY, hGS, hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 have hGdegree:∀ j:Fin 3, S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR := RCN315.residualStage_pderiv_one_ne_zero_of_support S
 let hZ:∀ C:RegularComponent Omega S.G Tred H, LiteralProjectionGate C 2 := by
   intro C htr
   exact finite_separable_z_of_flag_gate C.1 htr pchar S.G Tred
     S.irreducible_G (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C) hproperRed hR
     flag (reducedResidualAgreementFlag supp (w+1)) hGflag hTflag hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 := by
   intro C
   by_cases hz:Transcendental Omega (coordinate Omega C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy := (regularComponent_y_or_z_transcendental phi S.F S.G Tred
       S.G_dvd_surface C).resolve_right hz
     have hsep := finite_separable_at_y_of_z_algebraic C.1 pchar S.G
       S.irreducible_G (regularComponent_G_mem Omega S.G Tred H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 exact ⟨base, hactive, hZ,
   exists_adaptiveNestedProjectionDataActive base hactive
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.BoundaryTailProjection

namespace ProximityPrize.SubmissionLower.BoundaryTailProjection
open scoped Classical BigOperators
open BoundaryTailSharpGate
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN274 RCN198
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem exists_agreement_projection_of_caps
   (S:ResidualStage φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣agreementPolynomial φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag < p):
   ∃ base:∀ C:RegularComponent Ω S.G
       (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (support a b s) w)):=by
 classical
 let T:=agreementPolynomial φ S.F w x0 u0 u1
 let H:=regularitySurface φ S.F
 have hsy:s+2 < b+s+3:=by omega
 have hTflag:PolynomialInFlag (sharpResidualAgreementFlag (support a b s) w) T:=
   surfaceMap_agreement_in_sharp_flag hsy (phi:=φ)
     ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
     w (fun j:ℕ => (j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag S.flag_support
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hR := RCN315.residualStage_pderiv_one_ne_zero_of_support S
 let hZ:∀ C:RegularComponent Ω S.G T H, LiteralProjectionGate C 2 := by
   intro C htr
   exact finite_separable_z_of_flag_gate C.1 htr p S.G T
     S.irreducible_G (regularComponent_G_mem Ω S.G T H C)
     (regularComponent_T_mem Ω S.G T H C) hproper hR
     flag (sharpResidualAgreementFlag (support a b s) w) S.flag_support hTflag hmixed
 let choiceData:∀ C:RegularComponent Ω S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 := by
   intro C
   by_cases hz:Transcendental Ω (coordinate Ω C.1 2)
   · exact ⟨⟨2,hz,(hZ C hz).1,(hZ C hz).2⟩,Or.inr rfl⟩
   · have hy := (regularComponent_y_or_z_transcendental φ S.F S.G T
       S.G_dvd_surface C).resolve_right hz
     have hsep := finite_separable_at_y_of_z_algebraic C.1 p S.G
       S.irreducible_G (regularComponent_G_mem Ω S.G T H C)
       S.y_dependent hGdegree hy (not_not.mp hz)
     exact ⟨⟨0,hy,hsep.1,hsep.2⟩,Or.inl rfl⟩
 let base:∀ C:RegularComponent Ω S.G T H,
     SeparableLiteralCoordinate C.1:=fun C => (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Ω S.G T H,
     D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end ProximityPrize.SubmissionLower.BoundaryTailProjection
end MergedPart4
section MergedPart5
namespace ProximityPrize.SubmissionLower.BoundaryTailReduced
open scoped Classical BigOperators
open RCN332 BoundaryTailProjection
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
theorem exists_reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   Nonempty (ReducedActiveGeometry S):=by
 obtain ⟨base, hactive, hZ, -⟩ :=
   BoundaryTailProjection.exists_reduced_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
 obtain ⟨D, hlam, hmu⟩:=RCN038.exists_adaptiveNestedProjectionDataActive_in base hactive
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) (Set.range (polynomialEmbedding K))
   (Set.infinite_range_of_injective (polynomialEmbedding_injective K))
 exact ⟨⟨base, hactive, hZ, D, hlam, hmu⟩⟩
noncomputable def reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   ReducedActiveGeometry S :=
 Classical.choice (exists_reducedActiveGeometry S hfirstProper hflagChar hmixed)
noncomputable def reducedUnitFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :=
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 activeNestedUnitFamily A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
noncomputable def reducedBudgetFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :=
 PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
noncomputable def reducedBaseOrd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p)
   (C:FirstTailComponent S):SeparableLiteralCoordinate C.1:=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 exact (reducedActiveGeometry S hfirstProper hflagChar hmixed).base C'
theorem reducedBudgetFamily_yzPositive
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p)
   (C:FirstTailComponent S) :
   1 ≤ (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C:=by
 let hd:=ordinary_sub_reducedFirstCut_dvd S
 let C':=regularComponentEquiv hd C
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 let U:=reducedUnitFamily S hfirstProper hflagChar hmixed
 change 1 ≤ U.toPrimeFlagBudgetFamily.yzCost C'
 change 1 ≤ coordinateDegree (GenericField K)
   (CoordinateField (GenericField K) C'.1) (U.yzProjection C')
 apply one_le_coordinateDegree_of_transcendental_value
 have hproj:U.yzProjection C' = coordinateOfGate
     (RCN093.affineU
       (GenericField K) C'.1 A.data.lam) (A.data.uGate C'):=rfl
 rw [hproj, coordinateOfGate_value]
 exact A.data.uTranscendental C'
theorem reducedBudgetFamily_yzPole
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p)
   (C:FirstTailComponent S) :
   LiteralSupportPoleBound
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     (flagSupport unitYZFlag)
     ((reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C):=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 have heq:regularComponentEquiv (ordinary_sub_reducedFirstCut_dvd S) C = C':=by
   apply Subtype.ext
   rfl
 rw [show (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C =
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C' by
   simp only [reducedBudgetFamily, PrimeFlagBudgetFamily.ofCongruentCut, heq]]
 change LiteralSupportPoleBound
   ((reducedActiveGeometry S hfirstProper hflagChar hmixed).base C')
   (flagSupport unitYZFlag)
   ((reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C')
 exact (reducedUnitFamily S hfirstProper hflagChar hmixed).toAdaptiveUnitPoleBudget.yzPole C'
theorem reducedFixedPowersGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStageGeneral S)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicityGeneral S hfirstProper))
   (reducedFixedPowersGeneral S hfirstProper hflagChar hmixed)
theorem transportedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicityGeneral S hfirstProper)
   (reducedWeightedResultantsGeneral S hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.BoundaryTailReduced
end MergedPart5
section MergedPart6
namespace ProximityPrize.SubmissionLower.BoundaryTailRealization
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open RCN331 RCN027 RCN030 RCN029 RCN037 RCN038 RCN042 RCN002 RCN344 RCN277 RCN003 RCN314 RCN315 RCN093 RCN046 RCN001
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
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
end MergedPart6
section MergedPart7
namespace ProximityPrize.SubmissionLower.BoundaryTailGates6808
open RCN095 RCN198 RCN263 RCN287 RCN327 LocatorHybridCells
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def Safe (r y : ℕ) : Prop :=
  r * (cellFirstTail y y r).yz + y * (cellFirstTail y y r).all < 2130706433 ∧
  r * (sharpResidualAgreementFlag (cellSupport y y r) w).yz +
    y * (sharpResidualAgreementFlag (cellSupport y y r) w).all < 2130706433
instance (r y : ℕ) : Decidable (Safe r y) := by unfold Safe; infer_instance

theorem z_mixed_bound (f q : FlagDegree) (r y : ℕ)
    (hr : f.all ≤ r) (hy : f.yz + f.all ≤ y) :
    flagMixed f q unitZFlag ≤ r * q.yz + y * q.all := by
  have h1 := Nat.mul_le_mul_right q.yz hr
  have h2 := Nat.mul_le_mul_right q.all hy
  simp only [flagMixed, unitZFlag]
  nlinarith

theorem reduced_gate (f : FlagDegree) (t y r : ℕ)
    (hsafe : Safe r y) (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (cellFirstTail t y r) unitZFlag < 2130706433 := by
  have hy : (cellFirstTail t y r).yz = (cellFirstTail y y r).yz := rfl
  have hr : (cellFirstTail t y r).all = (cellFirstTail y y r).all := rfl
  exact (z_mixed_bound f _ r y hfa hfy).trans_lt (by rw [hy,hr]; exact hsafe.1)

theorem identity_gate (f : FlagDegree) (t y r : ℕ)
    (hsafe : Safe r y) (hfa : f.all ≤ r) (hfy : f.yz + f.all ≤ y) :
    flagMixed f (sharpResidualAgreementFlag (cellSupport t y r) w) unitZFlag < 2130706433 := by
  have hy : (sharpResidualAgreementFlag (cellSupport t y r) w).yz =
      (sharpResidualAgreementFlag (cellSupport y y r) w).yz := rfl
  have hr : (sharpResidualAgreementFlag (cellSupport t y r) w).all =
      (sharpResidualAgreementFlag (cellSupport y y r) w).all := rfl
  exact (z_mixed_bound f _ r y hfa hfy).trans_lt (by rw [hy,hr]; exact hsafe.2)
end ProximityPrize.SubmissionLower.BoundaryTailGates6808
end MergedPart7
section MergedPart8
namespace ProximityPrize.SubmissionLower.BoundaryTailIdentity
open scoped Classical BigOperators
open RCN146
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Γ:Finset K} {x:I → K} {p e a b s:ℕ} [CharP (GenericField K) p]
 {flag:FlagDegree} {w:ℕ}
theorem actual_identityCurveCountProvider
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀ γ∈Γ,agreements≤(S.agreementFiber γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag < p):
   IdentityCurveCountProvider S (identityCurveDegree flag a b s w):=by
 classical
 unfold IdentityCurveCountProvider
 intro i hi
 dsimp only
 intro hproper
 let T:=agreementPolynomial (polynomialEmbedding K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ => S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=BoundaryTailProjection.exists_agreement_projection_of_caps S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:RegularComponent (GenericField K) S.G T (regularitySurface (polynomialEmbedding K) S.F)→ℕ:=
   fun C => U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=componentSeeds (GenericField K) S.G T
     (regularitySurface (polynomialEmbedding K) S.F) Gi
     (selectedPoint (polynomialEmbedding K) S.selected) C
   have hGcGi:Gc⊆Gi:=componentSeeds_subset (GenericField K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀ W:Finset (RCN346.Place (GenericField K)
       (CoordinateField (GenericField K) C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate (GenericField K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,exponentSetPoleWeight v.val (coordinate (GenericField K) C.1)
       (flagSupport unitYZFlag))≤
       (coordinateDegree (GenericField K) (CoordinateField (GenericField K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder (GenericField K)
           (CoordinateField (GenericField K) C.1) v
           (coordinateValue (GenericField K) (CoordinateField (GenericField K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _ ≤ _:=finite_sum_coordinate_pole_le_degree (GenericField K)
         (CoordinateField (GenericField K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=coefficientPoleProfile_of_regular_agreement_curve
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toPrimeFlagBudgetFamily.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
       (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
       (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ) ≤
         ((U.family.toPrimeFlagBudgetFamily.zCost C+
           U.family.toPrimeFlagBudgetFamily.yzCost C:ℕ):ℤ)
       exact_mod_cast Nat.le_add_left _ _)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (polynomialEmbedding K) S.F rfl S.G_dvd_surface C
   apply prime_curve_card_le_of_coefficientPoleProfile
     (polynomialEmbedding K) C.1 S.F
     (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
     (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.characteristic_bound hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact componentSeeds_on_prime (GenericField K) S.G T
       (regularitySurface (polynomialEmbedding K) S.F) Gi
       (selectedPoint (polynomialEmbedding K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     exact hagreement γ hΓ
   · exact noLargeSelectedPencil_mono S.selected Γ Gc w e hGcΓ S.no_large_pencil
 · have hz:=U.family.sum_zDegree_le
   have hyz:=U.family.sum_yzDegree_le
   change (∑ C,U.family.toPrimeFlagBudgetFamily.zCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toPrimeFlagBudgetFamily.yzCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (mixed_sharp_le_padded a b s w flag unitZFlag)
   have hyz':=hyz.trans (mixed_sharp_le_padded a b s w flag unitYZFlag)
   have hz'':=hz'.trans (mixed_padded_le_succ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (mixed_padded_le_succ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C)) ≤ identityCurveDegree flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end ProximityPrize.SubmissionLower.BoundaryTailIdentity
end MergedPart8
section MergedPart9
namespace ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic

open RCN095 RCN146
open Lower80788.FixedStage
open Lower80788.HybridIdentityC2

def newNormal (f : FlagDegree) (a b s : ℕ) : ℕ :=
  flagMixed f (reducedABS a b s)
    (rationalABS a b s + 131071 • unitAllFlag)

def newCost (f : FlagDegree) (a b s : ℕ) : ℕ :=
  newNormal f a b s + 65539 * flagMixed f (mfibABS a b s) (mcutABS a b s)

end ProximityPrize.SubmissionLower.BoundaryTailIdentityArithmetic
end MergedPart9
section MergedPart10
namespace ProximityPrize.SubmissionLower.MovingFiberIdentityArithmetic6815
open RCN095 RCN146 Lower80788.HybridIdentityC2
open BoundaryTailIdentityArithmetic (newCost newNormal)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem generic_absorption (f : FlagDegree) (a b s : ℕ) (_ha : 0 ≤ a)
    (hb : 1 ≤ b) (hs : 1 ≤ s) :
    131073 * 80900 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a b s 131071 ≤
      50174 * newCost f a b s := by
  obtain ⟨b',rfl⟩ : ∃ b', b = b'+1 := ⟨b-1,by omega⟩
  obtain ⟨s',rfl⟩ : ∃ s', s = s'+1 := ⟨s-1,by omega⟩
  change 131073 * 80900 * ProximityPrize.SubmissionLower.RCN146.identityCurveDegree f a (b'+1) (s'+1)
    Lower80788.HybridIdentityC2.w ≤ _
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  simp [newCost, newNormal, reducedABS, rationalABS, mfibABS, mcutABS,
    flagMixed, unitAllFlag, add_zOnly, add_yz, add_all,
    nsmul_zOnly, nsmul_yz, nsmul_all]
  ring_nf
  omega

end ProximityPrize.SubmissionLower.MovingFiberIdentityArithmetic6815
end MergedPart10
section MergedPart11
namespace ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6815

open scoped Classical BigOperators
open RCN135 RCN136 RCN139 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095
open RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312
open RCN339 RCN330 RCN174 RCN319 RCN206 RCN287 RCN066 RCN338 RCN199 RCN207
open RCN271 RCN313 RCN234 RCN156 RCN341 RCN085 RCN087 RCN203 RCN084 RCN335
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

def bound (flag : FlagDegree) (t y r : ℕ) : ℕ :=
  flagMixed flag (cellFirstTail t y r) (BoundaryTailProvider.cellNormal t y r) +
    65539 * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)

theorem bound_eq_abs (flag : FlagDegree) (t y r : ℕ)
    (hr3 : 3 ≤ r) (hb : r+2 ≤ y) :
    bound flag t y r = BoundaryTailIdentityArithmetic.newCost flag
      (cellA t y) (cellB y r) (cellS r) := by
  have hfirst := SecondJetIdentity.cell_first_eq t y r
  have hnormal : BoundaryTailProvider.cellNormal t y r =
      Lower80788.HybridIdentityC2.rationalABS (cellA t y) (cellB y r) (cellS r) +
        131071 • unitAllFlag := by
    unfold BoundaryTailProvider.cellNormal
    rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hb,
      SecondJetIdentity.cell_normal_eq]
    rfl
  have hfiber : cellMovingFiber t y r =
      Lower80788.HybridIdentityC2.mfibABS (cellA t y) (cellB y r) (cellS r) := rfl
  have hrat : cellRational t y r =
      Lower80788.HybridIdentityC2.rationalABS (cellA t y) (cellB y r) (cellS r) :=
    SecondJetIdentity.cell_normal_eq t y r
  have hcut : cellMovingCut t y r =
      Lower80788.HybridIdentityC2.mcutABS (cellA t y) (cellB y r) (cellS r) := by
    simp only [cellMovingCut, Lower80788.HybridIdentityC2.mcutABS, hrat,
      RCN327.w, Nat.reduceAdd, Nat.reduceMul]
  unfold bound BoundaryTailIdentityArithmetic.newCost BoundaryTailIdentityArithmetic.newNormal
  rw [hfirst, hnormal, hfiber, hcut]

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

theorem stage_card_le (D t y r : ℕ)
    (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (hRcap : r ≤ 32) (hYcap : y ≤ 149) (hTcap : t ≤ 8121)
    (hSafe : BoundaryTailGates6808.Safe r y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80899 flag
      w (cellSupport t y r))
    (hnodes : S.nodes.card = 181245+80899)
    (hagreement : ∀ gamma ∈ Gamma, 181245 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧
      flag.zOnly+flag.yz+flag.all ≤ t) :
    Gamma.card ≤ bound flag t y r := by
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  have hshort : w+1 ≤ D := by simpa only [RCN327.w] using hDlow
  have hb1 : 1 ≤ cellB y r := by dsimp [cellB]; omega
  have hs1 : 1 ≤ cellS r := by dsimp [cellS]; omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator : S.G ∣ surfaceMap (polynomialEmbedding K)
        (numerator K S.F (w+1)) :=
      (globalTailCut_dvd_iff (polynomialEmbedding K)
        (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hidentityGate := BoundaryTailGates6808.identity_gate flag t y r hSafe hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider
      (a := cellA t y) (b := cellB y r) (s := cellS r) S 181245 hnodes hagreement
      (by norm_num [RCN327.w]) hTailNumerator D t r
      (by norm_num [RCN327.w]) hshort hDchar hbox hflagChar hidentityGate
    have hpositive : 1 ≤ ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r)
        (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hy : 0 < S.G.degreeOf 1 := S.y_dependent
      have hdeg := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181245
      (ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w)
      hprovider hagreement (by norm_num [RCN327.w])
      (by rw [hnodes]; norm_num [RCN327.w]) hpositive
    have habsorb := MovingFiberIdentityArithmetic6815.generic_absorption flag
      (cellA t y) (cellB y r) (cellS r) (Nat.zero_le _) hb1 hs1
    have hscaled : Gamma.card * 50174 ≤ 50174 * bound flag t y r := by
      calc
        Gamma.card * 50174 = Gamma.card * (181245-w) := by norm_num [RCN327.w]
        _ ≤ (S.nodes.card-w) * (80899+1) *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := hinc
        _ = 131073 * 80900 *
            ProximityPrize.SubmissionLower.RCN146.identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) 131071 := by
          rw [hnodes]
          norm_num [RCN327.w]
        _ ≤ 50174 * BoundaryTailIdentityArithmetic.newCost flag
            (cellA t y) (cellB y r) (cellS r) := habsorb
        _ = 50174 * bound flag t y r := by rw [bound_eq_abs flag t y r hr3 hb]
    apply Nat.le_of_mul_le_mul_right ?_ (by decide : 0 < 50174)
    simpa only [Nat.mul_comm] using hscaled
  · have hmixedRed := BoundaryTailGates6808.reduced_gate flag t y r hSafe hflag.1 hflag.2.1
    have hmix : 2 * (flag.zOnly+flag.yz+flag.all) *
        (cellA t y+cellB y r+cellS r+4) < 2130706433 := by
      have hf : flag.zOnly+flag.yz+flag.all ≤ 8121 := hflag.2.2.trans hTcap
      have ht : cellA t y+cellB y r+cellS r+4 ≤ 8122 := by
        dsimp [cellA, cellB, cellS]
        omega
      exact (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf) ht).trans_lt (by decide)
    have hrationalGate : 80899+1 ≤ (BoundaryTailProvider.cellNormal t y r).yz := by
      have hv : 2 ≤ y-r := by omega
      simp only [BoundaryTailProvider.cellNormal, BoundaryTailAlgebra.normalFlag, RCN327.w]
      omega
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G
          (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
            (80899+1) *
              (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail
        (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixedRed C)
        181245 D t r hnodes hagreement
        (by norm_num [RCN327.w]) (by norm_num [RCN327.w]) hshort hDchar hbox
        (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixedRed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixedRed C)
        hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixedRed C)
    obtain ⟨provider⟩ := BoundaryTailRealization.exists_provider hr3 hb hyt
      (by norm_num [RCN327.w]) S hTail hflagChar hmixedRed hmix hrationalGate htangent
    exact stage_card_le_divisorBound S provider

end
end ProximityPrize.SubmissionLower.MovingFiberOrdinaryHigh6815
end MergedPart11
