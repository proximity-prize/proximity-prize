/-
LOCATOR HYBRID TAIL PROVIDER — C2 (first-tail flag left free).

C1's provider proof never touches the sharp flag except through the type of its
budget family, so this file re-states it with the first-tail flag `tail1` as a
parameter.  Instantiating `tail1 := cellSharpTail t y r` recovers C1 exactly;
instantiating `tail1 := cellFirstTail t y r` (the REDUCED agreement flag, which
is strictly `Below` the sharp one) is the C2 tightening, worth about 1.29% on
the binding cells.

The C2 instantiation needs the reduced geometry transported to the components of
`globalTailCut (w+1)`; `LocatorHybridTransportC2` supplies the missing piece
(the unit-family transport and the moving budgets at a free first-tail flag),
while `RCN332` already supplies `reducedBudgetFamily`, `reducedBaseOrd` and
`transportedWeightedResultantsGeneral`.
-/
import ProximityPrize.SubmissionLower.LocatorHybridTransportC2
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

theorem exists_hybridTailMultiplicityProviderGen_of_localDVR
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
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
    (hmovingSum : (∑ C : FirstTailComponent S, (budget C).movingCost) ≤
      flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))
    (hgate : stageErrorCap + 1 ≤ (cellHybridCoordinateC1 t y r).yz)
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
      (tailFlag2 := cellHybridCoordinateC1 t y r) S
      (flagMixed flag tail1 (cellHybridCoordinateC1 t y r) +
        (w + 5) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
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
  -- the piecewise cost: flag route at multiplicity ≥ 6, moving route below
  let cost : FirstTailComponent S → ℕ := fun C =>
    if 6 ≤ multiplicity C then
      multiplicity C * B.weightedCost (cellHybridCoordinateC1 t y r) C
    else
      B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C +
        (w + multiplicity C) * (budget C).movingCost
  have hlow : ∀ C : FirstTailComponent S,
      B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C ≤
        multiplicity C * B.weightedCost (cellHybridCoordinateC1 t y r) C := by
    intro C
    have hle := cellRationalAt_le_smul t y r (multiplicity C) (hone C)
    have h := weightedCost_mono B C hle.1 hle.2.1 hle.2.2
    rwa [hscale] at h
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellHybridCoordinateC1 t y r) C +
        (w + 5) * (budget C).movingCost := by
    intro C
    by_cases hm : 6 ≤ multiplicity C
    · simp only [cost, if_pos hm]
      exact Nat.le_add_right _ _
    · simp only [cost, if_neg hm]
      have h2 : (w + multiplicity C) * (budget C).movingCost ≤
          (w + 5) * (budget C).movingCost :=
        Nat.mul_le_mul_right _ (by omega)
      have := hlow C
      omega
  have hbound : ∀ C,
      (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      cost C := by
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
              (globalTailCut (polynomialEmbedding K) S.F
                (w + 1 + delay)) = 0 := by
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
            (globalTailCut (polynomialEmbedding K) S.F
              (w + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F
            (w + 1 + delay),
            laterTail_in_hybridFlagC1 t y r hr3 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simp
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        simp only [cost, if_pos hm]
        rw [hscale] at hcount
        exact hcount
      · -- the dichotomy hands back `delay ≤ localMultiplicity …`; restate it
        -- against the local `multiplicity` so the atoms line up
        have hdm' : delay ≤ multiplicity C := hdelayMu
        have hcount := component_moving_card_le_delay t y r hr2 hry hyt
          S C (budget C) (base C) delay hdelay htail
        simp only [hwcEq] at hcount
        have hfold : B.weightedCost
              (center (cellA t y) (cellB y r) (cellS r)) C +
            (w + delay) *
              (B.weightedCost
                (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) C +
                (budget C).movingCost) =
            B.weightedCost (cellRationalAt t y r (w + delay)) C +
              (w + delay) * (budget C).movingCost := by
          simp only [cellRationalAt, PrimeFlagBudgetFamily.weightedCost,
            add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
          ring
        rw [hfold] at hcount
        have hmono := cellRationalAt_mono t y r (w + delay)
          (w + multiplicity C) (by omega)
        have h1 := weightedCost_mono B C hmono.1 hmono.2.1 hmono.2.2
        have h2 : (w + delay) * (budget C).movingCost ≤
            (w + multiplicity C) * (budget C).movingCost :=
          Nat.mul_le_mul_right _ (by omega)
        simp only [cost, if_neg hm]
        exact hcount.trans (Nat.add_le_add h1 h2)
    · have hcount := htangent C htangentBranch
      by_cases hm : 6 ≤ multiplicity C
      · simp only [cost, if_pos hm]
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellHybridCoordinateC1 t y r) C :=
            yzCost_mul_le_weightedCost B (cellHybridCoordinateC1 t y r) C
              (stageErrorCap + 1) hgate
          _ = 1 * B.weightedCost (cellHybridCoordinateC1 t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinateC1 t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      · simp only [cost, if_neg hm]
        have hmono := cellRationalAt_mono t y r (w + 1)
          (w + multiplicity C) (by have := hone C; omega)
        have h1 := weightedCost_mono B C hmono.1 hmono.2.1 hmono.2.2
        rw [cellRationalAt_succ_w] at h1
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellHybridCoordinateC1 t y r) C :=
            yzCost_mul_le_weightedCost B (cellHybridCoordinateC1 t y r) C
              (stageErrorCap + 1) hgate
          _ ≤ B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C :=
            h1
          _ ≤ B.weightedCost (cellRationalAt t y r (w + multiplicity C)) C +
              (w + multiplicity C) * (budget C).movingCost :=
            Nat.le_add_right _ _
  have hsum : (∑ C, cost C) ≤
      flagMixed flag tail1 (cellHybridCoordinateC1 t y r) +
        (w + 5) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    calc (∑ C, cost C) ≤
        ∑ C, (multiplicity C *
            B.weightedCost (cellHybridCoordinateC1 t y r) C +
          (w + 5) * (budget C).movingCost) :=
        Finset.sum_le_sum (fun C _ => hcost_pointwise C)
      _ = (∑ C, multiplicity C *
            B.weightedCost (cellHybridCoordinateC1 t y r) C) +
          (w + 5) * (∑ C, (budget C).movingCost) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ flagMixed flag tail1
            (cellHybridCoordinateC1 t y r) +
          (w + 5) *
            flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) :=
        Nat.add_le_add
          (hresultants.divisor_le B multiplicity)
          (Nat.mul_le_mul_left _ hmovingSum)
  have providerDichotomy := loosenStageGeneral_dichotomy_with_tangent S
    hfirstProper B htangent
  exact ⟨{
    budgetFamily := B
    multiplicity := multiplicity
    cost := cost
    one_le_multiplicity := hone
    tangentYZGate := hgate
    cost_sum_le := hsum
    componentBound := hbound
    dichotomy := providerDichotomy }⟩


end
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC2
