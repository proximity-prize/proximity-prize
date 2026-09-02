/-
LOCATOR HYBRID TAIL PROVIDER — C1 VARIANT.

Same architecture as `LocatorHybridTailProvider`, with the C1 trade:

  * the FLAG route (charge `mult · weightedCost hybrid`) is restricted to
    components of local multiplicity at least 6, which lets the coordinate drop
    from `cellRational + ⟨0,(w+1)/2,3·((w+1)/2)⟩` all the way to `cellRational`;
  * components of multiplicity 1..5 go through the MOVING engine at cut level
    `w + mult` (the dichotomy's `delay` satisfies `delay ≤ mult`), charging
    `weightedCost (cellRationalAt (w + mult)) + (w + mult) · movingCost`;
  * the moving term's outer factor therefore becomes `w + 5` instead of `w + 1`.

The structure `HybridTailMultiplicityProvider` and `stage_card_le_divisorBound`
are reused unchanged from `LocatorHybridTailProvider`.
-/
import ProximityPrize.SubmissionLower.LocatorHybridTailProvider
import ProximityPrize.SubmissionLower.LocatorHybridCellsC1
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
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

/-! ### 0. Arithmetic helpers -/

/-- `sharp_absorbs_total_C1` in the `(a, b + s)` shape used by the containment proof. -/
theorem sharp_absorbs_total_abs (a B delay mult : ℕ) (hA : 1 ≤ a + B)
    (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    1 + (2 * a + 2 * B + 4) * (131072 + delay) ≤
      mult * (131074 * a + 131072 * B + 2 * B + 5) := by
  have h := sharp_absorbs_total_C1 (a + B) delay mult hA hdm hm6
  have e1 : 2 * (a + B) + 4 = 2 * a + 2 * B + 4 := by ring
  have e2 : 131072 * (a + B) + 2 * (a + B) + 5 =
      131074 * a + 131072 * B + 2 * B + 5 := by ring
  rw [e1, e2] at h
  exact h

/-- The rational coordinate grows componentwise with the cut level. -/
theorem cellRationalAt_mono (t y r k l : Nat) (h : k ≤ l) :
    (cellRationalAt t y r k).zOnly ≤ (cellRationalAt t y r l).zOnly ∧
      (cellRationalAt t y r k).yz ≤ (cellRationalAt t y r l).yz ∧
      (cellRationalAt t y r k).all ≤ (cellRationalAt t y r l).all := by
  simp only [cellRationalAt_eq]
  exact ⟨by exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _,
    by exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _,
    by exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _⟩

/-! ### 1. L1 (C1) — the delayed cut lands in `mult • cellRational` for `mult ≥ 6` -/

theorem laterTail_in_hybridFlagC1
    (t y r : Nat) (hr3 : 3 ≤ r) (_hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult : ℕ) (_hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm6 : 6 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinateC1 t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  have hs1 : 1 ≤ cellS r := by simp only [cellS]; omega
  have hB1 : 1 ≤ cellB y r + cellS r := by omega
  have hA1 : 1 ≤ cellA t y + (cellB y r + cellS r) := by omega
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (w + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  have hallV : (sharpResidualAgreementFlag (cellSupport t y r)
      (w + 1 + delay)).all = (2 * cellS r + 3) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
  have hysV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * (cellB y r + cellS r) + 4) * (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have htotV : (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).zOnly +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).yz +
      (sharpResidualAgreementFlag (cellSupport t y r)
        (w + 1 + delay)).all =
      1 + (2 * cellA t y + 2 * (cellB y r + cellS r) + 4) *
        (131072 + delay) := by
    have e1 : ∀ m : ℕ, 2 * (m + 2) - 1 = 2 * m + 3 := fun m => by omega
    have e2 : ∀ m2 m3 : ℕ,
        2 * (m2 + m3 + 3 - (m3 + 2)) - 1 = 2 * m2 + 1 := fun m2 m3 => by omega
    have e3 : ∀ m1 m2 m3 : ℕ,
        m1 + m2 + m3 + 3 - (m2 + m3 + 3) = m1 := fun m1 m2 m3 => by omega
    simp only [sharpResidualAgreementFlag, sharpAgreementDirection,
      cellSupport, RCN198.support, w, e3, e2, e1]
    all_goals ring
  have hhallV : (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3)) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_all, w]
  have hhysV : (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_yz, nsmul_all, w]
    ring
  have hhtotV : (mult • cellHybridCoordinateC1 t y r).zOnly +
      (mult • cellHybridCoordinateC1 t y r).yz +
      (mult • cellHybridCoordinateC1 t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5) := by
    simp only [cellHybridCoordinateC1, cellRational, cellDirection,
      RCN206.directionFlag, nsmul_zOnly, nsmul_yz, nsmul_all, w]
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      sharp_absorbs_all_C1 (cellS r) delay mult hs1 hdm hm6)
  · exact (hysV ▸ hys).trans (hhysV ▸
      sharp_absorbs_ysall_C1 (cellB y r + cellS r) delay mult hB1 hdm hm6)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      sharp_absorbs_total_abs (cellA t y) (cellB y r + cellS r) delay mult
        hA1 hdm hm6)

/-! ### 2. L2 (C1) — the moving count at an arbitrary delay -/

set_option maxHeartbeats 20000000 in
theorem component_moving_card_le_delay
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y) (_hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (delay : ℕ) (hd : 1 ≤ delay)
    (hproper : globalTailCut (polynomialEmbedding K) S.F
      (w + 1 + delay) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + delay) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) := by
  classical
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hR : S.F.degreeOf 2 ≤ cellS r + 2 := by
    have h := Hsupport.coordinate_bounds.2.1
    simpa only [cellSupport, cellS, RCN198.support] using h
  have hYR : wt ![0, 1, 1, 0] S.F ≤ cellB y r + cellS r + 3 := by
    have h := Hsupport.ys_weight
    simpa only [residualYSWeights, cellSupport, cellB, cellS, RCN198.support] using h
  have hAll : wt ![0, 1, 1, 1] S.F ≤ cellA t y + cellB y r + cellS r + 3 := by
    have h := Hsupport.total_weight
    simpa only [residualTotalWeights, cellSupport, cellA, cellB, cellS,
      RCN198.support] using h
  obtain ⟨Bc, cf, heq, hcoeff, hclass⟩ :=
    globalTailCut_certificate (polynomialEmbedding K)
      (cellA t y) (cellB y r) (cellS r) S.F hR hYR hAll
      (w + delay) (by omega)
  rw [show w + delay + 1 = w + 1 + delay from by omega] at heq
  have hHrw : surfaceMap (polynomialEmbedding K) (polyH K S.F) =
      regularitySurface (polynomialEmbedding K) S.F := rfl
  rw [hHrw] at heq
  have hA : filteredCut
      (w + delay) Bc
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)) ∉ C.1 :=
    heq ▸ hproper
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (filteredCut (w + delay) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
      (budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + delay) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost)) :=
    budget.zero_le base (cellA t y) (cellB y r) (cellS r) (w + delay)
      (center (cellA t y) (cellB y r) (cellS r)) Bc cf hHnot hA hcoeff hclass
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
      (filteredCut (w + delay) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F))) = 0 := by
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
    exact heq ▸ hz
  have hbound : pts.card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + delay) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega

/-! ### 3. The C1 provider from a local DVR family -/

theorem exists_hybridTailMultiplicityProviderC1_of_localDVR
    (t y r : Nat) (hr3 : 3 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
      (w + 1))
    (B : PrimeFlagBudgetFamily
      (G := S.G) (T := globalTailCut (polynomialEmbedding K) S.F
        (w + 1))
      (H := regularitySurface (polynomialEmbedding K) S.F) flag
      (cellSharpTail t y r))
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
      (tailFlag1 := cellSharpTail t y r)
      (tailFlag2 := cellHybridCoordinateC1 t y r) S
      (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinateC1 t y r) +
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
      flagMixed flag (cellSharpTail t y r) (cellHybridCoordinateC1 t y r) +
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
      _ ≤ flagMixed flag (cellSharpTail t y r)
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
end ProximityPrize.SubmissionLower.LocatorHybridTailProviderC1
