import ProximityPrize.SubmissionLower.LocatorHybridCellsC1

/-! Packed from ProximityPrize.SubmissionLower.LocatorHybridTailProvider. -/
section PackedLocator_LocatorHybridTailProvider
/-
LOCATOR HYBRID TAIL PROVIDER (port of ContactHybridTailProvider6751Research, pr359).

Covers the `r + 2 ≤ y` ("hybrid second-surface") branch of `cellRegularCost`.
The delayed branch keeps the Locator's reduced-tail discharge (Q2.lean) verbatim.

§0 defines the *bounded* provider `HybridTailMultiplicityProvider`: it is
pr359's refactored `DelayedTailMultiplicityProvider` (an extra
`divisorBound` optParam and a single field `cost_sum_le : ∑ cost ≤ divisorBound`
in place of `cost_le`/`divisor_le`), kept as a NEW structure so that the
existing B3.lean structure and its constructors (Q2.lean, GZ.lean) stay
untouched.  `stage_card_le_divisorBound` is the generalized
`stage_card_le_flagMixed`.

Conclusion shape of §3:

  Nonempty (HybridTailMultiplicityProvider
    (tailFlag1 := cellSharpTail t y r) (tailFlag2 := cellHybridCoordinate t y r) S
    (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r)
      + (w + 1) * flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r)))

Caller-side obligations (discharged in LocatorHybridTailRealization.lean):
  B            : sharp unit family (activeNestedUnitFamily on T1 in the sharp
                 flag DIRECTLY — no congruent-cut transport)
  budget/hcost/hmovingSum : outputs of exists_firstTail_cut_budgets
  hresultants  : sharp-family certificate (activeNestedWeightedCertificate on T1)
  htangent     : the tangent count vs B.yzCost
  htangentGate / hrationalGate : numeric gates errors+1 ≤ hybrid.yz / rational.yz
                 (rational.yz = 131074·b + 2 ≥ 131076 whenever b ≥ 1, i.e. r+2 ≤ y).
-/
namespace ProximityPrize.SubmissionLower.LocatorHybridTailProvider
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-! ### 0. The bounded provider (pr359's refactored DelayedTailMultiplicityProvider) -/

section BoundedProvider
variable {K0 Omega Iota : Type} [Field K0] [Field Omega] [IsAlgClosed Omega]
  {phi : Polynomial K0 →+* Omega} {Gamma0 : Finset K0} {x0 : Iota → K0}
  {pchar errorCap d : ℕ} [CharP Omega pchar]
  {flag0 tailFlag1 tailFlag2 : FlagDegree}
  {support0 : RCN275.ResidualSupportParameters}

structure HybridTailMultiplicityProvider
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    (divisorBound : optParam ℕ (flagMixed flag0 tailFlag1 tailFlag2)) where
  budgetFamily : PrimeFlagBudgetFamily
    (G := S.G) (T := globalTailCut phi S.F (d + 1))
    (H := regularitySurface phi S.F) flag0 tailFlag1
  multiplicity : FirstTailComponent S → ℕ
  cost : FirstTailComponent S → ℕ
  one_le_multiplicity : ∀ C, 1 ≤ multiplicity C
  tangentYZGate : errorCap + 1 ≤ tailFlag2.yz
  cost_sum_le : (∑ C, cost C) ≤ divisorBound
  componentBound : ∀ C,
    (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
      (regularitySurface phi S.F) Gamma0
      (selectedPoint phi S.selected) C).card ≤ cost C
  dichotomy : ∀ C,
    (∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
      globalTailCut phi S.F (d + 1 + delay) ∉ C.1) ∨
    ((∀ delay, globalTailCut phi S.F (d + 1 + delay) ∈ C.1) ∧
      (componentSeeds Omega S.G (globalTailCut phi S.F (d + 1))
        (regularitySurface phi S.F) Gamma0
        (selectedPoint phi S.selected) C).card ≤
          (errorCap + 1) * budgetFamily.yzCost C)

/-- The generalized `stage_card_le_flagMixed`: any bounded provider bounds the
seed count by its `divisorBound`. -/
theorem stage_card_le_divisorBound
    (S : ResidualStage phi Gamma0 x0 pchar errorCap flag0 d support0)
    {divisorBound : ℕ}
    (P : HybridTailMultiplicityProvider
      (tailFlag1 := tailFlag1) (tailFlag2 := tailFlag2) S divisorBound) :
    Gamma0.card ≤ divisorBound := by
  classical
  let T1 := globalTailCut phi S.F (d + 1)
  let H := regularitySurface phi S.F
  let point := selectedPoint phi S.selected
  have hG : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) S.G = 0 := S.on_component
  have hT1 : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) T1 = 0 := by
    intro gamma hgamma
    exact selected_globalTailCut_zero phi S.F S.selected gamma d
      (S.degree_le gamma hgamma) (S.solution gamma hgamma)
  have hH : ∀ gamma ∈ Gamma0,
      MvPolynomial.eval (point gamma) H ≠ 0 := by
    intro gamma hgamma
    exact selectedPoint_evaluation phi S.selected gamma
      (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
  have hcover : Gamma0.card ≤
      ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card :=
    card_le_sum_componentSeeds Omega S.G T1 H Gamma0 point hG hT1 hH
  calc
    Gamma0.card ≤ ∑ C : RegularComponent Omega S.G T1 H,
        (componentSeeds Omega S.G T1 H Gamma0 point C).card := hcover
    _ ≤ ∑ C : RegularComponent Omega S.G T1 H, P.cost C :=
      Finset.sum_le_sum (fun C _ ↦ P.componentBound C)
    _ ≤ divisorBound := P.cost_sum_le

end BoundedProvider

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}

/-! ### 1. L1 — the delayed cut lands in mult • hybrid (mult ≥ 2)

Direct containment (no mod-G reduction): the (w+1+delay)-th tail cut lies in the
sharp flag at degree w+1+delay, and the three cumulative absorptions of
LocatorHybridCells push that into `mult • cellHybridCoordinate` whenever
1 ≤ delay ≤ mult and 2 ≤ mult. -/

theorem laterTail_in_hybridFlag
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (delay mult : ℕ) (hd : 1 ≤ delay) (hdm : delay ≤ mult) (hm2 : 2 ≤ mult) :
    PolynomialInFlag (mult • cellHybridCoordinate t y r)
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
  have hsy : (cellSupport t y r).s < (cellSupport t y r).ys := by
    simp only [cellSupport, cellA, cellB, cellS, RCN198.support]
    omega
  -- globalTailCut is definitionally surfaceMap of the agreement numerator with
  -- the tail selector, so the sharp containment applies directly.
  have hsharp : PolynomialInFlag
      (sharpResidualAgreementFlag (cellSupport t y r) (w + 1 + delay))
      (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) := by
    exact surfaceMap_agreement_in_sharp_flag hsy (polynomialEmbedding K)
      ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
      (w + 1 + delay) (tailSelector (w + 1 + delay)) 0 0 0
  intro exponent hexp
  have h := hsharp exponent hexp
  obtain ⟨hall, hys, htot⟩ := h
  -- rewrite the sharp cumulative sums into the subtraction-free atom form
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
  -- hybrid cumulative sums in atom form
  have hhallV : (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * cellS r + (2 * cellS r + 3) + 196608) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_all, nsmul_all, w]
  have hhysV : (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_yz, add_all, nsmul_yz, nsmul_all, w]
    norm_num
    ring
  have hhtotV : (mult • cellHybridCoordinate t y r).zOnly +
      (mult • cellHybridCoordinate t y r).yz +
      (mult • cellHybridCoordinate t y r).all =
      mult * (131074 * cellA t y + 131072 * (cellB y r + cellS r) +
        2 * (cellB y r + cellS r) + 5 + 262144) := by
    simp only [cellHybridCoordinate, cellRational, cellDirection,
      RCN206.directionFlag, add_zOnly, add_yz, add_all, nsmul_zOnly,
      nsmul_yz, nsmul_all, w]
    norm_num
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact (hallV ▸ hall).trans (hhallV ▸
      sharp_absorbs_all (cellA t y) (cellB y r) (cellS r) delay mult hdm hm2)
  · exact (hysV ▸ hys).trans (hhysV ▸
      sharp_absorbs_ysall (cellA t y) (cellB y r) (cellS r) delay mult
        hd hdm hm2)
  · exact (htotV ▸ htot).trans (hhtotV ▸
      sharp_absorbs_total (cellA t y) (cellB y r) (cellS r) delay mult
        hd hdm hm2)

/-! ### 2. L2 — the multiplicity-1 moving count

For a component whose (w+2)-cut is proper, the seeds are bounded by
wc(rational) + (w+1)·movingCost, via the filteredCut decomposition of the (w+2)
cut and the MovingPoleBudget zero bound at C := center, k := w+1. -/

set_option maxHeartbeats 20000000 in
theorem component_hybrid_moving_card_le
    (t y r : Nat) (_hr2 : 2 ≤ r) (_hry : r < y) (_hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (cellSupport t y r))
    (C : FirstTailComponent S)
    (budget : MovingPoleBudget C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
    (base : SeparableLiteralCoordinate C.1)
    (hproper : globalTailCut (polynomialEmbedding K) S.F
      (w + 1 + 1) ∉ C.1) :
    (componentSeeds (GenericField K) S.G
        (globalTailCut (polynomialEmbedding K) S.F (w + 1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
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
      (w + 1) (Nat.le_add_left 1 w)
  have hHrw : surfaceMap (polynomialEmbedding K) (polyH K S.F) =
      regularitySurface (polynomialEmbedding K) S.F := rfl
  rw [hHrw] at heq
  have hA : filteredCut
      (w + 1) Bc
      (regularitySurface (polynomialEmbedding K) S.F)
      (surfaceMap (polynomialEmbedding K) (polyG K S.F)) ∉ C.1 :=
    heq ▸ hproper
  have hHnot : regularitySurface (polynomialEmbedding K) S.F ∉ C.1 :=
    regularComponent_H_not_mem (GenericField K) S.G _ _ C
  have hzero : FiniteRegularZeroSetBound C.1
      (regularitySurface (polynomialEmbedding K) S.F)
      (filteredCut (w + 1) Bc
        (regularitySurface (polynomialEmbedding K) S.F)
        (surfaceMap (polynomialEmbedding K) (polyG K S.F)))
      (budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost)) :=
    budget.zero_le base (cellA t y) (cellB y r) (cellS r) (w + 1)
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
      (filteredCut (w + 1) Bc
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
          (w + 1 + 1)) = 0 :=
      selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F
        S.selected gamma w (w + 1 + 1)
        (S.degree_le gamma hGamma) (S.solution gamma hGamma) (by omega)
    exact heq ▸ hz
  have hbound : pts.card ≤
      budget.weightedCost (center (cellA t y) (cellB y r) (cellS r)) +
        (w + 1) *
          (budget.weightedCost
              (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) +
            budget.movingCost) :=
    hzero pts hprime hHne hAzero
  have hcard : pts.card = seeds.card :=
    Finset.card_image_of_injective seeds
      (selectedPoint_injective (polynomialEmbedding K) S.selected)
  show seeds.card ≤ _
  omega

/-! ### 3. The hybrid provider from a local DVR family -/

theorem exists_hybridTailMultiplicityProvider_of_localDVR
    (t y r : Nat) (hr2 : 2 ≤ r) (hb : r + 2 ≤ y) (hyt : y ≤ t)
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
    (htangentGate : stageErrorCap + 1 ≤ (cellHybridCoordinate t y r).yz)
    (hrationalGate : stageErrorCap + 1 ≤ (cellRational t y r).yz)
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
      (tailFlag2 := cellHybridCoordinate t y r) S
      (flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r))) := by
  classical
  have hry : r < y := by omega
  let S0 := loosenStageGeneral S
  let multiplicity : FirstTailComponent S → ℕ := fun C =>
    localMultiplicity S0 (canonicalLocalDVRFamily S0 hfirstProper) C
  have hone : ∀ C, 1 ≤ multiplicity C :=
    loosenStageGeneral_one_le_localMultiplicity S hfirstProper
  -- weightedCost over budget = weightedCost over B (cost equalities)
  have hwcEq : ∀ (C : FirstTailComponent S) (f : FlagDegree),
      (budget C).weightedCost f = B.weightedCost f C := by
    intro C f
    obtain ⟨hz, hy', ha⟩ := hcost C
    simp only [MovingPoleBudget.weightedCost,
      PrimeFlagBudgetFamily.weightedCost, hz, hy', ha]
  -- the piecewise cost
  let cost : FirstTailComponent S → ℕ := fun C =>
    if 2 ≤ multiplicity C then
      multiplicity C * B.weightedCost (cellHybridCoordinate t y r) C
    else
      B.weightedCost (cellRational t y r) C +
        (w + 1) * (budget C).movingCost
  -- pointwise: cost C ≤ mult C * wc(hybrid) + (w+1) * movingCost C
  have hcost_pointwise : ∀ C, cost C ≤
      multiplicity C * B.weightedCost (cellHybridCoordinate t y r) C +
        (w + 1) * (budget C).movingCost := by
    intro C
    by_cases hm : 2 ≤ multiplicity C
    · simp only [cost, if_pos hm]
      exact Nat.le_add_right _ _
    · simp only [cost, if_neg hm]
      have hmono := weightedCost_mono B C
        (cellRational_le_hybrid t y r).1
        (cellRational_le_hybrid t y r).2.1
        (cellRational_le_hybrid t y r).2.2
      have h1 : B.weightedCost (cellRational t y r) C ≤
          multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C := by
        calc B.weightedCost (cellRational t y r) C ≤
            B.weightedCost (cellHybridCoordinate t y r) C := hmono
          _ = 1 * B.weightedCost (cellHybridCoordinate t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      omega
  -- the component bound
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
      by_cases hm : 2 ≤ multiplicity C
      · -- mult ≥ 2: cut with the delayed cut inside mult • hybrid
        have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G
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
            (multiplicity C • cellHybridCoordinate t y r)
            (globalTailCut (polynomialEmbedding K) S.F
              (w + 1 + delay)) := by
          refine ⟨globalTailCut (polynomialEmbedding K) S.F
            (w + 1 + delay),
            laterTail_in_hybridFlag t y r hr2 hry S delay
              (multiplicity C) hdelay hdelayMu hm, ?_⟩
          simp
        have hcount := component_secondTail_card_le_mod (Seed := K) B C Gamma
          (selectedPoint (polynomialEmbedding K) S.selected)
          (selectedPoint_injective (polynomialEmbedding K) S.selected)
          hflagMod htail hzero
        have hscale : B.weightedCost
            (multiplicity C • cellHybridCoordinate t y r) C =
            multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C := by
          simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly,
            nsmul_yz, nsmul_all]
          ring
        simp only [cost, if_pos hm]
        rw [hscale] at hcount
        exact hcount
      · -- mult = 1: delay must be 1; use the moving engine
        have hm1 : multiplicity C = 1 := by
          have := hone C
          omega
        have hdelay1 : delay = 1 := by
          have h2 : delay ≤ 1 := by rw [← hm1]; exact hdelayMu
          omega
        subst hdelay1
        have hcount := component_hybrid_moving_card_le t y r hr2 hry hyt
          S C (budget C) (base C) htail
        simp only [cost, if_neg hm]
        simp only [hwcEq] at hcount
        -- fold wc(center) + (w+1)·wc(⟨a,b,s⟩) into wc(rational)
        have hfold : B.weightedCost
              (center (cellA t y) (cellB y r) (cellS r)) C +
            (w + 1) *
              (B.weightedCost
                (⟨cellA t y, cellB y r, cellS r⟩ : FlagDegree) C +
                (budget C).movingCost) =
            B.weightedCost (cellRational t y r) C +
              (w + 1) * (budget C).movingCost := by
          have hid := center_add_smul_eq_cellRational t y r
          simp only [← hid, PrimeFlagBudgetFamily.weightedCost, add_zOnly,
            add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
          ring
        omega
    · -- tangent branch
      have hcount := htangent C htangentBranch
      by_cases hm : 2 ≤ multiplicity C
      · simp only [cost, if_pos hm]
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellHybridCoordinate t y r) C :=
            yzCost_mul_le_weightedCost B (cellHybridCoordinate t y r) C
              (stageErrorCap + 1) htangentGate
          _ = 1 * B.weightedCost (cellHybridCoordinate t y r) C := by ring
          _ ≤ multiplicity C *
              B.weightedCost (cellHybridCoordinate t y r) C :=
            Nat.mul_le_mul_right _ (hone C)
      · simp only [cost, if_neg hm]
        calc _ ≤ (stageErrorCap + 1) * B.yzCost C := hcount
          _ ≤ B.weightedCost (cellRational t y r) C :=
            yzCost_mul_le_weightedCost B (cellRational t y r) C
              (stageErrorCap + 1) hrationalGate
          _ ≤ B.weightedCost (cellRational t y r) C +
              (w + 1) * (budget C).movingCost := Nat.le_add_right _ _
  -- the sum bound: certificate + moving sum
  have hsum : (∑ C, cost C) ≤
      flagMixed flag (cellSharpTail t y r) (cellHybridCoordinate t y r) +
        (w + 1) *
          flagMixed flag (cellMovingFiber t y r) (cellMovingCut t y r) := by
    calc (∑ C, cost C) ≤
        ∑ C, (multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C +
          (w + 1) * (budget C).movingCost) :=
        Finset.sum_le_sum (fun C _ => hcost_pointwise C)
      _ = (∑ C, multiplicity C *
            B.weightedCost (cellHybridCoordinate t y r) C) +
          (w + 1) * (∑ C, (budget C).movingCost) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ flagMixed flag (cellSharpTail t y r)
            (cellHybridCoordinate t y r) +
          (w + 1) *
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
    tangentYZGate := htangentGate
    cost_sum_le := hsum
    componentBound := hbound
    dichotomy := providerDichotomy }⟩

end
end ProximityPrize.SubmissionLower.LocatorHybridTailProvider
end PackedLocator_LocatorHybridTailProvider

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier50 : True := by trivial
end ProximityPrize.SubmissionLower


namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier51 : True := by trivial
end ProximityPrize.SubmissionLower

