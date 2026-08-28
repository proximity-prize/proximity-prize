import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily6600Research
import ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
import ProximityPrize.SubmissionLower.ContactFlagTrapezoidCaps6543Research
import ProximityPrize.SubmissionLower.ContactParameters6600Research

/-!
# Terminal adaptive projection families from the score-66 flag caps

This is the last local geometry adapter for the score-66 route.  A terminal
outer residual stage already carries the surface flag and its proper
agreement cut has the canonical residual flag.  The rectangular factor caps
put the literal `Y` and `Z` projection resultants below the fixed
characteristic.  Those two gates select a finite-separable literal base on
every regular curve component, after which the common adaptive nested-family
constructor applies directly.
-/

namespace ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research

open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum
open ContactParameters6600Research
open ContactPrimeSeedIncidence
open ContactGenericSurface
open ContactProperCutSeedCount
open ContactRegularComponentCover
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualIncidenceResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedUnitFamily6600Research
open ContactAdaptiveProjectionFactorProvider6600Research
open ContactWeakSeparableSeparatorResearch
open ContactResidualStageDerivative6600Research
open ContactFlagTrapezoidCaps6543Research
open TrivariateRationalCollection
open ActualPlaneCoordinateKernel ActualPlaneCoordinateCaps ActualPlanePositiveOrder

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Coordinatewise rectangular consequences of nested flag support. -/
theorem degree_bounds_of_polynomialInFlag
    {p : FlagDegree} {F : MvPolynomial (Fin 3) Omega}
    (hF : PolynomialInFlag p F) :
    F.degreeOf 0 ≤ p.yz + p.all ∧
      F.degreeOf 1 ≤ p.all ∧
      F.degreeOf 2 ≤ p.zOnly + p.yz + p.all := by
  refine ⟨?_, ?_, ?_⟩
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (hF e he).1
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    exact (Nat.le_add_left (e 2) (e 0 + e 1)).trans (by
      simpa only [Nat.add_assoc] using (hF e he).2.2)

/-- The robust rectangular surface caps are already enough to construct the
entire adaptive family at every proper terminal agreement cut. -/
theorem terminalAdaptiveProjectionFamilies_of_rectangular_caps
    [CharP Omega prime]
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x prime errors flag w)
    (hflagZ : flag.zOnly ≤ 528)
    (hflagY : flag.yz ≤ 40)
    (hflagS : flag.all ≤ 8) :
    TerminalAdaptiveProjectionFamilies S := by
  classical
  intro D i hi hproper
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let H := regularitySurface phi D.stage.F
  have hGflag : PolynomialInFlag flag D.stage.G := D.stage.flag_support
  have hTflag : PolynomialInFlag (residualAgreementFlag D.degree) T := by
    exact surfaceMap_agreement_in_flag_of_surface_weights
      D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
      D.stage.surface_total_weight D.degree
      (fun j ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  have hsurfaceNe : surfaceMap phi D.stage.F ≠ 0 := by
    intro hzero
    have hderivzero :
        surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) D.stage.F) = 0 := by
      rw [← ContactRegularFactorGate.surfaceMap_pderiv_R, hzero]
      simp
    apply D.stage.regular_proper
    simpa only [hderivzero] using (dvd_zero D.stage.G)
  have hsurfaceTotal :
      (surfaceMap phi D.stage.F).totalDegree ≤ 528 := by
    unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
      (support_surfaceMap_subset phi D.stage.F he)
    have hdTotal :=
      (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans
        D.stage.surface_total_weight
    rw [ContactFactorCaps.weight_fin4] at hdTotal
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 528 at hdTotal
    norm_num at hdTotal
    simpa [Finsupp.sum_fintype, Fin.sum_univ_three, Finsupp.tail_apply] using
      (show d 1 + d 2 + d 3 ≤ 528 by omega)
  have hGtotal : D.stage.G.totalDegree ≤ 528 :=
    (MvPolynomial.totalDegree_le_of_dvd_of_isDomain
      D.stage.G_dvd_surface hsurfaceNe).trans hsurfaceTotal
  have hGtrapezoid : FlagTrapezoidCaps flag D.stage.G :=
    flagTrapezoidCaps_of_inFlag flag D.stage.G hGflag
  have hTtrapezoid : FlagTrapezoidCaps (residualAgreementFlag D.degree) T :=
    flagTrapezoidCaps_of_inFlag (residualAgreementFlag D.degree) T hTflag
  obtain ⟨hGY, hGS, hGZ⟩ := degree_bounds_of_polynomialInFlag hGflag
  obtain ⟨hTY, hTS, hTZ⟩ := degree_bounds_of_polynomialInFlag hTflag
  have hD : D.degree ≤ w := D.degree_le.trans (Nat.le_refl w)
  have hGY' : D.stage.G.degreeOf 0 ≤ 48 := by omega
  have hGS' : D.stage.G.degreeOf 1 ≤ 8 := by omega
  have hTY' : T.degreeOf 0 ≤ 1 + 79 * w := by
    dsimp only [residualAgreementFlag] at hTY
    omega
  have hTS' : T.degreeOf 1 ≤ 15 * w := by
    dsimp only [residualAgreementFlag] at hTS
    omega
  have hTZ' : T.degreeOf 2 ≤ 1 + 1055 * w := by
    dsimp only [residualAgreementFlag] at hTZ
    omega
  have hGdegree : ∀ j : Fin 3, D.stage.G.degreeOf j < prime := by
    intro j
    exact ((MvPolynomial.degreeOf_le_totalDegree D.stage.G j).trans hGtotal).trans_lt
      (by norm_num [prime])
  have hmixedZ :
      coordinateMixedDegree Omega D.stage.G T 2 < prime := by
    rw [coordinateMixedDegree_two]
    apply (Nat.add_le_add
      (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt
    norm_num [w, prime]
  let hY : ∀ C : RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 0 := by
    intro C htr
    let order : Fin 3 ≃ Fin 3 :=
      ContactFlagTriangularProjectionResearch.uOrder
    have hTne : T ≠ 0 := by
      intro hzero
      have hdiv : D.stage.G ∣ T := by
        rw [hzero]
        exact dvd_zero D.stage.G
      exact hproper (by simpa only [T] using hdiv)
    have hGouter : (planeMap Omega order D.stage.G).natDegree ≤ 8 := by
      simpa [order, ContactFlagTriangularProjectionResearch.uOrder] using
        hGtrapezoid.uOuter.trans hflagS
    have hTouter : (planeMap Omega order T).natDegree ≤ 15 * w := by
      simpa [order, ContactFlagTriangularProjectionResearch.uOrder] using
        hTtrapezoid.uOuter.trans (show (residualAgreementFlag D.degree).all ≤ 15 * w by
          dsimp only [residualAgreementFlag]
          omega)
    have hGsupport : ∀ d ∈ (rationalMap Omega order D.stage.G).support,
        d 0 + d 1 ≤ 528 := by
      apply ActualPlaneJointProjection.rationalMap_joint_support_of_original
        Omega order D.stage.G 528
      intro d hd
      change d 1 + d 2 ≤ 528
      have h := (MvPolynomial.le_totalDegree hd).trans hGtotal
      have hsum : d 0 + d 1 + d 2 ≤ 528 := by
        simpa [Finsupp.sum_fintype, Fin.sum_univ_three] using h
      omega
    have hTsupport : ∀ d ∈ (rationalMap Omega order T).support,
        d 0 + d 1 ≤ 1 + 1055 * w := by
      intro d hd
      have h := hTtrapezoid.uTotal d (by
        simpa only [order] using hd)
      dsimp only [residualAgreementFlag] at h
      omega
    have hGswapOuter :
        (planeMap Omega (swapOtherOrder order) D.stage.G).natDegree ≤ 528 := by
      exact (planeMap_natDegree_le Omega (swapOtherOrder order) D.stage.G).trans
        ((MvPolynomial.degreeOf_le_totalDegree D.stage.G _).trans hGtotal)
    have hTswapInner : Polynomial.Bivariate.degreeX
        (planeMap Omega (swapOtherOrder order) T) ≤ 15 * w := by
      apply (planeMap_degreeX_le Omega (swapOtherOrder order) T).trans
      change T.degreeOf 1 ≤ 15 * w
      exact hTS'
    have hcertificate : JointOrderCertificate Omega order D.stage.G T prime := by
      apply jointOrderCertificate_of_projection_data Omega order C.1
        D.stage.G T prime 8 (15 * w) 528 (1 + 1055 * w)
          2128593048 528 (15 * w)
          D.stage.irreducible_G
          (regularComponent_G_mem Omega D.stage.G T H C) htr hTne
          hGouter hTouter hGsupport hTsupport hGswapOuter hTswapInner
      · norm_num [prime]
      · norm_num [prime]
      · norm_num [prime]
      · norm_num [w, prime]
      · intro m hm
        norm_num [w] at hm ⊢
        omega
    have hfinite := finite_separable_finrank_bound_of_joint_certificate Omega
      order C.1 htr prime D.stage.G T D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G T H C)
      (regularComponent_T_mem Omega D.stage.G T H C)
      hproper hcertificate
    exact ⟨hfinite.1, hfinite.2.1⟩
  let hZ : ∀ C : RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      prime D.stage.G T D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G T H C)
      (regularComponent_T_mem Omega D.stage.G T H C)
      hproper hGdegree hmixedZ
  have hbase : ∀ C : RegularComponent Omega D.stage.G T H,
      Nonempty (SeparableLiteralCoordinate C.1) := by
    intro C
    exact exists_separableLiteralCoordinate_of_YZ_gates C.1
      (regularComponent_ne_point Omega D.stage.G T H C) (hY C) (hZ C)
  let base : ∀ C : RegularComponent Omega D.stage.G T H,
      SeparableLiteralCoordinate C.1 := fun C ↦ Classical.choice (hbase C)
  refine ⟨base, ?_⟩
  exact exists_adaptiveUnitProjectionFamily_of_nested flag
    (residualAgreementFlag D.degree) base hY hZ
    (residualStage_pderiv_one_ne_zero D.stage)
    D.stage.irreducible_G hproper
    ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
    ((support_subset_flagSupport_iff (residualAgreementFlag D.degree) T).2 hTflag)

end

end ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research

#print axioms ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research.terminalAdaptiveProjectionFamilies_of_rectangular_caps
