import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily6600Research
import ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
import ProximityPrize.SubmissionLower.ContactParameters6600Research
import ProximityPrize.SubmissionLower.ContactTerminalTrapezoidProjection6622Research

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
open ContactTerminalTrapezoidProjection6622Research

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

/-- Removing the coefficient-polynomial coordinate cannot increase the
ordinary total degree beyond the residual total weight. -/
theorem surfaceMap_totalDegree_le_surfaceTotalWeight
    (F : MvPolynomial (Fin 4) K) :
    (surfaceMap phi F).totalDegree ≤
      MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  classical
  unfold MvPolynomial.totalDegree MvPolynomial.weightedTotalDegree
  apply Finset.sup_le
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi F he)
  calc
    d.tail.sum (fun _ exponent ↦ exponent) =
        Finsupp.weight residualTotalWeights d := by
      rw [ContactFactorCaps.weight_fin4]
      simp [residualTotalWeights, Finsupp.sum_fintype, Fin.sum_univ_succ,
        Finsupp.tail_apply, Nat.add_assoc]
    _ ≤ F.support.sup (Finsupp.weight residualTotalWeights) :=
      Finset.le_sup hd

/-- The robust rectangular surface caps are already enough to construct the
entire adaptive family at every proper terminal agreement cut. -/
theorem terminalAdaptiveProjectionFamilies_of_rectangular_caps
    [CharP Omega prime]
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x prime errors flag w)
    (hphi : Function.Injective phi)
    (hflagTotal : flag.zOnly + flag.yz + flag.all ≤ 528)
    (hflagYS : flag.yz + flag.all ≤ 43)
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
  obtain ⟨hGY, hGS, hGZ⟩ := degree_bounds_of_polynomialInFlag hGflag
  obtain ⟨hTY, hTS, hTZ⟩ := degree_bounds_of_polynomialInFlag hTflag
  have hD : D.degree ≤ w := D.degree_le.trans (Nat.le_refl w)
  have hGY' : D.stage.G.degreeOf 0 ≤ 43 := by omega
  have hGS' : D.stage.G.degreeOf 1 ≤ 8 := by omega
  have hFne : D.stage.F ≠ 0 := by
    intro hzero
    apply D.stage.regular_proper
    simp [hzero]
  have hsurfaceNe : surfaceMap phi D.stage.F ≠ 0 :=
    surfaceMap_ne_zero phi hphi D.stage.F hFne
  have hGTotal : D.stage.G.totalDegree ≤ 528 := by
    exact (MvPolynomial.totalDegree_le_of_dvd_of_isDomain
      D.stage.G_dvd_surface hsurfaceNe).trans
        ((surfaceMap_totalDegree_le_surfaceTotalWeight D.stage.F).trans
          D.stage.surface_total_weight)
  have hGZ' : D.stage.G.degreeOf 2 ≤ 528 :=
    (MvPolynomial.degreeOf_le_totalDegree D.stage.G 2).trans hGTotal
  have hTY' : T.degreeOf 0 ≤ 1 + 85 * w := by
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
    fin_cases j
    · exact hGY'.trans_lt (by norm_num [prime])
    · exact hGS'.trans_lt (by norm_num [prime])
    · exact hGZ'.trans_lt (by norm_num [prime])
  have hTflag6622 :
      PolynomialInFlag ⟨970 * w, 1 + 70 * w, 15 * w⟩ T := by
    intro e he
    have h := hTflag e he
    dsimp only [residualAgreementFlag] at h
    constructor
    · exact h.1.trans (Nat.mul_le_mul_left 15 hD)
    constructor
    · calc
        e 0 + e 1 ≤ 1 + 70 * D.degree + 15 * D.degree := h.2.1
        _ ≤ (1 + 70 * w) + 15 * w := by omega
    · calc
        e 0 + e 1 + e 2 ≤
            970 * D.degree + (1 + 70 * D.degree) + 15 * D.degree := h.2.2
        _ ≤ 970 * w + (1 + 70 * w) + 15 * w := by omega
  have hmixedZ :
      coordinateMixedDegree Omega D.stage.G T 2 < prime := by
    rw [coordinateMixedDegree_two]
    apply (Nat.add_le_add
      (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt
    norm_num [w, prime]
  let hY : ∀ C : RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 0 := by
    intro C
    exact finite_separable_at_Y_of_trapezoid C D.stage.irreducible_G
      hproper hGflag hflagS hflagTotal hTflag6622
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
