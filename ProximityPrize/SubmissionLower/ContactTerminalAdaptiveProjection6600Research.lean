import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research
import ProximityPrize.SubmissionLower.ContactAdaptiveNestedUnitFamily6600Research
import ProximityPrize.SubmissionLower.ContactResidualStageDerivative6600Research
import ProximityPrize.SubmissionLower.ActualCurveJointProjectionBounds
import ProximityPrize.SubmissionLower.ActualPlaneJointProjection
import ProximityPrize.SubmissionLower.TrivariateShearResearch
import ProximityPrize.SubmissionLower.ContactParameters6600Research

/-!
# Terminal adaptive projection families from the score-66 flag caps

This is the last local geometry adapter for the score-66 route.  A terminal
outer residual stage already carries the surface flag and its proper
agreement cut has the canonical residual flag.  The literal `Z` projection
resultant stays below the fixed characteristic through the rectangular cap.
The literal `Y` projection resultant no longer fits under the rectangular
product; it is certified instead through the sparse joint-support order
certificate, whose trapezoid budget uses the sharp stage weight caps rather
than the rectangular box.  The two gates select a finite-separable literal
base on every regular curve component, after which the common adaptive
nested-family constructor applies directly.
-/

namespace ProximityPrize.SubmissionLower.ContactTerminalAdaptiveProjection6600Research

open scoped Classical
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds
open ActualPlaneJointProjection
open ActualPlaneCoordinateCaps ActualPlanePositiveOrder
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
open ContactRegularFactorGate

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

/-- Weighted-degree monotonicity under divisibility in three variables,
obtained by transporting the four-variable multiplicativity theorem along
the injective variable renaming `Fin.succ`. -/
theorem weightedTotalDegree3_le_of_dvd (v : Fin 3 → ℕ)
    (P Q : MvPolynomial (Fin 3) Omega) (hdvd : P ∣ Q) (hQ : Q ≠ 0) :
    MvPolynomial.weightedTotalDegree v P ≤
      MvPolynomial.weightedTotalDegree v Q := by
  classical
  have hren : ∀ R : MvPolynomial (Fin 3) Omega,
      MvPolynomial.weightedTotalDegree (Fin.cases 0 v)
        (MvPolynomial.rename Fin.succ R) =
      MvPolynomial.weightedTotalDegree v R := by
    intro R
    unfold MvPolynomial.weightedTotalDegree
    rw [MvPolynomial.support_rename_of_injective (Fin.succ_injective 3),
      Finset.sup_image]
    apply congrArg (fun f : (Fin 3 →₀ ℕ) → ℕ => R.support.sup f)
    funext d
    rw [Function.comp_apply, ContactFactorCaps.weight_fin4,
      TrivariateShearResearch.weight_fin3]
    have h0 : (Finsupp.mapDomain Fin.succ d) 0 = 0 := by
      rw [Finsupp.mapDomain_notin_range]
      intro hmem
      obtain ⟨i, hi⟩ := hmem
      exact Fin.succ_ne_zero i hi
    have h1 : (Finsupp.mapDomain Fin.succ d) 1 = d 0 := by
      simpa using Finsupp.mapDomain_apply (Fin.succ_injective 3) d 0
    have h2 : (Finsupp.mapDomain Fin.succ d) 2 = d 1 := by
      simpa using Finsupp.mapDomain_apply (Fin.succ_injective 3) d 1
    have h3 : (Finsupp.mapDomain Fin.succ d) 3 = d 2 := by
      simpa using Finsupp.mapDomain_apply (Fin.succ_injective 3) d 2
    rw [h0, h1, h2, h3]
    show 0 * 0 + d 0 * v 0 + d 1 * v 1 + d 2 * v 2 =
      d 0 * v 0 + d 1 * v 1 + d 2 * v 2
    ring
  have hPne : P ≠ 0 := by
    rintro rfl
    obtain ⟨R, hR⟩ := hdvd
    exact hQ (by rw [hR, zero_mul])
  have h4 := ContactFactorCaps.weightedTotalDegree_le_of_dvd (Fin.cases 0 v)
    (MvPolynomial.rename Fin.succ P) (MvPolynomial.rename Fin.succ Q)
    (map_dvd _ hdvd)
    (by
      intro h0
      exact hQ (MvPolynomial.rename_injective _ (Fin.succ_injective 3)
        (by rw [h0, map_zero])))
  rw [hren P, hren Q] at h4
  exact h4

/-- The sharp stage weight caps are already enough to construct the entire
adaptive family at every proper terminal agreement cut: the `Z` gate is the
rectangular characteristic bound, and the `Y` gate is the sparse joint-order
certificate with the trapezoid budget. -/
theorem terminalAdaptiveProjectionFamilies_of_rectangular_caps
    [CharP Omega prime]
    {flag : FlagDegree}
    (S : ResidualStage phi Gamma x prime errors flag w)
    (hflagZ : flag.zOnly ≤ 520)
    (hflagY : flag.yz ≤ 41)
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
  have hGY' : D.stage.G.degreeOf 0 ≤ 49 := by omega
  have hGS' : D.stage.G.degreeOf 1 ≤ 8 := by omega
  have hGZ' : D.stage.G.degreeOf 2 ≤ 569 := by omega
  have hTY' : T.degreeOf 0 ≤ 1 + 81 * w := by
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
  have hmixedZ :
      coordinateMixedDegree Omega D.stage.G T 2 < prime := by
    rw [coordinateMixedDegree_two]
    apply (Nat.add_le_add
      (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt
    norm_num [w, prime]
  -- sharp joint (S,Z) support cap for the stage component, from the stage
  -- weight fields through the surface divisibility
  have hSurfne : surfaceMap phi D.stage.F ≠ 0 := by
    intro h0
    apply D.stage.regular_proper
    rw [← surfaceMap_pderiv_R, h0, map_zero]
    exact dvd_zero _
  have hSurfJoint : ∀ e ∈ (surfaceMap phi D.stage.F).support,
      e 1 + e 2 ≤ 528 := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
      (support_surfaceMap_subset phi D.stage.F he)
    have hw := (MvPolynomial.le_weightedTotalDegree residualTotalWeights
      hq).trans D.stage.surface_total_weight
    rw [ContactFactorCaps.weight_fin4] at hw
    change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ 528 at hw
    have he1 : Finsupp.tail q 1 = q 2 := rfl
    have he2 : Finsupp.tail q 2 = q 3 := rfl
    rw [he1, he2]
    omega
  have hSurfWt : MvPolynomial.weightedTotalDegree
      (![0, 1, 1] : Fin 3 → ℕ)
      (surfaceMap phi D.stage.F) ≤ 528 := by
    unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro d hd
    rw [TrivariateShearResearch.weight_fin3]
    have hj := hSurfJoint d hd
    show d 0 * 0 + d 1 * 1 + d 2 * 1 ≤ 528
    omega
  have hGjoint : ∀ e ∈ D.stage.G.support, e 1 + e 2 ≤ 528 := by
    intro e he
    have hmono := weightedTotalDegree3_le_of_dvd
      (![0, 1, 1] : Fin 3 → ℕ)
      D.stage.G (surfaceMap phi D.stage.F) D.stage.G_dvd_surface hSurfne
    have hle := (MvPolynomial.le_weightedTotalDegree
      (![0, 1, 1] : Fin 3 → ℕ) he).trans
      (hmono.trans hSurfWt)
    rw [TrivariateShearResearch.weight_fin3] at hle
    have hle' : e 0 * 0 + e 1 * 1 + e 2 * 1 ≤ 528 := hle
    omega
  have hGZsharp : D.stage.G.degreeOf 2 ≤ 528 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have := hGjoint e he
    omega
  have hTjoint : ∀ e ∈ T.support, e 1 + e 2 ≤ 138279906 := by
    intro e he
    obtain ⟨-, -, htot⟩ := hTflag e he
    dsimp only [residualAgreementFlag] at htot
    have hDw : D.degree ≤ w := hD
    have hwv : w = 131071 := rfl
    omega
  have hTne : T ≠ 0 := by
    intro h0
    apply hproper
    show D.stage.G ∣ T
    rw [h0]
    exact dvd_zero _
  -- literal `Y` gate through the sparse joint-order certificate
  let hY : ∀ C : RegularComponent Omega D.stage.G T H,
      LiteralProjectionGate C 0 := by
    intro C htr
    have hGmem := regularComponent_G_mem Omega D.stage.G T H C
    have hTmem := regularComponent_T_mem Omega D.stage.G T H C
    have hcert : JointOrderCertificate Omega (Equiv.refl (Fin 3))
        D.stage.G T prime := by
      apply jointOrderCertificate_of_projection_data Omega (Equiv.refl (Fin 3))
        C.1 D.stage.G T prime 8 1966065 528 138279906 2128593048 528 1966065
        D.stage.irreducible_G hGmem htr hTne
      · exact (planeMap_natDegree_le Omega _ _).trans (by simpa using hGS')
      · exact (planeMap_natDegree_le Omega _ _).trans
          (by simpa using hTS'.trans (by norm_num [w]))
      · exact rationalMap_joint_support_of_original Omega _ _ 528
          (by intro d hd; simpa using hGjoint d hd)
      · exact rationalMap_joint_support_of_original Omega _ _ 138279906
          (by intro d hd; simpa using hTjoint d hd)
      · exact (planeMap_natDegree_le Omega _ _).trans
          (by simpa using hGZsharp)
      · exact (planeMap_degreeX_le Omega _ _).trans
          (by simpa using hTS'.trans (by norm_num [w]))
      · norm_num [prime]
      · norm_num [prime]
      · norm_num [prime]
      · norm_num [prime]
      · intro m hm
        omega
    have h := finite_separable_finrank_bound_of_joint_certificate Omega
      (Equiv.refl (Fin 3)) C.1 htr prime D.stage.G T
      D.stage.irreducible_G hGmem hTmem hproper hcert
    exact ⟨h.1, h.2.1⟩
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
