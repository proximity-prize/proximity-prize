import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSharpTaylorYZFactorProviderResearch
import ProximityPrize.SubmissionLower.ContactReducedTaylorProfileResearch

/-!
# Reduced Taylor adaptive projection families

This file isolates the sound projection-family construction from the older
reduced-factor incidence wrapper.  The latter targeted an obsolete recursive
API; the hybrid moving proof only needs this construction on the reduced cut.
-/

namespace ProximityPrize.SubmissionLower.ContactReducedTaylorYZFactorProviderResearch

open scoped Classical BigOperators
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection
open ActualCurveJointProjectionBounds ActualCoordinateDegreeSum
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils ContactIncidence
open ContactFlagBezout6543Research
open ContactIdentityResidualIterationResearch
open ContactResidualSupportParametersResearch
open ContactAdaptiveUnitPoleFamilyResearch
open ContactRegularComponentYZPositivity6630Research
open ContactAdaptiveNestedProjection6600Research
open ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamilyActive6630Research
open ContactAdaptiveNestedYZFamily6630Research
open ContactWeakSeparableSeparatorResearch
open ContactScalarCoordinateSeparator6630Research
open ContactTerminalAdaptiveProjection6656Research
open ContactSharpTaylorYZFactorProviderResearch
open ContactReducedTaylorProfileResearch
open ContactRobustFixedMeet6656Research

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 50000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

/-- Every proper terminal reduced cut admits a YZ-positive adaptive projection
family with the reduced Taylor flag. -/
def TerminalAdaptiveProjectionFamiliesReducedYZ
    {e w : ℕ} {flag : FlagDegree}
    (support : ResidualSupportParameters)
    (S : ResidualStage phi Gamma x pchar e flag w support) : Prop :=
  ∀ (D : S.TerminalDescendant) (i : Iota), i ∈ D.stage.nodes →
    ¬ D.stage.G ∣ agreementPolynomial phi D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i) →
    ∃ base : ∀ C : RegularComponent Omega D.stage.G
        (reducedAgreementPolynomial phi support D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        (regularitySurface phi D.stage.F),
        SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
        (reducedResidualAgreementFlag support D.degree))

/-- The standard active-coordinate and characteristic gates construct the
reduced Taylor projection family needed by the hybrid moving ledger. -/
theorem terminalAdaptiveProjectionFamiliesReducedYZ_of_active_yz_caps
    {e w : ℕ} {flag : FlagDegree}
    (support : ResidualSupportParameters)
    (S : ResidualStage phi Gamma x pchar e flag w support)
    (surfaceY surfaceS surfaceZ cutY cutS : ℕ)
    (hflagY : flag.yz + flag.all ≤ surfaceY)
    (hflagS : flag.all ≤ surfaceS)
    (hflagZ : flag.zOnly + flag.yz + flag.all ≤ surfaceZ)
    (hcutY : 1 + w * (2 * support.ys - 2) ≤ cutY)
    (hcutS : (2 * support.s - 2) * w ≤ cutS)
    (hsurfaceChar : surfaceY < pchar ∧ surfaceS < pchar ∧
      surfaceZ < pchar)
    (hmixedZ : cutY * surfaceS + surfaceY * cutS < pchar) :
    TerminalAdaptiveProjectionFamiliesReducedYZ support S := by
  intro D i _hi hproper
  let T := agreementPolynomial phi D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let Tred := reducedAgreementPolynomial phi support D.stage.F D.degree
    (x i) (D.stage.u0 i) (D.stage.u1 i)
  let H := regularitySurface phi D.stage.F
  have hd : D.stage.G ∣ T - Tred :=
    D.stage.G_dvd_surface.trans
      (agreementPolynomial_sub_reduced_dvd phi support D.stage.F D.degree
        (x i) (D.stage.u0 i) (D.stage.u1 i))
  have hproperRed : ¬ D.stage.G ∣ Tred := by
    intro hr
    apply hproper
    have := hd.add hr
    simpa only [T, Tred, sub_add_cancel] using this
  have hGflag : PolynomialInFlag flag D.stage.G := D.stage.flag_support
  have hTflag : PolynomialInFlag
      (reducedResidualAgreementFlag support D.degree) Tred :=
    surfaceMap_reducedAgreement_in_flag phi support
      ⟨D.stage.surface_s_weight, D.stage.surface_ys_weight,
        D.stage.surface_total_weight⟩ D.degree
      (fun j : ℕ ↦ (j.factorial : K)⁻¹)
      (x i) (D.stage.u0 i) (D.stage.u1 i)
  obtain ⟨hGY, hGS, hGZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hGflag
  obtain ⟨hTY, hTS, _hTZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hTflag
  have hD : D.degree ≤ w := D.degree_le
  have hGY' : D.stage.G.degreeOf 0 ≤ surfaceY := hGY.trans hflagY
  have hGS' : D.stage.G.degreeOf 1 ≤ surfaceS := hGS.trans hflagS
  have hGZ' : D.stage.G.degreeOf 2 ≤ surfaceZ := hGZ.trans hflagZ
  have hTY' : Tred.degreeOf 0 ≤ cutY := by
    calc
      Tred.degreeOf 0 ≤ (reducedResidualAgreementFlag support D.degree).yz +
          (reducedResidualAgreementFlag support D.degree).all := hTY
      _ = 1 + D.degree * (2 * support.ys - 2) :=
        reducedResidualAgreementFlag_ys support D.degree
      _ ≤ 1 + w * (2 * support.ys - 2) :=
        Nat.add_le_add_left
          (Nat.mul_le_mul_right (2 * support.ys - 2) hD) 1
      _ ≤ cutY := hcutY
  have hTS' : Tred.degreeOf 1 ≤ cutS := by
    calc
      Tred.degreeOf 1 ≤ (reducedResidualAgreementFlag support D.degree).all := hTS
      _ = (2 * support.s - 2) * D.degree := rfl
      _ ≤ (2 * support.s - 2) * w :=
        Nat.mul_le_mul_left (2 * support.s - 2) hD
      _ ≤ cutS := hcutS
  have hGdegree : ∀ j : Fin 3, D.stage.G.degreeOf j < pchar := by
    intro j
    fin_cases j
    · exact hGY'.trans_lt hsurfaceChar.1
    · exact hGS'.trans_lt hsurfaceChar.2.1
    · exact hGZ'.trans_lt hsurfaceChar.2.2
  have hmixedZ' : coordinateMixedDegree Omega D.stage.G Tred 2 < pchar := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS')
      (Nat.mul_le_mul hGY' hTS')).trans_lt hmixedZ
  let choiceData : ∀ C : RegularComponent Omega D.stage.G Tred H,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
      phi D.stage.F D.stage.G Tred pchar D.stage.G_dvd_surface
      D.stage.irreducible_G hproperRed D.stage.y_dependent
      hGdegree hmixedZ' C
  let base : ∀ C : RegularComponent Omega D.stage.G Tred H,
      SeparableLiteralCoordinate C.1 := fun C ↦ (choiceData C).choose
  have hbaseIndex : ∀ C : RegularComponent Omega D.stage.G Tred H,
      (base C).index = 0 ∨ (base C).index = 2 :=
    fun C ↦ (choiceData C).choose_spec
  have hactive : ∀ C : RegularComponent Omega D.stage.G Tred H,
      KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 0) ≠ 0 ∨
        KaehlerDifferential.D Omega (CoordinateField Omega C.1)
          (coordinate Omega C.1 2) ≠ 0 := by
    intro C
    have hb := base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left
      simpa only [hidx] using hb
    · right
      simpa only [hidx] using hb
  let hZ : ∀ C : RegularComponent Omega D.stage.G Tred H,
      LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      pchar D.stage.G Tred D.stage.irreducible_G
      (regularComponent_G_mem Omega D.stage.G Tred H C)
      (regularComponent_T_mem Omega D.stage.G Tred H C)
      hproperRed hGdegree hmixedZ'
  obtain ⟨P⟩ := exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
    flag (reducedResidualAgreementFlag support D.degree)
    base hactive hZ (residualStage_pderiv_one_ne_zero_of_support D.stage)
    D.stage.irreducible_G hproperRed
    ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag support D.degree) Tred).2 hTflag)
  exact ⟨base, ⟨P⟩⟩

end
end ProximityPrize.SubmissionLower.ContactReducedTaylorYZFactorProviderResearch
