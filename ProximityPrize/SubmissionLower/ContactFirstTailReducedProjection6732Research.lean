import ProximityPrize.SubmissionLower.ContactFirstTailProjection6731Research
import ProximityPrize.SubmissionLower.ContactFirstTailReducedCertificate6732Research

/-! Active-YZ projections for the reduced representative of the global first tail. -/

namespace ProximityPrize.SubmissionLower.ContactFirstTailReducedProjection6732Research

open scoped Classical BigOperators
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover ContactProperCutSeedCount
open ContactFlagBezout6543Research ContactIdentityResidualIterationResearch
open ContactResidualSupportParametersResearch ContactSharpTaylorFixedMeet6656Research
open ContactWeakSeparableSeparatorResearch ContactScalarCoordinateSeparator6630Research
open ContactAdaptiveNestedProjection6600Research ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamilyActive6630Research ContactAdaptiveNestedYZFamily6630Research
open ContactRegularComponentYZPositivity6630Research ContactResidualStageDerivative6600Research
open ContactMovingAgreementCertificate6719Research ContactFirstTailCertificate6731Research
open ContactReducedTaylorProfileResearch ContactFirstTailReducedCertificate6732Research

noncomputable section

set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar e w a b s : ℕ} [CharP Omega pchar] {flag : FlagDegree}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

theorem exists_reduced_firstTail_projection_of_caps
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s))
    (hproper : ¬ S.G ∣ globalTailCut phi S.F (w + 1))
    (hflagChar : flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
      flag.zOnly + flag.yz + flag.all < pchar)
    (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
    ∃ base : ∀ C : RegularComponent Omega S.G
        (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
        (regularitySurface phi S.F),
        SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
        (reducedResidualAgreementFlag (support a b s) (w + 1))) := by
  classical
  let supp := support a b s
  let T := globalTailCut phi S.F (w + 1)
  let Tred := reducedGlobalTailCut phi supp S.F (w + 1)
  let H := regularitySurface phi S.F
  have hd : S.G ∣ T - Tred :=
    S.G_dvd_surface.trans
      (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
  have hproperRed : ¬ S.G ∣ Tred := by
    intro hr
    apply hproper
    have := hd.add hr
    simpa only [T, Tred, sub_add_cancel] using this
  have hGflag : PolynomialInFlag flag S.G := S.flag_support
  let Hsupport : ResidualSupportData supp S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  have hTflag : PolynomialInFlag
      (reducedResidualAgreementFlag supp (w + 1)) Tred :=
    reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
  obtain ⟨hGY, hGS, hGZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hGflag
  obtain ⟨hTY, hTS, _hTZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hTflag
  have hTY' : Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2) := by
    apply hTY.trans_eq
    exact reducedResidualAgreementFlag_ys supp (w + 1)
  have hTS' : Tred.degreeOf 1 ≤ (2 * (s + 2) - 2) * (w + 1) := by
    apply hTS.trans_eq
    rfl
  have hGdegree : ∀ j : Fin 3, S.G.degreeOf j < pchar := by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixedZ : coordinateMixedDegree Omega S.G Tred 2 < pchar := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
  let choiceData : ∀ C : RegularComponent Omega S.G Tred H,
      ∃ B : SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
    fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
      phi S.F S.G Tred pchar S.G_dvd_surface S.irreducible_G hproperRed
      S.y_dependent hGdegree hmixedZ C
  let base : ∀ C : RegularComponent Omega S.G Tred H,
      SeparableLiteralCoordinate C.1 := fun C ↦ (choiceData C).choose
  have hbaseIndex : ∀ C : RegularComponent Omega S.G Tred H,
      (base C).index = 0 ∨ (base C).index = 2 := by
    intro C
    exact (choiceData C).choose_spec
  have hactive : ∀ C : RegularComponent Omega S.G Tred H,
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
  let hZ : ∀ C : RegularComponent Omega S.G Tred H,
      LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      pchar S.G Tred S.irreducible_G
      (regularComponent_G_mem Omega S.G Tred H C)
      (regularComponent_T_mem Omega S.G Tred H C)
      hproperRed hGdegree hmixedZ
  obtain ⟨P⟩ := exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
    flag (reducedResidualAgreementFlag supp (w + 1)) base hactive hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    S.irreducible_G hproperRed
    ((support_subset_flagSupport_iff flag S.G).2 hGflag)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag supp (w + 1)) Tred).2 hTflag)
  exact ⟨base, ⟨P⟩⟩

end

end ProximityPrize.SubmissionLower.ContactFirstTailReducedProjection6732Research
