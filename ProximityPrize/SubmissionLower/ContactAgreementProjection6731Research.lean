import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFirstTailProjection6731Research

/-! Active YZ projection families for an actual order-w agreement cut. -/

namespace ProximityPrize.SubmissionLower.ContactAgreementProjection6731Research

open scoped Classical BigOperators
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum ContactGenericSurface
open ContactPrimeSeedIncidence ContactRegularComponentCover ContactProperCutSeedCount
open ContactFlagBezout6543Research ContactIdentityResidualIterationResearch
open ContactResidualSupportParametersResearch ContactSharpTaylorFixedMeet6656Research
open ContactWeakSeparableSeparatorResearch ContactScalarCoordinateSeparator6630Research
open ContactAdaptiveNestedProjection6600Research ContactAdaptiveNestedProjectionActive6630Research
open ContactAdaptiveNestedUnitFamily6600Research
open ContactAdaptiveNestedUnitFamilyActive6630Research ContactAdaptiveNestedYZFamily6630Research
open ContactRegularComponentYZPositivity6630Research ContactResidualStageDerivative6600Research
open ContactMovingAgreementCertificate6719Research

noncomputable section

set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000

variable {K Ω I : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable {φ : Polynomial K →+* Ω} {Γ : Finset K} {x : I → K}
variable {p e w a b s : ℕ} [CharP Ω p] {flag : FlagDegree}

theorem exists_agreement_projection_of_caps
    (S : ResidualStage φ Γ x p e flag w (support a b s))
    (x0 u0 u1 : K)
    (hproper : ¬S.G ∣ agreementPolynomial φ S.F w x0 u0 u1)
    (hflagChar : flag.yz+flag.all<p ∧ flag.all<p ∧
      flag.zOnly+flag.yz+flag.all<p)
    (hmixed : (1+w*(2*(b+s+3)-2))*flag.all+
      (flag.yz+flag.all)*((2*(s+2)-1)*w)<p) :
    ∃ base : ∀ C : RegularComponent Ω S.G
        (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F),
        SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
        (sharpResidualAgreementFlag (support a b s) w)) := by
  classical
  let T := agreementPolynomial φ S.F w x0 u0 u1
  let H := regularitySurface φ S.F
  have hsy : s+2 < b+s+3 := by omega
  have hTflag : PolynomialInFlag (sharpResidualAgreementFlag (support a b s) w) T :=
    surfaceMap_agreement_in_sharp_flag hsy (phi := φ)
      ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
      w (fun j : ℕ => (j.factorial : K)⁻¹) x0 u0 u1
  obtain ⟨hGY,hGS,hGZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag S.flag_support
  obtain ⟨hTY,hTS,_⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag hTflag
  have hTY' : T.degreeOf 0 ≤ 1+w*(2*(b+s+3)-2) := by
    apply hTY.trans_eq
    exact sharpResidualAgreementFlag_ys (support a b s) hsy w
  have hTS' : T.degreeOf 1 ≤ (2*(s+2)-1)*w := by
    apply hTS.trans_eq
    simp only [sharpResidualAgreementFlag,sharpAgreementDirection,
      ContactMovingAgreementCertificate6719Research.support]
  have hGdegree : ∀ j : Fin 3,S.G.degreeOf j<p := by
    intro j
    fin_cases j
    · exact hGY.trans_lt hflagChar.1
    · exact hGS.trans_lt hflagChar.2.1
    · exact hGZ.trans_lt hflagChar.2.2
  have hmixZ : coordinateMixedDegree Ω S.G T 2<p := by
    rw [coordinateMixedDegree_two]
    exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
      (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
  let choiceData : ∀ C : RegularComponent Ω S.G T H,
      ∃ B : SeparableLiteralCoordinate C.1,B.index=0 ∨ B.index=2 :=
    fun C => regularComponent_exists_separableLiteralCoordinate6630
      φ S.F S.G T p S.G_dvd_surface S.irreducible_G hproper
      S.y_dependent hGdegree hmixZ C
  let base : ∀ C : RegularComponent Ω S.G T H,
      SeparableLiteralCoordinate C.1 := fun C => (choiceData C).choose
  have hbaseIndex : ∀ C : RegularComponent Ω S.G T H,
      (base C).index=0 ∨ (base C).index=2 := by
    intro C
    exact (choiceData C).choose_spec
  have hactive : ∀ C : RegularComponent Ω S.G T H,
      D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0 ∨
        D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0 := by
    intro C
    have hb := base_differential_ne_zero (base C)
    rcases hbaseIndex C with hidx | hidx
    · left; simpa only [hidx] using hb
    · right; simpa only [hidx] using hb
  let hZ : ∀ C : RegularComponent Ω S.G T H,LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Ω C.1 2 htr
      p S.G T S.irreducible_G
      (regularComponent_G_mem Ω S.G T H C)
      (regularComponent_T_mem Ω S.G T H C)
      hproper hGdegree hmixZ
  obtain ⟨P⟩ := exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
    flag (sharpResidualAgreementFlag (support a b s) w) base hactive hZ
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)
    S.irreducible_G hproper
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
  exact ⟨base,⟨P⟩⟩

end
end ProximityPrize.SubmissionLower.ContactAgreementProjection6731Research
