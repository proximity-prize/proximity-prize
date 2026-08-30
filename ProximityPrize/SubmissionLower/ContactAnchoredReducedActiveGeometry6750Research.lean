import ProximityPrize.SubmissionLower.ContactAnchoredDelayedTailProviderAdapter6750Research
import ProximityPrize.SubmissionLower.ContactFirstTailActiveData6733Research
namespace ProximityPrize.SubmissionLower.ContactAnchoredReducedActiveGeometry6750Research
open scoped Classical BigOperators
open Polynomial KaehlerDifferential
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveJointProjectionBounds
open ActualCoordinateDegreeSum ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover ContactProperCutSeedCount
open ContactFlagBezout6543Research ContactIdentityResidualIterationResearch
open ContactResidualSupportParametersResearch ContactSharpTaylorFixedMeet6656Research
open ContactWeakSeparableSeparatorResearch ContactScalarCoordinateSeparator6630Research
open ContactAdaptiveNestedProjection6600Research ContactAdaptiveNestedProjectionActive6630Research
open ContactRegularComponentYZPositivity6630Research ContactResidualStageDerivative6600Research
open ContactMovingAgreementCertificate6719Research ContactFirstTailCertificate6731Research
open ContactReducedAgreementFlagBridge6800Research
open ContactAnchoredDelayedTailProviderAdapter6750Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar e w a b s : ℕ} [CharP Omega pchar] {flag : FlagDegree}
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota

def reducedFirstCut
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s)) :
    MvPolynomial (Fin 3) Omega :=
  reducedGlobalTailCut phi S.F (support a b s).s (w + 1)

theorem ordinary_sub_reducedFirstCut_dvd
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s)) :
    S.G ∣ globalTailCut phi S.F (w + 1) - reducedFirstCut S := by
  have h := cut_dvd_globalTailCut_sub_reducedGlobalTailCut
    phi S.F S.G S.G_dvd_surface (support a b s).s (w + 1)
  have hselector :
      (tailSelector6800 (w + 1) : ℕ → K) =
        (tailSelector (w + 1) : ℕ → K) := by
    funext j
    simp only [tailSelector6800, tailSelector]
  have hliteral : literalGlobalTailCut6800 phi S.F (w + 1) =
      globalTailCut phi S.F (w + 1) := by
    unfold literalGlobalTailCut6800 globalTailCut
    rw [hselector]
  rw [hliteral] at h
  simpa only [reducedFirstCut] using h

theorem reducedFirstCut_proper
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s))
    (hfirstProper : ¬ S.G ∣ globalTailCut phi S.F (w + 1)) :
    ¬ S.G ∣ reducedFirstCut S := by
  intro hr
  apply hfirstProper
  have h := (ordinary_sub_reducedFirstCut_dvd S).add hr
  simpa only [sub_add_cancel] using h

theorem reducedFirstCut_in_flag
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s)) :
    PolynomialInFlag
      (reducedResidualAgreementFlag6750 (support a b s) (w + 1))
      (reducedFirstCut S) := by
  let P := support a b s
  let Hsupport : ResidualSupportData P S.F :=
    ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
  apply reducedGlobalTailCut_in_flag phi
    (reducedResidualAgreementFlag6750 P (w + 1)) S.F P.s P.ys P.total (w + 1)
  · exact P.one_le_s
  · exact P.s_le_ys
  · exact P.s_le_ys.trans P.ys_le_total
  · exact P.two_le_ys
  · exact P.two_le_ys.trans P.ys_le_total
  · exact Hsupport.coordinate_bounds.2.1
  · exact S.surface_ys_weight
  · exact S.surface_total_weight
  · simp only [reducedResidualAgreementFlag6750,
      reducedAgreementDirection6750]
    have hs : 2 * (P.s - 1) = 2 * P.s - 2 := by omega
    rw [← hs]
    ring_nf
    exact le_rfl
  · rw [reducedResidualAgreementFlag6750_ys]
    have hys : 2 * (P.ys - 1) = 2 * P.ys - 2 := by omega
    rw [← hys]
    ring_nf
    exact le_rfl
  · rw [reducedResidualAgreementFlag6750_total]
    have htotal : 2 * (P.total - 1) = 2 * P.total - 2 := by omega
    rw [← htotal]
    ring_nf
    exact le_rfl

structure ReducedActiveGeometry
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s)) where
  base : ∀ C : RegularComponent Omega S.G (reducedFirstCut S)
      (regularitySurface phi S.F), SeparableLiteralCoordinate C.1
  hactive : ∀ C : RegularComponent Omega S.G (reducedFirstCut S)
      (regularitySurface phi S.F),
    KaehlerDifferential.D Omega (CoordinateField Omega C.1)
        (coordinate Omega C.1 0) ≠ 0 ∨
      KaehlerDifferential.D Omega (CoordinateField Omega C.1)
        (coordinate Omega C.1 2) ≠ 0
  hZ : ∀ C : RegularComponent Omega S.G (reducedFirstCut S)
      (regularitySurface phi S.F), LiteralProjectionGate C 2
  data : AdaptiveNestedProjectionDataActive base hactive
    (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S)

theorem exists_reducedActiveGeometry
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s))
    (hproper : ¬ S.G ∣ globalTailCut phi S.F (w + 1))
    (hflagChar : flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
      flag.zOnly + flag.yz + flag.all < pchar)
    (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
    Nonempty (ReducedActiveGeometry S) := by
  classical
  let supp := support a b s
  let Tred := reducedFirstCut S
  let H := regularitySurface phi S.F
  have hproperRed : ¬ S.G ∣ Tred := reducedFirstCut_proper S hproper
  have hGflag : PolynomialInFlag flag S.G := S.flag_support
  have hTflag : PolynomialInFlag
      (reducedResidualAgreementFlag6750 supp (w + 1)) Tred :=
    reducedFirstCut_in_flag S
  obtain ⟨hGY, hGS, hGZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hGflag
  obtain ⟨hTY, hTS, _hTZ⟩ :=
    ContactTerminalAdaptiveProjection6600Research.degree_bounds_of_polynomialInFlag
      hTflag
  have hTY' : Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2) := by
    apply hTY.trans_eq
    exact reducedResidualAgreementFlag6750_ys supp (w + 1)
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
  have hZ : ∀ C : RegularComponent Omega S.G Tred H,
      LiteralProjectionGate C 2 := by
    intro C htr
    exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
      pchar S.G Tred S.irreducible_G
      (regularComponent_G_mem Omega S.G Tred H C)
      (regularComponent_T_mem Omega S.G Tred H C)
      hproperRed hGdegree hmixedZ
  exact ⟨⟨base, hactive, hZ,
    Classical.choice (exists_adaptiveNestedProjectionDataActive base hactive
      (ContactTerminalAdaptiveProjection6656Research.residualStage_pderiv_one_ne_zero_of_support S))⟩⟩

noncomputable def reducedActiveGeometry
    (S : ResidualStage phi Gamma x pchar e flag w (support a b s))
    (hproper : ¬ S.G ∣ globalTailCut phi S.F (w + 1))
    (hflagChar : flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
      flag.zOnly + flag.yz + flag.all < pchar)
    (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
      (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
    ReducedActiveGeometry S :=
  Classical.choice (exists_reducedActiveGeometry S hproper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.ContactAnchoredReducedActiveGeometry6750Research
