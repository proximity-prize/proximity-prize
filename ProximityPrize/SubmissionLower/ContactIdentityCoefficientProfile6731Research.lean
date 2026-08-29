import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactOriginalFactorTail6731Research
import ProximityPrize.SubmissionLower.ContactFactorReconstruction6731Research
import ProximityPrize.SubmissionLower.ContactFreshProperCoefficientTrdeg6731Research
import ProximityPrize.SubmissionLower.ContactCoefficientBaseChange6731Research
import ProximityPrize.SubmissionLower.ContactCoefficientPole6731Research

/-! Actual coefficient-pole producer for a regular proper agreement curve in
the global first-tail identity branch. -/

namespace ProximityPrize.SubmissionLower.ContactIdentityCoefficientProfile6731Research

open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface ContactTaylorNumerators
open ContactIdentityResidualIterationResearch ContactOriginalFactorTail6731Research
open ContactFactorReconstruction6731Research ContactPolynomialRecenter6731Research
open ContactFreshProperCoefficientTrdeg6731Research
open ContactCoefficientBaseChange6731Research ContactCoefficientPole6731Research
open ContactComponentPencils ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactRegularComponentCover ContactPolynomialSolutions ContactPolynomialRecovery
open ContactFreshCoefficientFieldGenerationResearch ContactCoefficientFieldTrdeg6731Research
open ContactAgreementEvaluation ContactGlobalPolynomiality ContactInterpolation
open ContactFlagPoleInequality6543Research ContactSparsePoleSupportResearch
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactTranslation
open ActualCurveCoordinateField

noncomputable section

set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

abbrev Ω (K : Type) [Field K] := GenericField K

variable {Γ : Finset K} {x : I → K} {p e : ℕ} [CharP (Ω K) p]
variable {flag : FlagDegree} {w : ℕ} {support : ResidualSupportParameters}

theorem stage_surface_mem
    (S : ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
    (x0 u0 u1 : K)
    (C : RegularComponent (Ω K) S.G
      (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
      (regularitySurface (polynomialEmbedding K) S.F)) :
    surfaceMap (polynomialEmbedding K) S.F ∈ C.1 := by
  obtain ⟨A,hA⟩ := S.G_dvd_surface
  rw [hA]
  exact C.1.mul_mem_right A
    (regularComponent_G_mem (Ω K) S.G _ _ C)

theorem stage_regularity_not_mem
    (S : ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
    (x0 u0 u1 : K)
    (C : RegularComponent (Ω K) S.G
      (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
      (regularitySurface (polynomialEmbedding K) S.F)) :
    surfaceMap (polynomialEmbedding K) (polyH K S.F) ∉ C.1 :=
  regularComponent_H_not_mem (Ω K) S.G _ _ C

theorem coefficientPoleProfile_of_regular_agreement_curve
    (S : ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
    (hTail : S.G ∣ surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
    (x0 u0 u1 : K)
    (hproper : ¬S.G ∣ agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
    (C : RegularComponent (Ω K) S.G
      (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
      (regularitySurface (polynomialEmbedding K) S.F))
    (bound seedCap slopeCap cost : ℕ)
    (hw : 1≤w) (hshort : w+1≤bound) (hchar : bound<p)
    (hbox : S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
    (hyz : ∀ W : Finset (CoordinatePoleMass.Place (Ω K) (CoordinateField (Ω K) C.1)),
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
        (flagSupport unitYZFlag)) ≤ (cost : ℤ)) :
    CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
      (stage_surface_mem S x0 u0 u1 C)
      (stage_regularity_not_mem S x0 u0 u1 C) w cost := by
  classical
  let φ := polynomialEmbedding K
  let Pcurve := C.1
  let L := CoordinateField (Ω K) Pcurve
  let κ : K →+* L := componentCoefficients φ Pcurve
  let v0 : Fin 4 → L := componentPoint φ Pcurve
  letI : CharP L p :=
    charP_of_injective_algebraMap (algebraMap (Ω K) L).injective p
  have hFC := stage_surface_mem S x0 u0 u1 C
  have hHC := stage_regularity_not_mem S x0 u0 u1 C
  obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hGQ,hGH0,hTail0⟩ :=
    exists_original_factor_with_first_tail S hTail
  have hF0mem : surfaceMap φ F0 ∈ Pcurve := by
    obtain ⟨A,hA⟩ := hGF0
    rw [hA]
    exact Pcurve.mul_mem_right A (regularComponent_G_mem (Ω K) S.G _ _ C)
  have hHdecomp : surfaceMap φ (polyH K S.F) =
      surfaceMap φ (polyH K F0)*surfaceMap φ Q+
        surfaceMap φ F0*surfaceMap φ (polyH K Q) := by
    rw [hprod]
    unfold polyH
    rw [MvPolynomial.pderiv_mul]
    simp only [map_add,map_mul]
  have hHQnot : surfaceMap φ (polyH K F0)*surfaceMap φ Q ∉ Pcurve := by
    intro hm
    apply hHC
    rw [hHdecomp]
    exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0mem)
  have hQnot : surfaceMap φ Q ∉ Pcurve :=
    fun h => hHQnot (Pcurve.mul_mem_left _ h)
  have hH0not : surfaceMap φ (polyH K F0) ∉ Pcurve :=
    fun h => hHQnot (Pcurve.mul_mem_right _ h)
  have hF0rel : MvPolynomial.eval₂Hom κ v0 F0=0 :=
    (component_evaluation_zero_iff φ Pcurve F0).mpr hF0mem
  have hF0reg : MvPolynomial.eval₂Hom κ v0 (polyH K F0)≠0 :=
    (component_evaluation_zero_iff φ Pcurve (polyH K F0)).not.mpr hH0not
  have hQeval : MvPolynomial.eval₂Hom κ v0 Q≠0 :=
    (component_evaluation_zero_iff φ Pcurve Q).not.mpr hQnot
  have hprodrel : MvPolynomial.eval₂Hom κ v0 (F0*Q)=0 := by
    rw [map_mul,hF0rel,zero_mul]
  have hprodreg : MvPolynomial.eval₂Hom κ v0 (polyH K (F0*Q))≠0 := by
    rw [← hprod]
    exact component_regular φ Pcurve S.F hHC
  let P0 : Polynomial L := globalPolynomial κ F0 v0 hF0rel hF0reg w
  have hP0deg : P0.natDegree≤w := globalPolynomial_natDegree_le κ F0 v0 hF0rel hF0reg w
  have hSne : S.F≠0 := by
    intro hz
    apply S.regular_proper
    rw [hz]
    simp
  have hF0box : F0 ∈ globalCoefficientBox K bound w seedCap slopeCap := by
    apply ContactFactorCaps.mem_globalCoefficientBox_of_dvd F0 S.F bound w seedCap slopeCap
      hSne ⟨Q,hprod⟩ hbox
  have hP0solution : specialization L P0 (v0 3) (MvPolynomial.map κ F0)=0 :=
    canonical_polynomiality_of_first_tail κ F0 v0 hF0rel hF0reg
      p bound w seedCap slopeCap hw hshort hchar hF0box hTail0
  have hcanon : truncatedPolynomial φ Pcurve S.F hFC hHC w=P0 := by
    unfold truncatedPolynomial
    change globalPolynomial κ S.F v0 _ _ w = P0
    have hm := globalPolynomial_mul_factor κ F0 Q v0 hF0rel hQeval hF0reg
      hprodrel hprodreg w
    simpa only [hprod,P0] using hm
  have hagree : P0.eval (κ x0)=κ u0+v0 3*κ u1 := by
    have hm := regularComponent_T_mem (Ω K) S.G
      (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F) C
    have hv := (agreement_mem_iff_truncated_value φ Pcurve S.F hFC hHC
      w x0 u0 u1).mp (by simpa only [agreementPolynomial] using hm)
    rw [hcanon] at hv
    change P0.eval (componentCoefficients φ Pcurve x0) =
      componentCoefficients φ Pcurve u0+
        coordinate (Ω K) Pcurve 2*componentCoefficients φ Pcurve u1 at hv
    change P0.eval (componentCoefficients φ Pcurve x0) =
      componentCoefficients φ Pcurve u0+
        coordinate (Ω K) Pcurve 2*componentCoefficients φ Pcurve u1
    exact hv
  let A0 := agreementNumerator F0 w (fun j => (j.factorial : K)⁻¹) x0 u0 u1
  have hA0proper : ¬F0 ∣ A0 := by
    apply ContactOriginalFactorTail6731Research.original_factor_agreement_proper
      φ F0 Q S.G hGF0 w _ x0 u0 u1
    simpa only [agreementPolynomial,hprod] using hproper
  have hvpoint : polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0 := by
    funext i
    fin_cases i
    · rfl
    · exact globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
    · exact globalPolynomial_initial_slope κ F0 v0 hF0rel hF0reg w hw
    · rfl
  have hregspec : specialization L P0 (v0 3)
      (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.map κ F0))≠0 := by
    have hmapped : MvPolynomial.eval₂Hom (RingHom.id L) v0
        (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.map κ F0))≠0 := by
      simpa only [polyH,MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom,
        RingHom.id_comp] using hF0reg
    intro hz
    apply hmapped
    rw [← hvpoint]
    rw [eval_polynomialPoint_eq_specialization, hz]
    simp
  have hA0solution : specialization L P0 (v0 3) (MvPolynomial.map κ A0)=0 := by
    apply RatFunc.algebraMap_injective L
    rw [map_zero,← fresh_eval_eq]
    rw [map_agreementNumerator_base]
    have hfresh : MvPolynomial.eval₂Hom (algebraMap L (RatFunc L))
        (freshPoint P0 (v0 3))
        (MvPolynomial.pderiv (2 : Fin 4) (MvPolynomial.map κ F0))≠0 := by
      rw [fresh_eval_eq]
      exact RatFunc.algebraMap_ne_zero hregspec
    have heval := (factorial_agreement_zero_iff_original_agreement
      (algebraMap L (RatFunc L)) (MvPolynomial.map κ F0) P0 (v0 3) RatFunc.X
      hP0solution hfresh p w S.characteristic_bound
      hP0deg (κ x0) (κ u0) (κ u1)).mpr hagree
    simpa only [freshPoint,map_inv₀,map_natCast] using heval
  have htrK : Algebra.trdeg K (baseCoefficientField (k := K) P0 (v0 3))≤1 :=
    baseCoefficientField_trdeg_le_one_of_fresh_proper_relations F0 A0 P0 (v0 3)
      hF0irr hF0pos hA0proper hP0solution hA0solution hregspec
      p w S.characteristic_bound hP0deg
  let k := algebraicClosure K (Ω K)
  have htrk : Algebra.trdeg k (baseCoefficientField (k := k) P0 (v0 3))≤1 :=
    baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
  letI : IsAlgClosed k := IsAlgClosure.isAlgClosed K
  have hxK : Transcendental K (initialCoordinate K) := by
    rw [transcendental_iff_injective]
    intro f g hfg
    apply polynomialEmbedding_injective K
    change f.eval₂ (coefficientEmbedding K) (initialCoordinate K) =
      g.eval₂ (coefficientEmbedding K) (initialCoordinate K) at hfg
    rw [generic_eval_eq,generic_eval_eq] at hfg
    exact hfg
  have hxk : Transcendental k (initialCoordinate K) := hxK.algebraicClosure
  apply coefficientPoleProfile_of_unitYZ_bound φ Pcurve S.F hFC hHC w cost
  · intro place j
    rw [hcanon]
    apply coefficient_pole_le_of_trdeg_le_one P0 (v0 3) w hP0deg htrk
      (initialCoordinate K) hxk (coordinate (Ω K) Pcurve 0)
    exact globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
  · exact hyz

end
end ProximityPrize.SubmissionLower.ContactIdentityCoefficientProfile6731Research
