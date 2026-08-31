import ProximityPrize.SubmissionLower.ContactDelayedTailMultiplicityProvider6732Research
import ProximityPrize.SubmissionLower.ContactTwoTailTangentCost6732Research
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
import ProximityPrize.SubmissionLower.ContactIdentityCoefficientProfile6731Research
import ProximityPrize.SubmissionLower.ContactIdentityCurveCount6731Research
namespace ProximityPrize.SubmissionLower.ContactTangentCoefficientProvider6732Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactGenericSurface ContactTaylorNumerators
open ContactIdentityResidualIterationResearch ContactRegularComponentCover
open ContactDelayedTailMultiplicityProvider6732Research
open ContactFirstTailCertificate6731Research ContactTwoTailRecurrence6731Research
open ContactComponentPencils ContactPrimeSeedIncidence ContactProperCutSeedCount
open ContactPolynomialSolutions ContactGlobalPolynomiality ContactAgreementEvaluation
open ContactGeometricFactorCover ContactFactorCover ContactFactorReconstruction6731Research
open ContactReconstructionFieldMembershipResearch
open ContactNumeratorFactorScaling6731Research ContactFreshProperCoefficientTrdeg6731Research
open ContactFreshCoefficientFieldGenerationResearch ContactCoefficientFieldTrdeg6731Research
open ContactCoefficientBaseChange6731Research ContactCoefficientPole6731Research
open ContactIdentityCurveCount6731Research ContactTwoTailTangentCost6732Research
open ContactFlagBezout6543Research ContactPrimeFlagBudgetFamilyResearch
open ContactSparsePoleSupportResearch ContactInterpolation ContactTranslation
open ContactWeakSeparableSeparatorResearch
open ContactAdaptiveUnitPoleFamilyResearch ContactAdaptiveProjectionCoordinateResearch
open CoordinateBoxZeroCount
open ActualCurveCoordinateField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Omega (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I → K} {p errors w:ℕ}
variable [CharP (Omega K) p]
variable {flag tailFlag1:FlagDegree}
variable {support:ContactResidualSupportParametersResearch.ResidualSupportParameters}
theorem firstTailComponent_surface_mem
    (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (C:FirstTailComponent S):
    surfaceMap (polynomialEmbedding K) S.F∈C.1:=by
  obtain ⟨Q,hQ⟩:=S.G_dvd_surface
  rw [hQ]
  exact C.1.mul_mem_right Q
    (regularComponent_G_mem (Omega K) S.G _ _ C)
theorem firstTailComponent_regularity_not_mem
    (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (C:FirstTailComponent S):
    surfaceMap (polynomialEmbedding K) (polyH K S.F)∉C.1:=
  regularComponent_H_not_mem (Omega K) S.G _ _ C
theorem exists_original_factor_of_firstTailComponent
    (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (C:FirstTailComponent S):
    ∃ F0 Q:MvPolynomial (Fin 4) K,
      Irreducible F0∧0 < F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
      S.F=F0*Q∧
      S.G∣surfaceMap (polynomialEmbedding K) F0∧
      surfaceMap (polynomialEmbedding K) F0∈C.1∧
      surfaceMap (polynomialEmbedding K) Q∉C.1∧
      surfaceMap (polynomialEmbedding K) (polyH K F0)∉C.1:=by
  classical
  let phi:=polynomialEmbedding K
  let Pcurve:=C.1
  let L:=CoordinateField (Omega K) Pcurve
  let phiC:Polynomial K →+*L:=
    (algebraMap (Omega K) L).comp phi
  let vC:Fin 3 → L:=fun i => componentPoint phi Pcurve i.succ
  have hSne:S.F≠0:=by
    intro hzero
    apply S.regular_proper
    rw [hzero]
    simp
  have hsurfaceZero:MvPolynomial.eval vC (surfaceMap phiC S.F)=0:=by
    rw [eval_surfaceMap]
    change MvPolynomial.eval₂Hom (componentCoefficients phi Pcurve)
      (componentPoint phi Pcurve) S.F=0
    exact (component_evaluation_zero_iff phi Pcurve S.F).mpr
      (firstTailComponent_surface_mem S C)
  have hphiC:Function.Injective phiC:=
    (algebraMap (Omega K) L).injective.comp (polynomialEmbedding_injective K)
  obtain ⟨F0,hF0mem,hF0zero⟩:=
    exists_active_factor_of_surface_zero phiC hphiC S.F hSne vC hsurfaceZero
  have hF0spec:=activeFactors_spec S.F F0 hF0mem
  obtain ⟨Q,hprod⟩:=hF0spec.2.1
  have hF0curve:surfaceMap phi F0∈Pcurve:=by
    rw [←coordinateEvaluation_ker (Omega K) Pcurve]
    rw [eval_surfaceMap] at hF0zero
    change MvPolynomial.eval₂Hom (componentCoefficients phi Pcurve)
      (componentPoint phi Pcurve) F0=0 at hF0zero
    rw [component_evaluation] at hF0zero
    exact hF0zero
  have hHdecomp:surfaceMap phi (polyH K S.F)=
      surfaceMap phi (polyH K F0)*surfaceMap phi Q+
        surfaceMap phi F0*surfaceMap phi (polyH K Q):=by
    rw [hprod]
    unfold polyH
    rw [MvPolynomial.pderiv_mul]
    simp only [map_add,map_mul]
  have hHQnot:surfaceMap phi (polyH K F0)*surfaceMap phi Q∉Pcurve:=by
    intro hm
    apply firstTailComponent_regularity_not_mem S C
    rw [hHdecomp]
    exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0curve)
  have hQnot:surfaceMap phi Q∉Pcurve:=
    fun h => hHQnot (Pcurve.mul_mem_left _ h)
  have hH0not:surfaceMap phi (polyH K F0)∉Pcurve:=
    fun h => hHQnot (Pcurve.mul_mem_right _ h)
  have hGprod:S.G∣surfaceMap phi F0*surfaceMap phi Q:=by
    simpa only [←map_mul, ←hprod] using S.G_dvd_surface
  have hGsplit:=S.irreducible_G.prime.dvd_or_dvd hGprod
  have hGQfalse:¬ S.G∣surfaceMap phi Q:=by
    intro hGQ
    apply hQnot
    exact Pcurve.mem_of_dvd hGQ
      (regularComponent_G_mem (Omega K) S.G _ _ C)
  have hGF0:S.G∣surfaceMap phi F0:=hGsplit.resolve_right hGQfalse
  exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGF0,
    hF0curve,hQnot,hH0not⟩
theorem original_factor_firstTail_proper
    (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (F0 Q:MvPolynomial (Fin 4) K) (hprod:S.F=F0*Q)
    (hGF0:S.G∣surfaceMap (polynomialEmbedding K) F0):
    ¬ F0∣numerator K F0 (w+1):=by
  intro hdiv
  let phi:=polynomialEmbedding K
  have hscaled:S.G∣surfaceMap phi
      (Q^(2*(w+1))*numerator K F0 (w+1)):=by
    exact hGF0.trans (map_dvd (surfaceMap phi)
      (dvd_mul_of_dvd_right hdiv (Q^(2*(w+1)))))
  have hdiff:S.G∣surfaceMap phi
      (numerator K (F0*Q) (w+1)-
        Q^(2*(w+1))*numerator K F0 (w+1)):=
    hGF0.trans (map_dvd (surfaceMap phi)
      (factor_dvd_numerator_sub_power F0 Q (w+1)))
  have hwhole:S.G∣surfaceMap phi (numerator K S.F (w+1)):=by
    rw [hprod]
    simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using
      dvd_add hdiff hscaled
  apply hfirstProper
  exact (globalTailCut_dvd_iff phi (polynomialEmbedding_injective K)
    S.F (w+1) S.G).mpr hwhole
theorem tangent_truncatedPolynomial_solution
    (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (C:FirstTailComponent S)
    (bound seedCap slopeCap:ℕ) (hw:1 ≤ w)
    (hshort:w+1 ≤ bound) (hchar:bound < p)
    (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
    (hallTails:∀ delay,
      globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1):
    specialization (CoordinateField (Omega K) C.1)
      (truncatedPolynomial (polynomialEmbedding K) C.1 S.F
        (firstTailComponent_surface_mem S C)
        (firstTailComponent_regularity_not_mem S C) w)
      (coordinate (Omega K) C.1 2)
      (MvPolynomial.map (componentCoefficients (polynomialEmbedding K) C.1) S.F)=0:=by
  let phi:=polynomialEmbedding K
  let Pcurve:=C.1
  let coefficients:=componentCoefficients phi Pcurve
  let v:=componentPoint phi Pcurve
  let hF:=firstTailComponent_surface_mem S C
  let hH:=firstTailComponent_regularity_not_mem S C
  let hrel:=component_relation phi Pcurve S.F hF
  let hreg:=component_regular phi Pcurve S.F hH
  letI:CharP (CoordinateField (Omega K) Pcurve) p:=
    charP_of_injective_algebraMap
      (algebraMap (Omega K) (CoordinateField (Omega K) Pcurve)).injective p
  apply global_polynomiality_of_all_tails coefficients S.F v hrel hreg
    p bound w seedCap slopeCap hw hshort hchar hbox
  apply (all_tail_numerators_iff_all_tail_jets coefficients S.F v hrel hreg
    p bound w hchar).mp
  intro j hj _
  have hjbase:w+1 ≤ j:=by omega
  have hT:=hallTails (j-(w+1))
  have heq:w+1+(j-(w+1))=j:=Nat.add_sub_of_le hjbase
  rw [heq] at hT
  have hN:surfaceMap phi (numerator K S.F j)∈Pcurve:=
    (globalTailCut_mem_iff phi (polynomialEmbedding_injective K)
      S.F j Pcurve).mp hT
  exact (component_evaluation_zero_iff phi Pcurve _).mpr hN
theorem coefficientPoleProfile_of_tangent_firstTail
    (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (C:FirstTailComponent S)
    (hfirstProper:¬ S.G∣
      globalTailCut (polynomialEmbedding K) S.F (w+1))
    (bound seedCap slopeCap cost:ℕ) (hw:1 ≤ w)
    (hshort:w+1 ≤ bound) (hchar:bound < p)
    (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
    (hallTails:∀ delay,
      globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1)
    (hyz:∀ W:Finset
      (CoordinatePoleMass.Place (Omega K) (CoordinateField (Omega K) C.1)),
      (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Omega K) C.1)
        (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
    CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
      (firstTailComponent_surface_mem S C)
      (firstTailComponent_regularity_not_mem S C) w cost:=by
  classical
  let phi:=polynomialEmbedding K
  let Pcurve:=C.1
  let L:=CoordinateField (Omega K) Pcurve
  let kappa:K →+*L:=componentCoefficients phi Pcurve
  let v0:Fin 4 → L:=componentPoint phi Pcurve
  let hFC:=firstTailComponent_surface_mem S C
  let hHC:=firstTailComponent_regularity_not_mem S C
  let P0:Polynomial L:=truncatedPolynomial phi Pcurve S.F hFC hHC w
  letI:CharP L p:=charP_of_injective_algebraMap
    (algebraMap (Omega K) L).injective p
  have hP0deg:P0.natDegree ≤ w:=
    truncatedPolynomial_natDegree_le phi Pcurve S.F hFC hHC w
  have hSsolution:specialization L P0 (v0 3)
      (MvPolynomial.map kappa S.F)=0:=
    tangent_truncatedPolynomial_solution S C bound seedCap slopeCap hw
      hshort hchar hbox hallTails
  obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hF0curve,hQnot,hH0not⟩:=
    exists_original_factor_of_firstTailComponent S C
  have hF0rel:MvPolynomial.eval₂Hom kappa v0 F0=0:=
    (component_evaluation_zero_iff phi Pcurve F0).mpr hF0curve
  have hF0regPoint:MvPolynomial.eval₂Hom kappa v0 (polyH K F0)≠0:=
    (component_evaluation_zero_iff phi Pcurve (polyH K F0)).not.mpr hH0not
  have hQeval:MvPolynomial.eval₂Hom kappa v0 Q≠0:=
    (component_evaluation_zero_iff phi Pcurve Q).not.mpr hQnot
  have hvpoint:polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0:=by
    funext i
    fin_cases i
    · rfl
    · exact truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
    · exact truncatedPolynomial_initial_slope phi Pcurve S.F hFC hHC w hw
    · rfl
  have hQsolution_ne:specialization L P0 (v0 3)
      (MvPolynomial.map kappa Q)≠0:=by
    intro hz
    apply hQeval
    calc
      MvPolynomial.eval₂Hom kappa v0 Q=
          MvPolynomial.eval₂Hom (RingHom.id L)
            (polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0))
            (MvPolynomial.map kappa Q):=by
        rw [hvpoint,MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp]
      _=(specialization L P0 (v0 3)
          (MvPolynomial.map kappa Q)).eval (v0 0):=by
        simpa using eval_polynomialPoint_eq_specialization
          (RingHom.id L) P0 (v0 3) (v0 0) (MvPolynomial.map kappa Q)
      _=0:=by rw [hz];simp
  have hF0solution:specialization L P0 (v0 3)
      (MvPolynomial.map kappa F0)=0:=by
    have hmul:specialization L P0 (v0 3) (MvPolynomial.map kappa F0)*
        specialization L P0 (v0 3) (MvPolynomial.map kappa Q)=0:=by
      simpa only [hprod,map_mul] using hSsolution
    exact (mul_eq_zero.mp hmul).resolve_right hQsolution_ne
  have hF0reg:specialization L P0 (v0 3)
      (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
    have hmapped:MvPolynomial.eval₂Hom (RingHom.id L) v0
        (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
      simpa only [polyH,MvPolynomial.pderiv_map,
        MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp] using hF0regPoint
    intro hz
    apply hmapped
    rw [←hvpoint,eval_polynomialPoint_eq_specialization,hz]
    simp
  have hTsolution:specialization L P0 (v0 3)
      (MvPolynomial.map kappa (numerator K F0 (w+1)))=0:=by
    rw [map_numerator]
    exact specialization_numerator_zero_of_degree L (MvPolynomial.map kappa F0)
      P0 (v0 3) hF0solution (w+1) (hP0deg.trans_lt (by omega))
  have hTproper:¬ F0∣numerator K F0 (w+1):=
    original_factor_firstTail_proper S hfirstProper F0 Q hprod hGF0
  have htrK:Algebra.trdeg K (baseCoefficientField (k:=K) P0 (v0 3)) ≤ 1:=
    baseCoefficientField_trdeg_le_one_of_fresh_proper_relations
      F0 (numerator K F0 (w+1)) P0 (v0 3)
      hF0irr hF0pos hTproper hF0solution hTsolution hF0reg
      p w S.characteristic_bound hP0deg
  let k:=algebraicClosure K (Omega K)
  have htrk:Algebra.trdeg k (baseCoefficientField (k:=k) P0 (v0 3)) ≤ 1:=
    baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
  letI:IsAlgClosed k:=IsAlgClosure.isAlgClosed K
  have hxK:Transcendental K (initialCoordinate K):=by
    rw [transcendental_iff_injective]
    intro f g hfg
    apply polynomialEmbedding_injective K
    change f.eval₂ (coefficientEmbedding K) (initialCoordinate K)=
      g.eval₂ (coefficientEmbedding K) (initialCoordinate K) at hfg
    rw [generic_eval_eq,generic_eval_eq] at hfg
    exact hfg
  have hxk:Transcendental k (initialCoordinate K):=hxK.algebraicClosure
  apply coefficientPoleProfile_of_unitYZ_bound phi Pcurve S.F hFC hHC w cost
  · intro place j
    apply coefficient_pole_le_of_trdeg_le_one P0 (v0 3) w hP0deg htrk
      (initialCoordinate K) hxk (coordinate (Omega K) Pcurve 0)
    exact truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
  · exact hyz
theorem tangent_component_card_le
    (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
    (C:FirstTailComponent S)
    (hfirstProper:¬ S.G∣
      globalTailCut (polynomialEmbedding K) S.F (w+1))
    (base:SeparableLiteralCoordinate C.1)
    (agreements bound seedCap slopeCap:ℕ)
    (hnodes:S.nodes.card=agreements+errors)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hwa:w < agreements) (hw:1 ≤ w)
    (hshort:w+1 ≤ bound) (hchar:bound < p)
    (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
    (B:PrimeFlagBudgetFamily
      (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w+1))
      (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
    (hyzPositive:1 ≤ B.yzCost C)
    (hallTails:∀ delay,
      globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1)
    (hyz:∀ W:Finset
      (CoordinatePoleMass.Place (Omega K) (CoordinateField (Omega K) C.1)),
      (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Omega K) C.1)
        (flagSupport unitYZFlag)) ≤ (B.yzCost C:ℤ)):
    (componentSeeds (Omega K) S.G
      (globalTailCut (polynomialEmbedding K) S.F (w+1))
      (regularitySurface (polynomialEmbedding K) S.F) Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
        (errors+1)*B.yzCost C:=by
  classical
  let T1:=globalTailCut (polynomialEmbedding K) S.F (w+1)
  let H:=regularitySurface (polynomialEmbedding K) S.F
  let Gc:=componentSeeds (Omega K) S.G T1 H Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C
  have hGcGamma:Gc ⊆ Gamma:=
    componentSeeds_subset (Omega K) S.G T1 H Gamma _ C
  have hprofile:=coefficientPoleProfile_of_tangent_firstTail
    S C hfirstProper bound seedCap slopeCap (B.yzCost C) hw hshort hchar
    hbox hallTails hyz
  apply prime_curve_card_le_of_coefficientPoleProfile
    (polynomialEmbedding K) C.1 S.F
    (firstTailComponent_surface_mem S C)
    (firstTailComponent_regularity_not_mem S C)
    base p w agreements errors (B.yzCost C)
    S.characteristic_bound hwa hyzPositive hprofile
    S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
  · intro gamma hgamma
    exact S.degree_le gamma (hGcGamma hgamma)
  · intro gamma hgamma
    exact S.solution gamma (hGcGamma hgamma)
  · intro gamma hgamma
    exact S.regular gamma (hGcGamma hgamma)
  · intro gamma hgamma
    exact componentSeeds_on_prime (Omega K) S.G T1 H Gamma
      (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
  · intro gamma hgamma
    have hGamma:=hGcGamma hgamma
    simpa only [ResidualStage.agreementFiber,ResidualStage.Agrees] using
      hagreement gamma hGamma
  · exact noLargeSelectedPencil_mono S.selected Gamma Gc w errors
      hGcGamma S.no_large_pencil
end
end ProximityPrize.SubmissionLower.ContactTangentCoefficientProvider6732Research
