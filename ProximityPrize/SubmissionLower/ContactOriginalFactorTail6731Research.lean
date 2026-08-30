import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactGeometricFactorCover
import ProximityPrize.SubmissionLower.ContactNumeratorFactorScaling6731Research
import ProximityPrize.SubmissionLower.ContactAgreementFactorScaling6731Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualIterationResearch
namespace ProximityPrize.SubmissionLower.ContactOriginalFactorTail6731Research
open ContactGenericSurface ContactGenericInitialPoint ContactGeometricFirstTail
open ContactGeometricFactorCover ContactFactorCover GeometricFactorContraction
open ContactTaylorNumerators ContactIdentityResidualIterationResearch
open ContactNumeratorFactorScaling6731Research ActualCurveCoordinateField
open ContactAgreementFactorScaling6731Research
open ContactFlagBezout6543Research ContactResidualSupportParametersResearch
open ContactComponentPencils
noncomputable section
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
theorem exists_original_factor_with_first_tail
    {Γ:Finset K} {x:I → K} {p e:ℕ} [CharP (Ω K) p]
    {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
    (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
    (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1))):
    ∃ F0 Q:MvPolynomial (Fin 4) K,
      Irreducible F0∧0 < F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
      S.F=F0*Q∧S.G∣surfaceMap (polynomialEmbedding K) F0∧
      ¬ S.G∣surfaceMap (polynomialEmbedding K) Q∧
      ¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0)∧
      F0∣numerator K F0 (w+1):=by
  classical
  let P:=S.componentIdeal
  letI:P.IsPrime:=S.componentIdeal_isPrime
  have hFne:S.F≠0:=by
    intro hzero
    apply S.regular_proper
    rw [hzero]
    simp [polyH]
  let φC:Polynomial K →+*CoordinateField (Ω K) P:=
    (algebraMap (Ω K) (CoordinateField (Ω K) P)).comp (polynomialEmbedding K)
  let vC:Fin 3 → CoordinateField (Ω K) P:=
    fun i => componentPoint (polynomialEmbedding K) P i.succ
  have hsurfaceZero:MvPolynomial.eval vC (surfaceMap φC S.F)=0:=by
    rw [eval_surfaceMap]
    change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
      (componentPoint (polynomialEmbedding K) P) S.F=0
    rw [component_evaluation]
    rw [coordinateEvaluation_eq_aeval,aeval_coordinate_eq_quotient,
      Ideal.Quotient.eq_zero_iff_mem.mpr S.surface_mem_componentIdeal,map_zero]
  have hφC:Function.Injective φC:=
    (algebraMap (Ω K) (CoordinateField (Ω K) P)).injective.comp
      (polynomialEmbedding_injective K)
  obtain ⟨F0,hF0mem,hF0zero⟩:=exists_active_factor_of_surface_zero
    φC hφC S.F hFne vC hsurfaceZero
  have hF0spec:=activeFactors_spec S.F F0 hF0mem
  have hmapF0mem:surfaceMap (polynomialEmbedding K) F0∈P:=by
    rw [←coordinateEvaluation_ker (Ω K) P]
    rw [eval_surfaceMap] at hF0zero
    change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
      (componentPoint (polynomialEmbedding K) P) F0=0 at hF0zero
    rw [component_evaluation] at hF0zero
    exact hF0zero
  have hGdivF0:S.G∣surfaceMap (polynomialEmbedding K) F0:=
    Ideal.mem_span_singleton.mp hmapF0mem
  obtain ⟨Q,hprod⟩:=hF0spec.2.1
  have hQnot:¬ S.G∣surfaceMap (polynomialEmbedding K) Q:=by
    intro hGQ
    apply S.regular_proper
    rw [hprod,MvPolynomial.pderiv_mul]
    simp only [map_add,map_mul]
    exact dvd_add (dvd_mul_of_dvd_right hGQ _) (dvd_mul_of_dvd_left hGdivF0 _)
  have hH0not:¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0):=by
    intro hGH
    apply S.regular_proper
    rw [hprod,MvPolynomial.pderiv_mul]
    simp only [polyH,map_add,map_mul]
    exact dvd_add (dvd_mul_of_dvd_left hGH _) (dvd_mul_of_dvd_left hGdivF0 _)
  have hscale:=factor_dvd_numerator_sub_power F0 Q (w+1)
  have hdiff:S.G∣surfaceMap (polynomialEmbedding K)
      (numerator K (F0*Q) (w+1)-Q^(2*(w+1))*numerator K F0 (w+1)):=
    hGdivF0.trans (map_dvd (surfaceMap (polynomialEmbedding K)) hscale)
  have htail':S.G∣surfaceMap (polynomialEmbedding K) (numerator K (F0*Q) (w+1)):=by
    simpa only [hprod] using hTail
  have hmul:S.G∣surfaceMap (polynomialEmbedding K)
      (Q^(2*(w+1))*numerator K F0 (w+1)):=by
    simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using dvd_sub htail' hdiff
  have hfactor:S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))∨
      S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
    have hmul':S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))*
        surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
      rw [map_mul,map_pow] at hmul
      exact hmul
    exact S.irreducible_G.prime.dvd_or_dvd hmul'
  have hnum:S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
    rcases hfactor with hpow | hnum
    · exact False.elim (hQnot (Prime.dvd_of_dvd_pow S.irreducible_G.prime
        (by simpa only [map_pow] using hpow)))
    · exact hnum
  have hbase:F0∣numerator K F0 (w+1):=
    (geometric_factor_dvd_iff K (Ω K) F0 (numerator K F0 (w+1))
      hF0spec.1 hF0spec.2.2 S.G S.irreducible_G
      (by simpa only [canonical_geometricSurfaceMap] using hGdivF0)).mp
      (by simpa only [canonical_geometricSurfaceMap] using hnum)
  exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGdivF0,hQnot,hH0not,hbase⟩
theorem original_factor_agreement_proper
    (φ:Polynomial K →+*Ω K) (F0 Q:MvPolynomial (Fin 4) K)
    (G:MvPolynomial (Fin 3) (Ω K))
    (hGdivF0:G∣surfaceMap φ F0)
    (w:ℕ) (c:ℕ → K) (x0 u0 u1:K)
    (hproper:¬G∣surfaceMap φ (agreementNumerator (F0*Q) w c x0 u0 u1)):
    ¬F0∣agreementNumerator F0 w c x0 u0 u1:=by
  intro hF0cut
  have hcut:G∣surfaceMap φ (agreementNumerator F0 w c x0 u0 u1):=
    hGdivF0.trans (map_dvd (surfaceMap φ) hF0cut)
  have hscaled:G∣surfaceMap φ
      (Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=by
    have h:=dvd_mul_of_dvd_right hcut (surfaceMap φ Q^(2*w))
    simpa only [map_mul,map_pow,mul_comm] using h
  have hdiff:G∣surfaceMap φ
      (agreementNumerator (F0*Q) w c x0 u0 u1-
        Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=
    hGdivF0.trans (map_dvd (surfaceMap φ)
      (factor_dvd_agreement_sub_power F0 Q w c x0 u0 u1))
  apply hproper
  simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using dvd_add hdiff hscaled
end
end ProximityPrize.SubmissionLower.ContactOriginalFactorTail6731Research
