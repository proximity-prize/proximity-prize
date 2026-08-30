import ProximityPrize.SubmissionLower.ContactLocalizedPlaneRelation6733Research
import ProximityPrize.SubmissionLower.ContactFlagResidueDegreeCostAdapter6732Research
namespace ProximityPrize.SubmissionLower.ContactLocalizedResidueDegree6733Research
open ActualPlaneCoordinateKernel ArbitraryPlaneEvaluationFamilyResearch
open ArbitraryRationalProjectionResearch
open ContactPlaneRelationCoefficientFiber6733Research
open ContactLocalizedPlaneRelation6733Research
open ContactFlagResidueDegreeCostAdapter6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
variable (order:Fin 3 ≃ Fin 3)
variable (e:MvPolynomial (Fin 3) K →ₐ[K] L)
variable (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_under
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L):
    (localizedRelation K L order e ht hfinite).comap
      (localizePlane K L order e ht hfinite)=
      relationKernel K L order e ht:=by
  let p:=CoeffPrime K L order e ht
  let Rp:=LocalCoefficient K L order e ht hfinite
  let J:=relationKernel K L order e ht
  let f:=localizePlane K L order e ht hfinite
  let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
  have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
  letI:p.IsPrime:=hpmax.isPrime
  letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
  letI:IsLocalization p.primeCompl Rp:=inferInstance
  letI:Algebra (PlaneRing K) (Polynomial Rp):=
    Polynomial.algebra (Polynomial (RatFunc K)) Rp
  letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
      (Polynomial Rp):=Polynomial.isLocalization p.primeCompl Rp
  have hJprime:J.IsPrime:=RingHom.ker_isPrime _
  have hdisjoint:Disjoint
      ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K)) (J:Set (PlaneRing K)):=by
    rw [Set.disjoint_left]
    intro a ha haJ
    obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
    apply hr
    have hrJ:r∈J.comap c:=haJ
    have hcomap:J.comap c=p:=by
      simpa only [J,c,p] using relationKernel_comap_C K L order e ht
    rwa [hcomap] at hrJ
  change (Ideal.map f J).comap f=J
  change (Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).comap
    (algebraMap (PlaneRing K) (Polynomial Rp))=J
  exact IsLocalization.under_map_of_isPrime_disjoint
    (p.primeCompl.map c.toMonoidHom) (Polynomial Rp) hJprime hdisjoint
noncomputable def planeResidueEquiv
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hgen:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
    (PlaneRing K ⧸ relationKernel K L order e ht) ≃+*
      (LocalizedPlane K L order e ht hfinite ⧸
        localizedRelation K L order e ht hfinite):=by
  let p:=CoeffPrime K L order e ht
  let Rp:=LocalCoefficient K L order e ht hfinite
  let S:=PlaneRing K
  let Sp:=LocalizedPlane K L order e ht hfinite
  let J:=relationKernel K L order e ht
  let JP:=localizedRelation K L order e ht hfinite
  let f:=localizePlane K L order e ht hfinite
  let c:Polynomial (RatFunc K) →+*S:=Polynomial.C
  have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
  letI:p.IsPrime:=hpmax.isPrime
  have hJmax:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
  letI:J.IsPrime:=hJmax.isPrime
  have hJPmax:JP.IsMaximal:=localizedRelation_isMaximal
    K L order e ht hfinite hgen
  letI:JP.IsPrime:=hJPmax.isPrime
  letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
  letI:IsLocalization p.primeCompl Rp:=inferInstance
  letI:Algebra S Sp:=Polynomial.algebra (Polynomial (RatFunc K)) Rp
  letI:IsLocalization (p.primeCompl.map c.toMonoidHom) Sp:=
    Polynomial.isLocalization p.primeCompl Rp
  have hunder:JP.comap f=J:=localizedRelation_under K L order e ht hfinite
  have hf:f=algebraMap S Sp:=rfl
  have hunderAlg:JP.under S=J:=by
    change JP.comap (algebraMap S Sp)=J
    rw [←hf]
    exact hunder
  let g:(S ⧸ J) →+*(Sp ⧸ JP):=
    Ideal.quotientMap JP (algebraMap S Sp) hunderAlg.ge
  refine RingEquiv.ofBijective g ⟨?_,?_⟩
  · exact Ideal.quotientMap_injective' hunderAlg.le
  · exact IsLocalization.surjective_quotientMap_of_maximal_of_localization
      (p.primeCompl.map c.toMonoidHom) Sp (J:=J) (I:=JP)
        (H:=hunderAlg.ge) (hunderAlg ▸ hJmax)
@[simp] theorem planeResidueEquiv_mk
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (hgen:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      IntermediateField.adjoin (RatFunc K)
        ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤)
    (x:PlaneRing K):
    planeResidueEquiv K L order e ht hfinite hgen
        (Ideal.Quotient.mk (relationKernel K L order e ht) x)=
      Ideal.Quotient.mk (localizedRelation K L order e ht hfinite)
        (localizePlane K L order e ht hfinite x):=rfl
theorem maximalIdeal_le_localizedRelation_comap_C
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L):
    IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite) ≤
      (localizedRelation K L order e ht hfinite).comap Polynomial.C:=by
  let C:=Polynomial (RatFunc K)
  let p:=CoeffPrime K L order e ht
  let Rp:=LocalCoefficient K L order e ht hfinite
  let S:=PlaneRing K
  let Sp:=LocalizedPlane K L order e ht hfinite
  let J:=relationKernel K L order e ht
  let JP:=localizedRelation K L order e ht hfinite
  let a:C →+*Rp:=algebraMap C Rp
  let c:C →+*S:=Polynomial.C
  let cL:Rp →+*Sp:=Polynomial.C
  let f:S →+*Sp:=localizePlane K L order e ht hfinite
  have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
  letI:p.IsPrime:=hpmax.isPrime
  letI:Algebra C Rp:=inferInstance
  letI:IsLocalization p.primeCompl Rp:=inferInstance
  have hcontract:J.comap c=p:=by
    simpa only [J,c,p] using relationKernel_comap_C K L order e ht
  have hsquare:cL.comp a=f.comp c:=by
    apply DFunLike.ext _ _
    intro x
    change Polynomial.C (a x)=Polynomial.map a (Polynomial.C x)
    rw [Polynomial.map_C]
  rw [←IsLocalization.AtPrime.map_eq_maximalIdeal p Rp,
    ←Ideal.map_le_iff_le_comap]
  calc
    Ideal.map cL (Ideal.map a p)=Ideal.map (cL.comp a) p:=
      Ideal.map_map a cL
    _=Ideal.map (f.comp c) p:=by
      rw [hsquare]
    _=Ideal.map f (Ideal.map c p):=(Ideal.map_map c f).symm
    _ ≤ Ideal.map f J:=Ideal.map_mono
      (Ideal.map_le_iff_le_comap.mpr hcontract.ge)
    _=JP:=rfl
@[reducible] def localizedResidueAlgebra
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L):
    Algebra
      (LocalCoefficient K L order e ht hfinite ⧸
        IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
      (LocalizedPlane K L order e ht hfinite ⧸
        localizedRelation K L order e ht hfinite):=
  Ideal.Quotient.algebraQuotientOfLEComap
    (maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite)
noncomputable def coefficientResidueEquiv
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L):
    AdjoinRoot (projectedFactor K L order e ht) ≃+*
      (LocalCoefficient K L order e ht hfinite ⧸
        IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite)):=by
  let p:=CoeffPrime K L order e ht
  let Rp:=LocalCoefficient K L order e ht hfinite
  letI:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
  change (Polynomial (RatFunc K) ⧸ p) ≃+*
    (Rp ⧸ IsLocalRing.maximalIdeal Rp)
  exact IsLocalization.AtPrime.equivQuotMaximalIdeal p Rp
@[simp] theorem coefficientResidueEquiv_mk
    (hfinite:
      letI:Algebra (RatFunc K) L:=
        (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
      FiniteDimensional (RatFunc K) L)
    (x:Polynomial (RatFunc K)):
    coefficientResidueEquiv K L order e ht hfinite
        (AdjoinRoot.mk (projectedFactor K L order e ht) x)=
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
        (algebraMap (Polynomial (RatFunc K))
          (LocalCoefficient K L order e ht hfinite) x):=rfl
end
end ProximityPrize.SubmissionLower.ContactLocalizedResidueDegree6733Research
