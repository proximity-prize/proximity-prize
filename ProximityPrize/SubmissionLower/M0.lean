import ProximityPrize.SubmissionLower.C8
namespace ProximityPrize.SubmissionLower.ContactLocalizedResidueFinrank6733Research
open ActualPlaneCoordinateKernel ArbitraryPlaneEvaluationFamilyResearch
open ArbitraryRationalProjectionResearch
open ContactPlaneRelationCoefficientFiber6733Research
open ContactLocalizedPlaneRelation6733Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactLocalizedResidueDegree6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
variable (order:Fin 3 ≃ Fin 3)
variable (e:MvPolynomial (Fin 3) K →ₐ[K] L)
variable (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localized_residue_finrank_eq
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let q:=projectedFactor K L order e ht
   let J:=relationKernel K L order e ht
   let JP:=localizedRelation K L order e ht hfinite
   let a₀:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
   letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a₀
   letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a₀.toSMul
   let s₀:Semiring (PlaneRing K ⧸ J):=inferInstance
   letI:AddCommMonoid (PlaneRing K ⧸ J):=s₀.toAddCommMonoid
   letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
   let a₁:=localizedResidueAlgebra K L order e ht hfinite
   let Rp:=LocalCoefficient K L order e ht hfinite
   let Sp:=LocalizedPlane K L order e ht hfinite
   letI:Algebra (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁
   letI:SMul (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁.toSMul
   let r₁:CommRing (Rp ⧸ IsLocalRing.maximalIdeal Rp):=inferInstance
   letI:Semiring (Rp ⧸ IsLocalRing.maximalIdeal Rp):=r₁.toSemiring
   let s₁:Semiring (Sp ⧸ JP):=inferInstance
   letI:AddCommMonoid (Sp ⧸ JP):=s₁.toAddCommMonoid
   letI:Module (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=Algebra.toModule
   Module.finrank (AdjoinRoot q) (PlaneRing K ⧸ J)=
     Module.finrank (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=by
 let q:=projectedFactor K L order e ht
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let a₀:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (S ⧸ J):=a₀
 letI:SMul (AdjoinRoot q) (S ⧸ J):=a₀.toSMul
 let sr₀:Semiring (S ⧸ J):=inferInstance
 letI:AddCommMonoid (S ⧸ J):=sr₀.toAddCommMonoid
 letI:Module (AdjoinRoot q) (S ⧸ J):=Algebra.toModule
 let a₁:=localizedResidueAlgebra K L order e ht hfinite
 letI:Algebra (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁
 letI:SMul (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁.toSMul
 let r₁:CommRing (Rp ⧸ IsLocalRing.maximalIdeal Rp):=inferInstance
 letI:Semiring (Rp ⧸ IsLocalRing.maximalIdeal Rp):=r₁.toSemiring
 let sr₁:Semiring (Sp ⧸ JP):=inferInstance
 letI:AddCommMonoid (Sp ⧸ JP):=sr₁.toAddCommMonoid
 letI:Module (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=Algebra.toModule
 let i:=coefficientResidueEquiv K L order e ht hfinite
 let j:=planeResidueEquiv K L order e ht hfinite hgen
 apply Algebra.finrank_eq_of_equiv_equiv i j
 apply DFunLike.ext _ _
 intro x
 obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
 change Ideal.Quotient.mk JP
     (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
   Ideal.Quotient.mk JP
     (localizePlane K L order e ht hfinite (Polynomial.C x))
 apply congrArg (Ideal.Quotient.mk JP)
 change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
   Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
 rw [Polynomial.map_C]
end
end ProximityPrize.SubmissionLower.ContactLocalizedResidueFinrank6733Research
