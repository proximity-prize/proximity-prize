import ProximityPrize.SubmissionLower.M0
import ProximityPrize.SubmissionLower.C9
namespace ProximityPrize.SubmissionLower.RCN192
open RCN011 RCN021
open RCN022
open RCN226
open RCN191
open RCN193
open RCN120
open RCN014
open RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
variable (order:Fin 3 ≃ Fin 3)
variable (e:MvPolynomial (Fin 3) K →ₐ[K] L)
variable (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_comap_C_eq_maximalIdeal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (localizedRelation K L order e ht hfinite).comap Polynomial.C=
     IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite):=by
 apply le_antisymm
 · apply IsLocalRing.le_maximalIdeal
   apply Ideal.comap_ne_top
   intro htop
   have hunder:=localizedRelation_under K L order e ht hfinite
   have hJne:relationKernel K L order e ht≠⊤:=RingHom.ker_ne_top _
   apply hJne
   rw [←hunder,htop,Ideal.comap_top]
 · exact maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite
theorem localizedRelationResidue_finite
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=
     targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   FiniteDimensional (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=by
 let F:=RatFunc K
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:Algebra F L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional F L:=hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let quotientSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=quotientSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 let phi:PlaneRing K →ₐ[F] L:={
   toRingHom:=planeEvaluation K L order e ht
   commutes':=fun a => by
     change planeEvaluation K L order e ht
       (Polynomial.C (Polynomial.C a))=algebraMap F L a
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
 let eqv0:(PlaneRing K ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing K ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 letI:Module.Finite F (PlaneRing K ⧸ J):=
   Module.Finite.equiv eqv0.toLinearEquiv.symm
 letI:IsScalarTower F (AdjoinRoot q) (PlaneRing K ⧸ J):=
   IsScalarTower.of_algebraMap_eq fun c => by
     change Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))=
       Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))
     rfl
 letI:Module.Finite (AdjoinRoot q) (PlaneRing K ⧸ J):=
   Module.Finite.of_restrictScalars_finite F _ _
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 refine Module.Finite.of_equiv_equiv
   (A₁:=AdjoinRoot q) (B₁:=PlaneRing K ⧸ J)
   (A₂:=IsLocalRing.ResidueField Rp)
   (B₂:=LocalizedPlane K L order e ht hfinite ⧸ JP) e1 e2 ?_
 apply RingHom.ext
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
theorem localizedRelationResidue_finrank_eq_unlocalized
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
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
   letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
   letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
   let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
   letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
   letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
   let a1:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   Module.finrank (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP)=
     Module.finrank (AdjoinRoot q) (PlaneRing K ⧸ J):=by
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 have hcompat:(algebraMap (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP)).comp e1.toRingHom=
     e2.toRingHom.comp (algebraMap (AdjoinRoot q) (PlaneRing K ⧸ J)):=by
   apply RingHom.ext
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
 exact (Algebra.finrank_eq_of_equiv_equiv e1 e2 hcompat).symm
end
end ProximityPrize.SubmissionLower.RCN192
