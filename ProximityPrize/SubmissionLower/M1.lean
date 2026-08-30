import ProximityPrize.SubmissionLower.C8
namespace ProximityPrize.SubmissionLower.RCN195
open RCN011 RCN021
open RCN022
open RCN226
open RCN191
open RCN193
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
variable (order:Fin 3 ≃ Fin 3)
variable (e:MvPolynomial (Fin 3) K →ₐ[K] L)
variable (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localized_surface_residue_ne_zero
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (P₀:Polynomial (Polynomial (RatFunc K)))
   (hspecial:P₀.map
     (AdjoinRoot.mk (projectedFactor K L order e ht))≠0):
   (P₀.map (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))).map
       (IsLocalRing.residue (LocalCoefficient K L order e ht hfinite))≠0:=by
 let q:=projectedFactor K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let E:=Rp ⧸ IsLocalRing.maximalIdeal Rp
 let eqv:=coefficientResidueEquiv K L order e ht hfinite
 let source:Polynomial (AdjoinRoot q):=P₀.map (AdjoinRoot.mk q)
 let target:Polynomial E:=
   (P₀.map (algebraMap (Polynomial (RatFunc K)) Rp)).map
     (IsLocalRing.residue Rp)
 have hmap:source.map eqv.toRingHom=target:=by
   apply Polynomial.ext
   intro n
   simp only [source,target,Polynomial.coeff_map,Function.comp_apply]
   exact coefficientResidueEquiv_mk K L order e ht hfinite (P₀.coeff n)
 intro hzero
 apply hspecial
 apply (Polynomial.map_injective eqv.toRingHom eqv.injective)
 have htargetZero:target=0:=hzero
 rw [hmap,htargetZero,Polynomial.map_zero]
end
end ProximityPrize.SubmissionLower.RCN195
