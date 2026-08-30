import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Z
import ProximityPrize.SubmissionLower.AQ
namespace ProximityPrize.SubmissionLower.RCN022
open scoped Classical
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
def elementEmbedding (s:L) (hs:Transcendental K s):RatFunc K →ₐ[K] L:=
 RatFunc.liftAlgHom (Polynomial.aeval s)
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
     (Polynomial.aeval s).toRingHom (transcendental_iff_injective.mp hs))
theorem elementEmbedding_variable (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s:=by
 change RatFunc.liftAlgHom (Polynomial.aeval s) _
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=s
 calc
   _=Polynomial.aeval s Polynomial.X:=
     RatFunc.liftRingHom_algebraMap _ _ Polynomial.X
   _=s:=Polynomial.aeval_X s
theorem elementEmbedding_eq_adjoin_comp (s:L) (hs:Transcendental K s):
   elementEmbedding K L s hs=
     (IntermediateField.adjoin K ({s}:Set L)).val.comp
       (RatFunc.algEquivOfTranscendental s hs).toAlgHom:=by
 apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
 ext
 change elementEmbedding K L s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=
   ((RatFunc.algEquivOfTranscendental s hs
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X):
       IntermediateField.adjoin K ({s}:Set L)):L)
 rw [elementEmbedding_variable]
 simp
theorem finiteDimensional_elementEmbedding
   (base:RatFunc K →ₐ[K] L)
   (hfinite:
     letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (s:L) (hs:Transcendental K s):
   letI:Algebra (RatFunc K) L:=
     (elementEmbedding K L s hs).toRingHom.toAlgebra
   FiniteDimensional (RatFunc K) L:=by
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 have hadjoin:FiniteDimensional (IntermediateField.adjoin K ({s}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental hs
 let e:RatFunc K ≃ₐ[K] (IntermediateField.adjoin K ({s}:Set L)):=
   RatFunc.algEquivOfTranscendental s hs
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L s hs).toRingHom.toAlgebra
 have hsmul:∀ (c:IntermediateField.adjoin K ({s}:Set L)) (x:L),
     e.symm c • x=c • x:=by
   intro c x
   rw [Algebra.smul_def,Algebra.smul_def]
   change elementEmbedding K L s hs (e.symm c)*x=(c:L)*x
   rw [elementEmbedding_eq_adjoin_comp]
   simp [e]
 let b:=Module.finBasis (IntermediateField.adjoin K ({s}:Set L)) L
 exact (b.mapCoeffs e.symm hsmul).finiteDimensional_of_finite
end
end ProximityPrize.SubmissionLower.RCN022
