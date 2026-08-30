import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.L
namespace ProximityPrize.SubmissionLower.ActualCurveRationalProjection
open ActualCurveCoordinateField
noncomputable section
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def rationalBaseEmbedding (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   RatFunc K →ₐ[K] CoordinateField K P:=
 RatFunc.liftAlgHom (Polynomial.aeval (coordinate K P i))
   (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
     (Polynomial.aeval (coordinate K P i)).toRingHom
     (transcendental_iff_injective.mp hi))
theorem rationalBaseEmbedding_injective (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   Function.Injective (rationalBaseEmbedding K P i hi):=
 (rationalBaseEmbedding K P i hi).injective
theorem rationalBaseEmbedding_polynomial (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)) (f:Polynomial K):
   rationalBaseEmbedding K P i hi (algebraMap (Polynomial K) (RatFunc K) f)=
     Polynomial.aeval (coordinate K P i) f:=by
 exact RatFunc.liftRingHom_algebraMap _ _ f
abbrev rationalBaseAlgebra (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   Algebra (RatFunc K) (CoordinateField K P):=
 (rationalBaseEmbedding K P i hi).toRingHom.toAlgebra
theorem rationalBaseScalarTower (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IsScalarTower K (RatFunc K) (CoordinateField K P):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 exact IsScalarTower.of_algebraMap_eq fun c =>
   ((rationalBaseEmbedding K P i hi).commutes c).symm
theorem rational_variable_image (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   algebraMap (RatFunc K) (CoordinateField K P)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=coordinate K P i:=by
 change rationalBaseEmbedding K P i hi
   (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=coordinate K P i
 rw [rationalBaseEmbedding_polynomial,Polynomial.aeval_X]
theorem adjoin_two_coordinates_over_ratFunc_eq_top
   (i j k:Fin 3) (hi:Transcendental K (coordinate K P i))
   (hcover:∀ l:Fin 3,l=i∨l=j∨l=k):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   IntermediateField.adjoin (RatFunc K)
     ({coordinate K P j,coordinate K P k}:Set (CoordinateField K P))=⊤:=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
 letI:IsScalarTower K (RatFunc K) (CoordinateField K P):=
   rationalBaseScalarTower K P i hi
 let S:IntermediateField (RatFunc K) (CoordinateField K P):=
   IntermediateField.adjoin (RatFunc K) {coordinate K P j,coordinate K P k}
 have hcoords:Set.range (coordinate K P) ⊆ S.restrictScalars K:=by
   rintro x ⟨l,rfl⟩
   rcases hcover l with hl | hl | hl
   · subst l
     have hmem:=S.algebraMap_mem
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
     rw [rational_variable_image K P i hi] at hmem
     exact hmem
   · subst l
     exact IntermediateField.mem_adjoin_pair_left (RatFunc K)
       (coordinate K P j) (coordinate K P k)
   · subst l
     exact IntermediateField.mem_adjoin_pair_right (RatFunc K)
       (coordinate K P j) (coordinate K P k)
 have htop:S.restrictScalars K=⊤:=by
   apply top_unique
   rw [←adjoin_coordinates_eq_top K P]
   exact IntermediateField.adjoin_le_iff.mpr hcoords
 exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
theorem exists_complementary_coordinates (i:Fin 3):
   ∃ j k:Fin 3,j≠i∧k≠i∧j≠k∧
     ∀ l:Fin 3,l=i∨l=j∨l=k:=by
 fin_cases i <;> decide
theorem exists_two_generators_over_ratFunc (i:Fin 3)
   (hi:Transcendental K (coordinate K P i)):
   letI:Algebra (RatFunc K) (CoordinateField K P):=rationalBaseAlgebra K P i hi
   ∃ j k:Fin 3,j≠i∧k≠i∧j≠k∧
     IntermediateField.adjoin (RatFunc K)
       ({coordinate K P j,coordinate K P k}:Set (CoordinateField K P))=⊤:=by
 obtain ⟨j,k,hji,hki,hjk,hcover⟩:=exists_complementary_coordinates i
 exact ⟨j,k,hji,hki,hjk,
   adjoin_two_coordinates_over_ratFunc_eq_top K P i j k hi hcover⟩
end
end ProximityPrize.SubmissionLower.ActualCurveRationalProjection
