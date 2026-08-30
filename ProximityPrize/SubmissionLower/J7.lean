import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Y8
namespace ProximityPrize.SubmissionLower.ContactFlagDirectionalAvoidance6543Research
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain
open ArbitraryRationalProjectionResearch GlobalSeparableShearResearch
open CoordinateBoxZeroCount ContactSparsePoleSupportResearch
open ContactDependentGenericity6543Research
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ContactRegularComponentCover
open ContactFlagAffineFamilyDegree6543Research
open ContactFlagExactSeparableProjection6543Research
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem directional_bad_coefficient_subsingleton
   {K:Type*} [Field K] (G:MvPolynomial (Fin 3) K)
   (hS:MvPolynomial.pderiv (1:Fin 3) G≠0):
   ∀ {a b:K},
     MvPolynomial.pderiv (0:Fin 3) G-
         MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G=0 →
     MvPolynomial.pderiv (0:Fin 3) G-
         MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G=0 →
     a=b:=by
 intro a b ha hb
 have ha':MvPolynomial.pderiv (0:Fin 3) G=
     MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G:=
   sub_eq_zero.mp ha
 have hb':MvPolynomial.pderiv (0:Fin 3) G=
     MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G:=
   sub_eq_zero.mp hb
 have habmul:MvPolynomial.C a*MvPolynomial.pderiv (1:Fin 3) G=
     MvPolynomial.C b*MvPolynomial.pderiv (1:Fin 3) G:=
   ha'.symm.trans hb'
 have hfactor:(MvPolynomial.C a-MvPolynomial.C b)*
     MvPolynomial.pderiv (1:Fin 3) G=0:=by
   rw [sub_mul,habmul,sub_self]
 have hCsub:MvPolynomial.C a-MvPolynomial.C b=0:=
   (mul_eq_zero.mp hfactor).resolve_right hS
 apply MvPolynomial.C_injective
 exact sub_eq_zero.mp hCsub
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
variable {I:Type*} [Fintype I]
variable (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
variable (r z:∀ i,E i)
variable (W:∀ i,
 Finset (CoordinatePlaceClassification.NormalizedValuation K (E i)))
theorem exists_common_exact_finite_separable_shear_avoiding
   {J:Type*} [Finite J]
   (Extra:J → K → Prop)
   (hextra:∀ j {a b},Extra j a → Extra j b → a=b)
   (embeddingZ:∀ i,RatFunc K →ₐ[K] E i)
   (hvalueZ:∀ i,embeddingZ i
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=z i)
   (hfiniteZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (E i))
   (hsepZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) (E i)):
   ∃ a:K,a≠0∧(∀ j,¬ Extra j a)∧∀ i,
     ∃ hs:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 have hdz:∀ i,D K (E i) (z i)≠0:=by
   intro i
   have h:=parameterDifferential_ne_zero_of_isSeparable
     K (E i) (embeddingZ i) (hfiniteZ i) (hsepZ i)
   unfold SeparableShearKaehlerResearch.parameterDifferential at h
   rwa [hvalueZ i] at h
 let Q:=J ⊕ (I ⊕ Σ i:I,{v//v∈W i})
 let Bad:Q → K → Prop
   | Sum.inl j,a => Extra j a
   | Sum.inr (Sum.inl i),a =>
       D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr (Sum.inr iv),a =>
       iv.2.1.val (r iv.1+a • z iv.1) <
         max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ q {a b},Bad q a → Bad q b → a=b:=by
   intro q a b ha hb
   rcases q with j | i | ⟨i,v⟩
   · exact hextra j ha hb
   · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
       (hdz i) ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton Bad hsingle
 refine ⟨a,ha0,?_,fun i↦?_⟩
 · intro j
   exact havoid (Sum.inl j)
 · have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
     exact havoid (Sum.inr (Sum.inl i))
   obtain ⟨hs,hfinite,hsep⟩:=
     shear_transcendental_finite_separable_of_differential_ne_zero
       K (E i) (embeddingZ i) (r i) (z i) a
         (hvalueZ i) (hfiniteZ i) (hsepZ i) hdiff
   refine ⟨hs,hfinite,hsep,?_⟩
   intro v hv
   have hnotlt:=havoid (Sum.inr (Sum.inr ⟨i,⟨v,hv⟩⟩))
   have hupper:=v.val.map_add (r i) (a • z i)
   have haz:v.val (a • z i)=v.val (z i):=by
     letI:v.val.IsTrivialOn K:=v.property.2
     rw [Algebra.smul_def,map_mul,
       Valuation.IsTrivialOn.eq_one a ha0,one_mul]
   rw [haz] at hupper
   exact le_antisymm hupper (le_of_not_gt hnotlt)
end FiniteFamily
section RegularComponents
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H:MvPolynomial (Fin 3) Omega}
end RegularComponents
end
end ProximityPrize.SubmissionLower.ContactFlagDirectionalAvoidance6543Research
