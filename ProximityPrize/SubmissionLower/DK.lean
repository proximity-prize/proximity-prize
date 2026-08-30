import ProximityPrize.SubmissionLower.Y1
namespace ProximityPrize.SubmissionLower.RCN032
open scoped Classical BigOperators
open RCN042
open RCN344 RCN022
noncomputable section
set_option autoImplicit false
theorem sum_mul_eq_active_subtype
   {I:Type*} [Fintype I]
   (active:I → Prop) [DecidablePred active]
   (multiplicity cost:I → ℕ)
   (hzero:∀ i,¬ active i → cost i=0):
   (∑ i,multiplicity i*cost i)=
     ∑ i:{i//active i},multiplicity i.1*cost i.1:=by
 let f:I → ℕ:=fun i↦multiplicity i*cost i
 calc
   (∑ i,multiplicity i*cost i)=
       ∑ i∈(Finset.univ.filter active),f i:=by
     symm
     apply Finset.sum_subset (Finset.filter_subset active Finset.univ)
     intro i _ hi
     have hnot:¬ active i:=by simpa using hi
     simp [f,hzero i hnot]
   _=∑ i:{i//active i},multiplicity i.1*cost i.1:=by
     simpa only [f,Finset.subtype_univ] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset I)) f (p:=active)).symm
theorem sum_mul_coordinateOfGate_eq_active
   {K:Type} [Field K] [IsAlgClosed K]
   {I:Type*} [Fintype I]
   (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
   (x:∀ i,E i)
   (hgate:∀ i,∀ hx:Transcendental K (x i),
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc K) (E i))∧
     (letI:Algebra (RatFunc K) (E i):=
         (elementEmbedding K (E i) (x i) hx).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc K) (E i)))
   (multiplicity:I → ℕ):
   (∑ i,multiplicity i*coordinateDegree K (E i)
     (coordinateOfGate (K:=K) (L:=E i) (x i) (hgate i)))=
   ∑ i:{i//Transcendental K (x i)},
     multiplicity i.1*coordinateDegree K (E i.1)
       (coordinateOfGate (K:=K) (L:=E i.1) (x i.1) (hgate i.1)):=by
 classical
 apply sum_mul_eq_active_subtype
 intro i hi
 change ¬¬ IsAlgebraic K (x i) at hi
 exact coordinateOfGate_degree_of_isAlgebraic
   (K:=K) (L:=E i) (x i) (hgate i) (not_not.mp hi)
end
end ProximityPrize.SubmissionLower.RCN032
