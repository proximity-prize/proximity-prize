import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.RCN002
noncomputable section
abbrev CoordinateRing (K:Type) [Field K]
   (P:Ideal (MvPolynomial (Fin 3) K)):=MvPolynomial (Fin 3) K ⧸ P
abbrev CoordinateField (K:Type) [Field K]
   (P:Ideal (MvPolynomial (Fin 3) K)):=FractionRing (CoordinateRing K P)
variable (K:Type) [Field K] (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
def coordinateEvaluation:MvPolynomial (Fin 3) K →ₐ[K] CoordinateField K P:=
 (IsScalarTower.toAlgHom K (CoordinateRing K P) (CoordinateField K P)).comp
   (Ideal.Quotient.mkₐ K P)
def coordinate (i:Fin 3):CoordinateField K P:=
 coordinateEvaluation K P (MvPolynomial.X i)
theorem coordinateEvaluation_eq_aeval:
   coordinateEvaluation K P=MvPolynomial.aeval (coordinate K P):=
 MvPolynomial.aeval_unique (coordinateEvaluation K P)
theorem aeval_coordinate_eq_quotient (f:MvPolynomial (Fin 3) K):
   MvPolynomial.aeval (coordinate K P) f=
     algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P f):=by
 rw [←coordinateEvaluation_eq_aeval]
 rfl
theorem coordinateEvaluation_ker:
   RingHom.ker (coordinateEvaluation K P).toRingHom=P:=by
 change RingHom.ker ((algebraMap (CoordinateRing K P) (CoordinateField K P)).comp
   (Ideal.Quotient.mk P))=P
 rw [RingHom.ker_comp_of_injective _
   (IsFractionRing.injective (CoordinateRing K P) (CoordinateField K P)),Ideal.mk_ker]
theorem aeval_coordinate_ker:
   RingHom.ker (MvPolynomial.aeval (coordinate K P)).toRingHom=P:=by
 rw [←coordinateEvaluation_eq_aeval]
 exact coordinateEvaluation_ker K P
theorem adjoin_coordinates_eq_top:
   IntermediateField.adjoin K (Set.range (coordinate K P))=⊤:=by
 apply top_unique
 intro x _
 obtain ⟨a,b,_,hab⟩:=
   IsFractionRing.div_surjective (CoordinateRing K P) x
 obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective a
 obtain ⟨g,rfl⟩:=Ideal.Quotient.mk_surjective b
 apply (IntermediateField.mem_adjoin_range_iff K (coordinate K P) x).mpr
 refine ⟨f,g,?_⟩
 rw [aeval_coordinate_eq_quotient,aeval_coordinate_eq_quotient]
 exact hab.symm
section AlgebraicallyClosed
variable [IsAlgClosed K]
theorem coordinate_eq_scalar_of_isAlgebraic (i:Fin 3)
   (h:IsAlgebraic K (coordinate K P i)):
   ∃ c:K,algebraMap K (CoordinateField K P) c=coordinate K P i:=by
 let S:IntermediateField K (CoordinateField K P):=
   IntermediateField.adjoin K {coordinate K P i}
 letI:Algebra.IsAlgebraic K S:=
   IntermediateField.isAlgebraic_adjoin_simple h.isIntegral
 obtain ⟨c,hc⟩:=
   (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=K) (K:=S)).2
     (⟨coordinate K P i,IntermediateField.mem_adjoin_simple_self K _⟩:S)
 refine ⟨c,?_⟩
 have hcast:=congrArg (algebraMap S (CoordinateField K P)) hc
 simpa only [IntermediateField.algebraMap_apply,
   IntermediateField.coe_algebraMap_apply] using hcast
theorem eq_point_kernel_of_coordinates_algebraic
   (h:∀ i,IsAlgebraic K (coordinate K P i)):
   ∃ v:Fin 3 → K,P=RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
 classical
 choose v hv using fun i => coordinate_eq_scalar_of_isAlgebraic K P i (h i)
 have heval:coordinateEvaluation K P=
     (IsScalarTower.toAlgHom K K (CoordinateField K P)).comp (MvPolynomial.aeval v):=by
   apply MvPolynomial.algHom_ext
   intro i
   simp only [AlgHom.comp_apply,MvPolynomial.aeval_X]
   change coordinate K P i=algebraMap K (CoordinateField K P) (v i)
   exact (hv i).symm
 refine ⟨v,?_⟩
 calc
   P=RingHom.ker (coordinateEvaluation K P).toRingHom:=
     (coordinateEvaluation_ker K P).symm
   _=RingHom.ker ((algebraMap K (CoordinateField K P)).comp
       (MvPolynomial.aeval v).toRingHom):=by rw [heval];rfl
   _=RingHom.ker (MvPolynomial.aeval v).toRingHom:=
     RingHom.ker_comp_of_injective _ (algebraMap K (CoordinateField K P)).injective
theorem exists_transcendental_coordinate_of_ne_point_kernel
   (hnonpoint:∀ v:Fin 3 → K,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   ∃ i:Fin 3,Transcendental K (coordinate K P i):=by
 classical
 by_contra hnone
 have halg:∀ i,IsAlgebraic K (coordinate K P i):=by
   intro i
   by_contra hi
   exact hnone ⟨i,hi⟩
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic K P halg
 exact hnonpoint v hv
end AlgebraicallyClosed
end
end ProximityPrize.SubmissionLower.RCN002
