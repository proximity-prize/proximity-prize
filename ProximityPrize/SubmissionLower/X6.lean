import ProximityPrize.SubmissionLower.X4
namespace ProximityPrize.SubmissionLower.RCN014
open RCN002 RCN005
open RCN011 RCN010
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
theorem planeEvaluation_surjective_of_finite_generatingPair
   {F E:Type} [Field F] [Field E] [Algebra F E]
   [FiniteDimensional F E]
   (y r:E)
   (hgen:IntermediateField.adjoin F ({y,r}:Set E)=⊤):
   Function.Surjective
     (RCN361.planeEval F E y r):=by
 let φ:Polynomial (Polynomial F) →ₐ[F] E:={
   toRingHom:=RCN361.planeEval F E y r
   commutes':=fun a↦by simp [RCN361.planeEval]}
 let A:Subalgebra F E:=φ.range
 let inclusion:A →ₗ[F] E:=A.val
 letI:Module.Finite F A:=
   Module.Finite.of_injective inclusion Subtype.val_injective
 have hAfield:IsField A:=IsField.of_isDomain_of_finite F A
 let L:IntermediateField F E:=A.toIntermediateField' hAfield
 have hy:y∈L:=by
   change y∈A
   refine ⟨Polynomial.C Polynomial.X,?_⟩
   simp [φ,RCN361.planeEval]
 have hr:r∈L:=by
   change r∈A
   refine ⟨Polynomial.X,?_⟩
   simp [φ,RCN361.planeEval]
 have htop:L=⊤:=by
   apply top_unique
   rw [←hgen]
   apply IntermediateField.adjoin_le_iff.mpr
   intro x hx
   rcases hx with hx | hx
   · subst x
     exact hy
   · rw [Set.mem_singleton_iff] at hx
     subst x
     exact hr
 intro x
 have hxL:x∈L:=by rw [htop];trivial
 change x∈A at hxL
 exact hxL
variable (K:Type) [Field K]
variable (order:Fin 3 ≃ Fin 3)
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
variable (ht:Transcendental K (coordinate K P (order 0)))
theorem actualPlaneEvaluation_surjective
   (hfinite:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)):
   Function.Surjective
     (actualPlaneEvaluation K order P ht):=by
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   rationalBaseAlgebra K P (order 0) ht
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=hfinite
 exact planeEvaluation_surjective_of_finite_generatingPair
   (coordinate K P (order 2)) (coordinate K P (order 1))
   (actual_generators K order P ht)
theorem actualRelationKernel_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P (order 0) ht
     FiniteDimensional (RatFunc K) (CoordinateField K P)):
   (actualRelationKernel K order P ht).IsMaximal:=by
 apply RingHom.ker_isMaximal_of_surjective
 exact actualPlaneEvaluation_surjective K order P ht hfinite
theorem pairwise_coprime_of_injective_maximal_family
   {A I:Type*} [CommRing A]
   (J:I → Ideal A) (hmax:∀ i,(J i).IsMaximal)
   (hinjective:Function.Injective J):
   Pairwise fun i j↦IsCoprime (J i) (J j):=by
 intro i j hij
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (hmax i).coprime_of_ne (hmax j) fun heq↦hij (hinjective heq)
def mappedPrimaryPiece
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (surface:B) (multiplicity:I → ℕ) (i:I):Ideal B:=
 Ideal.span {surface} ⊔ (Ideal.map f (relation i))^multiplicity i
theorem mappedPrimaryPiece_pairwise_coprime
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (hcoprime:Pairwise fun i j↦IsCoprime (relation i) (relation j))
   (surface:B) (multiplicity:I → ℕ):
   Pairwise fun i j↦IsCoprime
     (mappedPrimaryPiece f relation surface multiplicity i)
     (mappedPrimaryPiece f relation surface multiplicity j):=by
 intro i j hij
 have hmap:IsCoprime (Ideal.map f (relation i)) (Ideal.map f (relation j)):=by
   apply Ideal.isCoprime_iff_sup_eq.mpr
   rw [←Ideal.map_sup,(hcoprime hij).sup_eq,Ideal.map_top]
 have hpows:(Ideal.map f (relation i))^multiplicity i ⊔
     (Ideal.map f (relation j))^multiplicity j=⊤:=
   Ideal.pow_sup_pow_eq_top hmap.sup_eq
 apply Ideal.isCoprime_iff_sup_eq.mpr
 apply top_unique
 rw [←hpows]
 exact sup_le
   ((le_sup_right:(Ideal.map f (relation i))^multiplicity i ≤
     mappedPrimaryPiece f relation surface multiplicity i).trans le_sup_left)
   ((le_sup_right:(Ideal.map f (relation j))^multiplicity j ≤
     mappedPrimaryPiece f relation surface multiplicity j).trans le_sup_right)
theorem span_pair_le_mappedPrimaryPiece
   {A B I:Type*} [CommRing A] [CommRing B]
   (f:A →+*B) (relation:I → Ideal A)
   (surface tail:B) (multiplicity:I → ℕ) (i:I)
   (htail:tail∈mappedPrimaryPiece f relation surface multiplicity i):
   Ideal.span {surface,tail} ≤
     mappedPrimaryPiece f relation surface multiplicity i:=by
 rw [Ideal.span_le]
 intro x hx
 rcases hx with hx | hx
 · rw [hx]
   exact (show Ideal.span {surface} ≤
       mappedPrimaryPiece f relation surface multiplicity i from le_sup_left)
     (Ideal.subset_span (Set.mem_singleton surface))
 · rw [Set.mem_singleton_iff] at hx
   subst x
   exact htail
end
end ProximityPrize.SubmissionLower.RCN014
