import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.FD
import ProximityPrize.SubmissionLower.X9
import ProximityPrize.SubmissionLower.D3
namespace ProximityPrize.SubmissionLower.RCN064
open scoped Classical BigOperators WithZero
open RCN212 RCN184
open RCN133 RCN295
open RCN095 RCN114
open RCN187 RCN344
open RCN002 RCN005 RCN006
open RCN341 RCN044
open RCN037 RCN207
open RCN208
open RCN264 RCN042
open RCN035 RCN022
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
private theorem exact_of_avoids {K L σ:Type*} [Field K] [Field L]
   [Algebra K L] [Fintype σ] [DecidableEq σ]
   (v:RCN345.NormalizedValuation K L) (x:σ → L)
   (E:Finset (σ →₀ ℕ)) (c:E → K)
   (hc:c∉cancellationSubmodule v.val (constant_value_le_one K L v) x E):
   v.val (coefficientEvaluation x E c)=WithZero.exp (exponentSetPoleWeight v.val x E):=by
 apply le_antisymm
 · exact valuation_eval_le_exp_exponentSet v.val (algebraMap K L)
     (constant_value_le_one K L v) x E _ (support_polynomialOfSupport_subset _ _)
 · exact le_of_not_gt hc
theorem exists_common_coefficients {K I:Type*} [Field K] [Infinite K] [Finite I]
   (L:I → Type*) [∀ i,Field (L i)] [∀ i,Algebra K (L i)]
   (x:∀ i,Fin 3 → L i) (w:∀ i,L i) (index:I → Fin 3)
   (hd:∀ i,KaehlerDifferential.D K (L i) (x i (index i))≠0)
   (V:∀ i,Finset (RCN345.NormalizedValuation K (L i))):
   ∃ c:movingSupport → K,∀ i,
     coefficientEvaluation (x i) linearSupport (restrictU c)≠0∧
     KaehlerDifferential.D K (L i)
       (coefficientEvaluation (movingCoordinates (x i) (w i)) movingSupport c)≠0∧
     ∀ v∈V i,
       v.val (coefficientEvaluation (movingCoordinates (x i) (w i)) movingSupport c)=
         WithZero.exp (max (2*max (poleOrder v.val (x i 1))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))))
           (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))+poleOrder v.val (w i)))∧
       v.val (coefficientEvaluation (x i) linearSupport (restrictU c))=
         WithZero.exp (max (poleOrder v.val (x i 0)) (poleOrder v.val (x i 2))):=by
 classical
 let evJ i:=coefficientEvaluation (K:=K) (movingCoordinates (x i) (w i)) movingSupport
 let evU i:=(coefficientEvaluation (K:=K) (x i) linearSupport).comp restrictU
 let Extra:=I × Bool
 let Pole:=Sigma fun i:I↦{v//v∈V i} × Bool
 let bad:Extra ⊕ Pole → Submodule K (movingSupport → K)
   | Sum.inl (i,false) => LinearMap.ker (evU i)
   | Sum.inl (i,true) => LinearMap.ker ((KaehlerDifferential.D K (L i)).toLinearMap.comp (evJ i))
   | Sum.inr ⟨i,v,false⟩ => (cancellationSubmodule v.1.val
       (constant_value_le_one K (L i) v.1) (x i) linearSupport).comap restrictU
   | Sum.inr ⟨i,v,true⟩ => cancellationSubmodule v.1.val
       (constant_value_le_one K (L i) v.1) (movingCoordinates (x i) (w i)) movingSupport
 have hbad:∀ j,bad j≠⊤:=by
   rintro (⟨i,b⟩ | ⟨i,v,b⟩)
   · cases b
     · obtain ⟨c,hc⟩:=restrictU_surjective (K:=K)
         (deltaCoefficient linearSupport ⟨0,zero_mem_flagSupport _⟩)
       have hone:evU i c=1:=by
         change coefficientEvaluation (x i) linearSupport (restrictU c)=1
         rw [hc]
         change MvPolynomial.eval₂Hom _ _ (polynomialOfSupport _ _)=_
         rw [polynomialOfSupport_deltaCoefficient]
         simp
       intro ht
       have hz:evU i c=0:=LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,false));rw [ht];trivial)
       exact one_ne_zero (hone.symm.trans hz)
     · obtain ⟨c,hc⟩:=exists_coordinate_evaluation (K:=K) (x i) (w i) (index i)
       intro ht
       have hz:KaehlerDifferential.D K (L i) (evJ i c)=0:=
         LinearMap.mem_ker.mp (by change c∈bad (Sum.inl (i,true));rw [ht];trivial)
       exact hd i (hc ▸ hz)
   · cases b
     · obtain ⟨d,hd⟩:=exists_exact_support_evaluation_of_downwardClosed (K:=K)
         v.1.val (x i) linearSupport (flagSupport_downwardClosed _) (zero_mem_flagSupport _)
       obtain ⟨c,hc⟩:=restrictU_surjective (K:=K) d
       intro ht
       have hm:c∈bad (Sum.inr ⟨i,v,false⟩):=by rw [ht];trivial
       change v.1.val (coefficientEvaluation (x i) linearSupport (restrictU c)) < _ at hm
       rw [hc,hd] at hm
       exact lt_irrefl _ hm
     · obtain ⟨c,hc⟩:=exists_exact_support_evaluation_of_downwardClosed (K:=K)
         v.1.val (movingCoordinates (x i) (w i)) movingSupport
         movingSupport_downwardClosed zero_mem_movingSupport
       exact cancellationSubmodule_ne_top_of_exact _ _ _ _ c hc
 obtain ⟨c,hc⟩:=exists_avoiding_finite_proper_submodules bad hbad
 refine ⟨c,fun i↦⟨?_,?_,?_⟩⟩
 · exact hc (Sum.inl (i,false))
 · exact hc (Sum.inl (i,true))
 · intro v hv
   have hj:=exact_of_avoids v (movingCoordinates (x i) (w i)) movingSupport c
     (hc (Sum.inr ⟨i,⟨v,hv⟩,true⟩))
   have hu:=exact_of_avoids v (x i) linearSupport (restrictU c)
     (hc (Sum.inr ⟨i,⟨v,hv⟩,false⟩))
   rw [exponentSetPoleWeight_moving] at hj
   rw [exponentSetPoleWeight_unitYZ] at hu
   exact ⟨hj,hu⟩
variable {K:Type} [Field K] [IsAlgClosed K]
def movingRelevantPlaces {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P) (w:CoordinateField K P):
   Finset (Place K (CoordinateField K P)):=by
 letI:=polynomialBaseAlgebra K P D.index
 letI:=rationalBaseAlgebra K P D.index D.transcendental
 letI:=polynomialBaseScalarTower K P D.index
 letI:=polynomialRationalScalarTower K P D.index D.transcendental
 letI:=rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=D.separable
 exact literalRelevantPlaces D ∪ if hw:w≠0 then
   RCN026.placesFor K (CoordinateField K P) w hw else ∅
theorem outside_movingRelevantPlaces {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (D:SeparableLiteralCoordinate P) (w:CoordinateField K P)
   (v:Place K (CoordinateField K P)) (hv:v∉movingRelevantPlaces D w):
   (∀ i,poleOrder v.val (coordinate K P i)=0)∧poleOrder v.val w=0:=by
 letI:=polynomialBaseAlgebra K P D.index
 letI:=rationalBaseAlgebra K P D.index D.transcendental
 letI:=polynomialBaseScalarTower K P D.index
 letI:=polynomialRationalScalarTower K P D.index D.transcendental
 letI:=rationalBaseScalarTower K P D.index D.transcendental
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=D.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=D.separable
 constructor
 · exact coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant D v
     (fun h↦hv (Finset.mem_union_left _ h))
 · by_cases hw:w=0
   · simp [hw,poleOrder]
   have horder:RCN026.order K (CoordinateField K P) v w=0:=by
     by_contra hn
     apply hv
     apply Finset.mem_union_right
     simp only [dif_pos hw]
     exact RCN026.placesFor_covers K (CoordinateField K P) w hw v hn
   simp only [RCN026.order] at horder
   simp [poleOrder,show (v.val w).log=0 by omega]
def movingRatio (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G:MvPolynomial (Fin 3) K):CoordinateField K P:=
 coordinateEvaluation K P G/coordinateEvaluation K P H
def movingPoleTarget (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G:MvPolynomial (Fin 3) K) (v:Place K (CoordinateField K P)):ℤ:=
 max (2*max (poleOrder v.val (coordinate K P 1))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))))
   (max (poleOrder v.val (coordinate K P 0)) (poleOrder v.val (coordinate K P 2))+
     poleOrder v.val (movingRatio P H G))
private theorem field_eval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (A:MvPolynomial (Fin 3) K):
   MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K P)) (coordinate K P) A=
     coordinateEvaluation K P A:=by
 rw [coordinateEvaluation_eq_aeval]
 exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm
theorem exists_common_original_projection (F A H G:MvPolynomial (Fin 3) K)
   (base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1):
   ∃ Q U:MvPolynomial (Fin 3) K,
     PolynomialInFlag (2 • unitAllFlag) Q∧PolynomialInFlag unitYZFlag U∧
     ∀ C:RegularComponent K F A H,
       U∉C.1∧KaehlerDifferential.D K (CoordinateField K C.1)
         (movingValue C.1 H G Q U)≠0∧
       (∀ v:Place K (CoordinateField K C.1),
         poleOrder v.val (movingValue C.1 H G Q U)=movingPoleTarget C.1 H G v)∧
       (∀ v∈movingRelevantPlaces (base C) (movingRatio C.1 H G),
         v.val (coordinateEvaluation K C.1 U)=
           WithZero.exp (max (poleOrder v.val (coordinate K C.1 0))
             (poleOrder v.val (coordinate K C.1 2)))):=by
 classical
 obtain ⟨c,hc⟩:=exists_common_coefficients (K:=K)
   (fun C:RegularComponent K F A H↦CoordinateField K C.1)
   (fun C↦coordinate K C.1) (fun C↦movingRatio C.1 H G)
   (fun C↦(base C).index) (fun C↦base_differential_ne_zero (base C))
   (fun C↦movingRelevantPlaces (base C) (movingRatio C.1 H G))
 let Q:=quadraticPolynomial c
 let U:=linearPolynomial c
 have hJ (C:RegularComponent K F A H):
     coefficientEvaluation (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G))
       movingSupport c=movingValue C.1 H G Q U:=by
   rw [coefficientEvaluation_eq,field_eval,field_eval]
   simp only [movingValue,movingRatio,Q,U,mul_div_assoc]
 have hU (C:RegularComponent K F A H):
     coefficientEvaluation (coordinate K C.1) linearSupport (restrictU c)=
       coordinateEvaluation K C.1 U:=field_eval C.1 U
 refine ⟨Q,U,quadraticPolynomial_inFlag c,linearPolynomial_inFlag c,fun C↦?_⟩
 have h:=hc C
 rw [hU C,hJ C] at h
 refine ⟨?_,h.2.1,?_,fun v hv↦(h.2.2 v hv).2⟩
 · intro hmem
   apply h.1
   apply RingHom.mem_ker.mp
   change U∈RingHom.ker (coordinateEvaluation K C.1).toRingHom
   rwa [coordinateEvaluation_ker]
 · intro v
   by_cases hv:v∈movingRelevantPlaces (base C) (movingRatio C.1 H G)
   · exact poleOrder_eq_of_valuation_eq_exp v.val _ _
       (by dsimp [movingPoleTarget,poleOrder];positivity) (h.2.2 v hv).1
   · obtain ⟨hcoord,hw⟩:=outside_movingRelevantPlaces (base C) (movingRatio C.1 H G) v hv
     have hz:exponentSetPoleWeight v.val
         (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G)) movingSupport=0:=by
       rw [exponentSetPoleWeight_moving]
       simp [hcoord,hw]
     have hp:=(poleOrder_eval_le_support v.val (algebraMap K (CoordinateField K C.1))
       (constant_value_le_one K (CoordinateField K C.1) v)
       (movingCoordinates (coordinate K C.1) (movingRatio C.1 H G))
       (polynomialOfSupport movingSupport c)).trans
       (supportPoleWeight_le_exponentSetPoleWeight _ _ _ movingSupport
         (support_polynomialOfSupport_subset _ _))
     change poleOrder v.val (coefficientEvaluation _ _ c) ≤ _ at hp
     rw [hJ C,hz] at hp
     have hp0:=le_antisymm hp (le_max_left _ _)
     simpa [movingPoleTarget,hcoord,hw] using hp0
theorem moving_projection_gate {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (base:SeparableLiteralCoordinate P) (H G Q U:MvPolynomial (Fin 3) K)
   (hd:KaehlerDifferential.D K (CoordinateField K P) (movingValue P H G Q U)≠0):
   ∃ ht:Transcendental K (movingValue P H G Q U),
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       (elementEmbedding K (CoordinateField K P) (movingValue P H G Q U) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (CoordinateField K P)∧
     Algebra.IsSeparable (RatFunc K) (CoordinateField K P)∧
     IsScalarTower K (RatFunc K) (CoordinateField K P)∧
     algebraMap (RatFunc K) (CoordinateField K P)
       (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=movingValue P H G Q U:=by
 obtain ⟨ht,hf,hs⟩:=element_transcendental_finite_separable_of_differential_ne_zero
   K (CoordinateField K P) (literalToSeparableCoordinate base) (movingValue P H G Q U) hd
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   (elementEmbedding K (CoordinateField K P) (movingValue P H G Q U) ht).toRingHom.toAlgebra
 refine ⟨ht,hf,hs,?_,elementEmbedding_variable K (CoordinateField K P) _ ht⟩
 exact IsScalarTower.of_algebraMap_eq fun c↦
   ((elementEmbedding K (CoordinateField K P) _ ht).commutes c).symm
theorem moving_pole_mem_relevant {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (base:SeparableLiteralCoordinate P) (w:CoordinateField K P)
   (v:Place K (CoordinateField K P)) (hw:poleOrder v.val w≠0):
   v∈movingRelevantPlaces base w:=by
 by_contra hv
 exact hw (outside_movingRelevantPlaces base w v hv).2
theorem value_one_at_finite_moving_pole {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
   (base:SeparableLiteralCoordinate P) (w u:CoordinateField K P)
   (hu:∀ v∈movingRelevantPlaces base w,
     v.val u=WithZero.exp (max (poleOrder v.val (coordinate K P 0))
       (poleOrder v.val (coordinate K P 2))))
   (v:Place K (CoordinateField K P)) (hw:poleOrder v.val w≠0)
   (h0:poleOrder v.val (coordinate K P 0)=0)
   (h2:poleOrder v.val (coordinate K P 2)=0):v.val u=1:=by
 rw [hu v (moving_pole_mem_relevant base w v hw),h0,h2]
 simp
end
end ProximityPrize.SubmissionLower.RCN064
