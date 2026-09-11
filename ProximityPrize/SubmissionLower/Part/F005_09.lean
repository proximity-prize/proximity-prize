import ProximityPrize.SubmissionLower.Part.F005_08
section Compact_PackedLegacyCore2
section PackedLegacy_EJ
namespace ProximityPrize.SubmissionLower.RCN134
open scoped BigOperators
open RCN002
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
variable {I:Type} (P:I → Ideal (MvPolynomial (Fin 3) K))
 [∀ i,(P i).IsPrime]
section CommonBase
variable {B:Type} [Field B] [Algebra K B] [Algebra B L]
 [IsScalarTower K B L]
 [∀ i,Algebra B (CoordinateField K (P i))]
 [∀ i,IsScalarTower K B (CoordinateField K (P i))]
variable [Fintype I] [IsAlgClosed L]
 [∀ i,FiniteDimensional B (CoordinateField K (P i))]
 [∀ i,Algebra.IsSeparable B (CoordinateField K (P i))]

def genericFiberPoints:Finset (Fin 3 → L):=by
 classical
 exact Finset.univ.image (commonBaseEmbeddingPoint (B:=B) (L:=L) P)
theorem genericFiberPoints_card (hP:Function.Injective P):
   (genericFiberPoints (B:=B) (L:=L) P).card=
     ∑ i,Module.finrank B (CoordinateField K (P i)):=by
 classical
 rw [genericFiberPoints,
   Finset.card_image_of_injective _ (commonBaseEmbeddingPoint_injective P hP)]
 simp only [Finset.card_univ,Fintype.card_sigma,AlgHom.card]
end CommonBase
end
end ProximityPrize.SubmissionLower.RCN134
end PackedLegacy_EJ

/-! Packed from ProximityPrize.SubmissionLower.D3. -/
section PackedLegacy_D3
namespace ProximityPrize.SubmissionLower.RCN208
open scoped Classical
open RCN002 RCN072 RCN264 RCN022 RCN207 RCN134
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
variable {K L:Type} [Field K] [Field L]
def coordinateFieldMap (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (ev:MvPolynomial (Fin 3) K →+*L) (hker:RingHom.ker ev=P):
   CoordinateField K P →+*L:=
 let hz:∀ A,A∈P → ev A=0:=fun A hA↦by
   exact RingHom.mem_ker.mp (hker.symm ▸ hA)
 IsFractionRing.lift (K:=CoordinateField K P)
   (RingHom.lift_injective_of_ker_le_ideal P hz hker.le)
theorem coordinateFieldMap_eval (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (ev:MvPolynomial (Fin 3) K →+*L) (hker:RingHom.ker ev=P)
   (A:MvPolynomial (Fin 3) K):
   coordinateFieldMap P ev hker (coordinateEvaluation K P A)=ev A:=by
 unfold coordinateFieldMap
 change IsFractionRing.lift _
   (algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P A))=ev A
 rw [IsFractionRing.lift_algebraMap,Ideal.Quotient.lift_mk]
def movingValue (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (H G Q U:MvPolynomial (Fin 3) K):CoordinateField K P:=
 coordinateEvaluation K P Q+
   coordinateEvaluation K P U*coordinateEvaluation K P G/
     coordinateEvaluation K P H
def scalarPolynomialMap (K E:Type) [Field K] [Field E] [Algebra K E]:
   MvPolynomial (Fin 3) K →+*MvPolynomial (Fin 3) E:=
 MvPolynomial.map (algebraMap K E)
theorem comap_le_of_embedding_point {E:Type} [Field E] [Algebra K E]
   (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
   (f:CoordinateField K P →ₐ[K] E) (D:Ideal (MvPolynomial (Fin 3) E))
   (hD:D ≤ RingHom.ker
     (MvPolynomial.aeval (embeddingPoint P f):MvPolynomial (Fin 3) E →ₐ[E] E).toRingHom):
   D.comap (scalarPolynomialMap K E) ≤ P:=by
 intro A hA
 rw [←embeddingPoint_kernel P f]
 apply RingHom.mem_ker.mpr
 have hv:=RingHom.mem_ker.mp (hD hA)
 simpa only [MvPolynomial.aeval_eq_eval₂Hom,scalarPolynomialMap,
   MvPolynomial.eval₂Hom_map_hom,Algebra.algebraMap_self,RingHom.id_comp,
   AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hv
end
end ProximityPrize.SubmissionLower.RCN208
end PackedLegacy_D3

/-! Packed from ProximityPrize.SubmissionLower.A9. -/
section PackedLegacy_A9
namespace ProximityPrize.SubmissionLower.RCN064
open scoped Classical BigOperators WithZero
open RCN212 RCN184 RCN133 RCN295 RCN095 RCN114 RCN187 RCN344 RCN002 RCN005 RCN006 RCN341 RCN044 RCN037 RCN207 RCN208 RCN264 RCN042 RCN035 RCN022
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
end
end ProximityPrize.SubmissionLower.RCN064
end PackedLegacy_A9

/-! Packed from ProximityPrize.SubmissionLower.M8. -/
section PackedLegacy_M8
namespace ProximityPrize.SubmissionLower.RCN204
open scoped Classical BigOperators WithZero
open RCN095 RCN114 RCN207 RCN212 RCN295 RCN187 RCN002 RCN344 RCN064
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
private theorem flag_eq {p q:FlagDegree} (hx:p.zOnly=q.zOnly)
   (hy:p.yz=q.yz) (hz:p.all=q.all):p=q:=by
 cases p;cases q;simp_all
theorem coefficient_flag_eq (a b s k:ℕ) (C:FlagDegree)
   (c:Fin (k+1) → FlagDegree)
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (j:Fin (k+1)):
   c j=C+k • (⟨a,b,s⟩:FlagDegree)+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag:=by
 have hx:=congrArg FlagDegree.zOnly (hc j)
 have hy:=congrArg FlagDegree.yz (hc j)
 have hz:=congrArg FlagDegree.all (hc j)
 have hj:k-j.val+j.val=k:=Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)
 apply flag_eq
 all_goals simp only [add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all,
   unitAllFlag,unitYZFlag] at*
 all_goals nlinarith
variable {K L:Type*} [Field K] [Field L]
theorem filteredCut_div_pow (k:ℕ) (B:Fin (k+1) → L) (H G:L) (hH:H≠0):
   filteredCut k B H G/H^k=∑ j,B j*(G/H)^j.val:=by
 apply (div_eq_iff (pow_ne_zero k hH)).mpr
 have hrel:H*(G/H)=(1:L)*G:=by field_simp
 have h:=binary_clearing k B H G 1 (G/H) hrel
 simpa [filteredCut,mul_comm,mul_left_comm,mul_assoc] using h.symm
def flagPole (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):ℤ:=
 (p.zOnly:ℤ)*poleOrder v (x 2)+
 (p.yz:ℤ)*max (poleOrder v (x 0)) (poleOrder v (x 2))+
 (p.all:ℤ)*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2)))
theorem flagPole_nonneg (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p:FlagDegree):0 ≤ flagPole v x p:=by
 unfold flagPole poleOrder
 positivity
@[simp] theorem flagPole_add (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (p q:FlagDegree):
   flagPole v x (p+q)=flagPole v x p+flagPole v x q:=by
 simp only [flagPole,add_zOnly,add_yz,add_all,Nat.cast_add]
 ring
@[simp] theorem flagPole_nsmul (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L) (k:ℕ) (p:FlagDegree):
   flagPole v x (k • p)=(k:ℤ)*flagPole v x p:=by
 simp only [flagPole,nsmul_zOnly,nsmul_yz,nsmul_all,Nat.cast_mul]
 ring
@[simp] theorem flagPole_unitAll (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitAllFlag=
     max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))):=by
 simp [flagPole,unitAllFlag]
@[simp] theorem flagPole_unitYZ (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:Fin 3 → L):flagPole v x unitYZFlag=
     max (poleOrder v (x 0)) (poleOrder v (x 2)):=by
 simp [flagPole,unitYZFlag]
theorem valuation_eval_le_flag (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (p:FlagDegree) (B:MvPolynomial (Fin 3) K) (hB:PolynomialInFlag p B):
   v (MvPolynomial.eval₂Hom coeff x B) ≤ WithZero.exp (flagPole v x p):=
 (valuation_eval_le_exp_exponentSet v coeff hcoeff x (flagSupport p) B
   ((support_subset_flagSupport_iff _ _).mpr hB)).trans
   (WithZero.exp_le_exp.mpr (exponentSetPoleWeight_flagSupport_le v x p))
private theorem mixed_weight_le (r j k:ℕ) (h:r+j=k) (A B:ℤ):
   (r:ℤ)*A+(j:ℤ)*B ≤ (k:ℤ)*max A B:=by
 calc
   _ ≤ (r:ℤ)*max A B+(j:ℤ)*max A B:=add_le_add
     (mul_le_mul_of_nonneg_left (le_max_left _ _) (Int.natCast_nonneg _))
     (mul_le_mul_of_nonneg_left (le_max_right _ _) (Int.natCast_nonneg _))
   _=((r+j:ℕ):ℤ)*max A B:=by push_cast;ring
   _=_:=by rw [h]
theorem valuation_polynomialInW_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (w:L) (k:ℕ) (C N:FlagDegree) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (hB:∀ j,PolynomialInFlag
     (C+k • N+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag) (B j)):
   v (∑ j,MvPolynomial.eval₂Hom coeff x (B j)*w^j.val) ≤
     WithZero.exp (flagPole v x C+(k:ℤ)*(flagPole v x N+
       max (2*flagPole v x unitAllFlag) (flagPole v x unitYZFlag+poleOrder v w))):=by
 apply v.map_sum_le
 intro j _
 let p:=C+k • N+(k-j.val) • (2 • unitAllFlag)+j.val • unitYZFlag
 have hBj:=valuation_eval_le_flag v coeff hcoeff x p (B j) (hB j)
 have hw:v w ≤ WithZero.exp (poleOrder v w):=
   WithZero.le_exp_of_log_le (le_max_right _ _)
 have hpow:v (w^j.val) ≤ WithZero.exp ((j.val:ℤ)*poleOrder v w):=by
   rw [map_pow]
   simpa only [←WithZero.exp_nsmul,nsmul_eq_mul] using
     pow_le_pow_left₀ (show (0:WithZero (Multiplicative ℤ)) ≤ v w from zero_le) hw j.val
 calc
   v (MvPolynomial.eval₂Hom coeff x (B j)*w^j.val) ≤
       WithZero.exp (flagPole v x p)*WithZero.exp ((j.val:ℤ)*poleOrder v w):=by
     rw [map_mul]
     exact mul_le_mul' hBj hpow
   _=WithZero.exp (flagPole v x p+(j.val:ℤ)*poleOrder v w):=by rw [WithZero.exp_add]
   _ ≤ _:=by
     apply WithZero.exp_le_exp.mpr
     have hm:=mixed_weight_le (k-j.val) j.val k
       (Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt))
       (2*flagPole v x unitAllFlag) (flagPole v x unitYZFlag+poleOrder v w)
     simp only [p,flagPole_add,flagPole_nsmul,Nat.cast_ofNat]
     nlinarith
private theorem poleOrder_le_of_value_le_exp (v:Valuation L (WithZero (Multiplicative ℤ)))
   (z:L) (q:ℤ) (hq:0 ≤ q) (hz:v z ≤ WithZero.exp q):poleOrder v z ≤ q:=by
 apply max_le hq
 by_cases hv:v z=0
 · simpa [hv] using hq
 · simpa only [WithZero.log_exp] using (WithZero.log_le_log hv WithZero.exp_ne_zero).mpr hz
theorem poleOrder_filteredCut_div_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (coeff:K →+*L) (hcoeff:∀ a,v (coeff a) ≤ 1) (x:Fin 3 → L)
   (a b s k:ℕ) (C:FlagDegree) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (H G:MvPolynomial (Fin 3) K) (c:Fin (k+1) → FlagDegree)
   (hH:MvPolynomial.eval₂Hom coeff x H≠0)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   poleOrder v (MvPolynomial.eval₂Hom coeff x (filteredCut k B H G)/
     (MvPolynomial.eval₂Hom coeff x H)^k) ≤
   flagPole v x C+(k:ℤ)*(flagPole v x (⟨a,b,s⟩:FlagDegree)+
     max (2*max (poleOrder v (x 1)) (max (poleOrder v (x 0)) (poleOrder v (x 2))))
       (max (poleOrder v (x 0)) (poleOrder v (x 2))+
         poleOrder v (MvPolynomial.eval₂Hom coeff x G/MvPolynomial.eval₂Hom coeff x H))):=by
 rw [map_filteredCut,filteredCut_div_pow k _ _ _ hH]
 apply poleOrder_le_of_value_le_exp
 · have hC:=flagPole_nonneg v x C
   have hN:=flagPole_nonneg v x (⟨a,b,s⟩:FlagDegree)
   dsimp [poleOrder]
   positivity
 · simpa only [flagPole_unitAll,flagPole_unitYZ] using
     valuation_polynomialInW_le v coeff hcoeff x
       (MvPolynomial.eval₂Hom coeff x G/MvPolynomial.eval₂Hom coeff x H)
       k C (⟨a,b,s⟩:FlagDegree) B (fun j↦by
         rw [←coefficient_flag_eq a b s k C c hc j]
         exact hB j)
theorem coordinate_filteredCut_pole_le {Ω:Type} [Field Ω]
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (v:Place Ω (CoordinateField Ω P)) (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1) → MvPolynomial (Fin 3) Ω) (H G:MvPolynomial (Fin 3) Ω)
   (c:Fin (k+1) → FlagDegree) (hH:coordinateEvaluation Ω P H≠0)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   poleOrder v.val (coordinateEvaluation Ω P (filteredCut k B H G)/
     (coordinateEvaluation Ω P H)^k) ≤
     flagPole v.val (coordinate Ω P) C+(k:ℤ)*
       (flagPole v.val (coordinate Ω P) (⟨a,b,s⟩:FlagDegree)+movingPoleTarget P H G v):=by
 have h:=poleOrder_filteredCut_div_le v.val (algebraMap Ω (CoordinateField Ω P))
   (constant_value_le_one Ω (CoordinateField Ω P) v) (coordinate Ω P)
   a b s k C B H G c (by
     simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom] using hH) hB hc
 simpa only [coordinateEvaluation_eq_aeval,MvPolynomial.aeval_eq_eval₂Hom,
   movingPoleTarget,movingRatio] using h
end
end ProximityPrize.SubmissionLower.RCN204
end PackedLegacy_M8

/-! Packed from ProximityPrize.SubmissionLower.O3. -/
section PackedLegacy_O3
namespace ProximityPrize.SubmissionLower.RCN271
open scoped Classical
open RCN272 RCN094 RCN162 RCN165
noncomputable section
variable {K:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
abbrev Ring3 (K:Type) [Field K]:=MvPolynomial (Fin 3) K
private theorem eval_eq_of_sub_mem (P:Ideal (Ring3 K))
   {A B:Ring3 K} (h:A-B∈P) (v:Fin 3 → K)
   (hv:P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom):
   MvPolynomial.aeval v A=MvPolynomial.aeval v B:=by
 have hz:=hv h
 change MvPolynomial.aeval v (A-B)=0 at hz
 rw [map_sub] at hz
 exact sub_eq_zero.mp hz
def FiniteRegularZeroSetBound (P:Ideal (Ring3 K)) (H A:Ring3 K)
   (cost:ℕ):Prop:=
 ∀ points:Finset (Fin 3 → K),
   (∀ v∈points,P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
   (∀ v∈points,MvPolynomial.aeval v H≠0) →
   (∀ v∈points,MvPolynomial.aeval v A=0) → points.card ≤ cost
theorem FiniteRegularZeroSetBound.mono
   {P:Ideal (Ring3 K)} {H A:Ring3 K} {cost cost':ℕ}
   (h:FiniteRegularZeroSetBound P H A cost) (hle:cost ≤ cost'):
   FiniteRegularZeroSetBound P H A cost':=by
 intro points hP hH hA
 exact (h points hP hH hA).trans hle
section Selected
open RCN136 RCN231 RCN319 RCN238 RCN243
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem agreement_fiber_card_le_of_regular_zero_bound
   (φ:Polynomial K →+*Ω) (P:Ideal (Ring3 Ω))
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K) (Γ:Finset K)
   (p w:ℕ) [CharP Ω p] (hchar:w < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (x u₀ u₁:K) (cost:ℕ)
   (hzero:FiniteRegularZeroSetBound P (regularitySurface φ F)
     (agreementPolynomial φ F w x u₀ u₁) cost):
   (Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)).card ≤ cost:=by
 classical
 let fiber:=Γ.filter (fun γ↦(selected γ).eval x=u₀+γ*u₁)
 let points:=fiber.image (selectedPoint φ selected)
 have hcount:points.card ≤ cost:=by
   apply hzero points
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     exact hpoint γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     change MvPolynomial.eval (selectedPoint φ selected γ)
       (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0
     rw [selectedPoint_evaluation]
     exact hregular γ (Finset.mem_filter.mp hγ).1
   · intro q hq
     obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hq
     obtain ⟨hΓ,hagree⟩:=Finset.mem_filter.mp hγ
     exact (selected_agreement_zero_iff φ F selected p w hchar γ
       (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) x u₀ u₁).mpr hagree
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (selectedPoint_injective φ selected)
 rwa [hcard] at hcount
end Selected
end
end ProximityPrize.SubmissionLower.RCN271
end PackedLegacy_O3

/-! Packed from ProximityPrize.SubmissionLower.E3. -/
section PackedLegacy_E3
namespace ProximityPrize.SubmissionLower.RCN257
open scoped Classical BigOperators WithZero
open RCN344 RCN000 RCN002 RCN005 RCN006 RCN007 RCN271 RCN341
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L] [IsAlgClosed K]
 [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
 [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
 [IsScalarTower (Polynomial K) (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]
 (A:Type) [CommRing A] [IsDomain A]
 [Algebra K A] [Algebra A L] [IsFractionRing A L]
 [Algebra (Polynomial K) A]
 [IsScalarTower K (Polynomial K) A] [IsScalarTower K A L]
 [IsScalarTower (Polynomial K) A L]
local instance:DecidableEq K:=Classical.decEq K
theorem model_regular_value_eq_one (ψ:A →ₐ[K] K) (h:A) (hψ:ψ h≠0):
   (modelPlace K L A ψ).val (algebraMap A L h)=1:=by
 apply le_antisymm
 · exact actual_model_value_le_one K A L ψ h
 · apply le_of_not_gt
   intro hlt
   exact hψ ((actual_model_value_lt_one_iff K A L ψ h).mp hlt)
theorem model_regular_quotient_zero_order
   (ψ:A →ₐ[K] K) (a h:A) (k:ℕ) (ha:a≠0)
   (hzero:ψ a=0) (hregular:ψ h≠0):
   1 ≤ RCN026.order K L (modelPlace K L A ψ)
     (algebraMap A L a/(algebraMap A L h)^k):=by
 have hv:=model_regular_value_eq_one K L A ψ h hregular
 change 1 ≤-((modelPlace K L A ψ).val
   (algebraMap A L a/(algebraMap A L h)^k)).log
 simp only [map_div₀,map_pow,hv,one_pow,div_one]
 exact actual_model_zero_order_ge_one K A L ψ a ha hzero
theorem finite_model_regular_zeros_le_poleMass
   (a h:A) (k cost:ℕ) (ha:a≠0) (hh:h≠0)
   (hpole:∀ W:Finset (Place K L),
     (∑ v∈W,RCN346.poleOrder K L v
       (algebraMap A L a/(algebraMap A L h)^k)) ≤ (cost:ℤ))
   (S:Finset (A →ₐ[K] K))
   (hzero:∀ ψ∈S,ψ a=0) (hregular:∀ ψ∈S,ψ h≠0):
   S.card ≤ cost:=by
 classical
 let f:L:=algebraMap A L a/(algebraMap A L h)^k
 have hfa:algebraMap A L a≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne ha
 have hfh:algebraMap A L h≠0:=by
   simpa only [map_zero] using (IsFractionRing.injective A L).ne hh
 have hf:f≠0:=div_ne_zero hfa (pow_ne_zero k hfh)
 let U:=S.image (modelPlace K L A)
 have hU:∀ v∈U,1 ≤ RCN026.order K L v f:=by
   intro v hv
   obtain ⟨ψ,hψ,rfl⟩:=Finset.mem_image.mp hv
   exact model_regular_quotient_zero_order K L A ψ a h k ha
     (hzero ψ hψ) (hregular ψ hψ)
 have hcount:=RCN026.finite_zero_places_le_poleMass K L f hf U hU
 have hcard:U.card=S.card:=
   Finset.card_image_of_injective _ (modelPlace_injective K L A)
 have hb:(S.card:ℤ) ≤ cost:=by
   rw [←hcard]
   exact hcount.trans (hpole _)
 exact_mod_cast hb
section ActualCurve
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
theorem quotient_fraction_eq_field_eval (T:MvPolynomial (Fin 3) K):
   algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P T)=
     MvPolynomial.aeval (coordinate K P) T:=by
 exact (aeval_coordinate_eq_quotient K P T).symm
theorem finite_regular_zero_bound_of_separator
   (base:SeparableLiteralCoordinate P)
   (H F:MvPolynomial (Fin 3) K) (k cost:ℕ) (hF:F∉P) (hH:H∉P)
   (hpole:
     letI:Algebra (RatFunc K) (CoordinateField K P):=
       rationalBaseAlgebra K P base.index base.transcendental
     ∀ W:Finset (Place K (CoordinateField K P)),
       (∑ v∈W,RCN346.poleOrder K (CoordinateField K P) v
         (MvPolynomial.aeval (coordinate K P) F/
           (MvPolynomial.aeval (coordinate K P) H)^k)) ≤ (cost:ℤ)):
   FiniteRegularZeroSetBound P H F cost:=by
 classical
 let i₀:=base.index
 let hi₀:=base.transcendental
 letI:Algebra (Polynomial K) (CoordinateRing K P):=
   quotientPolynomialAlgebra K P i₀
 letI:Algebra (Polynomial K) (CoordinateField K P):=
   polynomialBaseAlgebra K P i₀
 letI:Algebra (RatFunc K) (CoordinateField K P):=
   rationalBaseAlgebra K P i₀ hi₀
 letI:=quotientBaseScalarTower K P i₀
 letI:=polynomialBaseScalarTower K P i₀
 letI:=quotientFractionScalarTower K P i₀
 letI:=polynomialRationalScalarTower K P i₀ hi₀
 letI:=rationalBaseScalarTower K P i₀ hi₀
 letI:FiniteDimensional (RatFunc K) (CoordinateField K P):=base.finite
 letI:Algebra.IsSeparable (RatFunc K) (CoordinateField K P):=base.separable
 intro S hSP hSH hSF
 let liftPoint:{v:Fin 3 → K//v∈S} → (CoordinateRing K P →ₐ[K] K):=
   fun v↦pointHom K P ⟨v.1,hSP v.1 v.2⟩
 have hinj:Function.Injective liftPoint:=by
   intro v w hvw
   apply Subtype.ext
   exact congrArg (fun z:PointOn K P↦z.val) (pointHom_injective K P hvw)
 let points:=S.attach.image liftPoint
 have hzero:∀ ψ∈points,ψ (Ideal.Quotient.mk P F)=0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSF v.1 v.2
 have hregular:∀ ψ∈points,ψ (Ideal.Quotient.mk P H)≠0:=by
   intro ψ hψ
   obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hψ
   exact hSH v.1 v.2
 have hFq:Ideal.Quotient.mk P F≠0:=
   fun hz↦hF (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hHq:Ideal.Quotient.mk P H≠0:=
   fun hz↦hH (Ideal.Quotient.eq_zero_iff_mem.mp hz)
 have hcount:=finite_model_regular_zeros_le_poleMass K (CoordinateField K P)
   (CoordinateRing K P) (Ideal.Quotient.mk P F) (Ideal.Quotient.mk P H)
   k cost hFq hHq (by simpa only [quotient_fraction_eq_field_eval] using hpole)
   points hzero hregular
 have hcard:points.card=S.card:=by
   change (S.attach.image liftPoint).card=S.card
   rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
 rwa [hcard] at hcount
end ActualCurve
end
end ProximityPrize.SubmissionLower.RCN257
end PackedLegacy_E3

end Compact_PackedLegacyCore2

