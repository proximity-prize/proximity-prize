import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.D2
import ProximityPrize.SubmissionLower.G
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.EJ
namespace ProximityPrize.SubmissionLower.RCN208
open scoped Classical
open RCN002 RCN072 RCN264
open RCN022 RCN207
open RCN134
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
private theorem rational_base_diagram {E M:Type} [Field E] [Field M]
   [Algebra K E] [Algebra K L] [Algebra E M]
   (j:L) (hj:Transcendental K j) (t:E) (ht:Transcendental K t)
   (phi:L →+*M)
   (hc:∀ c:K,phi (algebraMap K L c)=algebraMap E M (algebraMap K E c))
   (hjmap:phi j=algebraMap E M t):
   (algebraMap E M).comp (elementEmbedding K E t ht).toRingHom=
     phi.comp (elementEmbedding K L j hj).toRingHom:=by
 apply IsFractionRing.ringHom_ext (A:=Polynomial K)
 intro p
 have hpoly:
     ((algebraMap E M).comp (elementEmbedding K E t ht).toRingHom).comp
         (algebraMap (Polynomial K) (RatFunc K))=
       (phi.comp (elementEmbedding K L j hj).toRingHom).comp
         (algebraMap (Polynomial K) (RatFunc K)):=by
   apply Polynomial.ringHom_ext
   · intro c
     change algebraMap E M (elementEmbedding K E t ht (algebraMap K (RatFunc K) c))=
       phi (elementEmbedding K L j hj (algebraMap K (RatFunc K) c))
     rw [AlgHom.commutes,AlgHom.commutes,hc]
   · simpa only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       AlgHom.coe_toRingHom,elementEmbedding_variable] using hjmap.symm
 exact RingHom.congr_fun hpoly p
theorem eliminatedCut_not_mem_of_contraction
   {E:Type} [Field E] [IsAlgClosed E] [Algebra K E]
   (F H G Q U:MvPolynomial (Fin 3) K)
   (k:ℕ) (B:Fin (k+1) → MvPolynomial (Fin 3) K)
   (C:RegularComponent K F (filteredCut k B H G) H)
   (hj:Transcendental K (movingValue C.1 H G Q U))
   (hfinite:
     letI:Algebra (RatFunc K) (CoordinateField K C.1):=
       (elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) hj).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (CoordinateField K C.1))
   (t:E) (ht:Transcendental K t)
   (D:RegularComponent E (scalarPolynomialMap K E F)
     (movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
       (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U) t)
     (scalarPolynomialMap K E H*scalarPolynomialMap K E U))
   (hbelow:D.1.comap (scalarPolynomialMap K E) ≤ C.1):
   eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U) t∉D.1:=by
 intro hT
 let mu:=scalarPolynomialMap K E
 let N:=movingEquation (mu H) (mu G) (mu Q) (mu U) t
 let evD:=coordinateEvaluation E D.1
 let ev:=evD.toRingHom.comp mu
 have hN:N∈D.1:=regularComponent_T_mem E _ _ _ D
 have hprod:mu H*mu U∉D.1:=regularComponent_H_not_mem E _ _ _ D
 have hH:mu H∉D.1:=fun h↦hprod (D.1.mul_mem_right (mu U) h)
 have hU:mu U∉D.1:=fun h↦hprod (D.1.mul_mem_left (mu H) h)
 have hTor:mu (filteredCut k B H G)∈D.1:=by
   rw [map_filteredCut]
   exact original_mem_of_eliminated_mem D.1 k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hT hU
 have hcut:cutIdeal K F (filteredCut k B H G) ≤ D.1.comap mu:=by
   apply Ideal.span_le.mpr
   intro A hA
   rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hA) with rfl | rfl
   · exact regularComponent_G_mem E _ _ _ D
   · exact hTor
 have hmin:=(mem_componentFamily K F (filteredCut k B H G) C.1).mp
   (regularComponent_mem K _ _ _ C)
 have hcontract:D.1.comap mu=C.1:=
   le_antisymm hbelow (hmin.2 ⟨inferInstance,hcut⟩ hbelow)
 have hker:RingHom.ker ev=C.1:=by
   rw [show RingHom.ker ev=(RingHom.ker evD.toRingHom).comap mu from rfl,
     coordinateEvaluation_ker E D.1]
   exact hcontract
 let phi:=coordinateFieldMap C.1 ev hker
 have hphi (A:MvPolynomial (Fin 3) K):
     phi (coordinateEvaluation K C.1 A)=ev A:=coordinateFieldMap_eval _ _ _ A
 have hscalar (c:K):
     phi (algebraMap K (CoordinateField K C.1) c)=
       algebraMap E (CoordinateField E D.1) (algebraMap K E c):=by
   have h:=hphi (MvPolynomial.C c)
   simpa [ev,mu,scalarPolynomialMap] using h
 have hHne:ev H≠0:=by
   intro hz
   have:mu H∈RingHom.ker evD.toRingHom:=hz
   rw [coordinateEvaluation_ker E D.1] at this
   exact hH this
 have hNzero:evD N=0:=by
   apply RingHom.mem_ker.mp
   change N∈RingHom.ker (coordinateEvaluation E D.1).toRingHom
   rw [coordinateEvaluation_ker E D.1]
   exact hN
 have hconst:evD (MvPolynomial.C t)=algebraMap E (CoordinateField E D.1) t:=
   evD.commutes t
 have hrel:ev H*(algebraMap E (CoordinateField E D.1) t-ev Q)=ev U*ev G:=by
   apply sub_eq_zero.mp
   simpa only [N,movingEquation,map_sub,map_mul,hconst,
     ev,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hNzero
 have hjmap:phi (movingValue C.1 H G Q U)=
     algebraMap E (CoordinateField E D.1) t:=by
   unfold movingValue
   rw [map_add,map_div₀,map_mul,hphi Q,hphi U,hphi G,hphi H]
   have hd:ev U*ev G/ev H=algebraMap E (CoordinateField E D.1) t-ev Q:=by
     apply (div_eq_iff hHne).mpr
     simpa only [mul_comm] using hrel.symm
   rw [hd]
   ring
 letI:Algebra (RatFunc K) (CoordinateField K C.1):=
   (elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) hj).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) (CoordinateField K C.1):=hfinite
 have hdiag:
     (algebraMap E (CoordinateField E D.1)).comp (elementEmbedding K E t ht).toRingHom=
       phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1)):=
   rational_base_diagram (movingValue C.1 H G Q U) hj t ht phi hscalar hjmap
 have halg:∀ i,IsAlgebraic E (coordinate E D.1 i):=by
   intro i
   have hint:=IsIntegral.map_of_comp_eq (elementEmbedding K E t ht).toRingHom
     phi hdiag (IsIntegral.of_finite (RatFunc K) (coordinate K C.1 i))
   have hcoord:phi (coordinate K C.1 i)=coordinate E D.1 i:=by
     simpa only [coordinate,ev,evD,RingHom.comp_apply,mu,scalarPolynomialMap,
       MvPolynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hphi (MvPolynomial.X i)
   rw [hcoord] at hint
   exact hint.isAlgebraic
 obtain ⟨point,hpoint⟩:=eq_point_kernel_of_coordinates_algebraic E D.1 halg
 exact regularComponent_ne_point E _ _ _ D point hpoint
end
end ProximityPrize.SubmissionLower.RCN208
