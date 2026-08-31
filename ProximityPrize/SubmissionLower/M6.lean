import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Y5
import ProximityPrize.SubmissionLower.I7
namespace ProximityPrize.SubmissionLower.RCN202
open scoped Classical BigOperators
open RCN002 RCN072 RCN264
open RCN207 RCN208
open RCN134 RCN084
open RCN095 RCN341
open RCN037
open RCN076
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
variable [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
local notation "Poly" => MvPolynomial (Fin 3) K
local notation "PE" => MvPolynomial (Fin 3) E
def rationalVariable (K:Type) [Field K]:RatFunc K:=
 algebraMap (Polynomial K) (RatFunc K) Polynomial.X
theorem eliminated_not_mem_nonpoint
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (C:RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=
     movingValue C.1 H G Q U)
   (D:Ideal PE) [D.IsPrime]
   (hnonpoint:∀ v:Fin 3 → E,D≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (hF:scalarPolynomialMap K E F∈D)
   (hN:movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (rationalVariable K))∈D)
   (hH:scalarPolynomialMap K E H∉D) (hU:scalarPolynomialMap K E U∉D)
   (hbelow:D.comap (scalarPolynomialMap K E) ≤ C.1):
   eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
     (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
     (algebraMap (RatFunc K) E (rationalVariable K))∉D:=by
 intro hA
 let mu:=scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (rationalVariable K)
 let evD:=coordinateEvaluation E D
 let ev:=evD.toRingHom.comp mu
 have hTor:mu (filteredCut k B H G)∈D:=by
   rw [map_filteredCut]
   exact original_mem_of_eliminated_mem D k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hA hU
 have hcut:cutIdeal K F (filteredCut k B H G) ≤ D.comap mu:=by
   apply Ideal.span_le.mpr
   intro A hA
   rcases (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hA) with rfl | rfl
   · exact hF
   · exact hTor
 have hmin:=(mem_componentFamily K F (filteredCut k B H G) C.1).mp
   (regularComponent_mem K _ _ _ C)
 have hcontract:D.comap mu=C.1:=
   le_antisymm hbelow (hmin.2 ⟨inferInstance,hcut⟩ hbelow)
 have hker:RingHom.ker ev=C.1:=by
   rw [show RingHom.ker ev=(RingHom.ker evD.toRingHom).comap mu from rfl,
     coordinateEvaluation_ker E D]
   exact hcontract
 let phi:=coordinateFieldMap C.1 ev hker
 have hphi (A:Poly):phi (coordinateEvaluation K C.1 A)=ev A:=
   coordinateFieldMap_eval _ _ _ A
 have hscalar (c:K):phi (algebraMap K (CoordinateField K C.1) c)=
     algebraMap E (CoordinateField E D) (algebraMap K E c):=by
   simpa [ev,mu,scalarPolynomialMap] using hphi (MvPolynomial.C c)
 have hHne:ev H≠0:=by
   intro hz
   have:mu H∈RingHom.ker evD.toRingHom:=hz
   rw [coordinateEvaluation_ker E D] at this
   exact hH this
 have hNzero:evD (movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   apply RingHom.mem_ker.mp
   change _∈RingHom.ker (coordinateEvaluation E D).toRingHom
   rwa [coordinateEvaluation_ker E D]
 have hrel:ev H*(algebraMap E (CoordinateField E D) t-ev Q)=ev U*ev G:=by
   have hconst:evD (MvPolynomial.C t)=algebraMap E (CoordinateField E D) t:=evD.commutes t
   apply sub_eq_zero.mp
   simpa only [movingEquation,map_sub,map_mul,hconst,
     ev,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hNzero
 have hjmap:phi (movingValue C.1 H G Q U)=algebraMap E (CoordinateField E D) t:=by
   unfold movingValue
   rw [map_add,map_div₀,map_mul,hphi Q,hphi U,hphi G,hphi H]
   have hd:ev U*ev G/ev H=algebraMap E (CoordinateField E D) t-ev Q:=by
     apply (div_eq_iff hHne).mpr
     simpa only [mul_comm] using hrel.symm
   rw [hd];ring
 have hdiag:(algebraMap E (CoordinateField E D)).comp (algebraMap (RatFunc K) E)=
     phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1)):=by
   apply IsFractionRing.ringHom_ext (A:=Polynomial K)
   intro p
   have hp:((algebraMap E (CoordinateField E D)).comp (algebraMap (RatFunc K) E)).comp
       (algebraMap (Polynomial K) (RatFunc K))=
       (phi.comp (algebraMap (RatFunc K) (CoordinateField K C.1))).comp
         (algebraMap (Polynomial K) (RatFunc K)):=by
     apply Polynomial.ringHom_ext
     · intro c
       change algebraMap E (CoordinateField E D)
         (algebraMap (RatFunc K) E (algebraMap K (RatFunc K) c))=
         phi (algebraMap (RatFunc K) (CoordinateField K C.1) (algebraMap K (RatFunc K) c))
       rw [←IsScalarTower.algebraMap_apply K (RatFunc K) E,
         ←IsScalarTower.algebraMap_apply K (RatFunc K) (CoordinateField K C.1),hscalar]
     · change algebraMap E (CoordinateField E D) t=
         phi (algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K))
       rw [hj];exact hjmap.symm
   exact RingHom.congr_fun hp p
 have halg:∀ i,IsAlgebraic E (coordinate E D i):=by
   intro i
   have hint:=IsIntegral.map_of_comp_eq (algebraMap (RatFunc K) E) phi hdiag
     (IsIntegral.of_finite (RatFunc K) (coordinate K C.1 i))
   have hcoord:phi (coordinate K C.1 i)=coordinate E D i:=by
     simpa only [coordinate,ev,evD,RingHom.comp_apply,mu,scalarPolynomialMap,
       MvPolynomial.map_X,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hphi (MvPolynomial.X i)
   rw [hcoord] at hint
   exact hint.isAlgebraic
 obtain ⟨v,hv⟩:=eq_point_kernel_of_coordinates_algebraic E D halg
 exact hnonpoint v hv
theorem embedding_point_certificate
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (C:RegularComponent K F (filteredCut k B H G) H)
   [Algebra (RatFunc K) (CoordinateField K C.1)]
   [IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   (hj:algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=
     movingValue C.1 H G Q U) (hU:U∉C.1)
   (f:CoordinateField K C.1 →ₐ[RatFunc K] E):
   let mu:=scalarPolynomialMap K E
   let t:=algebraMap (RatFunc K) E (rationalVariable K)
   let v:=embeddingPoint C.1 (f.restrictScalars K)
   let N:=movingEquation (mu H) (mu G) (mu Q) (mu U) t
   let A:=eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t
   MvPolynomial.eval v (mu F)=0∧MvPolynomial.eval v N=0∧
     MvPolynomial.aeval v A=0∧MvPolynomial.eval v (mu H*mu U)≠0∧
     IsolatedPoint (mu F) N A v:=by
 dsimp only
 let mu:=scalarPolynomialMap K E
 let t:=algebraMap (RatFunc K) E (rationalVariable K)
 let v:=embeddingPoint C.1 (f.restrictScalars K)
 let ev:=MvPolynomial.eval v
 have hev (A:Poly):ev (mu A)=f (coordinateEvaluation K C.1 A):=by
   have h:=AlgHom.congr_fun (embeddingPoint_aeval C.1 (f.restrictScalars K)) A
   change MvPolynomial.eval v (MvPolynomial.map (algebraMap K E) A)=_
   rw [MvPolynomial.eval_map]
   exact h
 have hz (A:Poly) (hA:A∈C.1):ev (mu A)=0:=by
   rw [hev]
   have ha:coordinateEvaluation K C.1 A=0:=by
     apply RingHom.mem_ker.mp
     change A∈RingHom.ker (coordinateEvaluation K C.1).toRingHom
     rwa [coordinateEvaluation_ker K C.1]
   rw [ha,map_zero]
 have hne (A:Poly) (hA:A∉C.1):ev (mu A)≠0:=by
   rw [hev]
   exact fun h↦hA (by
     rw [←coordinateEvaluation_ker K C.1]
     exact (map_eq_zero_iff f f.injective).mp h)
 have hHne:=hne H (regularComponent_H_not_mem K _ _ _ C)
 have hUne:=hne U hU
 have hjval:ev (mu Q)+ev (mu U)*ev (mu G)/ev (mu H)=t:=by
   simp only [hev]
   have h:=f.commutes (rationalVariable K)
   rw [hj] at h
   simpa only [movingValue,map_add,map_div₀,map_mul] using h
 have hN:ev (movingEquation (mu H) (mu G) (mu Q) (mu U) t)=0:=by
   have hevC:ev (MvPolynomial.C t)=t:=by simp [ev]
   simp only [movingEquation,map_sub,map_mul,hevC]
   have h:=(div_eq_iff hHne).mp (show ev (mu U)*ev (mu G)/ev (mu H)=t-ev (mu Q) by
     linear_combination hjval)
   linear_combination-h
 have hA:ev (eliminatedCut k (fun j↦mu (B j)) (mu Q) (mu U) t)=0:=by
   apply (eliminatedCut_zero_iff ev k (fun j↦mu (B j))
     (mu H) (mu G) (mu Q) (mu U) t hN hHne hUne).mpr
   rw [←map_filteredCut]
   exact hz _ (regularComponent_T_mem K _ _ _ C)
 refine ⟨hz F (regularComponent_G_mem K _ _ _ C),hN,hA,?_,?_⟩
 · simpa only [map_mul] using mul_ne_zero hHne hUne
 · intro D hD hn hp hDF hDN
   letI:=hD
   apply eliminated_not_mem_nonpoint F H G Q U k B C hj D hn hDF hDN
   · exact fun h↦hHne (hp h)
   · exact fun h↦hUne (hp h)
   · exact comap_le_of_embedding_point C.1 (f.restrictScalars K) D hp
abbrev fiberEquation (H G Q U:Poly):PE:=
 movingEquation (scalarPolynomialMap K E H) (scalarPolynomialMap K E G)
   (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
   (algebraMap (RatFunc K) E (rationalVariable K))
abbrev fiberCut (k:ℕ) (B:Fin (k+1) → Poly) (Q U:Poly):PE:=
 eliminatedCut k (fun j↦scalarPolynomialMap K E (B j))
   (scalarPolynomialMap K E Q) (scalarPolynomialMap K E U)
   (algebraMap (RatFunc K) E (rationalVariable K))
theorem sum_moving_degrees_le
   (F H G Q U:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     IsScalarTower K (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     FiniteDimensional (RatFunc K) (CoordinateField K C.1)]
   [∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1)]
   (hj:∀ C:RegularComponent K F (filteredCut k B H G) H,
     algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=movingValue C.1 H G Q U)
   (hU:∀ C:RegularComponent K F (filteredCut k B H G) H,U∉C.1)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (p q r:FlagDegree) (hFp:PolynomialInFlag p F)
   (hNq:PolynomialInFlag q (fiberEquation (E:=E) H G Q U))
   (hAr:PolynomialInFlag r (fiberCut (E:=E) k B Q U))
   (c:ℕ) [CharP E c] (hdeg:p.zOnly+p.yz+p.all < c)
   (hmix:2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c):
   (∑ C:RegularComponent K F (filteredCut k B H G) H,
     Module.finrank (RatFunc K) (CoordinateField K C.1)) ≤ flagMixed p q r:=by
 classical
 let mu:=scalarPolynomialMap K E
 let N:=fiberEquation (E:=E) H G Q U
 let A:=fiberCut (E:=E) k B Q U
 let R:=mu H*mu U
 let P:=fun C:RegularComponent K F (filteredCut k B H G) H↦C.1
 let points:=genericFiberPoints (B:=RatFunc K) (L:=E) P
 have hc:∀ v∈points,MvPolynomial.eval v (mu F)=0∧MvPolynomial.eval v N=0∧
     MvPolynomial.aeval v A=0∧MvPolynomial.eval v R≠0∧IsolatedPoint (mu F) N A v:=by
   intro v hv
   obtain ⟨⟨C,f⟩,_,rfl⟩:=Finset.mem_image.mp hv
   exact embedding_point_certificate F H G Q U k B C (hj C) (hU C) f
 have hinj:Function.Injective mu:=
   MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective
 have hMF:mu F≠0:=fun h↦hF (hinj (h.trans (map_zero mu).symm))
 have hMFp:=inFlag_map (algebraMap K E) hFp
 obtain ⟨base,hY,hZ⟩:=exists_small_projection_data (mu F) N R hMF p q hMFp hNq c hdeg hmix
 rw [←genericFiberPoints_card (B:=RatFunc K) (L:=E) P Subtype.val_injective]
 apply isolated_points_card_le (mu F) N A R p q r hMF
   hMFp hNq hAr base hY hZ points
 · intro v hv
   have hv:=hc v hv
   apply exists_active_factor_of_isolated (mu F) N A R hMF v hv.1 hv.2.2.1 hv.2.2.2.1
   · have hH:MvPolynomial.eval v (mu H)≠0:=
       (mul_ne_zero_iff.mp (by simpa only [R,map_mul] using hv.2.2.2.1)).1
     exact map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval v) (mu F) (mu H)
       (scalar_derivative_span F H hderiv) hv.1 hH
   · exact hv.2.2.2.2
 · exact fun v hv↦(hc v hv).2.1
 · exact fun v hv↦(hc v hv).2.2.1
 · exact fun v hv↦(hc v hv).2.2.2.1
 · intro g C v hv hp
   have hCF:=C.1.mem_of_dvd (activeFactors_spec (mu F) N g).2.1
     (regularComponent_G_mem E g.1 N R C)
   exact (hc v hv).2.2.2.2 C.1 inferInstance (regularComponent_ne_point E g.1 N R C)
     hp hCF (regularComponent_T_mem E g.1 N R C)
theorem fiber_small_flags (a b s k:ℕ) (C:FlagDegree)
   (H G Q U:Poly) (B:Fin (k+1) → Poly) (c:Fin (k+1) → FlagDegree)
   (hH:PolynomialInFlag ⟨a,b+1,s+1⟩ H) (hG:PolynomialInFlag ⟨a,b,s+3⟩ G)
   (hQ:PolynomialInFlag (2 • unitAllFlag) Q) (hU:PolynomialInFlag unitYZFlag U)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   PolynomialInFlag ⟨a,b+1,s+3⟩ (fiberEquation (E:=E) H G Q U)∧
   PolynomialInFlag (C+k • (⟨a,b+1,s+2⟩:FlagDegree)) (fiberCut (E:=E) k B Q U):=by
 constructor
 · exact movingEquation_inFlag a b s _ _ _ _ _
     (inFlag_map (algebraMap K E) hH) (inFlag_map (algebraMap K E) hG)
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU)
 · exact eliminatedCut_small_flag a b s k C _ _ _ _ c
     (fun j↦inFlag_map (algebraMap K E) (hB j))
     (inFlag_map (algebraMap K E) hQ) (inFlag_map (algebraMap K E) hU) hc
end
end ProximityPrize.SubmissionLower.RCN202
