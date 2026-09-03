import ProximityPrize.SubmissionLower.PackedLegacyCore2

/-! Packed from ProximityPrize.SubmissionLower.M3. -/
section PackedLegacy_M3
namespace ProximityPrize.SubmissionLower.RCN199
open scoped Classical BigOperators WithZero
open RCN002 RCN344 RCN341 RCN095 RCN114 RCN295 RCN187 RCN207 RCN064 RCN204 RCN271 RCN257
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K:Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 3) K
structure MovingPoleBudget (P:Ideal Poly) [P.IsPrime] (H G:Poly) where
 zCost:ℕ
 yzCost:ℕ
 allCost:ℕ
 movingCost:ℕ
 zPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitZFlag)) ≤ (zCost:ℤ)
 yzPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitYZFlag)) ≤ (yzCost:ℤ)
 allPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,exponentSetPoleWeight v.val (coordinate K P) (flagSupport unitAllFlag)) ≤ (allCost:ℤ)
 movingPole:∀ W:Finset (Place K (CoordinateField K P)),
   (∑ v∈W,movingPoleTarget P H G v) ≤ (movingCost:ℤ)
namespace MovingPoleBudget
variable {P:Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime]
 {H G:MvPolynomial (Fin 3) K}
def weightedCost (budget:MovingPoleBudget P H G) (r:FlagDegree):ℕ:=
 r.zOnly*budget.zCost+r.yz*budget.yzCost+r.all*budget.allCost
theorem sum_flagPole_le (budget:MovingPoleBudget P H G) (r:FlagDegree)
   (W:Finset (Place K (CoordinateField K P))):
   (∑ v∈W,flagPole v.val (coordinate K P) r) ≤ (budget.weightedCost r:ℤ):=by
 have hz:=budget.zPole W
 have hy:=budget.yzPole W
 have ha:=budget.allPole W
 simp only [exponentSetPoleWeight_unitZ] at hz
 simp only [exponentSetPoleWeight_unitYZ] at hy
 simp only [exponentSetPoleWeight_unitAll] at ha
 have h:=add_le_add (add_le_add
   (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg r.zOnly))
   (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg r.yz)))
   (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg r.all))
 simpa only [flagPole,Finset.sum_add_distrib,←Finset.mul_sum,
   weightedCost,Nat.cast_add,Nat.cast_mul] using h
theorem sum_filteredCut_pole_le (budget:MovingPoleBudget P H G)
   (a b s k:ℕ) (C:FlagDegree) (B:Fin (k+1) → Poly)
   (c:Fin (k+1) → FlagDegree) (hH:H∉P)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (W:Finset (Place K (CoordinateField K P))):
   (∑ v∈W,poleOrder v.val (coordinateEvaluation K P (filteredCut k B H G)/
     (coordinateEvaluation K P H)^k)) ≤
     (budget.weightedCost C+k*(budget.weightedCost (⟨a,b,s⟩:FlagDegree)+budget.movingCost):ℕ):=by
 have hHne:coordinateEvaluation K P H≠0:=by
   intro hz
   apply hH
   rw [←coordinateEvaluation_ker K P]
   exact hz
 have hloc:=Finset.sum_le_sum (s:=W) (fun v _↦
   coordinate_filteredCut_pole_le P v a b s k C B H G c hHne hB hc)
 have hflagC:=budget.sum_flagPole_le C W
 have hflagN:=budget.sum_flagPole_le (⟨a,b,s⟩:FlagDegree) W
 have hmoving:=budget.movingPole W
 calc
   _ ≤ ∑ v∈W,(flagPole v.val (coordinate K P) C+(k:ℤ)*
       (flagPole v.val (coordinate K P) (⟨a,b,s⟩:FlagDegree)+movingPoleTarget P H G v)):=hloc
   _=(∑ v∈W,flagPole v.val (coordinate K P) C)+(k:ℤ)*
       ((∑ v∈W,flagPole v.val (coordinate K P) (⟨a,b,s⟩:FlagDegree))+
         ∑ v∈W,movingPoleTarget P H G v):=by
     simp only [Finset.sum_add_distrib,←Finset.mul_sum]
   _ ≤ (budget.weightedCost C:ℤ)+(k:ℤ)*
       ((budget.weightedCost (⟨a,b,s⟩:FlagDegree):ℤ)+budget.movingCost):=
     add_le_add hflagC (mul_le_mul_of_nonneg_left (add_le_add hflagN hmoving) (Int.natCast_nonneg k))
   _=_:=by push_cast;rfl
theorem zero_le [IsAlgClosed K] (budget:MovingPoleBudget P H G)
   (base:SeparableLiteralCoordinate P) (a b s k:ℕ) (C:FlagDegree)
   (B:Fin (k+1) → Poly) (c:Fin (k+1) → FlagDegree)
   (hH:H∉P) (hA:filteredCut k B H G∉P)
   (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree)):
   FiniteRegularZeroSetBound P H (filteredCut k B H G)
     (budget.weightedCost C+k*(budget.weightedCost (⟨a,b,s⟩:FlagDegree)+budget.movingCost)):=by
 apply finite_regular_zero_bound_of_separator K P base H (filteredCut k B H G) k _ hA hH
 intro W
 simpa only [RCN346.poleOrder,coordinateEvaluation_eq_aeval] using
   budget.sum_filteredCut_pole_le a b s k C B c hH hB hc W
end MovingPoleBudget
end
end ProximityPrize.SubmissionLower.RCN199
end PackedLegacy_M3

/-! Packed from ProximityPrize.SubmissionLower.I7. -/
section PackedLegacy_I7
namespace ProximityPrize.SubmissionLower.RCN076
open RCN208
noncomputable section
set_option autoImplicit false
variable {K E:Type} [Field K] [Field E]
local notation "Poly" => MvPolynomial (Fin 3) K
theorem derivative_eq_mem_span (F H:Poly)
   (h:H=MvPolynomial.pderiv (1:Fin 3) F):
   H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
 rw [h]
 exact Ideal.subset_span (by simp)
theorem pderiv_mem_span_of_mul (F U Q:Poly) (hQ:Q=F*U):
   MvPolynomial.pderiv (1:Fin 3) Q∈
     Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
 apply Ideal.mem_span_pair.mpr
 refine ⟨MvPolynomial.pderiv (1:Fin 3) U,U,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul]
 ring
theorem pderiv_mem_span_of_dvd (F Q:Poly) (hFQ:F∣Q):
   MvPolynomial.pderiv (1:Fin 3) Q∈
     Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly):=by
 obtain ⟨U,hU⟩:=hFQ
 exact pderiv_mem_span_of_mul F U Q hU
theorem map_derivative_span (φ:K →+*E) (F H:Poly)
   (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly)):
   MvPolynomial.map φ H∈Ideal.span
     ({MvPolynomial.map φ F,
       MvPolynomial.pderiv (1:Fin 3) (MvPolynomial.map φ F)}:
         Set (MvPolynomial (Fin 3) E)):=by
 obtain ⟨A,B,hAB⟩:=Ideal.mem_span_pair.mp h
 apply Ideal.mem_span_pair.mpr
 refine ⟨MvPolynomial.map φ A,MvPolynomial.map φ B,?_⟩
 rw [MvPolynomial.pderiv_map]
 simpa only [map_add,map_mul] using congrArg (MvPolynomial.map φ) hAB
theorem scalar_derivative_span [Algebra K E] (F H:Poly)
   (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly)):
   scalarPolynomialMap K E H∈Ideal.span
     ({scalarPolynomialMap K E F,
       MvPolynomial.pderiv (1:Fin 3) (scalarPolynomialMap K E F)}:
         Set (MvPolynomial (Fin 3) E)):=
 map_derivative_span (algebraMap K E) F H h
theorem map_pderiv_ne_zero_of_mem_span (ev:Poly →+*E) (F H:Poly)
   (h:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (hF:ev F=0) (hH:ev H≠0):
   ev (MvPolynomial.pderiv (1:Fin 3) F)≠0:=by
 intro hD
 obtain ⟨A,B,hAB⟩:=Ideal.mem_span_pair.mp h
 apply hH
 rw [←hAB,map_add,map_mul,map_mul,hF,hD]
 ring
end
end ProximityPrize.SubmissionLower.RCN076
end PackedLegacy_I7

/-! Packed from ProximityPrize.SubmissionLower.M6. -/
section PackedLegacy_M6
namespace ProximityPrize.SubmissionLower.RCN202
open scoped Classical BigOperators
open RCN002 RCN072 RCN264 RCN207 RCN208 RCN134 RCN084 RCN095 RCN341 RCN037 RCN076
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 300000
variable {K E:Type} [Field K] [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
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
end PackedLegacy_M6

/-! Packed from ProximityPrize.SubmissionLower.M9. -/
section PackedLegacy_M9
namespace ProximityPrize.SubmissionLower.RCN209
open scoped Classical BigOperators WithZero
open RCN002 RCN264 RCN344 RCN341 RCN022 RCN207 RCN208 RCN064 RCN202 RCN095 RCN187
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K
theorem exists_separable_moving_coordinates (F A H G:Poly)
   (base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1):
   ∃ (Q U:Poly) (J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1)),
     PolynomialInFlag (2 • unitAllFlag) Q∧PolynomialInFlag unitYZFlag U∧
     ∀ C:RegularComponent K F A H,
       U∉C.1∧SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U∧
       (∀ v:Place K (CoordinateField K C.1),
         poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
           movingPoleTarget C.1 H G v)∧
       (∀ v∈movingRelevantPlaces (base C) (movingRatio C.1 H G),
         v.val (coordinateEvaluation K C.1 U)=WithZero.exp
           (max (poleOrder v.val (coordinate K C.1 0)) (poleOrder v.val (coordinate K C.1 2)))):=by
 obtain ⟨Q,U,hQ,hU,h⟩:=exists_common_original_projection F A H G base
 have gate (C:RegularComponent K F A H):=moving_projection_gate (base C) H G Q U (h C).2.1
 let J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1):=
   fun C↦{
     embedding:=elementEmbedding K (CoordinateField K C.1) (movingValue C.1 H G Q U) (gate C).choose
     finite:=(gate C).choose_spec.1
     separable:=(gate C).choose_spec.2.1}
 have hv (C:RegularComponent K F A H):
     SeparableCoordinate.value K (CoordinateField K C.1) (J C)=movingValue C.1 H G Q U:=
   elementEmbedding_variable K (CoordinateField K C.1) _ (gate C).choose
 refine ⟨Q,U,J,hQ,hU,fun C↦⟨(h C).1,hv C,?_,(h C).2.2.2⟩⟩
 intro v
 rw [hv C]
 exact (h C).2.2.1 v
variable {E:Type} [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
theorem exists_moving_projection_family (F H G:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (base:∀ C:RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (p:FlagDegree) (hFp:PolynomialInFlag p F) (a b s:ℕ) (C0:FlagDegree)
   (hH:PolynomialInFlag (⟨a,b+1,s+1⟩:FlagDegree) H)
   (hG:PolynomialInFlag (⟨a,b,s+3⟩:FlagDegree) G)
   (c:Fin (k+1) → FlagDegree) (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar):
   ∃ J:∀ C:RegularComponent K F (filteredCut k B H G) H,
       SeparableCoordinate K (CoordinateField K C.1),
     (∀ (C:RegularComponent K F (filteredCut k B H G) H)
         (v:Place K (CoordinateField K C.1)),
       poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
         movingPoleTarget C.1 H G v)∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,
       SeparableCoordinate.degree K (CoordinateField K C.1) (J C)) ≤
       flagMixed p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree)):=by
 classical
 obtain ⟨Q,U,J,hQ,hU,hJ⟩:=exists_separable_moving_coordinates F (filteredCut k B H G) H G base
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).embedding.toRingHom.toAlgebra
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     IsScalarTower K (RatFunc K) (CoordinateField K C.1):=fun C↦
       IsScalarTower.of_algebraMap_eq fun a↦((J C).embedding.commutes a).symm
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     FiniteDimensional (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).finite
 letI:∀ C:RegularComponent K F (filteredCut k B H G) H,
     Algebra.IsSeparable (RatFunc K) (CoordinateField K C.1):=fun C↦(J C).separable
 have hj (C:RegularComponent K F (filteredCut k B H G) H):
     algebraMap (RatFunc K) (CoordinateField K C.1) (rationalVariable K)=movingValue C.1 H G Q U:=
   (hJ C).2.1
 have hdeg:p.zOnly+p.yz+p.all < pchar:=by
   nlinarith
 obtain ⟨hN,hA⟩:=fiber_small_flags (E:=E) a b s k C0 H G Q U B c hH hG hQ hU hB hc
 have hcount:=sum_moving_degrees_le (E:=E) F H G Q U k B hj (fun C↦(hJ C).1)
   hF hderiv p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree))
   hFp hN hA pchar hdeg hmix
 refine ⟨J,fun C v↦(hJ C).2.2.1 v,?_⟩
 simpa only [SeparableCoordinate.degree] using hcount
end
end ProximityPrize.SubmissionLower.RCN209
end PackedLegacy_M9

/-! Packed from ProximityPrize.SubmissionLower.M4. -/
section PackedLegacy_M4
namespace ProximityPrize.SubmissionLower.RCN200
open scoped Classical BigOperators WithZero
open RCN002 RCN264 RCN344 RCN341 RCN046 RCN095 RCN295 RCN187 RCN207 RCN064 RCN209 RCN199
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K:Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K
def budgetOfProjections (F A H G:Poly)
   {base:∀ C:RegularComponent K F A H,SeparableLiteralCoordinate C.1}
   {p q:FlagDegree} (unit:AdaptiveUnitProjectionFamily base p q)
   (J:∀ C:RegularComponent K F A H,SeparableCoordinate K (CoordinateField K C.1))
   (hJ:∀ (C:RegularComponent K F A H) (v:Place K (CoordinateField K C.1)),
     poleOrder v.val (SeparableCoordinate.value K (CoordinateField K C.1) (J C))=
       movingPoleTarget C.1 H G v) (C:RegularComponent K F A H):
   MovingPoleBudget C.1 H G where
 zCost:=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)
 yzCost:=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)
 allCost:=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C)
 movingCost:=SeparableCoordinate.degree K (CoordinateField K C.1) (J C)
 zPole:=unit.toAdaptiveUnitPoleBudget.zPole C
 yzPole:=unit.toAdaptiveUnitPoleBudget.yzPole C
 allPole:=unit.toAdaptiveUnitPoleBudget.allPole C
 movingPole:=by
   intro W
   calc
     (∑ v∈W,movingPoleTarget C.1 H G v)=
         ∑ v∈W,RCN346.poleOrder K (CoordinateField K C.1) v
           (SeparableCoordinate.value K (CoordinateField K C.1) (J C)):=by
       apply Finset.sum_congr rfl
       intro v _
       exact (hJ C v).symm
     _ ≤ (SeparableCoordinate.degree K (CoordinateField K C.1) (J C):ℤ):=
       SeparableCoordinate.finite_sum_pole_le_degree K (CoordinateField K C.1) (J C) W
variable {E:Type} [Field E] [IsAlgClosed E]
 [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
theorem exists_moving_pole_budget_family (F H G:Poly) (k:ℕ) (B:Fin (k+1) → Poly)
   (base:∀ C:RegularComponent K F (filteredCut k B H G) H,SeparableLiteralCoordinate C.1)
   (p firstCutFlag:FlagDegree) (unit:AdaptiveUnitProjectionFamily base p firstCutFlag)
   (hF:F≠0)
   (hderiv:H∈Ideal.span ({F,MvPolynomial.pderiv (1:Fin 3) F}:Set Poly))
   (hFp:PolynomialInFlag p F) (a b s:ℕ) (C0:FlagDegree)
   (hH:PolynomialInFlag (⟨a,b+1,s+1⟩:FlagDegree) H)
   (hG:PolynomialInFlag (⟨a,b,s+3⟩:FlagDegree) G)
   (c:Fin (k+1) → FlagDegree) (hB:∀ j,PolynomialInFlag (c j) (B j))
   (hc:∀ j,c j+(k-j.val) • (⟨a,b+1,s+1⟩:FlagDegree)+
     j.val • (⟨a,b,s+3⟩:FlagDegree)=C0+k • (⟨2*a,2*b+1,2*s+3⟩:FlagDegree))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < pchar):
   ∃ budget:∀ C:RegularComponent K F (filteredCut k B H G) H,MovingPoleBudget C.1 H G,
     (∀ C,(budget C).zCost=coordinateDegree K (CoordinateField K C.1) (unit.zProjection C)∧
       (budget C).yzCost=coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C)∧
       (budget C).allCost=coordinateDegree K (CoordinateField K C.1) (unit.allProjection C))∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).zCost) ≤
       flagMixed p firstCutFlag unitZFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).yzCost) ≤
       flagMixed p firstCutFlag unitYZFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).allCost) ≤
       flagMixed p firstCutFlag unitAllFlag∧
     (∑ C:RegularComponent K F (filteredCut k B H G) H,(budget C).movingCost) ≤
       flagMixed p (⟨a,b+1,s+3⟩:FlagDegree) (C0+k • (⟨a,b+1,s+2⟩:FlagDegree)):=by
 obtain ⟨J,hJ,hdegree⟩:=exists_moving_projection_family (E:=E) F H G k B base
   hF hderiv p hFp a b s C0 hH hG c hB hc pchar hmix
 refine ⟨budgetOfProjections F (filteredCut k B H G) H G unit J hJ,?_,?_,?_,?_,?_⟩
 · exact fun C↦⟨rfl,rfl,rfl⟩
 · exact unit.sum_zDegree_le
 · exact unit.sum_yzDegree_le
 · exact unit.sum_allDegree_le
 · exact hdegree
end
end ProximityPrize.SubmissionLower.RCN200
end PackedLegacy_M4

/-! Packed from ProximityPrize.SubmissionLower.M5. -/
section PackedLegacy_M5
namespace ProximityPrize.SubmissionLower.RCN201
open scoped Classical
open RCN198 RCN136 RCN313 RCN095 RCN234 RCN156 RCN057 RCN055
noncomputable section
set_option maxHeartbeats 3000000
variable {K Ω:Type} [Field K] [Field Ω]
private theorem mapped_flag (φ:Polynomial K →+*Ω)
   (Q:MvPolynomial (Fin 4) K) (a b s:ℕ)
   (hR:wt residualSWeights Q ≤ s)
   (hM:wt residualYSWeights Q ≤ b+s)
   (hT:wt residualTotalWeights Q ≤ a+b+s):
   PolynomialInFlag ⟨a,b,s⟩ (surfaceMap φ Q):=by
 intro e he
 obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp (support_surfaceMap_subset φ Q he)
 have hr:=(MvPolynomial.le_weightedTotalDegree residualSWeights hq).trans hR
 have hm:=(MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hM
 have ht:=(MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hT
 simp [RCN081.weight_fin4,residualSWeights] at hr
 simp [RCN081.weight_fin4,residualYSWeights] at hm
 simp [RCN081.weight_fin4,residualTotalWeights] at ht
 exact ⟨hr,hm,ht⟩
private theorem G_weight (w:Fin 4 → ℕ) (t:ℕ)
   (h0:w 0=0) (h1:w 1=t) (h2:w 2=1) (ht:t≤1)
   (F:MvPolynomial (Fin 4) K) (C:ℕ)
   (hC:1≤C) (hF:wt w F≤C):wt w (polyG K F)≤C+1-t:=by
 have hf:WeightBound w F (C:ℤ):=Or.inr (by exact_mod_cast hF)
 have hg:WeightBound w (polyG K F) ((C:ℤ)+1-t):=by
   simpa only [polyG,horizontalDerivation,Derivation.add_apply,
     Derivation.smul_apply,smul_eq_mul] using (hf.horizontal t h0 h1 h2 ht).neg
 rcases hg with hz | hb
 · simp [hz,wt,MvPolynomial.weightedTotalDegree]
 · have htc:t≤C+1:=by omega
   have hb':(wt w (polyG K F):ℤ) ≤ ((C+1-t:ℕ):ℤ):=by
     rw [Nat.cast_sub htc]
     push_cast
     exact hb
   exact_mod_cast hb'
theorem surfaceMap_HG_flags (φ:Polynomial K →+*Ω)
   (a b s:ℕ) (F:MvPolynomial (Fin 4) K)
   (hR:F.degreeOf 2 ≤ s+2)
   (hYR:wt ![0,1,1,0] F ≤ b+s+3)
   (hAll:wt ![0,1,1,1] F ≤ a+b+s+3):
   PolynomialInFlag ⟨a,b+1,s+1⟩ (surfaceMap φ (polyH K F))∧
   PolynomialInFlag ⟨a,b,s+3⟩ (surfaceMap φ (polyG K F)):=by
 have hS:=support_data a b s F hR hYR hAll
 have hr:=hS.s_weight
 have hm:=hS.ys_weight
 have ha:=hS.total_weight
 change wt residualSWeights F≤s+2 at hr
 change wt residualYSWeights F≤b+s+3 at hm
 change wt residualTotalWeights F≤a+b+s+3 at ha
 constructor
 · apply mapped_flag φ (polyH K F) a (b+1) (s+1)
   · simpa [residualSWeights] using wt_polyH_le residualSWeights F (s+2) hr
   · have h:=wt_polyH_le residualYSWeights F (b+s+3) hm
     change wt residualYSWeights (polyH K F) ≤ b+s+3-1 at h
     omega
   · have h:=wt_polyH_le residualTotalWeights F (a+b+s+3) ha
     change wt residualTotalWeights (polyH K F) ≤ a+b+s+3-1 at h
     omega
 · apply mapped_flag φ (polyG K F) a b (s+3)
   · simpa using G_weight residualSWeights 0 rfl rfl rfl (by omega) F
       (s+2) (by omega) hr
   · simpa [Nat.add_assoc] using G_weight residualYSWeights 1 rfl rfl rfl (by omega) F
       (b+s+3) (by omega) hm
   · have h:=G_weight residualTotalWeights 1 rfl rfl rfl (by omega) F
       (a+b+s+3) (by omega) ha
     omega
end
end ProximityPrize.SubmissionLower.RCN201
end PackedLegacy_M5

/-! Packed from ProximityPrize.SubmissionLower.M7. -/
section PackedLegacy_M7
namespace ProximityPrize.SubmissionLower.RCN203
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN201 RCN275 RCN287
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
 [IsScalarTower Ω (RatFunc Ω) E]
def paddedCut (a b s d:ℕ):FlagDegree:=
 RCN206.centreFlag a b s+
   d • RCN206.directionFlag a b s
theorem mixed_add_second (p q r t:FlagDegree):
   flagMixed p (q+r) t=flagMixed p q t+flagMixed p r t:=by
 simp only [flagMixed,add_zOnly,add_yz,add_all]
 ring
theorem mixed_affine_third (p q C R:FlagDegree) (k:ℕ):
   flagMixed p q (C+k • R)=flagMixed p q C+k*flagMixed p q R:=by
 simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
 ring
theorem mixed_sharp_le_padded (a b s d:ℕ) (p r:FlagDegree):
   flagMixed p (sharpResidualAgreementFlag (support a b s) d) r ≤
     flagMixed p (paddedCut a b s d) r:=by
 have he:paddedCut a b s d=
     sharpResidualAgreementFlag (support a b s) d+direction a b s:=by
   rw [sharp_flag_eq]
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1 <;> simp [paddedCut,RCN206.centreFlag,
     RCN206.directionFlag,direction,unitYZFlag] <;> ring
 rw [he,mixed_add_second]
 exact Nat.le_add_right _ _
theorem exists_actual_cut_budgets
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Ω) (a b s d:ℕ) (xI u0 u1:K)
   (hT:T=agreementPolynomial φ F d xI u0 u1)
   (hF:ResidualSupportData (support a b s) F) (flag:FlagDegree)
   (hG:G≠0) (hdiv:G∣surfaceMap φ F) (hGflag:PolynomialInFlag flag G)
   (base:∀ C:RegularComponent Ω G T (regularitySurface φ F),SeparableLiteralCoordinate C.1)
   (unit:AdaptiveUnitProjectionFamily base flag (sharpResidualAgreementFlag (support a b s) d))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar):
   ∃ budget:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
     (∀ C,(budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C∧
       (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C∧
       (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C)∧
     (∑ C,(budget C).zCost) ≤ flagMixed flag (paddedCut a b s d) unitZFlag∧
     (∑ C,(budget C).yzCost) ≤ flagMixed flag (paddedCut a b s d) unitYZFlag∧
     (∑ C,(budget C).allCost) ≤ flagMixed flag (paddedCut a b s d) unitAllFlag∧
     (∑ C,(budget C).movingCost) ≤ flagMixed flag
       (RCN206.fiberFlag a b s)
       (center a b s+d • RCN206.surfaceFlag a b s):=by
 classical
 obtain ⟨coeffs,cflags,heq,hcoeff,hclass,_⟩:=exists_actual_agreement_certificate
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight d xI u0 u1
 obtain ⟨hHflag,hGcontact⟩:=surfaceMap_HG_flags
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
 have hderiv:regularitySurface φ F∈
     Ideal.span ({G,MvPolynomial.pderiv (1:Fin 3) G}:Set (MvPolynomial (Fin 3) Ω)):=by
   rw [regularitySurface, ←RCN267.surfaceMap_pderiv_R]
   exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
 have hT':T=filteredCut (d-1) coeffs (surfaceMap φ (polyH K F))
     (surfaceMap φ (polyG K F)):=hT.trans heq
 clear hT
 subst T
 obtain ⟨budget,hcost,hz,hyz,ha,hm⟩:=exists_moving_pole_budget_family (E:=E)
   G (regularitySurface φ F) (surfaceMap φ (polyG K F)) (d-1) coeffs
   base flag (sharpResidualAgreementFlag (support a b s) d) unit hG hderiv hGflag
   a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
   (by convert hmix using 1 <;> ring)
 refine ⟨budget,hcost,hz.trans (mixed_sharp_le_padded a b s d flag unitZFlag),
   hyz.trans (mixed_sharp_le_padded a b s d flag unitYZFlag),
   ha.trans (mixed_sharp_le_padded a b s d flag unitAllFlag),hm.trans ?_⟩
 rw [mixed_affine_third,mixed_affine_third]
 exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le d 1)) _
end
end ProximityPrize.SubmissionLower.RCN203
end PackedLegacy_M7

/-! Packed from ProximityPrize.SubmissionLower.J3. -/
section PackedLegacy_J3
namespace ProximityPrize.SubmissionLower.RCN085
open scoped Classical BigOperators
open RCN136 RCN313 RCN238 RCN243 RCN264 RCN341 RCN046 RCN095 RCN199 RCN200 RCN207 RCN198 RCN203 RCN201 RCN275 RCN287 RCN086
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
 [IsScalarTower Ω (RatFunc Ω) E]
theorem exists_firstTail_cut_budgets
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Ω) (a b s w:ℕ) (hw:1 ≤ w)
   (hT:T=globalTailCut φ F (w+1))
   (hF:ResidualSupportData (support a b s) F) (flag:FlagDegree)
   (hG:G≠0) (hdiv:G∣surfaceMap φ F) (hGflag:PolynomialInFlag flag G)
   (base:∀ C:RegularComponent Ω G T (regularitySurface φ F),SeparableLiteralCoordinate C.1)
   (unit:AdaptiveUnitProjectionFamily base flag (sharpResidualAgreementFlag (support a b s) (w+1)))
   (pchar:ℕ) [CharP E pchar]
   (hmix:2*(flag.zOnly+flag.yz+flag.all)*(a+b+s+4) < pchar):
   ∃ budget:∀ C:RegularComponent Ω G T (regularitySurface φ F),
     MovingPoleBudget C.1 (regularitySurface φ F) (surfaceMap φ (polyG K F)),
     (∀ C,(budget C).zCost=unit.toPrimeFlagBudgetFamily.zCost C∧
       (budget C).yzCost=unit.toPrimeFlagBudgetFamily.yzCost C∧
       (budget C).allCost=unit.toPrimeFlagBudgetFamily.allCost C)∧
     (∑ C,(budget C).zCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitZFlag∧
     (∑ C,(budget C).yzCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitYZFlag∧
     (∑ C,(budget C).allCost) ≤ flagMixed flag (paddedCut a b s (w+1)) unitAllFlag∧
     (∑ C,(budget C).movingCost) ≤ flagMixed flag
       (RCN206.fiberFlag a b s)
       (center a b s+(w+1) • RCN206.surfaceFlag a b s):=by
 classical
 obtain ⟨coeffs,cflags,heq,hcoeff,hclass⟩:=globalTailCut_certificate
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight w hw
 obtain ⟨hHflag,hGcontact⟩:=surfaceMap_HG_flags
   φ a b s F hF.coordinate_bounds.2.1 hF.ys_weight hF.total_weight
 have hderiv:regularitySurface φ F∈
     Ideal.span ({G,MvPolynomial.pderiv (1:Fin 3) G}:Set (MvPolynomial (Fin 3) Ω)):=by
   rw [regularitySurface, ←RCN267.surfaceMap_pderiv_R]
   exact RCN076.pderiv_mem_span_of_dvd G (surfaceMap φ F) hdiv
 have hT':T=filteredCut w coeffs (surfaceMap φ (polyH K F))
     (surfaceMap φ (polyG K F)):=hT.trans heq
 clear hT
 subst T
 obtain ⟨budget,hcost,hz,hyz,ha,hm⟩:=exists_moving_pole_budget_family (E:=E)
   G (regularitySurface φ F) (surfaceMap φ (polyG K F)) w coeffs
   base flag (sharpResidualAgreementFlag (support a b s) (w+1)) unit hG hderiv hGflag
   a b s (center a b s) hHflag hGcontact cflags hcoeff hclass pchar
   (by convert hmix using 1 <;> ring)
 refine ⟨budget,hcost,hz.trans (mixed_sharp_le_padded a b s (w+1) flag unitZFlag),
   hyz.trans (mixed_sharp_le_padded a b s (w+1) flag unitYZFlag),
   ha.trans (mixed_sharp_le_padded a b s (w+1) flag unitAllFlag),hm.trans ?_⟩
 rw [mixed_affine_third,mixed_affine_third]
 exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ w)) _
end
end ProximityPrize.SubmissionLower.RCN085
end PackedLegacy_J3

/-! Packed from ProximityPrize.SubmissionLower.ET. -/
section PackedLegacy_ET
namespace ProximityPrize.SubmissionLower.RCN151
open scoped Classical
open RCN136 RCN231 RCN319 RCN313 RCN065 RCN238 RCN160 RCN157 RCN163 RCN156 RCN275 RCN234 RCN094 RCN095 RCN125 RCN162
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
abbrev Poly3 (Omega:Type) [Field Omega]:=MvPolynomial (Fin 3) Omega
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
structure CurveResidualStage
   (phi:Polynomial K →+*Omega) (Gamma:Finset K) (x:Iota → K)
   (p e:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree) (d:ℕ)
   (support:ResidualSupportParameters:=
     ResidualSupportParameters.acceptedSupport) where
 nodes:Finset Iota
 u0:Iota → K
 u1:Iota → K
 selected:K → Polynomial K
 F:Poly4 K
 G:Poly3 Omega
 T:Poly3 Omega
 primeData:RegularPrimeData G T
   (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))
 G_dvd_surface:G∣surfaceMap phi F
 G_flag_support:RCN095.PolynomialInFlag surfaceFlag G
 T_flag_support:RCN095.PolynomialInFlag cutFlag T
 surface_s_weight:wt residualSWeights F ≤ support.s
 surface_ys_weight:wt residualYSWeights F ≤ support.ys
 surface_total_weight:wt residualTotalWeights F ≤ support.total
 x_injective:Set.InjOn x nodes
 degree_le:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d
 solution:∀ gamma∈Gamma,
   specialization K (selected gamma) gamma F=0
 regular:∀ gamma∈Gamma,
   MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
       (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0
 on_prime:∀ gamma∈Gamma,primeData.ideal ≤ RingHom.ker
   (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom
 no_large_pencil:NoLargeSelectedPencil selected Gamma d e
 characteristic_bound:d < p
namespace CurveResidualStage
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K}
 {x:Iota → K} {p e:ℕ} [CharP Omega p]
 {surfaceFlag cutFlag:FlagDegree} {d:ℕ}
 {support:ResidualSupportParameters}
def primeIdeal
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   Ideal (Poly3 Omega):=S.primeData.ideal
def identities
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   Finset Iota:=
 identityNodes phi S.primeIdeal S.F S.nodes x S.u0 S.u1 d
def Agrees
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (gamma:K) (i:Iota):Prop:=
 (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i
local instance
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   ∀ gamma i,Decidable (S.Agrees gamma i):=
 fun _ _↦Classical.propDecidable _
def agreementFiber
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (gamma:K):Finset Iota:=
 S.nodes.filter (S.Agrees gamma)
theorem primeIdeal_isPrime
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   S.primeIdeal.IsPrime:=S.primeData.isPrime
theorem surface_mem_primeIdeal
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   surfaceMap phi S.F∈S.primeIdeal:=by
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 rw [hQ]
 exact S.primeData.ideal.mul_mem_right Q S.primeData.G_mem
theorem regularity_not_mem_primeIdeal
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F)∉
     S.primeIdeal:=
 S.primeData.H_not_mem
theorem agrees_on_identities
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   ∀ gamma∈Gamma,∀ i∈S.identities,S.Agrees gamma i:=by
 let P:=S.primeIdeal
 letI:P.IsPrime:=S.primeIdeal_isPrime
 intro gamma hgamma i hi
 exact selected_agrees_on_identity_nodes
   phi P S.F S.nodes x S.u0 S.u1 p d S.characteristic_bound
   (S.selected gamma) gamma (S.degree_le gamma hgamma)
   (S.solution gamma hgamma) (S.regular gamma hgamma)
   (S.on_prime gamma hgamma) i hi
def ResidualTransition
   {dnext:ℕ}
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (Snext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag dnext support):Prop:=
 ∃ (aY v bY aS bS cS:Omega) (hv:v≠0),
   Snext.G=residualAlgHom aY v bY aS bS cS S.G∧
   Snext.T=residualAlgHom aY v bY aS bS cS S.T∧
   Snext.primeIdeal=
     S.primeIdeal.map
       (residualEquiv aY v bY aS bS cS hv).toRingEquiv.toRingHom
theorem advance_certified
   (hphi:Function.Injective phi)
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (hne:S.identities≠∅)
   (hcard:S.identities.card ≤ d):
   0 < S.identities.card∧
     ∃ Snext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
         (d-S.identities.card) support,
       ResidualTransition S Snext∧
       Snext.nodes=S.nodes \ S.identities∧
       (∀ gamma∈Gamma,∀ i∈S.identities,
         S.Agrees gamma i)∧
       ∀ gamma∈Gamma,∀ i∈Snext.nodes,
         S.Agrees gamma i → Snext.Agrees gamma i:=by
 classical
 let P:=S.primeIdeal
 letI:P.IsPrime:=S.primeIdeal_isPrime
 let J:=S.identities
 have hJsub:J ⊆ S.nodes:=identityNodes_subset
   phi P S.F S.nodes x S.u0 S.u1 d
 have hJcard:J.card ≤ d:=by simpa only [J] using hcard
 have hJpos:0 < J.card:=Finset.card_pos.mpr
   (Finset.nonempty_iff_ne_empty.mpr (by simpa only [J] using hne))
 have hvalues:∀ gamma∈Gamma,∀ i∈J,
     (S.selected gamma).eval (x i)=S.u0 i+gamma*S.u1 i:=by
   intro gamma hgamma i hi
   exact S.agrees_on_identities gamma hgamma i hi
 obtain ⟨P0,P1,residual,hP0,hP1,hresdeg,hnores,hnormal,
     hagree,hsolution,hregular⟩:=
   exists_residual_family_with_surface_data
     phi hphi J S.nodes x S.u0 S.u1 d e hJsub hJcard S.x_injective
     S.selected Gamma S.degree_le hvalues S.no_large_pencil S.F
     S.solution S.regular
 let V:Polynomial K:=Lagrange.nodal J x
 have hV:V≠0:=(Lagrange.nodal_monic (s:=J) (v:=x)).ne_zero
 have hvphi:phi V≠0:=(map_ne_zero_iff phi hphi).mpr hV
 let Fres:Poly4 K:=globalResidualHom P0 P1 V S.F
 let Gres:Poly3 Omega:=
   residualAlgHom (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.G
 let Tres:Poly3 Omega:=
   residualAlgHom (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative) S.T
 let Hres:Poly3 Omega:=
   residualAlgHom (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) S.F))
 let Dmap:RegularPrimeData Gres Tres Hres:=by
   simpa only [Gres,Tres,Hres] using
     S.primeData.mapResidual
       (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative) hvphi
 have hHres:
     surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) Fres)=
       MvPolynomial.C (phi V)*Hres:=by
   simpa only [Fres,Hres] using
     surfaceMap_pderiv_globalResidualHom phi P0 P1 V S.F
 let Dnext:RegularPrimeData Gres Tres
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) Fres)):=by
   have hu:IsUnit (MvPolynomial.C (phi V):Poly3 Omega):=
     (isUnit_iff_ne_zero.mpr hvphi).map MvPolynomial.C
   refine {
     ideal:=Dmap.ideal
     isPrime:=Dmap.isPrime
     G_mem:=Dmap.G_mem
     T_mem:=Dmap.T_mem
     H_not_mem:=?_
     ne_point:=Dmap.ne_point
   }
   intro hmem
   apply Dmap.H_not_mem
   apply (Dmap.ideal.unit_mul_mem_iff_mem hu).mp
   rwa [←hHres]
 have hDnextIdeal:Dnext.ideal=
     S.primeData.ideal.map
       (residualEquiv
         (phi P0) (phi V) (phi P1)
         (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
         hvphi).toRingEquiv.toRingHom:=by
   change Dmap.ideal=_
   simpa only [Dmap,id_eq,RegularPrimeData.mapResidual_ideal]
 have hGdiv:Gres∣surfaceMap phi Fres:=by
   exact (residual_dvd_surfaceMap_globalResidualHom_iff
     phi hphi P0 P1 V hV S.G S.F).mpr S.G_dvd_surface
 have hGflag:RCN095.PolynomialInFlag
     surfaceFlag Gres:=
   polynomialInFlag_residualAlgHom surfaceFlag S.G
     (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
     S.G_flag_support
 have hTflag:RCN095.PolynomialInFlag
     cutFlag Tres:=
   polynomialInFlag_residualAlgHom cutFlag S.T
     (phi P0) (phi V) (phi P1)
     (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
     S.T_flag_support
 let hsupport:ResidualSupportData support S.F:=
   ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
 have hsupportRes:=hsupport.globalResidual P0 P1 V
 let u0res:Iota → K:=fun i↦residualReceived J x S.u0 P0 i
 let u1res:Iota → K:=fun i↦residualReceived J x S.u1 P1 i
 let Snext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
     (d-J.card) support:={
   nodes:=S.nodes \ J
   u0:=u0res
   u1:=u1res
   selected:=residual
   F:=Fres
   G:=Gres
   T:=Tres
   primeData:=Dnext
   G_dvd_surface:=hGdiv
   G_flag_support:=hGflag
   T_flag_support:=hTflag
   surface_s_weight:=hsupportRes.s_weight
   surface_ys_weight:=hsupportRes.ys_weight
   surface_total_weight:=hsupportRes.total_weight
   x_injective:=S.x_injective.mono (Finset.sdiff_subset)
   degree_le:=hresdeg
   solution:=hsolution
   regular:=hregular
   on_prime:=by
     intro gamma hgamma
     have hcoords:
         forwardResidualPoint
             (phi P0) (phi V) (phi P1)
             (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
             (selectedPoint phi (fun _↦residual gamma) gamma)=
           selectedPoint phi S.selected gamma:=by
       funext i
       fin_cases i <;>
         simp [forwardResidualPoint,selectedPoint,
           RCN231.polynomialPoint,
           hnormal gamma hgamma,RingHom.comp_apply] <;> ring
     change Dnext.ideal ≤ RingHom.ker
       (MvPolynomial.aeval
         (selectedPoint phi (fun _↦residual gamma) gamma)).toRingHom
     rw [hDnextIdeal]
     exact map_le_pointKernel_of_forward_eq
       (phi P0) (phi V) (phi P1)
       (phi P0.derivative) (phi V.derivative) (phi P1.derivative)
       hvphi S.primeData.ideal
       (selectedPoint phi (fun _↦residual gamma) gamma)
       (selectedPoint phi S.selected gamma) hcoords
       (S.on_prime gamma hgamma)
   no_large_pencil:=hnores
   characteristic_bound:=lt_of_le_of_lt (Nat.sub_le d J.card)
     S.characteristic_bound
 }
 refine ⟨?_,Snext,?_,rfl,?_,?_⟩
 · simpa only [J] using hJpos
 · refine ⟨phi P0,phi V,phi P1,phi P0.derivative,
     phi V.derivative,phi P1.derivative,hvphi,rfl,rfl,?_⟩
   change Dnext.ideal=_
   exact hDnextIdeal
 · intro gamma hgamma i hi
   exact S.agrees_on_identities gamma hgamma i hi
 · intro gamma hgamma i hi hold
   exact hagree gamma hgamma i (by simpa [Snext,J] using hi) hold
theorem advance
   (hphi:Function.Injective phi)
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (hne:S.identities≠∅)
   (hcard:S.identities.card ≤ d):
   0 < S.identities.card∧
     ∃ Snext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
         (d-S.identities.card) support,
       Snext.nodes=S.nodes \ S.identities∧
       (∀ gamma∈Gamma,∀ i∈S.identities,
         S.Agrees gamma i)∧
       ∀ gamma∈Gamma,∀ i∈Snext.nodes,
         S.Agrees gamma i → Snext.Agrees gamma i:=by
 obtain ⟨hpos,Snext,_,hnodes,hid,hremaining⟩:=
   S.advance_certified hphi hne hcard
 exact ⟨hpos,Snext,hnodes,hid,hremaining⟩
theorem card_le_pencil_of_many_identities
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (hmany:d < S.identities.card):
   Gamma.card ≤ e+1:=by
 classical
 let P:=S.primeIdeal
 letI:P.IsPrime:=S.primeIdeal_isPrime
 have hvalues:∀ t:{gamma:K//gamma∈Gamma},∀ i,
     i∈S.identities →
       (S.selected t.1).eval (x i)=S.u0 i+t.1*S.u1 i:=by
   intro t i hi
   exact S.agrees_on_identities t.1 t.2 i hi
 obtain ⟨P0,P1,hP0,hP1,_,hpencil⟩:=
   exists_common_pencil_of_many_identities
     phi P S.F S.surface_mem_primeIdeal S.regularity_not_mem_primeIdeal
     S.nodes x S.u0 S.u1 d S.x_injective hmany
     (fun t:{gamma:K//gamma∈Gamma}↦t.1)
     (fun t↦S.selected t.1)
     (fun t↦S.degree_le t.1 t.2) hvalues
 have hfilter:Gamma.filter
     (fun gamma↦S.selected gamma=
       P0+Polynomial.C gamma*P1)=Gamma:=
   Finset.filter_eq_self.mpr
     (fun gamma hgamma↦hpencil ⟨gamma,hgamma⟩)
 have hbound:=S.no_large_pencil P0 P1 hP0 hP1
 rwa [hfilter] at hbound
theorem advance_card
   (hphi:Function.Injective phi)
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (hne:S.identities≠∅)
   (hcard:S.identities.card ≤ d):
   ∃ Snext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
       (d-S.identities.card) support,
     Snext.nodes.card=S.nodes.card-S.identities.card∧
     ∀ gamma∈Gamma,
       (S.agreementFiber gamma).card-S.identities.card ≤
         (Snext.agreementFiber gamma).card:=by
 letI:S.primeIdeal.IsPrime:=S.primeIdeal_isPrime
 obtain ⟨_,Snext,hnodes,hidAgree,hdescend⟩:=
   S.advance hphi hne hcard
 have hIdentityNodesSubset:S.identities ⊆ S.nodes:=by
   exact identityNodes_subset
     phi S.primeIdeal S.F S.nodes x S.u0 S.u1 d
 refine ⟨Snext,?_,?_⟩
 · rw [hnodes,Finset.card_sdiff_of_subset hIdentityNodesSubset]
 · intro gamma hgamma
   have hIdentitySubset:S.identities ⊆ S.agreementFiber gamma:=by
     intro i hi
     exact Finset.mem_filter.mpr ⟨hIdentityNodesSubset hi,
       hidAgree gamma hgamma i hi⟩
   have hRemainingSubset:
       S.agreementFiber gamma \ S.identities ⊆
         Snext.agreementFiber gamma:=by
     intro i hi
     obtain ⟨holdFiber,hnotIdentity⟩:=Finset.mem_sdiff.mp hi
     obtain ⟨hinode,hold⟩:=Finset.mem_filter.mp holdFiber
     apply Finset.mem_filter.mpr
     refine ⟨?_,hdescend gamma hgamma i ?_ hold⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
   calc
     (S.agreementFiber gamma).card-S.identities.card=
         (S.agreementFiber gamma \ S.identities).card:=by
       rw [Finset.card_sdiff_of_subset hIdentitySubset]
     _ ≤ (Snext.agreementFiber gamma).card:=
       Finset.card_le_card hRemainingSubset
theorem advance_card_certified
   (hphi:Function.Injective phi)
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (hne:S.identities≠∅)
   (hcard:S.identities.card ≤ d):
   ∃ Snext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag
       (d-S.identities.card) support,
     ResidualTransition S Snext∧
     Snext.nodes.card=S.nodes.card-S.identities.card∧
     ∀ gamma∈Gamma,
       (S.agreementFiber gamma).card-S.identities.card ≤
         (Snext.agreementFiber gamma).card:=by
 letI:S.primeIdeal.IsPrime:=S.primeIdeal_isPrime
 obtain ⟨_,Snext,htransition,hnodes,hidAgree,hdescend⟩:=
   S.advance_certified hphi hne hcard
 have hIdentityNodesSubset:S.identities ⊆ S.nodes:=by
   exact identityNodes_subset
     phi S.primeIdeal S.F S.nodes x S.u0 S.u1 d
 refine ⟨Snext,htransition,?_,?_⟩
 · rw [hnodes,Finset.card_sdiff_of_subset hIdentityNodesSubset]
 · intro gamma hgamma
   have hIdentitySubset:S.identities ⊆ S.agreementFiber gamma:=by
     intro i hi
     exact Finset.mem_filter.mpr ⟨hIdentityNodesSubset hi,
       hidAgree gamma hgamma i hi⟩
   have hRemainingSubset:
       S.agreementFiber gamma \ S.identities ⊆
         Snext.agreementFiber gamma:=by
     intro i hi
     obtain ⟨holdFiber,hnotIdentity⟩:=Finset.mem_sdiff.mp hi
     obtain ⟨hinode,hold⟩:=Finset.mem_filter.mp holdFiber
     apply Finset.mem_filter.mpr
     refine ⟨?_,hdescend gamma hgamma i ?_ hold⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
     · rw [hnodes]
       exact Finset.mem_sdiff.mpr ⟨hinode,hnotIdentity⟩
   calc
     (S.agreementFiber gamma).card-S.identities.card=
         (S.agreementFiber gamma \ S.identities).card:=by
       rw [Finset.card_sdiff_of_subset hIdentitySubset]
     _ ≤ (Snext.agreementFiber gamma).card:=
       Finset.card_le_card hRemainingSubset
structure TerminalDescendant
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support) where
 degree:ℕ
 degree_le:degree ≤ d
 stage:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag degree support
 terminal:stage.identities=∅∨
   (degree < stage.identities.card∧Gamma.card ≤ e+1)
 nodes_card:stage.nodes.card=S.nodes.card-(d-degree)
 agreement_card:∀ gamma∈Gamma,
   (S.agreementFiber gamma).card-(d-degree) ≤
     (stage.agreementFiber gamma).card
theorem proper_agreement_of_terminal
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (hterminal:S.identities=∅) {i:Iota} (hi:i∈S.nodes):
   agreementPolynomial phi S.F d (x i) (S.u0 i) (S.u1 i)∉
     S.primeIdeal:=by
 intro hmem
 have hid:i∈S.identities:=
   Finset.mem_filter.mpr ⟨hi,hmem⟩
 rw [hterminal] at hid
 simpa using hid
theorem exists_terminal_descendant
   (hphi:Function.Injective phi)
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support):
   Nonempty S.TerminalDescendant:=by
 induction d using Nat.strong_induction_on with
 | h d ih =>
     by_cases hempty:S.identities=∅
     · exact ⟨{
         degree:=d
         degree_le:=le_rfl
         stage:=S
         terminal:=Or.inl hempty
         nodes_card:=by simp
         agreement_card:=by simp
       }⟩
     · by_cases hcard:S.identities.card ≤ d
       · have hkpos:0 < S.identities.card:=Finset.card_pos.mpr
           (Finset.nonempty_iff_ne_empty.mpr hempty)
         obtain ⟨Snext,hnodes,hagreements⟩:=
           S.advance_card hphi hempty hcard
         have hdegree_lt:d-S.identities.card < d:=by omega
         obtain ⟨Dnext⟩:=ih (d-S.identities.card) hdegree_lt Snext
         have hDle:Dnext.degree ≤ d-S.identities.card:=
           Dnext.degree_le
         have hdegree_split:d-Dnext.degree=
             S.identities.card+
               ((d-S.identities.card)-Dnext.degree):=by
           omega
         refine ⟨{
           degree:=Dnext.degree
           degree_le:=Dnext.degree_le.trans
             (Nat.sub_le d S.identities.card)
           stage:=Dnext.stage
           terminal:=Dnext.terminal
           nodes_card:=?_
           agreement_card:=?_
         }⟩
         · rw [Dnext.nodes_card,hnodes,hdegree_split]
           exact Nat.sub_sub _ _ _
         · intro gamma hgamma
           have hstep:=hagreements gamma hgamma
           have htail:=Dnext.agreement_card gamma hgamma
           have hmono:
               ((S.agreementFiber gamma).card-S.identities.card)-
                   ((d-S.identities.card)-Dnext.degree) ≤
                 (Snext.agreementFiber gamma).card-
                   ((d-S.identities.card)-Dnext.degree):=
             Nat.sub_le_sub_right hstep _
           calc
             (S.agreementFiber gamma).card-(d-Dnext.degree)=
                 ((S.agreementFiber gamma).card-S.identities.card)-
                   ((d-S.identities.card)-Dnext.degree):=by
               rw [hdegree_split]
               exact (Nat.sub_sub _ _ _).symm
             _ ≤ (Snext.agreementFiber gamma).card-
                   ((d-S.identities.card)-Dnext.degree):=hmono
             _ ≤ (Dnext.stage.agreementFiber gamma).card:=htail
       · have hmany:d < S.identities.card:=Nat.lt_of_not_ge hcard
         exact ⟨{
           degree:=d
           degree_le:=le_rfl
           stage:=S
           terminal:=Or.inr
             ⟨hmany,S.card_le_pencil_of_many_identities hmany⟩
           nodes_card:=by simp
           agreement_card:=by simp
         }⟩
theorem exists_terminal_descendant_with_invariant
   (hphi:Function.Injective phi)
   (Inv:∀ n,CurveResidualStage phi Gamma x p e surfaceFlag cutFlag n support → Prop)
   (htransport:∀ {n m}
     {A:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag n support}
     {B:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag m support},
     ResidualTransition A B → Inv n A → Inv m B)
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (hInv:Inv d S):
   ∃ D:S.TerminalDescendant,Inv D.degree D.stage:=by
 induction d using Nat.strong_induction_on with
 | h d ih =>
     by_cases hempty:S.identities=∅
     · refine ⟨{
         degree:=d
         degree_le:=le_rfl
         stage:=S
         terminal:=Or.inl hempty
         nodes_card:=by simp
         agreement_card:=by simp
       },hInv⟩
     · by_cases hcard:S.identities.card ≤ d
       · have hkpos:0 < S.identities.card:=Finset.card_pos.mpr
           (Finset.nonempty_iff_ne_empty.mpr hempty)
         obtain ⟨Snext,htransition,hnodes,hagreements⟩:=
           S.advance_card_certified hphi hempty hcard
         have hdegree_lt:d-S.identities.card < d:=by omega
         have hInvNext:=htransport htransition hInv
         obtain ⟨Dnext,hDInv⟩:=
           ih (d-S.identities.card) hdegree_lt Snext hInvNext
         have hDle:Dnext.degree ≤ d-S.identities.card:=
           Dnext.degree_le
         have hdegree_split:d-Dnext.degree=
             S.identities.card+
               ((d-S.identities.card)-Dnext.degree):=by
           omega
         refine ⟨{
           degree:=Dnext.degree
           degree_le:=Dnext.degree_le.trans
             (Nat.sub_le d S.identities.card)
           stage:=Dnext.stage
           terminal:=Dnext.terminal
           nodes_card:=?_
           agreement_card:=?_
         },?_⟩
         · rw [Dnext.nodes_card,hnodes,hdegree_split]
           exact Nat.sub_sub _ _ _
         · intro gamma hgamma
           have hstep:=hagreements gamma hgamma
           have htail:=Dnext.agreement_card gamma hgamma
           have hmono:
               ((S.agreementFiber gamma).card-S.identities.card)-
                   ((d-S.identities.card)-Dnext.degree) ≤
                 (Snext.agreementFiber gamma).card-
                   ((d-S.identities.card)-Dnext.degree):=
             Nat.sub_le_sub_right hstep _
           calc
             (S.agreementFiber gamma).card-(d-Dnext.degree)=
                 ((S.agreementFiber gamma).card-S.identities.card)-
                   ((d-S.identities.card)-Dnext.degree):=by
               rw [hdegree_split]
               exact (Nat.sub_sub _ _ _).symm
             _ ≤ (Snext.agreementFiber gamma).card-
                   ((d-S.identities.card)-Dnext.degree):=hmono
             _ ≤ (Dnext.stage.agreementFiber gamma).card:=htail
         · exact hDInv
       · have hmany:d < S.identities.card:=Nat.lt_of_not_ge hcard
         refine ⟨{
           degree:=d
           degree_le:=le_rfl
           stage:=S
           terminal:=Or.inr
             ⟨hmany,S.card_le_pencil_of_many_identities hmany⟩
           nodes_card:=by simp
           agreement_card:=by simp
         },hInv⟩
end CurveResidualStage
end
end ProximityPrize.SubmissionLower.RCN151
end PackedLegacy_ET

/-! Packed from ProximityPrize.SubmissionLower.EY. -/
section PackedLegacy_EY
namespace ProximityPrize.SubmissionLower.RCN158
open RCN213
section FiniteAgreement
variable {Node:Type*} [DecidableEq Node]
theorem residual_agreement_card
   (nodes I:Finset Node) (oldRelation residualRelation:Node → Prop)
   [DecidablePred oldRelation] [DecidablePred residualRelation]
   (a:ℕ)
   (hI:I ⊆ nodes.filter oldRelation)
   (ha:a ≤ (nodes.filter oldRelation).card)
   (hdescend:∀ i∈nodes \ I,oldRelation i → residualRelation i):
   a-I.card ≤ ((nodes \ I).filter residualRelation).card:=by
 have hsub:(nodes.filter oldRelation) \ I ⊆
     (nodes \ I).filter residualRelation:=by
   intro i hi
   obtain ⟨hiold,hiI⟩:=Finset.mem_sdiff.mp hi
   obtain ⟨hinodes,hold⟩:=Finset.mem_filter.mp hiold
   exact Finset.mem_filter.mpr
     ⟨Finset.mem_sdiff.mpr ⟨hinodes,hiI⟩,
       hdescend i (Finset.mem_sdiff.mpr ⟨hinodes,hiI⟩) hold⟩
 calc
   a-I.card ≤ (nodes.filter oldRelation).card-I.card:=
     Nat.sub_le_sub_right ha I.card
   _=((nodes.filter oldRelation) \ I).card:=by
     rw [Finset.card_sdiff_of_subset hI]
   _ ≤ ((nodes \ I).filter residualRelation).card:=
     Finset.card_le_card hsub
theorem residual_family_agreement_card
   {Seed:Type*} (seeds:Finset Seed)
   (nodes I:Finset Node)
   (oldRelation residualRelation:Seed → Node → Prop)
   [∀ seed,DecidablePred (oldRelation seed)]
   [∀ seed,DecidablePred (residualRelation seed)]
   (a:ℕ)
   (hidentity:∀ seed∈seeds,I ⊆ nodes.filter (oldRelation seed))
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (oldRelation seed)).card)
   (hdescend:∀ seed∈seeds,∀ i∈nodes \ I,
     oldRelation seed i → residualRelation seed i):
   ∀ seed∈seeds,
     a-I.card ≤ ((nodes \ I).filter (residualRelation seed)).card:=by
 intro seed hseed
 exact residual_agreement_card nodes I (oldRelation seed)
   (residualRelation seed) a (hidentity seed hseed)
   (hagreement seed hseed) (hdescend seed hseed)
end FiniteAgreement
section IteratedSets
variable {Node:Type*} [DecidableEq Node]
theorem disjoint_of_subset_sdiff
   (nodes I J:Finset Node) (hJ:J ⊆ nodes \ I):Disjoint I J:=by
 refine Finset.disjoint_left.mpr ?_
 intro i hiI hiJ
 exact (Finset.mem_sdiff.mp (hJ hiJ)).2 hiI
theorem sdiff_sdiff_eq_sdiff_union
   (nodes I J:Finset Node):
   (nodes \ I) \ J=nodes \ (I ∪ J):=by
 ext i
 simp only [Finset.mem_sdiff,Finset.mem_union]
 tauto
theorem card_union_of_subset_sdiff
   (nodes I J:Finset Node) (hJ:J ⊆ nodes \ I):
   (I ∪ J).card=I.card+J.card:=by
 rw [Finset.card_union_of_disjoint (disjoint_of_subset_sdiff nodes I J hJ)]
theorem sub_cards_eq_sub_union_card
   (q:ℕ) (nodes I J:Finset Node) (hJ:J ⊆ nodes \ I):
   (q-I.card)-J.card=q-(I ∪ J).card:=by
 rw [Nat.sub_sub,card_union_of_subset_sdiff nodes I J hJ]
end IteratedSets
section Arithmetic
theorem residual_gap_eq
   (a w k:ℕ) (hk:k ≤ w) (hwa:w ≤ a):
   (a-k)-(w-k)=a-w:=by
 omega
theorem residual_node_degree_eq
   (n w k:ℕ) (hk:k ≤ w) (hwn:w ≤ n):
   (n-k)-(w-k)=n-w:=by
 omega
theorem iterated_residual_invariants
   (n a w k j:ℕ) (hkj:k+j ≤ w)
   (hwa:w ≤ a) (hwn:w ≤ n):
   ((a-k)-j)-((w-k)-j)=a-w∧
     ((n-k)-j)-((w-k)-j)=n-w:=by
 constructor <;> omega
theorem residual_degree_strictly_decreases
   (w k j:ℕ) (hk:k ≤ w) (hjpos:0 < j) (hj:j ≤ w-k):
   (w-k)-j < w-k:=by
 omega
theorem score6600_iterated_compression
   (k j:ℕ) (hkj:k+j ≤ w):
   (n-(k+j))*gap*(w-(k+j)) ≤
       degreeIncidence*(agreements-(k+j))∧
     (n-(k+j))*gap ≤
       unitIncidence*(agreements-(k+j)):=by
 exact ⟨degree_part_bound (k+j) hkj,
   unit_part_bound (k+j) hkj⟩
end Arithmetic
section Terminalization
open scoped Classical
open RCN159 RCN157 RCN156 RCN275
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p]
 {flag:RCN095.FlagDegree}
 {support:ResidualSupportParameters}
def IsTerminalStage {d:ℕ}
   (S:ResidualStage phi Gamma x p e flag d support):Prop:=
 S.identities=∅
theorem terminal_iff_all_cuts_proper {d:ℕ}
   (S:ResidualStage phi Gamma x p e flag d support):
   IsTerminalStage S ↔
     ∀ i∈S.nodes,
       RCN238.agreementPolynomial
         phi S.F d (x i) (S.u0 i) (S.u1 i)∉S.componentIdeal:=by
 classical
 constructor
 · intro hempty i hi hmem
   have hid:i∈S.identities:=by
     exact Finset.mem_filter.mpr ⟨hi,hmem⟩
   rw [hempty] at hid
   simpa using hid
 · intro hproper
   change S.identities=∅
   unfold RCN159.ResidualStage.identities
   unfold RCN065.identityNodes
   exact Finset.filter_eq_empty_iff.mpr hproper
@[simp] theorem globalResidualHom_zero_zero_one
   (F:MvPolynomial (Fin 4) K):
   globalResidualHom (0:Polynomial K) 0 1 F=F:=by
 induction F using MvPolynomial.induction_on with
 | C a => simp
 | add F G hF hG => simp [hF,hG]
 | mul_X F i hF =>
     fin_cases i <;> simp [globalResidualImage,hF]
theorem surfaceMap_agreement_in_flag_of_support
   (support:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K)
   (hS:RCN234.wt
     residualSWeights F ≤ support.s)
   (hYS:RCN234.wt
     residualYSWeights F ≤ support.ys)
   (hTotal:RCN234.wt
     residualTotalWeights F ≤ support.total)
   (d:ℕ) (coeffs:ℕ → K) (x0 u0 u1:K):
   RCN095.PolynomialInFlag
     (support.residualAgreementFlag d)
     (RCN136.surfaceMap phi
       (RCN313.agreementNumerator F d coeffs x0 u0 u1)):=by
 let hsupport:ResidualSupportData support F:=⟨hS,hYS,hTotal⟩
 exact hsupport.surfaceMap_agreement_in_flag phi d coeffs x0 u0 u1
theorem surfaceMap_agreement_in_flag_of_surface_weights
   (F:MvPolynomial (Fin 4) K)
   (hS:RCN234.wt
     residualSWeights F ≤ 8)
   (hYS:RCN234.wt
     residualYSWeights F ≤ 43)
   (hTotal:RCN234.wt
     residualTotalWeights F ≤ 503)
   (d:ℕ) (coeffs:ℕ → K) (x0 u0 u1:K):
   RCN095.PolynomialInFlag (residualAgreementFlag d)
     (RCN136.surfaceMap phi
       (RCN313.agreementNumerator F d coeffs x0 u0 u1)):=by
 simpa only [ResidualSupportParameters.accepted_agreement_flag] using
   surfaceMap_agreement_in_flag_of_support
     (phi:=phi) ResidualSupportParameters.acceptedSupport F
       hS hYS hTotal d coeffs x0 u0 u1
theorem terminal_proper_cuts_in_residual_flag {d:ℕ}
   (S:ResidualStage phi Gamma x p e flag d support)
   (hterminal:IsTerminalStage S):
   ∀ i∈S.nodes,
     RCN238.agreementPolynomial
         phi S.F d (x i) (S.u0 i) (S.u1 i)∉S.componentIdeal∧
       RCN095.PolynomialInFlag
         (support.residualAgreementFlag d)
         (RCN238.agreementPolynomial
           phi S.F d (x i) (S.u0 i) (S.u1 i)):=by
 intro i hi
 refine ⟨(terminal_iff_all_cuts_proper S).mp hterminal i hi,?_⟩
 exact surfaceMap_agreement_in_flag_of_support support
   S.F S.surface_s_weight S.surface_ys_weight S.surface_total_weight
   d (fun j↦(j.factorial:K)⁻¹) (x i) (S.u0 i) (S.u1 i)
inductive ResidualAdvance:
   (Σ d,ResidualStage phi Gamma x p e flag d support) →
     (Σ d,ResidualStage phi Gamma x p e flag d support) → Prop
 | step {d:ℕ} (S:ResidualStage phi Gamma x p e flag d support)
     (hne:S.identities≠∅)
     (Snext:ResidualStage phi Gamma x p e flag
       (d-S.identities.card) support)
     (hnodes:Snext.nodes=S.nodes \ S.identities)
     (hold:∀ gamma∈Gamma,∀ i∈S.identities,
       S.Agrees gamma i)
     (hdescend:∀ gamma∈Gamma,∀ i∈Snext.nodes,
       S.Agrees gamma i → Snext.Agrees gamma i):
     ResidualAdvance ⟨d,S⟩ ⟨d-S.identities.card,Snext⟩
theorem exists_strict_advance
   (hphi:Function.Injective phi) {d:ℕ}
   (S:ResidualStage phi Gamma x p e flag d support)
   (hnot:¬ IsTerminalStage S):
   ∃ T:Σ d',ResidualStage phi Gamma x p e flag d' support,
     ResidualAdvance ⟨d,S⟩ T∧T.1 < d:=by
 have hne:S.identities≠∅:=hnot
 obtain ⟨hpos,Snext,hnodes,hold,hdescend⟩:=
   S.advance hphi hne
 refine ⟨⟨d-S.identities.card,Snext⟩,
   ResidualAdvance.step S hne Snext hnodes hold hdescend,?_⟩
 have hcap:=S.identities_card_le
 change d-S.identities.card < d
 omega
abbrev ResidualReachable:=Relation.ReflTransGen
 (ResidualAdvance (phi:=phi) (Gamma:=Gamma) (x:=x)
   (p:=p) (e:=e) (flag:=flag) (support:=support))
theorem exists_terminal_reachable
   (hphi:Function.Injective phi) {d:ℕ}
   (S:ResidualStage phi Gamma x p e flag d support):
   ∃ T:Σ d',ResidualStage phi Gamma x p e flag d' support,
     ResidualReachable ⟨d,S⟩ T∧IsTerminalStage T.2:=by
 induction d using Nat.strong_induction_on with
 | h d ih =>
     by_cases hterm:IsTerminalStage S
     · exact ⟨⟨d,S⟩,Relation.ReflTransGen.refl,hterm⟩
     · obtain ⟨⟨dnext,Snext⟩,hstep,hlt⟩:=
         exists_strict_advance hphi S hterm
       obtain ⟨T,hreach,hterminal⟩:=ih dnext hlt Snext
       exact ⟨T,Relation.ReflTransGen.head hstep hreach,hterminal⟩
theorem exists_terminal_with_incidence_data
   (hphi:Function.Injective phi) {d a:ℕ}
   (S:ResidualStage phi Gamma x p e flag d support)
   (hda:d ≤ a)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card):
   ∃ T:Σ d',ResidualStage phi Gamma x p e flag d' support,
     ResidualReachable ⟨d,S⟩ T∧
     IsTerminalStage T.2∧
     T.1 ≤ d∧
     T.2.nodes.card-T.1=S.nodes.card-d∧
     ∀ gamma∈Gamma,
       a-(d-T.1) ≤ (T.2.agreementFiber gamma).card:=by
 classical
 letI:DecidableEq Iota:=Classical.decEq Iota
 induction d using Nat.strong_induction_on generalizing a with
 | h d ih =>
     by_cases hterm:IsTerminalStage S
     · refine ⟨⟨d,S⟩,Relation.ReflTransGen.refl,hterm,
         le_rfl,rfl,?_⟩
       simpa using hagreement
     · have hne:S.identities≠∅:=hterm
       obtain ⟨hpos,Snext,hnodes,hold,hdescend⟩:=
         S.advance hphi hne
       let k:=S.identities.card
       have hk:k ≤ d:=S.identities_card_le
       have hlt:d-k < d:=by
         dsimp only [k]
         omega
       have hdaNext:d-k ≤ a-k:=Nat.sub_le_sub_right hda k
       have hnextAgreement:∀ gamma∈Gamma,
           a-k ≤ (Snext.agreementFiber gamma).card:=by
         intro gamma hgamma
         letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
         have hidentity:S.identities ⊆
             S.nodes.filter (S.Agrees gamma):=by
           intro i hi
           exact Finset.mem_filter.mpr
             ⟨RCN065.identityNodes_subset
                 phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d hi,
               hold gamma hgamma i hi⟩
         have hcard:=residual_agreement_card
           S.nodes S.identities (S.Agrees gamma) (Snext.Agrees gamma)
           a hidentity (hagreement gamma hgamma)
           (fun i hi↦hdescend gamma hgamma i (by simpa [hnodes] using hi))
         simpa only [k,ResidualStage.agreementFiber,hnodes] using hcard
       obtain ⟨⟨dFinal,T⟩,hreach,hterminal,hdFinal,
           hnodeInvariant,hfinalAgreement⟩:=
         ih (d-k) hlt Snext hdaNext hnextAgreement
       letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
       have hidentitiesSub:S.identities ⊆ S.nodes:=
         RCN065.identityNodes_subset
           phi S.componentIdeal S.F S.nodes x S.u0 S.u1 d
       have hstepNode:
           Snext.nodes.card-(d-k)=S.nodes.card-d:=by
         rw [hnodes,Finset.card_sdiff_of_subset hidentitiesSub]
         dsimp only [k]
         omega
       have hstep:ResidualAdvance ⟨d,S⟩ ⟨d-k,Snext⟩:=by
         exact ResidualAdvance.step S hne Snext hnodes hold hdescend
       refine ⟨⟨dFinal,T⟩,
         Relation.ReflTransGen.head hstep hreach,hterminal,
         ?_,?_,?_⟩
       · exact hdFinal.trans (Nat.sub_le d k)
       · exact hnodeInvariant.trans hstepNode
       · intro gamma hgamma
         have hbound:=hfinalAgreement gamma hgamma
         change dFinal ≤ d-k at hdFinal
         have hdecomp:
             d-dFinal=k+((d-k)-dFinal):=by
           omega
         have heq:
             a-(d-dFinal)=
               (a-k)-((d-k)-dFinal):=by
           calc
             a-(d-dFinal)=
                 a-(k+((d-k)-dFinal)):=by rw [hdecomp]
             _=(a-k)-((d-k)-dFinal):=by
               exact (Nat.sub_sub a k ((d-k)-dFinal)).symm
         rwa [heq]
end
end Terminalization
end ProximityPrize.SubmissionLower.RCN158
end PackedLegacy_EY

/-! Packed from ProximityPrize.SubmissionLower.D6. -/
section PackedLegacy_D6
namespace ProximityPrize.SubmissionLower.RCN216
open RCN173 RCN213
theorem stratified_incidence_bound
   {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
   (relation:Seed → Node → Prop) [∀ seed node,Decidable (relation seed node)]
   (seeds:Finset Seed) (nodes identities:Finset Node)
   (a w degreeCost unitCost U V:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed↦relation seed node)).card ≤
       (w-identities.card)*degreeCost+unitCost)
   (hdegree:
     (nodes.card-identities.card)*(a-w)*(w-identities.card) ≤
       U*(a-identities.card))
   (hunit:
     (nodes.card-identities.card)*(a-w) ≤
       V*(a-identities.card)):
   seeds.card*(a-w) ≤ U*degreeCost+V*unitCost:=by
 have hraw:=incidence_after_exempt_nodes relation seeds nodes identities a
   ((w-identities.card)*degreeCost+unitCost)
   hidentities hagreement hfiber
 exact stratified_incidence_linear seeds.card nodes.card a w identities.card
   degreeCost unitCost U V hcard hwa hraw hdegree hunit
theorem scaled_stratified_incidence_bound
   {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
   (relation:Seed → Node → Prop) [∀ seed node,Decidable (relation seed node)]
   (seeds:Finset Seed) (nodes identities:Finset Node)
   (a w degreeCost unitCost U V:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed↦relation seed node)).card*(a-w) ≤
       (w-identities.card)*degreeCost+unitCost)
   (hdegree:
     (nodes.card-identities.card)*(a-w)*(w-identities.card) ≤
       U*(a-identities.card))
   (hunit:
     (nodes.card-identities.card)*(a-w) ≤
       V*(a-identities.card)):
   seeds.card*(a-w)^2 ≤ U*degreeCost+V*unitCost:=by
 let geometricCost:=(w-identities.card)*degreeCost+unitCost
 have hgap:0 < a-w:=Nat.sub_pos_of_lt hwa
 have hfiberDiv:∀ node∈nodes \ identities,
     (seeds.filter (fun seed↦relation seed node)).card ≤
       geometricCost/(a-w):=by
   intro node hnode
   exact (Nat.le_div_iff_mul_le hgap).mpr (hfiber node hnode)
 have hraw:=incidence_after_exempt_nodes relation seeds nodes identities a
   (geometricCost/(a-w)) hidentities hagreement hfiberDiv
 have hrawScaled:
     (seeds.card*(a-w))*(a-identities.card) ≤
       (nodes.card-identities.card)*
         ((w-identities.card)*degreeCost+unitCost):=by
   calc
     (seeds.card*(a-w))*(a-identities.card)=
         (seeds.card*(a-identities.card))*(a-w):=by ring
     _ ≤ ((nodes.card-identities.card)*
         (geometricCost/(a-w)))*(a-w):=
       Nat.mul_le_mul_right (a-w) hraw
     _=(nodes.card-identities.card)*
         ((geometricCost/(a-w))*(a-w)):=by ring
     _ ≤ (nodes.card-identities.card)*geometricCost:=
       Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
     _=(nodes.card-identities.card)*
         ((w-identities.card)*degreeCost+unitCost):=rfl
 have hcompressed:=stratified_incidence_linear
   (seeds.card*(a-w)) nodes.card a w identities.card
   degreeCost unitCost U V hcard hwa hrawScaled hdegree hunit
 calc
   seeds.card*(a-w)^2=(seeds.card*(a-w))*(a-w):=by ring
   _ ≤ U*degreeCost+V*unitCost:=hcompressed
end ProximityPrize.SubmissionLower.RCN216
end PackedLegacy_D6

/-! Packed from ProximityPrize.SubmissionLower.EU. -/
section PackedLegacy_EU
namespace ProximityPrize.SubmissionLower.RCN152
open scoped Classical
open RCN136 RCN231 RCN319 RCN238 RCN173 RCN151 RCN151.CurveResidualStage RCN216 RCN213 RCN272 RCN095 RCN156 RCN158 RCN165 RCN275
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e:ℕ} [CharP Omega p]
 {surfaceFlag cutFlag:FlagDegree}
 {support:ResidualSupportParameters}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem recursive_curve_stratified_incidence_bound
   (hphi:Function.Injective phi) {d a:ℕ}
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (degreeCost unitCost U V zCharge:ℕ)
   (hda:d < a)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,
     D.stage.identities=∅ → ∀ i∈D.stage.nodes,
       (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
         D.degree*degreeCost+unitCost)
   (hlarge:∀ D:S.TerminalDescendant,
     D.degree < D.stage.identities.card →
       Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
   (hdegree:∀ k ≤ d,
     (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
 classical
 obtain ⟨D⟩:=S.exists_terminal_descendant hphi
 rcases D.terminal with hproper | hpencil
 · let k:=d-D.degree
   have hk:k ≤ d:=Nat.sub_le d D.degree
   have hDle:D.degree ≤ d:=D.degree_le
   have hdegreeEq:D.degree=d-k:=by
     dsimp only [k]
     omega
   have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
     simpa only [k] using D.nodes_card
   have hterminalAgreement:∀ gamma∈Gamma,
       a-k ≤ (D.stage.agreementFiber gamma).card:=by
     intro gamma hgamma
     exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
       (by simpa only [k] using D.agreement_card gamma hgamma)
   have hterminalFiber:∀ i∈D.stage.nodes,
       (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
         D.degree*degreeCost+unitCost:=by
     intro i hi
     exact hfiber D hproper i hi
   have hrawTerminal:=incidence_after_exempt_nodes
     (fun gamma i↦D.stage.Agrees gamma i)
     Gamma D.stage.nodes ∅ (a-k)
       (D.degree*degreeCost+unitCost)
     (by simp) hterminalAgreement (by
       intro i hi
       exact hterminalFiber i (by simpa using hi))
   have hraw:Gamma.card*(a-k) ≤
       (S.nodes.card-k)*((d-k)*degreeCost+unitCost):=by
     simpa only [Finset.card_empty,Nat.sub_zero,hnodeEq,hdegreeEq] using
       hrawTerminal
   have hmain:Gamma.card*(a-d) ≤
       U*degreeCost+V*unitCost:=
     stratified_incidence_linear Gamma.card S.nodes.card a d k
       degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
   exact hmain.trans (Nat.le_add_right _ _)
 · have htail:=hlarge D hpencil.1
   exact htail.trans (Nat.le_add_left _ _)
theorem recursive_curve_stratified_incidence_of_zero_bounds
   (hphi:Function.Injective phi) {d a:ℕ}
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (degreeCost unitCost U V zCharge:ℕ)
   (hda:d < a)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card)
   (hzero:∀ D:S.TerminalDescendant,
     D.stage.identities=∅ → ∀ i∈D.stage.nodes,
       FiniteZeroSetBound D.stage.primeIdeal
         (agreementPolynomial phi D.stage.F D.degree
           (x i) (D.stage.u0 i) (D.stage.u1 i))
         (D.degree*degreeCost+unitCost))
   (hlarge:∀ D:S.TerminalDescendant,
     D.degree < D.stage.identities.card →
       Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
   (hdegree:∀ k ≤ d,
     (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
 apply recursive_curve_stratified_incidence_bound hphi S
   degreeCost unitCost U V zCharge hda hagreement
 · intro D hterminal i hi
   exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
     D.stage.F D.stage.selected Gamma p D.degree
     D.stage.characteristic_bound D.stage.degree_le D.stage.solution
     D.stage.regular D.stage.on_prime
     (x i) (D.stage.u0 i) (D.stage.u1 i)
     (D.degree*degreeCost+unitCost)
     (hzero D hterminal i hi)
 · exact hlarge
 · exact hdegree
 · exact hunit
theorem recursive_curve_stratified_incidence_of_prime_flag_budget
   (hphi:Function.Injective phi) {d a:ℕ}
   (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
   (cost:FlagDegree → ℕ)
   (B:PrimeFlagZeroBudget S.primeIdeal cost)
   (degreeCost unitCost U V zCharge:ℕ)
   (hcost:∀ t:ℕ,
     cost (support.residualAgreementFlag t)=t*degreeCost+unitCost)
   (hda:d < a)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card)
   (hlarge:∀ D:S.TerminalDescendant,
     D.degree < D.stage.identities.card →
       Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
   (hdegree:∀ k ≤ d,
     (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
 classical
 let Inv:∀ n,CurveResidualStage phi Gamma x p e
     surfaceFlag cutFlag n support → Prop:=
   fun _ A↦PrimeFlagZeroBudget A.primeIdeal cost
 have htransport:∀ {n m}
     {A:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag n support}
     {Anext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag m support},
     A.ResidualTransition Anext → Inv n A → Inv m Anext:=by
   intro n m A Anext htransition hbudget
   obtain ⟨aY,v,bY,aS,bS,cS,hv,_,_,hprime⟩:=htransition
   dsimp only [Inv] at hbudget ⊢
   rw [hprime]
   exact hbudget.mapResidual aY v bY aS bS cS hv
 obtain ⟨D,hDBudget⟩:=S.exists_terminal_descendant_with_invariant
   hphi Inv htransport B
 rcases D.terminal with hproper | hpencil
 · let k:=d-D.degree
   have hk:k ≤ d:=Nat.sub_le d D.degree
   have hDle:D.degree ≤ d:=D.degree_le
   have hdegreeEq:D.degree=d-k:=by
     dsimp only [k]
     omega
   have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
     simpa only [k] using D.nodes_card
   have hterminalAgreement:∀ gamma∈Gamma,
       a-k ≤ (D.stage.agreementFiber gamma).card:=by
     intro gamma hgamma
     exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
       (by simpa only [k] using D.agreement_card gamma hgamma)
   have hterminalFiber:∀ i∈D.stage.nodes,
       (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
         D.degree*degreeCost+unitCost:=by
     intro i hi
     have hflag:PolynomialInFlag (support.residualAgreementFlag D.degree)
         (agreementPolynomial phi D.stage.F D.degree
           (x i) (D.stage.u0 i) (D.stage.u1 i)):=
       surfaceMap_agreement_in_flag_of_support support
         D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
         D.stage.surface_total_weight D.degree
         (fun j↦(j.factorial:K)⁻¹)
         (x i) (D.stage.u0 i) (D.stage.u1 i)
     have hzero:=hDBudget.zero_le (support.residualAgreementFlag D.degree)
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       hflag (D.stage.proper_agreement_of_terminal hproper hi)
     rw [hcost D.degree] at hzero
     exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
       D.stage.F D.stage.selected Gamma p D.degree
       D.stage.characteristic_bound D.stage.degree_le D.stage.solution
       D.stage.regular D.stage.on_prime
       (x i) (D.stage.u0 i) (D.stage.u1 i)
       (D.degree*degreeCost+unitCost) hzero
   have hrawTerminal:=incidence_after_exempt_nodes
     (fun gamma i↦D.stage.Agrees gamma i)
     Gamma D.stage.nodes ∅ (a-k)
       (D.degree*degreeCost+unitCost)
     (by simp) hterminalAgreement (by
       intro i hi
       exact hterminalFiber i (by simpa using hi))
   have hraw:Gamma.card*(a-k) ≤
       (S.nodes.card-k)*((d-k)*degreeCost+unitCost):=by
     simpa only [Finset.card_empty,Nat.sub_zero,hnodeEq,hdegreeEq] using
       hrawTerminal
   have hmain:Gamma.card*(a-d) ≤
       U*degreeCost+V*unitCost:=
     stratified_incidence_linear Gamma.card S.nodes.card a d k
       degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
   exact hmain.trans (Nat.le_add_right _ _)
 · have htail:=hlarge D hpencil.1
   exact htail.trans (Nat.le_add_left _ _)
end
end ProximityPrize.SubmissionLower.RCN152
end PackedLegacy_EU

/-! Packed from ProximityPrize.SubmissionLower.GJ. -/
section PackedLegacy_GJ
namespace ProximityPrize.SubmissionLower.RCN305
open scoped Classical BigOperators
open RCN002 RCN007 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN272 RCN216
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K Omega:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
 {Iota:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem prime_seed_incidence_of_stratified_residual_cost
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ gamma∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w e)
   (degreeCost unitCost U V:ℕ)
   (hfiber:∀ i∈nodes \
       identityNodes phi P F nodes x u0 u1 w,
     (Gamma.filter (fun gamma↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card ≤
       (w-(identityNodes phi P F nodes x u0 u1 w).card)*degreeCost+
         unitCost)
   (hdegree:∀ k ≤ w,
     (nodes.card-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:∀ k ≤ w,
     (nodes.card-k)*(a-w) ≤ V*(a-k)):
   Gamma.card*(a-w) ≤
     U*degreeCost+V*unitCost+
       (e+1)*(a-w)*actualCoordinateDegree Omega P 2:=by
 classical
 let identities:=identityNodes phi P F nodes x u0 u1 w
 let relation:K → Iota → Prop:=fun gamma i↦
   (selected gamma).eval (x i)=u0 i+gamma*u1 i
 by_cases hcard:identities.card ≤ w
 · have hmain:=stratified_incidence_bound relation Gamma nodes identities
     a w degreeCost unitCost U V
     (identityNodes_subset phi P F nodes x u0 u1 w)
     hcard hwa hagreement
     (by
       intro i hi
       exact hfiber i (by simpa only [identities] using hi))
     (hdegree identities.card hcard) (hunit identities.card hcard)
   exact hmain.trans (Nat.le_add_right _ _)
 · have hc:w < identities.card:=Nat.lt_of_not_ge hcard
   have hvalues:∀ (t:{gamma:K//gamma∈Gamma}) i,
       i∈identities →
       (selected t.1).eval (x i)=u0 i+t.1*u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes phi P F nodes x u0 u1 p w
       hchar (selected t.1) t.1 (hdegreeSelected t.1 t.2)
       (hsolution t.1 t.2) (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=
     exists_common_pencil_of_many_identities phi P F hF hH nodes x u0 u1 w
       hinj hc (fun t:{gamma:K//gamma∈Gamma}↦t.1)
       (fun t↦selected t.1) (fun t↦hdegreeSelected t.1 t.2) hvalues
   have hfilter:Gamma.filter
       (fun gamma↦selected gamma=P0+Polynomial.C gamma*P1)=
       Gamma:=
     Finset.filter_eq_self.mpr (fun gamma hgamma↦hpencil ⟨gamma,hgamma⟩)
   have hGamma:Gamma.card ≤ e+1:=by
     have h:=hnoPencil P0 P1 h0 h1
     rwa [hfilter] at h
   have hZ:=seed_transcendental_of_many_identities phi P F hF hH
     nodes x u0 u1 w hw hinj hc hnonpoint
   have hdelta:=coordinateDegree_pos_of_transcendental P hproj
     (2:Fin 3) hZ
   have htail:Gamma.card*(a-w) ≤
       (e+1)*(a-w)*actualCoordinateDegree Omega P 2:=by
     calc
       Gamma.card*(a-w) ≤ (e+1)*(a-w):=
         Nat.mul_le_mul_right _ hGamma
       _ ≤ (e+1)*(a-w)*actualCoordinateDegree Omega P 2:=by
         simpa only [Nat.mul_one] using
           Nat.mul_le_mul_left ((e+1)*(a-w)) hdelta
   exact htail.trans (Nat.le_add_left _ _)
theorem aggregate_component_stratified_incidence
   (G T H:MvPolynomial (Fin 3) Omega)
   {Seed:Type*} (S:Finset Seed) (v:Seed → Fin 3 → Omega)
   (hG:∀ gamma∈S,MvPolynomial.eval (v gamma) G=0)
   (hT:∀ gamma∈S,MvPolynomial.eval (v gamma) T=0)
   (hH:∀ gamma∈S,MvPolynomial.eval (v gamma) H≠0)
   (gap U V pencil degreeWhole unitWhole zBudget:ℕ)
   (degreeCost unitCost zDegree:RegularComponent Omega G T H → ℕ)
   (hcomponent:∀ C,
     (componentSeeds Omega G T H S v C).card*gap ≤
       U*degreeCost C+V*unitCost C+
         pencil*gap*zDegree C)
   (hdegree:(∑ C,degreeCost C) ≤ degreeWhole)
   (hunit:(∑ C,unitCost C) ≤ unitWhole)
   (hz:(∑ C,zDegree C) ≤ zBudget):
   S.card*gap ≤
     U*degreeWhole+V*unitWhole+pencil*gap*zBudget:=by
 classical
 calc
   S.card*gap ≤
       (∑ C:RegularComponent Omega G T H,
         (componentSeeds Omega G T H S v C).card)*gap:=
     Nat.mul_le_mul_right gap
       (card_le_sum_componentSeeds Omega G T H S v hG hT hH)
   _=∑ C:RegularComponent Omega G T H,
       (componentSeeds Omega G T H S v C).card*gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ C:RegularComponent Omega G T H,
       (U*degreeCost C+V*unitCost C+pencil*gap*zDegree C):=
     Finset.sum_le_sum (fun C _↦hcomponent C)
   _=U*(∑ C:RegularComponent Omega G T H,degreeCost C)+
       V*(∑ C:RegularComponent Omega G T H,unitCost C)+
       pencil*gap*
         (∑ C:RegularComponent Omega G T H,zDegree C):=by
     simp only [Finset.sum_add_distrib,Finset.mul_sum]
   _ ≤ U*degreeWhole+V*unitWhole+pencil*gap*zBudget:=
     Nat.add_le_add
       (Nat.add_le_add (Nat.mul_le_mul_left U hdegree)
         (Nat.mul_le_mul_left V hunit))
       (Nat.mul_le_mul_left (pencil*gap) hz)
theorem proper_cut_seed_bound_of_stratified_component_budgets
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (hdiv:G∣surfaceMap phi F)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w e)
   (degreeWhole unitWhole zBudget U V:ℕ)
   (degreeCost unitCost:RegularComponent Omega G T
     (regularitySurface phi F) → ℕ)
   (hfiber:∀ C:RegularComponent Omega G T
       (regularitySurface phi F),
     ∀ i∈nodes \
       identityNodes phi C.1 F nodes x u0 u1 w,
     ((componentSeeds Omega G T (regularitySurface phi F) Gamma
         (selectedPoint phi selected) C).filter (fun gamma↦
         (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card ≤
       (w-(identityNodes phi C.1 F nodes x u0 u1 w).card)*
           degreeCost C+unitCost C)
   (hsumDegree:(∑ C,degreeCost C) ≤ degreeWhole)
   (hsumUnit:(∑ C,unitCost C) ≤ unitWhole)
   (hproj:∀ C:RegularComponent Omega G T (regularitySurface phi F),
     ProjectionsFiniteSeparable Omega C.1)
   (hzbudget:
     (∑ C:RegularComponent Omega G T (regularitySurface phi F),
       actualCoordinateDegree Omega C.1 2) ≤ zBudget)
   (hdegree:∀ k ≤ w,
     (nodes.card-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunit:∀ k ≤ w,
     (nodes.card-k)*(a-w) ≤ V*(a-k)):
   Gamma.card*(a-w) ≤
     U*degreeWhole+V*unitWhole+(e+1)*(a-w)*zBudget:=by
 classical
 let H:=regularitySurface phi F
 have hHp:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) H≠0:=by
   intro gamma hgamma
   change MvPolynomial.eval (selectedPoint phi selected gamma)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular gamma hgamma
 let zDegree:RegularComponent Omega G T H → ℕ:=
   fun C↦actualCoordinateDegree Omega C.1 2
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma
         (selectedPoint phi selected) C).card*(a-w) ≤
       U*degreeCost C+V*unitCost C+
         (e+1)*(a-w)*zDegree C:=by
   intro C
   have hsub:=componentSeeds_subset Omega G T H Gamma
     (selectedPoint phi selected) C
   have hgmem:=regularComponent_G_mem Omega G T H C
   have hFmem:surfaceMap phi F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   apply prime_seed_incidence_of_stratified_residual_cost phi C.1
     (hproj C) (regularComponent_ne_point Omega G T H C)
     F hFmem (regularComponent_H_not_mem Omega G T H C)
     selected
     (componentSeeds Omega G T H Gamma (selectedPoint phi selected) C)
     nodes x u0 u1 hinj p w a e hw hchar hwa han
     (fun gamma hgamma↦hdegreeSelected gamma (hsub hgamma))
     (fun gamma hgamma↦hsolution gamma (hsub hgamma))
     (fun gamma hgamma↦hregular gamma (hsub hgamma))
     (fun gamma hgamma↦componentSeeds_on_prime Omega G T H Gamma
       (selectedPoint phi selected) C gamma hgamma)
     (fun gamma hgamma↦hagreement gamma (hsub hgamma))
     (noLargeSelectedPencil_mono selected Gamma _ w e hsub hnoPencil)
     (degreeCost C) (unitCost C) U V
     (by
       intro i hi
       exact hfiber C i hi)
     hdegree hunit
 exact aggregate_component_stratified_incidence G T H Gamma
   (selectedPoint phi selected) hGpoint hTpoint hHp (a-w) U V (e+1)
   degreeWhole unitWhole zBudget degreeCost unitCost zDegree hcomponent
   hsumDegree hsumUnit hzbudget
end
end ProximityPrize.SubmissionLower.RCN305
end PackedLegacy_GJ

/-! Packed from ProximityPrize.SubmissionLower.ER. -/
section PackedLegacy_ER
namespace ProximityPrize.SubmissionLower.RCN148
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN151 RCN152 RCN156 RCN165 RCN237 RCN305 RCN234 RCN215 RCN275
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def regularComponentCurveStageOfSupport
   (support:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ support.s)
   (hFys:wt residualYSWeights F ≤ support.ys)
   (hFtotal:wt residualTotalWeights F ≤ support.total)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d support:=by
 classical
 let GammaC:=componentSeeds Omega G T (regularitySurface phi F) Gamma
   (selectedPoint phi selected) C
 have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T
   (regularitySurface phi F) Gamma (selectedPoint phi selected) C
 exact {
   nodes:=nodes
   u0:=u0
   u1:=u1
   selected:=selected
   F:=F
   G:=G
   T:=T
   primeData:={
     ideal:=C.1
     isPrime:=inferInstance
     G_mem:=regularComponent_G_mem Omega G T (regularitySurface phi F) C
     T_mem:=regularComponent_T_mem Omega G T (regularitySurface phi F) C
     H_not_mem:=regularComponent_H_not_mem Omega G T
       (regularitySurface phi F) C
     ne_point:=regularComponent_ne_point Omega G T
       (regularitySurface phi F) C
   }
   G_dvd_surface:=hdiv
   G_flag_support:=hGflag
   T_flag_support:=hTflag
   surface_s_weight:=hFs
   surface_ys_weight:=hFys
   surface_total_weight:=hFtotal
   x_injective:=hinj
   degree_le:=fun gamma hgamma↦hdegree gamma (hsub hgamma)
   solution:=fun gamma hgamma↦hsolution gamma (hsub hgamma)
   regular:=fun gamma hgamma↦hregular gamma (hsub hgamma)
   on_prime:=fun gamma hgamma↦componentSeeds_on_prime Omega G T
     (regularitySurface phi F) Gamma (selectedPoint phi selected) C gamma hgamma
   no_large_pencil:=noLargeSelectedPencil_mono selected Gamma GammaC d e
     hsub hnoPencil
   characteristic_bound:=hchar
 }
def activeDifferentialSupport:ResidualSupportParameters where
 s:=6
 ys:=33
 total:=582
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
def regularComponentCurveStageActive
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 6)
   (hFys:wt residualYSWeights F ≤ 33)
   (hFtotal:wt residualTotalWeights F ≤ 582)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d activeDifferentialSupport:=
 regularComponentCurveStageOfSupport activeDifferentialSupport
   F G T selected Gamma nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag
   hTflag hFs hFys hFtotal hinj hdegree hsolution hregular hnoPencil hchar C
def regularComponentCurveStage
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d:ℕ) [CharP Omega p] (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 8)
   (hFys:wt residualYSWeights F ≤ 43)
   (hFtotal:wt residualTotalWeights F ≤ 503)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   CurveResidualStage phi
     (componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C)
     x p e surfaceFlag cutFlag d:=
 regularComponentCurveStageOfSupport ResidualSupportParameters.acceptedSupport
   F G T selected Gamma nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag
   hTflag hFs hFys hFtotal hinj hdegree hsolution hregular hnoPencil hchar C
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d a U V:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 6)
   (hFys:wt residualYSWeights F ≤ 33)
   (hFtotal:wt residualTotalWeights F ≤ 582)
   (hinj:Set.InjOn x nodes)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p) (hda:d < a)
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T)
     (H:=regularitySurface phi F) surfaceFlag cutFlag)
   (hlarge:∀ C:RegularComponent Omega G T (regularitySurface phi F),
     let GammaC:=componentSeeds Omega G T (regularitySurface phi F) Gamma
       (selectedPoint phi selected) C
     let S:=regularComponentCurveStageActive F G T selected Gamma nodes x u0 u1
       p e d surfaceFlag cutFlag hdiv hGflag hTflag hFs hFys hFtotal hinj
       hdegreeSelected hsolution hregular hnoPencil hchar C
     ∀ D:S.TerminalDescendant,
       D.degree < D.stage.identities.card →
         GammaC.card*(a-d) ≤ (e+1)*(a-d)*B.zCost C)
   (hdegree:∀ k ≤ d,
     (nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*flagMixed surfaceFlag cutFlag activeDifferentialSupport.agreementDirection+
       V*flagMixed surfaceFlag cutFlag unitYZFlag+
       (e+1)*(a-d)*flagMixed surfaceFlag cutFlag unitZFlag:=by
 classical
 let H:=regularitySurface phi F
 have hHp:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) H≠0:=by
   intro gamma hgamma
   change MvPolynomial.eval (selectedPoint phi selected gamma)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular gamma hgamma
 let degreeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost activeDifferentialSupport.agreementDirection C
 let unitCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost unitYZFlag C
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma
         (selectedPoint phi selected) C).card*(a-d) ≤
       U*degreeCost C+V*unitCost C+
         (e+1)*(a-d)*B.zCost C:=by
   intro C
   let GammaC:=componentSeeds Omega G T H Gamma
     (selectedPoint phi selected) C
   let S:=regularComponentCurveStageActive F G T selected Gamma nodes x u0 u1
     p e d surfaceFlag cutFlag hdiv hGflag hTflag hFs hFys hFtotal hinj
     hdegreeSelected hsolution hregular hnoPencil hchar C
   have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T H Gamma
     (selectedPoint phi selected) C
   apply recursive_curve_stratified_incidence_of_prime_flag_budget
     hphi S (fun r↦B.weightedCost r C) (B.primeBudget C)
     (degreeCost C) (unitCost C) U V (B.zCost C)
   · intro t
     simpa [degreeCost,unitCost,activeDifferentialSupport,
       ResidualSupportParameters.agreementDirection] using
       B.weightedCost_supportResidualAgreementFlag
         activeDifferentialSupport C t
   · exact hda
   · intro gamma hgamma
     exact hagreement gamma (hsub hgamma)
   · simpa only [GammaC,S,H] using hlarge C
   · simpa only [S,regularComponentCurveStageActive,
       regularComponentCurveStageOfSupport] using hdegree
   · simpa only [S,regularComponentCurveStageActive,
       regularComponentCurveStageOfSupport] using hunit
 exact aggregate_component_stratified_incidence G T H Gamma
   (selectedPoint phi selected) hGpoint hTpoint hHp (a-d) U V (e+1)
   (flagMixed surfaceFlag cutFlag activeDifferentialSupport.agreementDirection)
   (flagMixed surfaceFlag cutFlag unitYZFlag)
   (flagMixed surfaceFlag cutFlag unitZFlag)
   degreeCost unitCost B.zCost hcomponent
   (by simpa only [degreeCost] using
     B.sum_weightedCost_le activeDifferentialSupport.agreementDirection)
   (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
   B.sum_zCost_le
end
end ProximityPrize.SubmissionLower.RCN148
end PackedLegacy_ER

/-! Packed from ProximityPrize.SubmissionLower.BN. -/
section PackedLegacy_BN
namespace ProximityPrize.SubmissionLower.RCN149
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN151 RCN152 RCN156 RCN165 RCN237 RCN305 RCN234 RCN215 RCN148 RCN275
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all_of_support
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d a U V:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree)
   (support:ResidualSupportParameters)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ support.s)
   (hFys:wt residualYSWeights F ≤ support.ys)
   (hFtotal:wt residualTotalWeights F ≤ support.total)
   (hinj:Set.InjOn x nodes)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p) (hda:d < a)
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T)
     (H:=regularitySurface phi F) surfaceFlag cutFlag)
   (hallPositive:∀ C:RegularComponent Omega G T
     (regularitySurface phi F),1 ≤ B.allCost C)
   (hdegree:∀ k ≤ d,
     (nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*flagMixed surfaceFlag cutFlag support.agreementDirection+
       V*flagMixed surfaceFlag cutFlag unitYZFlag+
       (e+1)*(a-d)*
         (flagMixed surfaceFlag cutFlag unitZFlag+
           flagMixed surfaceFlag cutFlag unitAllFlag):=by
 classical
 let H:=regularitySurface phi F
 have hHp:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) H≠0:=by
   intro gamma hgamma
   change MvPolynomial.eval (selectedPoint phi selected gamma)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular gamma hgamma
 let degreeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost support.agreementDirection C
 let unitCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost unitYZFlag C
 let largeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.zCost C+B.allCost C
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma
         (selectedPoint phi selected) C).card*(a-d) ≤
       U*degreeCost C+V*unitCost C+
         (e+1)*(a-d)*largeCost C:=by
   intro C
   let GammaC:=componentSeeds Omega G T H Gamma
     (selectedPoint phi selected) C
   let S:=regularComponentCurveStageOfSupport support F G T selected Gamma
     nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag hTflag
     hFs hFys hFtotal hinj
     hdegreeSelected hsolution hregular hnoPencil hchar C
   have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T H Gamma
     (selectedPoint phi selected) C
   apply recursive_curve_stratified_incidence_of_prime_flag_budget
     hphi S (fun r↦B.weightedCost r C) (B.primeBudget C)
     (degreeCost C) (unitCost C) U V (largeCost C)
   · intro t
     simpa only [degreeCost,unitCost] using
       B.weightedCost_supportResidualAgreementFlag support C t
   · exact hda
   · intro gamma hgamma
     exact hagreement gamma (hsub hgamma)
   · intro D hmany
     have hcard:GammaC.card ≤ e+1:=
       D.stage.card_le_pencil_of_many_identities hmany
     have hlargePositive:1 ≤ largeCost C:=by
       exact (hallPositive C).trans (Nat.le_add_left _ _)
     have hscaled:GammaC.card*(a-d) ≤ (e+1)*(a-d):=
       Nat.mul_le_mul_right (a-d) hcard
     have hcharged:(e+1)*(a-d) ≤
         (e+1)*(a-d)*largeCost C:=by
       have hmul:=Nat.mul_le_mul_left ((e+1)*(a-d)) hlargePositive
       simpa only [Nat.mul_one] using hmul
     exact hscaled.trans hcharged
   · simpa only [S,regularComponentCurveStageOfSupport] using hdegree
   · simpa only [S,regularComponentCurveStageOfSupport] using hunit
 have hlargeSum:
     (∑ C:RegularComponent Omega G T H,largeCost C) ≤
       flagMixed surfaceFlag cutFlag unitZFlag+
         flagMixed surfaceFlag cutFlag unitAllFlag:=by
   calc
     (∑ C:RegularComponent Omega G T H,largeCost C)=
         (∑ C:RegularComponent Omega G T H,B.zCost C)+
           ∑ C:RegularComponent Omega G T H,B.allCost C:=by
       simp only [largeCost,Finset.sum_add_distrib]
     _ ≤ flagMixed surfaceFlag cutFlag unitZFlag+
         flagMixed surfaceFlag cutFlag unitAllFlag:=
       Nat.add_le_add B.sum_zCost_le B.sum_allCost_le
 exact aggregate_component_stratified_incidence G T H Gamma
   (selectedPoint phi selected) hGpoint hTpoint hHp (a-d) U V (e+1)
   (flagMixed surfaceFlag cutFlag support.agreementDirection)
   (flagMixed surfaceFlag cutFlag unitYZFlag)
   (flagMixed surfaceFlag cutFlag unitZFlag+
     flagMixed surfaceFlag cutFlag unitAllFlag)
   degreeCost unitCost largeCost hcomponent
   (by simpa only [degreeCost] using
     B.sum_weightedCost_le support.agreementDirection)
   (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
   hlargeSum
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d a U V:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ 8)
   (hFys:wt residualYSWeights F ≤ 43)
   (hFtotal:wt residualTotalWeights F ≤ 503)
   (hinj:Set.InjOn x nodes)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p) (hda:d < a)
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T)
     (H:=regularitySurface phi F) surfaceFlag cutFlag)
   (hallPositive:∀ C:RegularComponent Omega G T
     (regularitySurface phi F),1 ≤ B.allCost C)
   (hdegree:∀ k ≤ d,
     (nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*flagMixed surfaceFlag cutFlag agreementDirection6600+
       V*flagMixed surfaceFlag cutFlag unitYZFlag+
       (e+1)*(a-d)*
         (flagMixed surfaceFlag cutFlag unitZFlag+
           flagMixed surfaceFlag cutFlag unitAllFlag):=by
 simpa only [ResidualSupportParameters.acceptedSupport,
   ResidualSupportParameters.agreementDirection,agreementDirection6600] using
   proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all_of_support
     hphi F G T selected Gamma nodes x u0 u1 p e d a U V surfaceFlag cutFlag
     ResidualSupportParameters.acceptedSupport hdiv hGflag hTflag
     hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hGpoint hTpoint
     hagreement hnoPencil hchar hda B hallPositive hdegree hunit
end
end ProximityPrize.SubmissionLower.RCN149
end PackedLegacy_BN

/-! Packed from ProximityPrize.SubmissionLower.ES. -/
section PackedLegacy_ES
namespace ProximityPrize.SubmissionLower.RCN150
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN151 RCN152 RCN156 RCN165 RCN237 RCN305 RCN234 RCN148 RCN275
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_z_yz_of_direction
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d a U V:ℕ) [CharP Omega p]
   (surfaceFlag cutFlag:FlagDegree)
   (support:ResidualSupportParameters) (direction:FlagDegree)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag cutFlag T)
   (hFs:wt residualSWeights F ≤ support.s)
   (hFys:wt residualYSWeights F ≤ support.ys)
   (hFtotal:wt residualTotalWeights F ≤ support.total)
   (hinj:Set.InjOn x nodes)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p) (hda:d < a)
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T)
     (H:=regularitySurface phi F) surfaceFlag cutFlag)
   (hcost:∀ C:RegularComponent Omega G T (regularitySurface phi F),
     ∀ t:ℕ,B.weightedCost (support.residualAgreementFlag t) C=
       t*B.weightedCost direction C+B.weightedCost unitYZFlag C)
   (hzyzPositive:∀ C:RegularComponent Omega G T
     (regularitySurface phi F),1 ≤ B.zCost C+B.yzCost C)
   (hdegree:∀ k ≤ d,
     (nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*flagMixed surfaceFlag cutFlag direction+
       V*flagMixed surfaceFlag cutFlag unitYZFlag+
       (e+1)*(a-d)*
         (flagMixed surfaceFlag cutFlag unitZFlag+
           flagMixed surfaceFlag cutFlag unitYZFlag):=by
 classical
 let H:=regularitySurface phi F
 have hHp:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) H≠0:=by
   intro gamma hgamma
   change MvPolynomial.eval (selectedPoint phi selected gamma)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular gamma hgamma
 let degreeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost direction C
 let unitCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost unitYZFlag C
 let largeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.zCost C+B.yzCost C
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma
         (selectedPoint phi selected) C).card*(a-d) ≤
       U*degreeCost C+V*unitCost C+
         (e+1)*(a-d)*largeCost C:=by
   intro C
   let GammaC:=componentSeeds Omega G T H Gamma
     (selectedPoint phi selected) C
   let S:=regularComponentCurveStageOfSupport support F G T selected Gamma
     nodes x u0 u1 p e d surfaceFlag cutFlag hdiv hGflag hTflag
     hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hnoPencil hchar C
   have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T H Gamma
     (selectedPoint phi selected) C
   apply recursive_curve_stratified_incidence_of_prime_flag_budget
     hphi S (fun r↦B.weightedCost r C) (B.primeBudget C)
     (degreeCost C) (unitCost C) U V (largeCost C)
   · intro t
     simpa only [degreeCost,unitCost] using hcost C t
   · exact hda
   · intro gamma hgamma
     exact hagreement gamma (hsub hgamma)
   · intro D hmany
     have hcard:GammaC.card ≤ e+1:=
       D.stage.card_le_pencil_of_many_identities hmany
     have hscaled:GammaC.card*(a-d) ≤ (e+1)*(a-d):=
       Nat.mul_le_mul_right (a-d) hcard
     have hcharged:(e+1)*(a-d) ≤
         (e+1)*(a-d)*largeCost C:=by
       have hmul:=Nat.mul_le_mul_left ((e+1)*(a-d))
         (hzyzPositive C)
       simpa only [largeCost,Nat.mul_one] using hmul
     exact hscaled.trans hcharged
   · simpa only [S,regularComponentCurveStageOfSupport] using hdegree
   · simpa only [S,regularComponentCurveStageOfSupport] using hunit
 have hlargeSum:
     (∑ C:RegularComponent Omega G T H,largeCost C) ≤
       flagMixed surfaceFlag cutFlag unitZFlag+
         flagMixed surfaceFlag cutFlag unitYZFlag:=by
   calc
     (∑ C:RegularComponent Omega G T H,largeCost C)=
         (∑ C:RegularComponent Omega G T H,B.zCost C)+
           ∑ C:RegularComponent Omega G T H,B.yzCost C:=by
       simp only [largeCost,Finset.sum_add_distrib]
     _ ≤ flagMixed surfaceFlag cutFlag unitZFlag+
         flagMixed surfaceFlag cutFlag unitYZFlag:=
       Nat.add_le_add B.sum_zCost_le B.sum_yzCost_le
 exact aggregate_component_stratified_incidence G T H Gamma
   (selectedPoint phi selected) hGpoint hTpoint hHp (a-d) U V (e+1)
   (flagMixed surfaceFlag cutFlag direction)
   (flagMixed surfaceFlag cutFlag unitYZFlag)
   (flagMixed surfaceFlag cutFlag unitZFlag+
     flagMixed surfaceFlag cutFlag unitYZFlag)
   degreeCost unitCost largeCost hcomponent
   (by simpa only [degreeCost] using
     B.sum_weightedCost_le direction)
   (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
   hlargeSum
end
end ProximityPrize.SubmissionLower.RCN150
end PackedLegacy_ES

/-! Packed from ProximityPrize.SubmissionLower.DP. -/
section PackedLegacy_DP
namespace ProximityPrize.SubmissionLower.RCN038
open scoped Classical WithZero TensorProduct
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN044 RCN093 RCN099 RCN096 RCN114 RCN116 RCN295 RCN022 RCN369 RCN370
 RCN351
open RCN037
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveNestedProjectionDataActive
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0) where
 lam:Omega
 lam_ne:lam≠0
 mu:Omega
 mu_ne:mu≠0
 uProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 allProjection:∀ C:RegularComponent Omega G T H,
   Coordinate Omega (CoordinateField Omega C.1)
 uGate:∀ C:RegularComponent Omega G T H,
   ∀ htr:Transcendental Omega (affineU Omega C.1 lam),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1)
           (affineU Omega C.1 lam) htr).toRingHom.toAlgebra;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 uTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega (affineU Omega C.1 lam)
 allAffineTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega (affineV Omega C.1 mu (mu*lam))
 allFinite:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1)
 allSeparable:∀ C:RegularComponent Omega G T H,
   letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 mu (mu*lam))
       (allAffineTranscendental C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)
 uValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=
     affineU Omega C.1 lam
 allValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1) (allProjection C)=
     affineV Omega C.1 mu (mu*lam)
 allTranscendental:∀ C:RegularComponent Omega G T H,
   Transcendental Omega
     (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))
 uPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (uProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
       (RCN187.poleOrder v.val (coordinate Omega C.1 2))
 allPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
   RCN187.poleOrder v.val
       (coordinateValue Omega (CoordinateField Omega C.1) (allProjection C))=
     max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
       (max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)))
 directional:MvPolynomial.pderiv (0:Fin 3) G-
   MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G≠0
theorem exists_adaptiveNestedProjectionDataActive
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0):
   Nonempty (AdaptiveNestedProjectionDataActive base hactive hSderiv):=by
 classical
 let E:RegularComponent Omega G T H → Type:=
   fun C => CoordinateField Omega C.1
 let rY:∀ C,E C:=fun C => coordinate Omega C.1 0
 let z:∀ C,E C:=fun C => coordinate Omega C.1 2
 let W:∀ C,Finset (Place Omega (E C)):=
   fun C => literalRelevantPlaces (base C)
 let baseC:∀ C,SeparableCoordinate Omega (E C):=
   fun C => literalToSeparableCoordinate (base C)
 obtain ⟨lam,hlam0,hlam⟩:=
   exists_common_exact_finite_separable_affine_adaptive E rY z W
     baseC hactive
 let U:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=fun C => affineU Omega C.1 lam
 have hUgate:∀ C:RegularComponent Omega G T H,
     ∀ htr:Transcendental Omega (U C),
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (U C) htr).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
   intro C htr
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   have hp:htr=hs:=Subsingleton.elim _ _
   cases hp
   exact ⟨hfinite,hsep⟩
 let uProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=
   fun C => coordinateOfGate (U C) (hUgate C)
 have huValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (uProjection C)=U C:=
   fun C => coordinateOfGate_value (U C) (hUgate C)
 have huPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (U C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 0))
         (RCN187.poleOrder v.val (coordinate Omega C.1 2)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rY,z,U,affineU] using
         (hlam C).choose_spec.2.2 v hv)
   · have h0:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 0
     have h2:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 2
     have h0le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h0
     have h2le:=valuation_le_one_of_poleOrder_eq_zero v.val _ h2
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (lam • coordinate Omega C.1 2)=
         v.val (coordinate Omega C.1 2):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one lam hlam0,one_mul]
     have hUle:v.val (U C) ≤ 1:=by
       exact (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le h0le h2le)
     have hU0:RCN187.poleOrder v.val (U C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.1) v _ hUle
     rw [hU0,h0,h2]
     simp
 have hactiveV:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 1)≠0∨
       D Omega (CoordinateField Omega C.1) (U C)≠0:=by
   intro C
   obtain ⟨hs,hfinite,hsep,_⟩:=hlam C
   exact Or.inr (differential_ne_zero_of_gate _ hs ⟨hfinite,hsep⟩)
 let rS:∀ C,E C:=fun C => coordinate Omega C.1 1
 let Extra:Omega → Prop:=fun mu =>
   MvPolynomial.pderiv (0:Fin 3) G-
     MvPolynomial.C mu*MvPolynomial.pderiv (1:Fin 3) G=0
 have hextra:∀ {a b},Extra a → Extra b → a=b:=by
   exact directional_bad_coefficient_subsingleton G hSderiv
 obtain ⟨mu,hmu0,hmudir,hmu⟩:=
   exists_common_exact_finite_separable_affine_adaptive_avoiding_one
     E rS U W Extra hextra baseC hactiveV
 let V:∀ C:RegularComponent Omega G T H,
     CoordinateField Omega C.1:=
   fun C => coordinate Omega C.1 1+mu • U C
 let hV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (V C):=fun C => (hmu C).choose
 let vProjection:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C)
   finite:=(hmu C).choose_spec.1
   separable:=(hmu C).choose_spec.2.1}
 have hvValue:∀ C:RegularComponent Omega G T H,
     coordinateValue Omega (CoordinateField Omega C.1) (vProjection C)=V C:=by
   intro C
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1) (V C) (hV C)
 have hvPole:∀ (C:RegularComponent Omega G T H)
     (v:Place Omega (CoordinateField Omega C.1)),
     RCN187.poleOrder v.val (V C)=
       max (RCN187.poleOrder v.val (coordinate Omega C.1 1))
         (RCN187.poleOrder v.val (U C)):=by
   intro C v
   by_cases hv:v∈literalRelevantPlaces (base C)
   · exact poleOrder_eq_max_of_valuation_eq_max v.val _ _ _ (by
       simpa only [W,rS,V] using (hmu C).choose_spec.2.2 v hv)
   · have hS:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 1
     have hY:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 0
     have hZ:=coordinate_poleOrder_eq_zero_of_not_mem_literalRelevant
         (base C) v hv 2
     have hU:RCN187.poleOrder v.val (U C)=0:=by
       rw [huPole C v,hY,hZ]
       simp
     have hSle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hS
     have hUle:=valuation_le_one_of_poleOrder_eq_zero v.val _ hU
     letI:v.val.IsTrivialOn Omega:=v.property.2
     have hscalar:v.val (mu • U C)=v.val (U C):=by
       rw [Algebra.smul_def,map_mul,
         Valuation.IsTrivialOn.eq_one mu hmu0,one_mul]
     have hVle:v.val (V C) ≤ 1:=
       (v.val.map_add _ _).trans
         (by rw [hscalar];exact max_le hSle hUle)
     have hV0:RCN187.poleOrder v.val (V C)=0:=
       RCN346.poleOrder_eq_zero_of_le_one Omega
         (CoordinateField Omega C.1) v _ hVle
     rw [hV0,hS,hU]
     simp
 let hVAff:∀ C:RegularComponent Omega G T H,
     Transcendental Omega (affineV Omega C.1 mu (mu*lam)):=fun C => by
   rw [show affineV Omega C.1 mu (mu*lam)=V C by
     simp only [V,U,affineU,affineV]
     module]
   exact hV C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 mu (mu*lam)) (hVAff C)=
       elementEmbedding Omega (CoordinateField Omega C.1) (V C) (hV C):=
   elementEmbedding_congr (hVAff C) (hV C) (by
     simp only [V,U,affineU,affineV]
     simp only [smul_add,smul_smul,add_assoc])
 refine ⟨{
   lam:=lam
   lam_ne:=hlam0
   mu:=mu
   mu_ne:=hmu0
   uProjection:=uProjection
   allProjection:=vProjection
   uGate:=hUgate
   uTranscendental:=fun C => (hlam C).choose
   allAffineTranscendental:=hVAff
   allFinite:=?_
   allSeparable:=?_
   uValue:=huValue
   allValue:=?_
   allTranscendental:=?_
   uPole:=?_
   allPole:=?_
   directional:=hmudir}⟩
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.1
 · intro C
   rw [hembV C]
   exact (hmu C).choose_spec.2.1
 · intro C
   rw [hvValue C]
   simp only [V,U,affineU,affineV]
   simp only [smul_add,smul_smul,add_assoc]
 · intro C
   rw [hvValue C]
   exact hV C
 · intro C v
   rw [huValue C]
   exact huPole C v
 · intro C v
   rw [hvValue C,hvPole C v,huPole C v]
end
end ProximityPrize.SubmissionLower.RCN038
end PackedLegacy_DP

/-! Packed from ProximityPrize.SubmissionLower.A2. -/
section PackedLegacy_A2
namespace ProximityPrize.SubmissionLower.RCN040
open scoped Classical BigOperators WithZero
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN046 RCN037 RCN038 RCN095 RCN114 RCN093 RCN123 RCN121 RCN117 RCN116 RCN125 RCN022
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamily_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamily base p q:=by
 classical
 let lam:=D.lam
 let mu:=D.mu
 let nu:=D.mu*D.lam
 let zProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (coordinate Omega C.1 2) (hZ C)
 let uProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C =>
   coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)
 let vProj:∀ C:RegularComponent Omega G T H,
     Coordinate Omega (CoordinateField Omega C.1):=fun C => Sum.inr {
   embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
   finite:=D.allFinite C
   separable:=D.allSeparable C}
 let gCaps:=flagTrapezoidCaps_flagAlgHom p G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom q T lam mu nu hTsupport
 have hTne:T≠0:=by
   intro hzero
   apply hproper
   rw [hzero]
   exact dvd_zero G
 let sZ:={C:RegularComponent Omega G T H//
   Transcendental Omega (coordinate Omega C.1 2)}
 have hinjZ:Function.Injective (fun C:sZ => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htZ:∀ C:sZ,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (zOrder 0))):=by
   intro C
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using C.2
 have hembZ (C:sZ):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (coordinate Omega C.1.1 2) C.2:=
   elementEmbedding_congr (htZ C) C.2
     (by simp [zOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenZ:∀ C:sZ,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (zOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembZ C]
   simpa [zOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_z Omega C.1.1 lam mu nu C.2
 have hfamilyZ:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sZ => C.1.1) hinjZ lam mu nu zOrder
   htZ hgenZ G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
   p.all q.all (p.yz+p.all) (q.yz+q.all)
   (flagMixed p q unitZFlag) hTne
   (by simpa only [gCaps] using gCaps.zOuter)
   (by simpa only [tCaps] using tCaps.zOuter)
   (by simpa only [gCaps] using gCaps.zTotal)
   (by simpa only [tCaps] using tCaps.zTotal)
   (z_flag_trapezoid_budget p q)
 have hsumZ:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (zProj C)) ≤
       flagMixed p q unitZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => coordinate Omega C.1 2) hZ
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sZ,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (coordinate Omega C.1.1 2) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sZ,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (zOrder 0))) (htZ C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembZ C]
     _ ≤ _:=hfamilyZ.2
 let sU:={C:RegularComponent Omega G T H//
   Transcendental Omega (affineU Omega C.1 D.lam)}
 have hinjU:Function.Injective (fun C:sU => C.1.1):=by
   intro C E hCE
   apply Subtype.ext
   apply Subtype.ext
   exact hCE
 let htU:∀ C:sU,
     Transcendental Omega
       (flagEvaluation Omega C.1.1 lam mu nu
         (MvPolynomial.X (uOrder 0))):=by
   intro C
   simpa [uOrder,lam,mu,nu] using C.2
 have hembU (C:sU):
     elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)=
       elementEmbedding Omega (CoordinateField Omega C.1.1)
         (affineU Omega C.1.1 D.lam) C.2:=
   elementEmbedding_congr (htU C) C.2
     (by simp [uOrder,lam,mu,nu])
 have hgenU:∀ C:sU,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1.1)
         (flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 2)),
         flagEvaluation Omega C.1.1 lam mu nu
           (MvPolynomial.X (uOrder 1))}:
         Set (CoordinateField Omega C.1.1))=⊤:=by
   intro C
   rw [hembU C]
   simpa [uOrder,lam,mu,nu] using
     flag_generators_u Omega C.1.1 lam mu nu C.2
 have hfamilyU:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:sU => C.1.1) hinjU lam mu nu uOrder
   htU hgenU G T hG
   (fun C => regularComponent_G_mem Omega G T H C.1)
   (fun C => regularComponent_T_mem Omega G T H C.1)
   hproper
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
   p.all q.all (p.zOnly+p.yz+p.all)
   (q.zOnly+q.yz+q.all) (flagMixed p q unitYZFlag) hTne
   (by simpa only [gCaps] using gCaps.uOuter)
   (by simpa only [tCaps] using tCaps.uOuter)
   (by simpa only [gCaps] using gCaps.uTotal)
   (by simpa only [tCaps] using tCaps.uTotal)
   (u_flag_trapezoid_budget p q)
 have hsumU:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (uProj C)) ≤
       flagMixed p q unitYZFlag:=by
   have hsplit:=sum_coordinateOfGate_degree_eq
     (K:=Omega)
     (E:=fun C:RegularComponent Omega G T H => CoordinateField Omega C.1)
     (x:=fun C => affineU Omega C.1 D.lam) D.uGate
   change (∑ C:RegularComponent Omega G T H,
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C))) ≤ _
   rw [hsplit]
   calc
     (∑ C:sU,
       (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
         (elementEmbedding Omega (CoordinateField Omega C.1.1)
           (affineU Omega C.1.1 D.lam) C.2).toRingHom.toAlgebra
        Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)))=
         ∑ C:sU,
           (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1.1):=
             (elementEmbedding Omega (CoordinateField Omega C.1.1)
               (flagEvaluation Omega C.1.1 lam mu nu
                 (MvPolynomial.X (uOrder 0))) (htU C)).toRingHom.toAlgebra
            Module.finrank (RatFunc Omega) (CoordinateField Omega C.1.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembU C]
     _ ≤ _:=hfamilyU.2
 let htV:∀ C:RegularComponent Omega G T H,
     Transcendental Omega
       (flagEvaluation Omega C.1 lam mu nu
         (MvPolynomial.X (vOrder 0))):=by
   intro C
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     D.allAffineTranscendental C
 have hembV (C:RegularComponent Omega G T H):
     elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)=
       elementEmbedding Omega (CoordinateField Omega C.1)
         (affineV Omega C.1 D.mu (D.mu*D.lam))
           (D.allAffineTranscendental C):=
   elementEmbedding_congr (htV C) (D.allAffineTranscendental C)
     (by simp [vOrder,Equiv.swap_apply_def,lam,mu,nu])
 have hgenV:∀ C:RegularComponent Omega G T H,
     letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
       (elementEmbedding Omega (CoordinateField Omega C.1)
         (flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 2)),
         flagEvaluation Omega C.1 lam mu nu
           (MvPolynomial.X (vOrder 1))}:
         Set (CoordinateField Omega C.1))=⊤:=by
   intro C
   rw [hembV C]
   simpa [vOrder,Equiv.swap_apply_def,lam,mu,nu] using
     flag_generators_v Omega C.1 lam mu nu (D.allAffineTranscendental C)
 have hinjV:Function.Injective
     (fun C:RegularComponent Omega G T H => C.1):=by
   intro C E hCE
   exact Subtype.ext hCE
 have hfamilyV:=finite_sum_flag_finrank_trapezoid
   (K:=Omega) (Q:=fun C:RegularComponent Omega G T H => C.1)
   hinjV lam mu nu vOrder htV hgenV G T hG
   (fun C => regularComponent_G_mem Omega G T H C)
   (fun C => regularComponent_T_mem Omega G T H C)
   hproper
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
   (p.yz+p.all) (q.yz+q.all)
   (p.zOnly+p.yz+p.all) (q.zOnly+q.yz+q.all)
   (flagMixed p q unitAllFlag) hTne
   (by simpa only [gCaps] using gCaps.vOuter)
   (by simpa only [tCaps] using tCaps.vOuter)
   (by simpa only [gCaps] using gCaps.vTotal)
   (by simpa only [tCaps] using tCaps.vTotal)
   (v_flag_trapezoid_budget p q)
 have hsumV:
     (∑ C:RegularComponent Omega G T H,
       coordinateDegree Omega (CoordinateField Omega C.1) (vProj C)) ≤
       flagMixed p q unitAllFlag:=by
   calc
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (affineV Omega C.1 D.mu (D.mu*D.lam))
               (D.allAffineTranscendental C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rfl
     _=∑ C:RegularComponent Omega G T H,
         (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
           (elementEmbedding Omega (CoordinateField Omega C.1)
             (flagEvaluation Omega C.1 lam mu nu
               (MvPolynomial.X (vOrder 0))) (htV C)).toRingHom.toAlgebra
          Module.finrank (RatFunc Omega) (CoordinateField Omega C.1)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [hembV C]
     _ ≤ _:=hfamilyV.2
 have hvValue (C:RegularComponent Omega G T H):
     coordinateValue Omega (CoordinateField Omega C.1) (vProj C)=
       affineV Omega C.1 D.mu (D.mu*D.lam):=by
   dsimp only [vProj,coordinateValue,SeparableCoordinate.value,Sum.elim_inr]
   exact elementEmbedding_variable Omega (CoordinateField Omega C.1)
     (affineV Omega C.1 D.mu (D.mu*D.lam))
     (D.allAffineTranscendental C)
 refine {
   zProjection:=zProj
   yzProjection:=uProj
   allProjection:=vProj
   zValue:=?_
   allTranscendental:=?_
   zPole_eq:=?_
   yzPole_eq:=?_
   allPole_eq:=?_
   sum_zDegree_le:=hsumZ
   sum_yzDegree_le:=hsumU
   sum_allDegree_le:=hsumV}
 · intro C
   exact coordinateOfGate_value _ _
 · intro C
   rw [hvValue C]
   exact D.allAffineTranscendental C
 · intro C v
   rw [exponentSetPoleWeight_unitZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
 · intro C v
   rw [exponentSetPoleWeight_unitYZ]
   change _=RCN187.poleOrder v.val _
   rw [coordinateOfGate_value]
   rw [←D.uValue C]
   exact (D.uPole C v).symm
 · intro C v
   rw [exponentSetPoleWeight_unitAll]
   change _=RCN187.poleOrder v.val _
   rw [hvValue C, ←D.allValue C]
   exact (D.allPole C v).symm
theorem exists_adaptiveUnitProjectionFamily_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamily base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionDataActive base hactive hSderiv
 exact ⟨adaptiveUnitProjectionFamily_of_active_nested p q base hactive hZ hSderiv D
   hG hproper hGsupport hTsupport⟩
end
end ProximityPrize.SubmissionLower.RCN040
end PackedLegacy_A2

/-! Packed from ProximityPrize.SubmissionLower.E7. -/
section PackedLegacy_E7
namespace ProximityPrize.SubmissionLower.RCN265
open scoped Classical
open RCN002 RCN136 RCN243 RCN264 RCN267 RCN344 RCN341 RCN042 RCN037 RCN039 RCN046 RCN142 RCN093 RCN095
noncomputable section
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
def verticalPoint (y z:Omega):Fin 3 → Polynomial Omega:=
 ![Polynomial.C y,Polynomial.X,Polynomial.C z]
def verticalPolynomial (y z:Omega):
   MvPolynomial (Fin 3) Omega →ₐ[Omega] Polynomial Omega:=
 MvPolynomial.aeval (verticalPoint y z)
theorem verticalPolynomial_derivative (y z:Omega)
   (F:MvPolynomial (Fin 3) Omega):
   (verticalPolynomial y z F).derivative=
     verticalPolynomial y z (MvPolynomial.pderiv (1:Fin 3) F):=by
 induction F using MvPolynomial.induction_on with
 | C a => simp [verticalPolynomial]
 | add P Q hP hQ => simp only [map_add,Polynomial.derivative_add,hP,hQ]
 | mul_X P i hP =>
     fin_cases i <;>
       simp [verticalPolynomial,verticalPoint,Polynomial.derivative_mul] at hP ⊢ <;>
       rw [hP] <;> ring
theorem aeval_verticalPolynomial_eq_coordinateEvaluation
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (y z:Omega)
   (hy:algebraMap Omega (CoordinateField Omega P) y=coordinate Omega P 0)
   (hz:algebraMap Omega (CoordinateField Omega P) z=coordinate Omega P 2)
   (F:MvPolynomial (Fin 3) Omega):
   Polynomial.aeval (coordinate Omega P 1) (verticalPolynomial y z F)=
     coordinateEvaluation Omega P F:=by
 let lhs:MvPolynomial (Fin 3) Omega →ₐ[Omega] CoordinateField Omega P:=
   (Polynomial.aeval (coordinate Omega P 1)).comp (verticalPolynomial y z)
 have hlhs:lhs=coordinateEvaluation Omega P:=by
   apply MvPolynomial.algHom_ext
   intro i
   fin_cases i <;>
     simp [lhs,verticalPolynomial,verticalPoint,coordinate,hy,hz]
 exact AlgHom.congr_fun hlhs F
theorem y_or_z_transcendental_of_regular_polynomial
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (F:MvPolynomial (Fin 3) Omega)
   (hF:F∈P)
   (hFR:MvPolynomial.pderiv (1:Fin 3) F∉P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2):=by
 by_contra hYZ
 push_neg at hYZ
 have hYalg:IsAlgebraic Omega (coordinate Omega P 0):=not_not.mp hYZ.1
 have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hYZ.2
 obtain ⟨y,hy⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 0 hYalg
 obtain ⟨z,hz⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P 2 hZalg
 obtain ⟨i,hi⟩:=
   exists_transcendental_coordinate_of_ne_point_kernel Omega P hnonpoint
 have hiR:i=(1:Fin 3):=by
   fin_cases i <;> simp_all
 subst i
 let Q:=verticalPolynomial y z F
 have hQeval:Polynomial.aeval (coordinate Omega P 1) Q=0:=by
   rw [aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz F]
   change coordinateEvaluation Omega P F=0
   have hm:F∈RingHom.ker (coordinateEvaluation Omega P).toRingHom:=by
     rwa [coordinateEvaluation_ker Omega P]
   exact hm
 have hQ:Q=0:=by
   apply transcendental_iff_injective.mp hi
   simpa using hQeval
 have hQderiv:Q.derivative=0:=by rw [hQ,Polynomial.derivative_zero]
 have hFReval:coordinateEvaluation Omega P
     (MvPolynomial.pderiv (1:Fin 3) F)=0:=by
   rw [←aeval_verticalPolynomial_eq_coordinateEvaluation P y z hy hz]
   rw [←verticalPolynomial_derivative]
   simpa [Q] using congrArg
     (Polynomial.aeval (coordinate Omega P 1)) hQderiv
 apply hFR
 rw [←coordinateEvaluation_ker Omega P,RingHom.mem_ker]
 exact hFReval
variable {K:Type} [Field K]
theorem regularComponent_y_or_z_transcendental
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:MvPolynomial (Fin 3) Omega)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   Transcendental Omega (coordinate Omega C.1 0)∨
     Transcendental Omega (coordinate Omega C.1 2):=by
 let H:=regularitySurface phi F
 have hGmem:G∈C.1:=regularComponent_G_mem Omega G T H C
 have hFmem:surfaceMap phi F∈C.1:=by
   obtain ⟨Q,hQ⟩:=hdiv
   rw [hQ]
   exact C.1.mul_mem_right Q hGmem
 have hFRnot:MvPolynomial.pderiv (1:Fin 3) (surfaceMap phi F)∉C.1:=by
   rw [surfaceMap_pderiv_R]
   exact regularComponent_H_not_mem Omega G T H C
 exact y_or_z_transcendental_of_regular_polynomial C.1 (surfaceMap phi F)
   hFmem hFRnot (regularComponent_ne_point Omega G T H C)
section RefinedAdaptiveFamily
variable {G T H:MvPolynomial (Fin 3) Omega}
structure AdaptiveUnitProjectionFamilyYZ
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (p q:FlagDegree) where
 family:AdaptiveUnitProjectionFamily base p q
 lam:Omega
 yzValue:∀ C:RegularComponent Omega G T H,
   coordinateValue Omega (CoordinateField Omega C.1)
       (family.yzProjection C)=affineU Omega C.1 lam
def adaptiveUnitProjectionFamilyYZ_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionData base hY hZ hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamilyYZ base p q where
 family:=adaptiveUnitProjectionFamily_of_nested p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport
 lam:=D.lam
 yzValue:=by
   intro C
   exact coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)
theorem AdaptiveUnitProjectionFamilyYZ.one_le_zCost_add_yzCost
   {base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1}
   {p q:FlagDegree}
   (P:AdaptiveUnitProjectionFamilyYZ base p q)
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (hH:H=regularitySurface phi F)
   (hdiv:G∣surfaceMap phi F)
   (C:RegularComponent Omega G T H):
   1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C+
     P.family.toPrimeFlagBudgetFamily.yzCost C:=by
 subst H
 have hYZ:=regularComponent_y_or_z_transcendental phi F G T hdiv C
 by_cases hZ:Transcendental Omega (coordinate Omega C.1 2)
 · have hzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.zCost C:=
     P.family.one_le_toPrimeFlagBudgetFamily_zCost C hZ
   omega
 · have hZalg:IsAlgebraic Omega (coordinate Omega C.1 2):=
     not_not.mp hZ
   have hY:Transcendental Omega (coordinate Omega C.1 0):=by
     rcases hYZ with hY | hZ'
     · exact hY
     · exact (hZ hZ').elim
   have hU:Transcendental Omega (affineU Omega C.1 P.lam):=by
     exact transcendental_add_smul_of_transcendental_isAlgebraic
       Omega C.1 (coordinate Omega C.1 0) (coordinate Omega C.1 2)
         P.lam hY hZalg
   have hyzpos:1 ≤ P.family.toPrimeFlagBudgetFamily.yzCost C:=by
     apply one_le_coordinateDegree_of_transcendental_value
     rw [P.yzValue C]
     exact hU
   omega
theorem exists_adaptiveUnitProjectionFamilyYZ_of_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamilyYZ base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionData base hY hZ hSderiv
 exact ⟨adaptiveUnitProjectionFamilyYZ_of_nested p q base hY hZ hSderiv D
   hG hproper hGsupport hTsupport⟩
end RefinedAdaptiveFamily
end
end ProximityPrize.SubmissionLower.RCN265
end PackedLegacy_E7

/-! Packed from ProximityPrize.SubmissionLower.DQ. -/
section PackedLegacy_DQ
namespace ProximityPrize.SubmissionLower.RCN041
open scoped Classical
open Polynomial KaehlerDifferential RCN002 RCN005 RCN344 RCN264 RCN341 RCN042 RCN035 RCN093 RCN037 RCN038 RCN040 RCN046 RCN265 RCN095
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 30000
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
def adaptiveUnitProjectionFamilyYZ_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   AdaptiveUnitProjectionFamilyYZ base p q where
 family:=adaptiveUnitProjectionFamily_of_active_nested p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport
 lam:=D.lam
 yzValue:=by
   intro C
   exact coordinateOfGate_value (affineU Omega C.1 D.lam) (D.uGate C)
theorem exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   (p q:FlagDegree)
   (base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent Omega G T H,
     D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 0)≠0∨
       D Omega (CoordinateField Omega C.1) (coordinate Omega C.1 2)≠0)
   (hZ:∀ C:RegularComponent Omega G T H,
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGsupport:G.support ⊆ flagSupport p)
   (hTsupport:T.support ⊆ flagSupport q):
   Nonempty (AdaptiveUnitProjectionFamilyYZ base p q):=by
 obtain ⟨D⟩:=exists_adaptiveNestedProjectionDataActive base hactive hSderiv
 exact ⟨adaptiveUnitProjectionFamilyYZ_of_active_nested p q base hactive hZ
   hSderiv D hG hproper hGsupport hTsupport⟩
end
end ProximityPrize.SubmissionLower.RCN041
end PackedLegacy_DQ

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier19 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.O6. -/
section PackedLegacy_O6
namespace ProximityPrize.SubmissionLower.RCN277
open scoped Classical
open RCN002 RCN005 RCN003 RCN009 RCN001 RCN072 RCN264 RCN136 RCN243 RCN341 RCN265
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 20000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
abbrev Poly3:=MvPolynomial (Fin 3) Omega
theorem exists_coordinate_difference_mem_of_isAlgebraic
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime] (i:Fin 3)
   (hi:IsAlgebraic Omega (coordinate Omega P i)):
   ∃ c:Omega,MvPolynomial.X i-MvPolynomial.C c∈P:=by
 obtain ⟨c,hc⟩:=coordinate_eq_scalar_of_isAlgebraic Omega P i hi
 refine ⟨c,?_⟩
 rw [←aeval_coordinate_ker Omega P]
 change MvPolynomial.aeval (coordinate Omega P)
     (MvPolynomial.X i-MvPolynomial.C c)=0
 simp only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
 rw [←hc,sub_self]
theorem not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos
   (G:Poly3 (Omega:=Omega)) (hG:G≠0)
   (hdep:0 < G.degreeOf (1:Fin 3)) (c:Omega):
   ¬ G∣(MvPolynomial.X (2:Fin 3)-MvPolynomial.C c):=by
 let H:Poly3 (Omega:=Omega):=
   MvPolynomial.X (2:Fin 3)-MvPolynomial.C c
 have hHne:H≠0:=coordinate_difference_ne_zero Omega 2 c
 have hHdegree:H.degreeOf (1:Fin 3) ≤ 0:=by
   calc
     H.degreeOf (1:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 1)
           ((MvPolynomial.C c:Poly3).degreeOf 1):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (1:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=0:=by
       rw [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2),
         MvPolynomial.degreeOf_C]
       rfl
 intro hdiv
 obtain ⟨A,hA⟩:=hdiv
 have hHA:H=G*A:=by simpa only [H] using hA
 have hAne:A≠0:=by
   intro hzero
   apply hHne
   rw [hHA,hzero,mul_zero]
 have hle:G.degreeOf (1:Fin 3) ≤ H.degreeOf (1:Fin 3):=by
   calc
     G.degreeOf (1:Fin 3) ≤
         G.degreeOf (1:Fin 3)+A.degreeOf (1:Fin 3):=
       Nat.le_add_right _ _
     _=(G*A).degreeOf (1:Fin 3):=by
       rw [MvPolynomial.degreeOf_mul_eq hG hAne]
     _=H.degreeOf (1:Fin 3):=by rw [hHA]
 omega
theorem finite_separable_at_y_of_z_algebraic
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hY:Transcendental Omega (coordinate Omega P 0))
   (hZ:IsAlgebraic Omega (coordinate Omega P 2)):
   letI:Algebra (RatFunc Omega) (CoordinateField Omega P):=
     rationalBaseAlgebra Omega P 0 hY
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)∧
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega P):=by
 obtain ⟨c,hHmem⟩:=
   exists_coordinate_difference_mem_of_isAlgebraic P 2 hZ
 let H:Poly3 (Omega:=Omega):=
   MvPolynomial.X (2:Fin 3)-MvPolynomial.C c
 have hproper:¬ G∣H:=
   not_dvd_coordinate_two_sub_C_of_degreeOf_one_pos G hG.ne_zero hdep c
 have hHone:H.degreeOf (1:Fin 3) ≤ 0:=by
   calc
     H.degreeOf (1:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 1)
           ((MvPolynomial.C c:Poly3).degreeOf 1):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (1:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=0:=by
       rw [MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2),
         MvPolynomial.degreeOf_C]
       rfl
 have hHtwo:H.degreeOf (2:Fin 3) ≤ 1:=by
   calc
     H.degreeOf (2:Fin 3) ≤
         max ((MvPolynomial.X (2:Fin 3):Poly3).degreeOf 2)
           ((MvPolynomial.C c:Poly3).degreeOf 2):=by
       simpa only [H] using MvPolynomial.degreeOf_sub_le (2:Fin 3)
         (MvPolynomial.X (2:Fin 3):Poly3) (MvPolynomial.C c)
     _=1:=by simp
 have hmixed:coordinateMixedDegree Omega G H 0 < p:=by
   rw [coordinateMixedDegree_zero]
   calc
     H.degreeOf 1*G.degreeOf 2+G.degreeOf 1*H.degreeOf 2 ≤
         0*G.degreeOf 2+G.degreeOf 1*1:=
       Nat.add_le_add (Nat.mul_le_mul hHone (Nat.le_refl _))
         (Nat.mul_le_mul (Nat.le_refl _) hHtwo)
     _=G.degreeOf 1:=by simp
     _ < p:=hdegree 1
 exact finite_separable_at_of_original_coordinate_gate Omega P 0 hY p G H
   hG hGmem hHmem hproper hdegree hmixed
theorem exists_separableLiteralCoordinate_y_or_z
   (P:Ideal (Poly3 (Omega:=Omega))) [P.IsPrime]
   (p:ℕ) [CharP Omega p]
   (G T:Poly3 (Omega:=Omega))
   (hG:Irreducible G) (hGmem:G∈P) (hTmem:T∈P)
   (hproper:¬ G∣T)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedZ:coordinateMixedDegree Omega G T 2 < p)
   (hYZ:Transcendental Omega (coordinate Omega P 0)∨
     Transcendental Omega (coordinate Omega P 2)):
   ∃ D:SeparableLiteralCoordinate P,
     D.index=0∨D.index=2:=by
 by_cases hZ:Transcendental Omega (coordinate Omega P 2)
 · have hz:=finite_separable_at_of_original_coordinate_gate
     Omega P 2 hZ p G T hG hGmem hTmem hproper hdegree hmixedZ
   exact ⟨⟨2,hZ,hz.1,hz.2⟩,Or.inr rfl⟩
 · have hY:Transcendental Omega (coordinate Omega P 0):=
     hYZ.resolve_right hZ
   have hZalg:IsAlgebraic Omega (coordinate Omega P 2):=not_not.mp hZ
   have hy:=finite_separable_at_y_of_z_algebraic P p G hG hGmem hdep
     hdegree hY hZalg
   exact ⟨⟨0,hY,hy.1,hy.2⟩,Or.inl rfl⟩
theorem regularComponent_exists_separableLiteralCoordinate6630
   {K:Type} [Field K]
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:Poly3 (Omega:=Omega))
   (p:ℕ) [CharP Omega p]
   (hdiv:G∣surfaceMap phi F)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedZ:coordinateMixedDegree Omega G T 2 < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   ∃ D:SeparableLiteralCoordinate C.1,
     D.index=0∨D.index=2:=by
 apply exists_separableLiteralCoordinate_y_or_z C.1 p G T hG
   (regularComponent_G_mem Omega G T (regularitySurface phi F) C)
   (regularComponent_T_mem Omega G T (regularitySurface phi F) C)
   hproper hdep hdegree hmixedZ
 exact regularComponent_y_or_z_transcendental phi F G T hdiv C
theorem regularComponent_nonempty_separableLiteralCoordinate6630
   {K:Type} [Field K]
   (phi:Polynomial K →+*Omega)
   (F:MvPolynomial (Fin 4) K)
   (G T:Poly3 (Omega:=Omega))
   (p:ℕ) [CharP Omega p]
   (hdiv:G∣surfaceMap phi F)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hdep:0 < G.degreeOf (1:Fin 3))
   (hdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedZ:coordinateMixedDegree Omega G T 2 < p)
   (C:RegularComponent Omega G T (regularitySurface phi F)):
   Nonempty (SeparableLiteralCoordinate C.1):=by
 obtain ⟨D,_⟩:=regularComponent_exists_separableLiteralCoordinate6630
   phi F G T p hdiv hG hproper hdep hdegree hmixedZ C
 exact ⟨D⟩
end
end ProximityPrize.SubmissionLower.RCN277
end PackedLegacy_O6

/-! Packed from ProximityPrize.SubmissionLower.EV. -/
section PackedLegacy_EV
namespace ProximityPrize.SubmissionLower.RCN153
open scoped Classical
open RCN159 RCN164 RCN213 RCN215 RCN214 RCN238 RCN095 RCN275
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
def factorRegularLedgerFor (p direction:FlagDegree):ℕ:=
 degreeIncidence*
     ((flagMixed p direction direction*degreeIncidence+
         flagMixed p direction unitYZFlag*unitIncidence)+
       (errors+1)*gap*
         (flagMixed p direction unitZFlag+
           flagMixed p direction unitAllFlag))+
   unitIncidence*
     ((flagMixed p direction unitYZFlag*degreeIncidence+
         flagMixed p unitYZFlag unitYZFlag*unitIncidence)+
       (errors+1)*gap*
         (flagMixed p unitYZFlag unitZFlag+
           flagMixed p unitYZFlag unitAllFlag))
theorem recursive_scaled_factor_with_support_6600
   (hphi:Function.Injective phi)
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (p:FlagDegree)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*gap ≤
       D.degree*
           ((flagMixed p support.agreementDirection support.agreementDirection*
               degreeIncidence+
             flagMixed p support.agreementDirection unitYZFlag*
               unitIncidence)+
             (errors+1)*gap*
               (flagMixed p support.agreementDirection unitZFlag+
                 flagMixed p support.agreementDirection unitAllFlag))+
         ((flagMixed p support.agreementDirection unitYZFlag*
               degreeIncidence+
             flagMixed p unitYZFlag unitYZFlag*unitIncidence)+
           (errors+1)*gap*
             (flagMixed p unitYZFlag unitZFlag+
               flagMixed p unitYZFlag unitAllFlag))):
   Gamma.card*gap^2 ≤
     factorRegularLedgerFor p support.agreementDirection:=by
 have h:=recursive_scaled_stratified_incidence_bound
   hphi S
   ((flagMixed p support.agreementDirection support.agreementDirection*
         degreeIncidence+
       flagMixed p support.agreementDirection unitYZFlag*unitIncidence)+
     (errors+1)*gap*
       (flagMixed p support.agreementDirection unitZFlag+
         flagMixed p support.agreementDirection unitAllFlag))
   ((flagMixed p support.agreementDirection unitYZFlag*degreeIncidence+
       flagMixed p unitYZFlag unitYZFlag*unitIncidence)+
     (errors+1)*gap*
       (flagMixed p unitYZFlag unitZFlag+
         flagMixed p unitYZFlag unitAllFlag))
   degreeIncidence unitIncidence
   (by norm_num [agreements,n,errors,w])
   hagreement hfiber
   (by
     intro k hk
     rw [hnodes]
     exact degree_part_bound k hk)
   (by
     intro k hk
     rw [hnodes]
     exact unit_part_bound k hk)
 calc
   Gamma.card*gap^2 ≤
       degreeIncidence*
           ((flagMixed p support.agreementDirection support.agreementDirection*
                 degreeIncidence+
               flagMixed p support.agreementDirection unitYZFlag*
                 unitIncidence)+
             (errors+1)*gap*
               (flagMixed p support.agreementDirection unitZFlag+
                 flagMixed p support.agreementDirection unitAllFlag))+
         unitIncidence*
           ((flagMixed p support.agreementDirection unitYZFlag*
                 degreeIncidence+
               flagMixed p unitYZFlag unitYZFlag*unitIncidence)+
             (errors+1)*gap*
               (flagMixed p unitYZFlag unitZFlag+
                 flagMixed p unitYZFlag unitAllFlag)):=by
     simpa only [gap] using h
   _=factorRegularLedgerFor p support.agreementDirection:=rfl
theorem recursive_scaled_factor_6600
   (hphi:Function.Injective phi)
   (S:ResidualStage phi Gamma x pchar errors flag w)
   (p:FlagDegree)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*gap ≤
       D.degree*
           ((flagMixed p agreementDirection6600 agreementDirection6600*
               degreeIncidence+
             flagMixed p agreementDirection6600 unitYZFlag*
               unitIncidence)+
             (errors+1)*gap*
               (flagMixed p agreementDirection6600 unitZFlag+
                 flagMixed p agreementDirection6600 unitAllFlag))+
         ((flagMixed p agreementDirection6600 unitYZFlag*
               degreeIncidence+
             flagMixed p unitYZFlag unitYZFlag*unitIncidence)+
           (errors+1)*gap*
             (flagMixed p unitYZFlag unitZFlag+
               flagMixed p unitYZFlag unitAllFlag))):
   Gamma.card*gap^2 ≤ factorRegularLedger p:=by
 have h:=recursive_scaled_factor_with_support_6600 hphi
   ResidualSupportParameters.acceptedSupport S p hnodes hagreement
     (by
       simpa [ResidualSupportParameters.acceptedSupport,
         ResidualSupportParameters.agreementDirection,
         agreementDirection6600] using hfiber)
 calc
   Gamma.card*gap^2 ≤
       factorRegularLedgerFor p
         ResidualSupportParameters.acceptedSupport.agreementDirection:=h
   _=factorRegularLedger p:=by
     simp [factorRegularLedgerFor,factorRegularLedger,factorPrimary,
       factorZTail,factorAllTail,
       ResidualSupportParameters.acceptedSupport,
       ResidualSupportParameters.agreementDirection,
       agreementDirection6600]
     ring
end
end ProximityPrize.SubmissionLower.RCN153
end PackedLegacy_EV

/-! Packed from ProximityPrize.SubmissionLower.EW. -/
section PackedLegacy_EW
namespace ProximityPrize.SubmissionLower.RCN154
open scoped Classical
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN159 RCN159.ResidualStage RCN151 RCN148 RCN149 RCN153 RCN156 RCN158 RCN275 RCN237 RCN213 RCN215 RCN214 RCN234 RCN276 RCN091
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 40000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def TerminalLargeZChargeOfSupport
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (D:S.TerminalDescendant) (i:Iota)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (support.residualAgreementFlag D.degree)):Prop:=
 let GammaI:=Gamma.filter (fun gamma↦D.stage.Agrees gamma i)
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let aD:=agreements-(w-D.degree)
 ∀ C:RegularComponent Omega D.stage.G T
     (regularitySurface phi D.stage.F),
   let GammaC:=componentSeeds Omega D.stage.G T
     (regularitySurface phi D.stage.F) GammaI
     (selectedPoint phi D.stage.selected) C
   let SC:=regularComponentCurveStageOfSupport support D.stage.F D.stage.G T
     D.stage.selected GammaI D.stage.nodes x D.stage.u0 D.stage.u1
     pchar errors D.degree flag (support.residualAgreementFlag D.degree)
     D.stage.G_dvd_surface D.stage.flag_support
     (surfaceMap_agreement_in_flag_of_support support
       D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
       D.stage.surface_total_weight D.degree
       (fun j↦(j.factorial:K)⁻¹)
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     D.stage.surface_s_weight D.stage.surface_ys_weight
     D.stage.surface_total_weight D.stage.x_injective
     (fun gamma hgamma↦D.stage.degree_le gamma
       (Finset.mem_filter.mp hgamma).1)
     (fun gamma hgamma↦D.stage.solution gamma
       (Finset.mem_filter.mp hgamma).1)
     (fun gamma hgamma↦D.stage.regular gamma
       (Finset.mem_filter.mp hgamma).1)
     (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
       D.degree errors (Finset.filter_subset _ _) D.stage.no_large_pencil)
     D.stage.characteristic_bound C
   ∀ E:SC.TerminalDescendant,
     E.degree < E.stage.identities.card →
       GammaC.card*(aD-D.degree) ≤
         (errors+1)*(aD-D.degree)*B.zCost C
abbrev TerminalLargeZCharge
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w)
   (D:S.TerminalDescendant) (i:Iota)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (residualAgreementFlag D.degree)):Prop:=
 TerminalLargeZChargeOfSupport S D i B
theorem terminal_outer_fiber_bound_of_prime_flag_budget_profile
   (hphi:Function.Injective phi)
   (n a w e U V:ℕ)
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (S.agreementFiber gamma).card)
   (hwa:w < a) (_han:a ≤ n)
   (hdegreeGlobal:∀ k ≤ w,
     (n-k)*(a-w)*(w-k) ≤ U*(a-k))
   (hunitGlobal:∀ k ≤ w,
     (n-k)*(a-w) ≤ V*(a-k))
   (D:S.TerminalDescendant) (i:Iota) (_hi:i∈D.stage.nodes)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (support.residualAgreementFlag D.degree))
   (hallPositive:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
   (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*(a-w) ≤
     D.degree*
         ((flagMixed flag support.agreementDirection support.agreementDirection*
             U+
           flagMixed flag support.agreementDirection unitYZFlag*
             V)+
           (e+1)*(a-w)*
             (flagMixed flag support.agreementDirection unitZFlag+
               flagMixed flag support.agreementDirection unitAllFlag))+
       ((flagMixed flag support.agreementDirection unitYZFlag*
             U+
           flagMixed flag unitYZFlag unitYZFlag*V)+
         (e+1)*(a-w)*
           (flagMixed flag unitYZFlag unitZFlag+
             flagMixed flag unitYZFlag unitAllFlag)):=by
 classical
 let GammaI:=Gamma.filter (fun gamma↦D.stage.Agrees gamma i)
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let aD:=a-(w-D.degree)
 have hTflag:PolynomialInFlag
     (support.residualAgreementFlag D.degree) T:=by
   exact surfaceMap_agreement_in_flag_of_support support
     D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
     D.stage.surface_total_weight D.degree
     (fun j↦(j.factorial:K)⁻¹)
     (x i) (D.stage.u0 i) (D.stage.u1 i)
 have hsub:GammaI ⊆ Gamma:=Finset.filter_subset _ _
 have hTpoint:∀ gamma∈GammaI,
     MvPolynomial.eval (selectedPoint phi D.stage.selected gamma) T=0:=by
   intro gamma hgamma
   obtain ⟨hGamma,hagree⟩:=Finset.mem_filter.mp hgamma
   exact (selected_agreement_zero_iff phi D.stage.F D.stage.selected
     pchar D.degree D.stage.characteristic_bound gamma
     (D.stage.degree_le gamma hGamma) (D.stage.solution gamma hGamma)
     (D.stage.regular gamma hGamma)
     (x i) (D.stage.u0 i) (D.stage.u1 i)).mpr hagree
 have hinnerAgreement:∀ gamma∈GammaI,
     aD ≤ (D.stage.nodes.filter (fun j↦
       (D.stage.selected gamma).eval (x j)=
         D.stage.u0 j+gamma*D.stage.u1 j)).card:=by
   intro gamma hgamma
   have hGamma:=hsub hgamma
   have h0:=Nat.sub_le_sub_right (hagreement gamma hGamma)
     (w-D.degree)
   exact h0.trans (by
     simpa only [aD,ResidualStage.agreementFiber,
       ResidualStage.Agrees] using D.agreement_card gamma hGamma)
 have hda:D.degree < aD:=by
   have hD:=D.degree_le
   dsimp only [aD]
   omega
 have hdegree:∀ k ≤ D.degree,
     (D.stage.nodes.card-k)*(aD-D.degree)*(D.degree-k) ≤
       U*(aD-k):=by
   intro k hk
   have hDle:D.degree ≤ w:=D.degree_le
   let total:=(w-D.degree)+k
   have htotal:total ≤ w:=by
     dsimp only [total]
     omega
   have h:=hdegreeGlobal total htotal
   have hnodesD:=D.nodes_card
   rw [hnodes] at hnodesD
   have hgap:
       aD-D.degree=a-w:=by
     dsimp only [aD]
     omega
   have hn:n-total=D.stage.nodes.card-k:=by
     rw [hnodesD]
     dsimp only [total]
     omega
   have hw:w-total=D.degree-k:=by
     dsimp only [total]
     omega
   have ha:a-total=aD-k:=by
     dsimp only [total,aD]
     omega
   rw [hgap]
   rw [hn,hw,ha] at h
   exact h
 have hunit:∀ k ≤ D.degree,
     (D.stage.nodes.card-k)*(aD-D.degree) ≤
       V*(aD-k):=by
   intro k hk
   have hDle:D.degree ≤ w:=D.degree_le
   let total:=(w-D.degree)+k
   have htotal:total ≤ w:=by
     dsimp only [total]
     omega
   have h:=hunitGlobal total htotal
   have hnodesD:=D.nodes_card
   rw [hnodes] at hnodesD
   have hgap:
       aD-D.degree=a-w:=by
     dsimp only [aD]
     omega
   have hn:n-total=D.stage.nodes.card-k:=by
     rw [hnodesD]
     dsimp only [total]
     omega
   have ha:a-total=aD-k:=by
     dsimp only [total,aD]
     omega
   rw [hgap]
   rw [hn,ha] at h
   exact h
 have hbound:=
   proper_cut_seed_bound_of_recursive_prime_flag_budget_z_all_of_support
   hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
   x D.stage.u0 D.stage.u1 pchar e D.degree aD
   U V flag
   (support.residualAgreementFlag D.degree) support
   D.stage.G_dvd_surface D.stage.flag_support hTflag
   D.stage.surface_s_weight D.stage.surface_ys_weight
   D.stage.surface_total_weight D.stage.x_injective
   (fun gamma hgamma↦D.stage.degree_le gamma (hsub hgamma))
   (fun gamma hgamma↦D.stage.solution gamma (hsub hgamma))
   (fun gamma hgamma↦D.stage.regular gamma (hsub hgamma))
   (fun gamma hgamma↦D.stage.on_component gamma (hsub hgamma))
   hTpoint hinnerAgreement
   (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
     D.degree e hsub D.stage.no_large_pencil)
   D.stage.characteristic_bound hda B (by
     simpa only [T] using hallPositive)
   hdegree hunit
 have hgapEq:aD-D.degree=a-w:=by
   have:=D.degree_le
   dsimp only [aD]
   omega
 rw [hgapEq] at hbound
 rw [flagMixed_supportResidualAgreement_direction,
   flagMixed_supportResidualAgreement_unit,
   flagMixed_supportResidualAgreement_z,
   flagMixed_supportResidualAgreement_all] at hbound
 dsimp only [GammaI] at hbound
 calc
   _ ≤ _:=hbound
   _=_:=by ring
theorem terminal_outer_fiber_bound_of_prime_flag_budget_of_support
   (hphi:Function.Injective phi)
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (D:S.TerminalDescendant) (i:Iota) (hi:i∈D.stage.nodes)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (support.residualAgreementFlag D.degree))
   (hallPositive:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
   (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*gap ≤
     D.degree*
         ((flagMixed flag support.agreementDirection support.agreementDirection*
             degreeIncidence+
           flagMixed flag support.agreementDirection unitYZFlag*
             unitIncidence)+
           (errors+1)*gap*
             (flagMixed flag support.agreementDirection unitZFlag+
               flagMixed flag support.agreementDirection unitAllFlag))+
       ((flagMixed flag support.agreementDirection unitYZFlag*
             degreeIncidence+
           flagMixed flag unitYZFlag unitYZFlag*unitIncidence)+
         (errors+1)*gap*
           (flagMixed flag unitYZFlag unitZFlag+
             flagMixed flag unitYZFlag unitAllFlag)):=by
 apply terminal_outer_fiber_bound_of_prime_flag_budget_profile hphi
   n agreements w errors degreeIncidence unitIncidence S hnodes hagreement
   (by norm_num [agreements,n,errors,w])
   (by norm_num [agreements,n,errors])
   (fun k hk => by simpa only [gap] using degree_part_bound k hk)
   (fun k hk => by simpa only [gap] using unit_part_bound k hk)
   D i hi B hallPositive
theorem terminal_outer_fiber_bound_of_prime_flag_budget
   (hphi:Function.Injective phi)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (D:S.TerminalDescendant) (i:Iota) (hi:i∈D.stage.nodes)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (residualAgreementFlag D.degree))
   (hallPositive:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
   (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*gap ≤
     D.degree*
         ((flagMixed flag agreementDirection6600 agreementDirection6600*
             degreeIncidence+
           flagMixed flag agreementDirection6600 unitYZFlag*
             unitIncidence)+
           (errors+1)*gap*
             (flagMixed flag agreementDirection6600 unitZFlag+
               flagMixed flag agreementDirection6600 unitAllFlag))+
       ((flagMixed flag agreementDirection6600 unitYZFlag*
             degreeIncidence+
           flagMixed flag unitYZFlag unitYZFlag*unitIncidence)+
         (errors+1)*gap*
           (flagMixed flag unitYZFlag unitZFlag+
             flagMixed flag unitYZFlag unitAllFlag)):=by
 simpa [ResidualSupportParameters.acceptedSupport,
   ResidualSupportParameters.agreementDirection,agreementDirection6600] using
   terminal_outer_fiber_bound_of_prime_flag_budget_of_support
     hphi S hnodes hagreement D i hi B hallPositive
theorem recursive_scaled_factor_6600_of_prime_flag_budgets_of_support
   (hphi:Function.Injective phi)
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hbudget:∀ (D:S.TerminalDescendant) (i:Iota),
     i∈D.stage.nodes →
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     ∃ B:PrimeFlagBudgetFamily
       (G:=D.stage.G)
         (T:=agreementPolynomial phi D.stage.F D.degree
           (x i) (D.stage.u0 i) (D.stage.u1 i))
         (H:=regularitySurface phi D.stage.F)
       flag (support.residualAgreementFlag D.degree),
       ∀ C:RegularComponent Omega D.stage.G
         (agreementPolynomial phi D.stage.F D.degree
           (x i) (D.stage.u0 i) (D.stage.u1 i))
         (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
   Gamma.card*gap^2 ≤
     factorRegularLedgerFor flag support.agreementDirection:=by
 apply recursive_scaled_factor_with_support_6600 hphi support S flag
   hnodes hagreement
 intro D i hi hproper
 obtain ⟨B,hallPositive⟩:=hbudget D i hi hproper
 exact terminal_outer_fiber_bound_of_prime_flag_budget_of_support
   hphi S hnodes hagreement D i hi B hallPositive
theorem recursive_scaled_factor_6656_of_prime_flag_budgets
   (hphi:Function.Injective phi)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (hnodes:S.nodes.card=meetProfile.n)
   (hagreement:∀ gamma∈Gamma,
     meetProfile.agreements ≤ (S.agreementFiber gamma).card)
   (hbudget:∀ (D:S.TerminalDescendant) (i:Iota),
     i∈D.stage.nodes →
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     ∃ B:PrimeFlagBudgetFamily
       (G:=D.stage.G)
       (T:=agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (H:=regularitySurface phi D.stage.F)
       flag (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree),
       ∀ C:RegularComponent Omega D.stage.G
         (agreementPolynomial phi D.stage.F D.degree
           (x i) (D.stage.u0 i) (D.stage.u1 i))
         (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
   Gamma.card*meetProfile.gap^2 ≤
     meetProfile.factorRegularLedger flag:=by
 apply recursive_scaled_factor_6656 hphi S flag hnodes hagreement
 intro D i hi hproper
 obtain ⟨B,hallPositive⟩:=hbudget D i hi hproper
 have h:=terminal_outer_fiber_bound_of_prime_flag_budget_profile hphi
   meetProfile.n meetProfile.agreements meetProfile.w meetProfile.errors
   meetProfile.degreeIncidence meetProfile.unitIncidence S hnodes hagreement
   (by norm_num [meetProfile]) (by norm_num [meetProfile])
   meet_degree_part_bound meet_unit_part_bound D i hi B hallPositive
 simpa only [Profile.gap,meetFactorDegreeCost,meetFactorUnitCost] using h
theorem recursive_scaled_factor_6600_of_prime_flag_budgets
   (hphi:Function.Injective phi)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hbudget:∀ (D:S.TerminalDescendant) (i:Iota),
     i∈D.stage.nodes →
     ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i) →
     ∃ B:PrimeFlagBudgetFamily
       (G:=D.stage.G)
       (T:=agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (H:=regularitySurface phi D.stage.F)
       flag (residualAgreementFlag D.degree),
       ∀ C:RegularComponent Omega D.stage.G
         (agreementPolynomial phi D.stage.F D.degree
           (x i) (D.stage.u0 i) (D.stage.u1 i))
         (regularitySurface phi D.stage.F),1 ≤ B.allCost C):
   Gamma.card*gap^2 ≤ factorRegularLedger flag:=by
 have h:=recursive_scaled_factor_6600_of_prime_flag_budgets_of_support
   hphi S hnodes hagreement hbudget
 calc
   Gamma.card*gap^2 ≤
       factorRegularLedgerFor flag
         ResidualSupportParameters.acceptedSupport.agreementDirection:=h
   _=factorRegularLedger flag:=by
     simp [factorRegularLedgerFor,factorRegularLedger,factorPrimary,
       factorZTail,factorAllTail,
       ResidualSupportParameters.acceptedSupport,
       ResidualSupportParameters.agreementDirection,
       agreementDirection6600]
     ring
end
end ProximityPrize.SubmissionLower.RCN154
end PackedLegacy_EW

/-! Packed from ProximityPrize.SubmissionLower.DR. -/
section PackedLegacy_DR
namespace ProximityPrize.SubmissionLower.RCN043
open scoped Classical
open RCN213 RCN231 RCN238 RCN264 RCN243 RCN095 RCN159 RCN151 RCN156 RCN154 RCN237 RCN215 RCN214 RCN341 RCN046
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def TerminalAdaptiveProjectionFamilies
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (residualAgreementFlag D.degree))
theorem recursive_scaled_factor_6600_of_adaptive_projection_families
   (hphi:Function.Injective phi)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar errors flag w)
   (hnodes:S.nodes.card=n)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hprojection:TerminalAdaptiveProjectionFamilies S):
   Gamma.card*gap^2 ≤ factorRegularLedger flag:=by
 apply recursive_scaled_factor_6600_of_prime_flag_budgets
   hphi S hnodes hagreement
 intro D i hi hproper
 obtain ⟨base,⟨P⟩⟩:=hprojection D i hi hproper
 refine ⟨P.toPrimeFlagBudgetFamily,?_⟩
 intro C
 exact P.one_le_toPrimeFlagBudgetFamily_allCost C
end
end ProximityPrize.SubmissionLower.RCN043
end PackedLegacy_DR

/-! Packed from ProximityPrize.SubmissionLower.O5. -/
section PackedLegacy_O5
namespace ProximityPrize.SubmissionLower.RCN274
open RCN136 RCN267 RCN159 RCN095
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
theorem residualStage_pderiv_one_ne_zero
   (S:ResidualStage phi Gamma x p e flag d):
   MvPolynomial.pderiv (1:Fin 3) S.G≠0:=by
 intro hzero
 apply S.regular_proper
 rw [←surfaceMap_pderiv_R]
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 refine ⟨MvPolynomial.pderiv (1:Fin 3) Q,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul,hzero,zero_mul,zero_add]
end
end ProximityPrize.SubmissionLower.RCN274
end PackedLegacy_O5

/-! Packed from ProximityPrize.SubmissionLower.GN. -/
section PackedLegacy_GN
namespace ProximityPrize.SubmissionLower.RCN314
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN095 RCN159 RCN158 RCN156 RCN037 RCN039 RCN043 RCN341 RCN274
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem degree_bounds_of_polynomialInFlag
   {p:FlagDegree} {F:MvPolynomial (Fin 3) Omega}
   (hF:PolynomialInFlag p F):
   F.degreeOf 0 ≤ p.yz+p.all∧
     F.degreeOf 1 ≤ p.all∧
     F.degreeOf 2 ≤ p.zOnly+p.yz+p.all:=by
 refine ⟨?_,?_,?_⟩
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_right (e 0) (e 1)).trans (hF e he).2.1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (hF e he).1
 · apply MvPolynomial.degreeOf_le_iff.mpr
   intro e he
   exact (Nat.le_add_left (e 2) (e 0+e 1)).trans (by
     simpa only [Nat.add_assoc] using (hF e he).2.2)
theorem terminalAdaptiveProjectionFamilies_of_rectangular_caps
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime errors flag w)
   (hflagZ:flag.zOnly ≤ 495)
   (hflagY:flag.yz ≤ 43)
   (hflagS:flag.all ≤ 8):
   TerminalAdaptiveProjectionFamilies S:=by
 classical
 intro D i hi hproper
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let H:=regularitySurface phi D.stage.F
 have hGflag:PolynomialInFlag flag D.stage.G:=D.stage.flag_support
 have hTflag:PolynomialInFlag (residualAgreementFlag D.degree) T:=by
   exact surfaceMap_agreement_in_flag_of_surface_weights
     D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
     D.stage.surface_total_weight D.degree
     (fun j↦(j.factorial:K)⁻¹)
     (x i) (D.stage.u0 i) (D.stage.u1 i)
 obtain ⟨hGY,hGS,hGZ⟩:=degree_bounds_of_polynomialInFlag hGflag
 obtain ⟨hTY,hTS,hTZ⟩:=degree_bounds_of_polynomialInFlag hTflag
 have hD:D.degree ≤ w:=D.degree_le.trans (Nat.le_refl w)
 have hGY':D.stage.G.degreeOf 0 ≤ 51:=by omega
 have hGS':D.stage.G.degreeOf 1 ≤ 8:=by omega
 have hGZ':D.stage.G.degreeOf 2 ≤ 546:=by omega
 have hTY':T.degreeOf 0 ≤ 1+85*w:=by
   dsimp only [residualAgreementFlag] at hTY
   omega
 have hTS':T.degreeOf 1 ≤ 15*w:=by
   dsimp only [residualAgreementFlag] at hTS
   omega
 have hTZ':T.degreeOf 2 ≤ 1+1005*w:=by
   dsimp only [residualAgreementFlag] at hTZ
   omega
 have hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < prime:=by
   intro j
   fin_cases j
   · exact hGY'.trans_lt (by norm_num [prime])
   · exact hGS'.trans_lt (by norm_num [prime])
   · exact hGZ'.trans_lt (by norm_num [prime])
 have hmixedY:
     coordinateMixedDegree Omega D.stage.G T 0 < prime:=by
   rw [coordinateMixedDegree_zero]
   apply (Nat.add_le_add
     (Nat.mul_le_mul hTS' hGZ')
     (Nat.mul_le_mul hGS' hTZ')).trans_lt
   norm_num [w,prime]
 have hmixedZ:
     coordinateMixedDegree Omega D.stage.G T 2 < prime:=by
   rw [coordinateMixedDegree_two]
   apply (Nat.add_le_add
     (Nat.mul_le_mul hTY' hGS')
     (Nat.mul_le_mul hGY' hTS')).trans_lt
   norm_num [w,prime]
 let hY:∀ C:RegularComponent Omega D.stage.G T H,
     LiteralProjectionGate C 0:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 0 htr
     prime D.stage.G T D.stage.irreducible_G
     (regularComponent_G_mem Omega D.stage.G T H C)
     (regularComponent_T_mem Omega D.stage.G T H C)
     hproper hGdegree hmixedY
 let hZ:∀ C:RegularComponent Omega D.stage.G T H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     prime D.stage.G T D.stage.irreducible_G
     (regularComponent_G_mem Omega D.stage.G T H C)
     (regularComponent_T_mem Omega D.stage.G T H C)
     hproper hGdegree hmixedZ
 have hbase:∀ C:RegularComponent Omega D.stage.G T H,
     Nonempty (SeparableLiteralCoordinate C.1):=by
   intro C
   exact exists_separableLiteralCoordinate_of_YZ_gates C.1
     (regularComponent_ne_point Omega D.stage.G T H C) (hY C) (hZ C)
 let base:∀ C:RegularComponent Omega D.stage.G T H,
     SeparableLiteralCoordinate C.1:=fun C↦Classical.choice (hbase C)
 refine ⟨base,?_⟩
 exact exists_adaptiveUnitProjectionFamily_of_nested flag
   (residualAgreementFlag D.degree) base hY hZ
   (residualStage_pderiv_one_ne_zero D.stage)
   D.stage.irreducible_G hproper
   ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
   ((support_subset_flagSupport_iff (residualAgreementFlag D.degree) T).2 hTflag)
end
end ProximityPrize.SubmissionLower.RCN314
end PackedLegacy_GN

/-! Packed from ProximityPrize.SubmissionLower.GO. -/
section PackedLegacy_GO
namespace ProximityPrize.SubmissionLower.RCN315
open scoped Classical
open RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN267 RCN095 RCN159 RCN158 RCN037 RCN039 RCN046 RCN341 RCN274 RCN275 RCN276
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem residualStage_pderiv_one_ne_zero_of_support
   {p e d:ℕ} [CharP Omega p] {flag:FlagDegree}
   {support:ResidualSupportParameters}
   (S:ResidualStage phi Gamma x p e flag d support):
   MvPolynomial.pderiv (1:Fin 3) S.G≠0:=by
 intro hzero
 apply S.regular_proper
 rw [←surfaceMap_pderiv_R]
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 refine ⟨MvPolynomial.pderiv (1:Fin 3) Q,?_⟩
 rw [hQ,MvPolynomial.pderiv_mul,hzero,zero_mul,zero_add]
def FixedMeetTerminalAdaptiveProjectionFamilies
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree))
theorem fixedMeet_cut_coordinate_caps {d:ℕ} (hd:d ≤ 131071):
   (1+56*d)+11*d ≤ 1+67*131071∧
     11*d ≤ 11*131071∧
     1140*d+(1+56*d)+11*d ≤ 1+1207*131071:=by
 refine ⟨?_,Nat.mul_le_mul_left 11 hd,?_⟩
 · calc
     (1+56*d)+11*d=1+67*d:=by ring
     _ ≤ 1+67*131071:=Nat.add_le_add_left
       (Nat.mul_le_mul_left 67 hd) 1
 · calc
     1140*d+(1+56*d)+11*d=1+1207*d:=by ring
     _ ≤ 1+1207*131071:=Nat.add_le_add_left
       (Nat.mul_le_mul_left 1207 hd) 1
theorem fixedMeet_terminal_mixed_gates:
   (11*131071)*638+6*(1+1207*131071)=1869072466∧
     (1+67*131071)*6+40*(11*131071)=110361788∧
     1869072466 < prime:=by
 norm_num [prime]
theorem literalProjectionGates_of_fixedMeet_caps
   [CharP Omega prime]
   {G T H:MvPolynomial (Fin 3) Omega}
   (hGirreducible:Irreducible G)
   (hproper:¬ G∣T)
   (hGY:G.degreeOf 0 ≤ 40)
   (hGS:G.degreeOf 1 ≤ 6)
   (hGZ:G.degreeOf 2 ≤ 638)
   (hTY:T.degreeOf 0 ≤ 1+67*131071)
   (hTS:T.degreeOf 1 ≤ 11*131071)
   (hTZ:T.degreeOf 2 ≤ 1+1207*131071):
   (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)∧
     (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2):=by
 have hGdegree:∀ j:Fin 3,G.degreeOf j < prime:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt (by norm_num [prime])
   · exact hGS.trans_lt (by norm_num [prime])
   · exact hGZ.trans_lt (by norm_num [prime])
 have hmixedY:coordinateMixedDegree Omega G T 0 < prime:=by
   rw [coordinateMixedDegree_zero]
   apply (Nat.add_le_add
     (Nat.mul_le_mul hTS hGZ)
     (Nat.mul_le_mul hGS hTZ)).trans_lt
   norm_num [prime]
 have hmixedZ:coordinateMixedDegree Omega G T 2 < prime:=by
   rw [coordinateMixedDegree_two]
   apply (Nat.add_le_add
     (Nat.mul_le_mul hTY hGS)
     (Nat.mul_le_mul hGY hTS)).trans_lt
   norm_num [prime]
 constructor
 · intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 0 htr
     prime G T hGirreducible
     (regularComponent_G_mem Omega G T H C)
     (regularComponent_T_mem Omega G T H C)
     hproper hGdegree hmixedY
 · intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     prime G T hGirreducible
     (regularComponent_G_mem Omega G T H C)
     (regularComponent_T_mem Omega G T H C)
     hproper hGdegree hmixedZ
theorem exists_adaptiveUnitProjectionFamily_of_literal_gates
   {G T H:MvPolynomial (Fin 3) Omega} {p q:FlagDegree}
   (hY:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (hGflag:PolynomialInFlag p G) (hTflag:PolynomialInFlag q T):
   ∃ base:∀ C:RegularComponent Omega G T H,
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base p q):=by
 have hbase:∀ C:RegularComponent Omega G T H,
     Nonempty (SeparableLiteralCoordinate C.1):=by
   intro C
   exact exists_separableLiteralCoordinate_of_YZ_gates C.1
     (regularComponent_ne_point Omega G T H C) (hY C) (hZ C)
 let base:∀ C:RegularComponent Omega G T H,
     SeparableLiteralCoordinate C.1:=fun C↦Classical.choice (hbase C)
 refine ⟨base,?_⟩
 exact exists_adaptiveUnitProjectionFamily_of_nested p q base hY hZ
   hSderiv hG hproper
   ((support_subset_flagSupport_iff p G).2 hGflag)
   ((support_subset_flagSupport_iff q T).2 hTflag)
theorem literalProjectionGates_of_fixedMeet_flags
   [CharP Omega prime]
   {G T H:MvPolynomial (Fin 3) Omega} {flag:FlagDegree} {d:ℕ}
   (hGirreducible:Irreducible G) (hproper:¬ G∣T)
   (hGflag:PolynomialInFlag flag G)
   (hTflag:PolynomialInFlag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag d) T)
   (hd:d ≤ 131071)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6):
   (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 0)∧
     (∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2):=by
 obtain ⟨hGY,hGS,hGZ⟩:=
   _root_.ProximityPrize.SubmissionLower.RCN314.degree_bounds_of_polynomialInFlag hGflag
 obtain ⟨hTY,hTS,hTZ⟩:=
   _root_.ProximityPrize.SubmissionLower.RCN314.degree_bounds_of_polynomialInFlag hTflag
 have hGY':G.degreeOf 0 ≤ 40:=
   hGY.trans (Nat.add_le_add hflagY hflagS)
 have hGS':G.degreeOf 1 ≤ 6:=hGS.trans hflagS
 have hGZ':G.degreeOf 2 ≤ 638:=
   hGZ.trans (Nat.add_le_add (Nat.add_le_add hflagZ hflagY) hflagS)
 have hTY':T.degreeOf 0 ≤ 1+67*131071:=by
   apply hTY.trans
   change (1+56*d)+11*d ≤ 1+67*131071
   exact (fixedMeet_cut_coordinate_caps hd).1
 have hTS':T.degreeOf 1 ≤ 11*131071:=by
   apply hTS.trans
   change 11*d ≤ 11*131071
   exact (fixedMeet_cut_coordinate_caps hd).2.1
 have hTZ':T.degreeOf 2 ≤ 1+1207*131071:=by
   apply hTZ.trans
   change 1140*d+(1+56*d)+11*d ≤ 1+1207*131071
   exact (fixedMeet_cut_coordinate_caps hd).2.2
 exact literalProjectionGates_of_fixedMeet_caps hGirreducible hproper
   hGY' hGS' hGZ' hTY' hTS' hTZ'
theorem fixedMeetTerminalAdaptiveProjection_at_cut_of_gates
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (D:S.TerminalDescendant) (i:Iota)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (hGflag:PolynomialInFlag flag D.stage.G)
   (hTflag:PolynomialInFlag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag D.degree)
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i)))
   (hY:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),LiteralProjectionGate C 2):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree)):=by
 exact exists_adaptiveUnitProjectionFamily_of_literal_gates
   (G:=D.stage.G)
   (T:=agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (H:=regularitySurface phi D.stage.F)
   (p:=flag)
   (q:=ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
     D.degree)
   hY hZ
   (residualStage_pderiv_one_ne_zero_of_support D.stage)
   D.stage.irreducible_G hproper
   hGflag hTflag
theorem fixedMeetTerminalAdaptiveProjection_at_cut
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6)
   (D:S.TerminalDescendant) (i:Iota)
   (hi:i∈D.stage.nodes)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i)):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
         D.degree)):=by
 classical
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let H:=regularitySurface phi D.stage.F
 change ¬ D.stage.G∣T at hproper
 change ∃ base:∀ C:RegularComponent Omega D.stage.G T H,
     SeparableLiteralCoordinate C.1,
   Nonempty (AdaptiveUnitProjectionFamily base flag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag
       D.degree))
 have hGflag:PolynomialInFlag flag D.stage.G:=D.stage.flag_support
 have hTflag:PolynomialInFlag
     (ResidualSupportParameters.fixedMeetSupport.residualAgreementFlag D.degree) T:=by
   exact (terminal_proper_cuts_in_residual_flag D.stage D.terminal i hi).2
 have hD:D.degree ≤ meetProfile.w:=
   D.degree_le.trans (Nat.le_refl meetProfile.w)
 change D.degree ≤ 131071 at hD
 obtain ⟨hY,hZ⟩:=literalProjectionGates_of_fixedMeet_flags
   D.stage.irreducible_G hproper hGflag hTflag hD hflagZ hflagY hflagS
 exact fixedMeetTerminalAdaptiveProjection_at_cut_of_gates S D i hproper
   hGflag hTflag hY hZ
theorem fixedMeetTerminalAdaptiveProjectionFamilies_of_rectangular_caps
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6):
   FixedMeetTerminalAdaptiveProjectionFamilies S:=by
 intro D i hi hproper
 exact fixedMeetTerminalAdaptiveProjection_at_cut S hflagZ hflagY hflagS
   D i hi hproper
end
end ProximityPrize.SubmissionLower.RCN315
end PackedLegacy_GO

/-! Packed from ProximityPrize.SubmissionLower.GP. -/
section PackedLegacy_GP
namespace ProximityPrize.SubmissionLower.RCN316
open scoped Classical
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN223 RCN238 RCN136 RCN243 RCN264 RCN095 RCN159 RCN158 RCN037 RCN038 RCN040 RCN041 RCN046 RCN265 RCN341 RCN277 RCN274 RCN275 RCN276 RCN315
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 30000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def TerminalAdaptiveProjectionFamiliesOfSupport
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (support.residualAgreementFlag D.degree))
def TerminalAdaptiveProjectionFamiliesYZOfSupport
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (support.residualAgreementFlag D.degree))
theorem terminalAdaptiveProjectionAtCutYZ_of_active_yz_gates
   {pchar e w:ℕ} [CharP Omega pchar]
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (D:S.TerminalDescendant) (i:Iota)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar)
   (hmixedZ:coordinateMixedDegree Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i)) 2 < pchar)
   (hGflag:PolynomialInFlag flag D.stage.G)
   (hTflag:PolynomialInFlag (support.residualAgreementFlag D.degree)
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (support.residualAgreementFlag D.degree)):=by
 classical
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let H:=regularitySurface phi D.stage.F
 let choiceData:∀ C:RegularComponent Omega D.stage.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C↦regularComponent_exists_separableLiteralCoordinate6630
     phi D.stage.F D.stage.G T pchar D.stage.G_dvd_surface
     D.stage.irreducible_G hproper D.stage.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega D.stage.G T H,
     SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega D.stage.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega D.stage.G T H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0)≠0∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Omega D.stage.G T H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar D.stage.G T D.stage.irreducible_G
     (regularComponent_G_mem Omega D.stage.G T H C)
     (regularComponent_T_mem Omega D.stage.G T H C)
     hproper hGdegree hmixedZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (support.residualAgreementFlag D.degree)
   base hactive hZ (residualStage_pderiv_one_ne_zero_of_support D.stage)
   D.stage.irreducible_G hproper
   ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
   ((support_subset_flagSupport_iff (support.residualAgreementFlag D.degree)
     T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
theorem terminalAdaptiveProjectionAtCut_of_active_yz_gates
   {pchar e w:ℕ} [CharP Omega pchar]
   {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (D:S.TerminalDescendant) (i:Iota)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar)
   (hmixedZ:coordinateMixedDegree Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i)) 2 < pchar)
   (hGflag:PolynomialInFlag flag D.stage.G)
   (hTflag:PolynomialInFlag (support.residualAgreementFlag D.degree)
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamily base flag
       (support.residualAgreementFlag D.degree)):=by
 obtain ⟨base,⟨P⟩⟩:=terminalAdaptiveProjectionAtCutYZ_of_active_yz_gates
   S D i hproper hGdegree hmixedZ hGflag hTflag
 exact ⟨base,⟨P.family⟩⟩
theorem terminalAdaptiveProjectionFamiliesYZOfSupport_of_active_yz_caps
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (surfaceY surfaceS surfaceZ cutY cutS:ℕ)
   (hflagY:flag.yz+flag.all ≤ surfaceY)
   (hflagS:flag.all ≤ surfaceS)
   (hflagZ:flag.zOnly+flag.yz+flag.all ≤ surfaceZ)
   (hcutY:1+w*(2*support.ys-1) ≤ cutY)
   (hcutS:(2*support.s-1)*w ≤ cutS)
   (hsurfaceChar:surfaceY < pchar∧surfaceS < pchar∧
     surfaceZ < pchar)
   (hmixedZ:cutY*surfaceS+surfaceY*cutS < pchar):
   TerminalAdaptiveProjectionFamiliesYZOfSupport support S:=by
 intro D i hi hproper
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 have hGflag:PolynomialInFlag flag D.stage.G:=D.stage.flag_support
 have hTflag:PolynomialInFlag (support.residualAgreementFlag D.degree) T:=
   (terminal_proper_cuts_in_residual_flag D.stage D.terminal i hi).2
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY,hTS,_hTZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hD:D.degree ≤ w:=D.degree_le.trans (Nat.le_refl w)
 have hGY':D.stage.G.degreeOf 0 ≤ surfaceY:=hGY.trans hflagY
 have hGS':D.stage.G.degreeOf 1 ≤ surfaceS:=hGS.trans hflagS
 have hGZ':D.stage.G.degreeOf 2 ≤ surfaceZ:=hGZ.trans hflagZ
 have hTY':T.degreeOf 0 ≤ cutY:=by
   calc
     T.degreeOf 0 ≤
         (support.residualAgreementFlag D.degree).yz+
           (support.residualAgreementFlag D.degree).all:=hTY
     _=1+D.degree*(2*support.ys-1):=
       support.residualAgreementFlag_ys D.degree
     _ ≤ 1+w*(2*support.ys-1):=
       Nat.add_le_add_left
         (Nat.mul_le_mul_right (2*support.ys-1) hD) 1
     _ ≤ cutY:=hcutY
 have hTS':T.degreeOf 1 ≤ cutS:=by
   calc
     T.degreeOf 1 ≤ (support.residualAgreementFlag D.degree).all:=hTS
     _=(2*support.s-1)*D.degree:=by
       simp only [ResidualSupportParameters.residualAgreementFlag,
         ResidualSupportParameters.agreementDirection]
     _ ≤ (2*support.s-1)*w:=
       Nat.mul_le_mul_left (2*support.s-1) hD
     _ ≤ cutS:=hcutS
 have hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY'.trans_lt hsurfaceChar.1
   · exact hGS'.trans_lt hsurfaceChar.2.1
   · exact hGZ'.trans_lt hsurfaceChar.2.2
 have hmixedZ':coordinateMixedDegree Omega D.stage.G T 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add
     (Nat.mul_le_mul hTY' hGS')
     (Nat.mul_le_mul hGY' hTS')).trans_lt hmixedZ
 exact terminalAdaptiveProjectionAtCutYZ_of_active_yz_gates S D i hproper
   hGdegree hmixedZ' hGflag hTflag
theorem terminalAdaptiveProjectionFamiliesOfSupport_of_active_yz_caps
   {pchar e w:ℕ} [CharP Omega pchar]
   {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (surfaceY surfaceS surfaceZ cutY cutS:ℕ)
   (hflagY:flag.yz+flag.all ≤ surfaceY)
   (hflagS:flag.all ≤ surfaceS)
   (hflagZ:flag.zOnly+flag.yz+flag.all ≤ surfaceZ)
   (hcutY:1+w*(2*support.ys-1) ≤ cutY)
   (hcutS:(2*support.s-1)*w ≤ cutS)
   (hsurfaceChar:surfaceY < pchar∧surfaceS < pchar∧
     surfaceZ < pchar)
   (hmixedZ:cutY*surfaceS+surfaceY*cutS < pchar):
   TerminalAdaptiveProjectionFamiliesOfSupport support S:=by
 intro D i hi hproper
 obtain ⟨base,⟨P⟩⟩:=
   terminalAdaptiveProjectionFamiliesYZOfSupport_of_active_yz_caps
     support S surfaceY surfaceS surfaceZ cutY cutS hflagY hflagS hflagZ
     hcutY hcutS hsurfaceChar hmixedZ D i hi hproper
 exact ⟨base,⟨P.family⟩⟩
theorem fixedMeetTerminalAdaptiveProjectionFamilies_of_active_yz
   [CharP Omega prime]
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime meetProfile.errors flag meetProfile.w
     ResidualSupportParameters.fixedMeetSupport)
   (hflagZ:flag.zOnly ≤ 598)
   (hflagY:flag.yz ≤ 34)
   (hflagS:flag.all ≤ 6):
   FixedMeetTerminalAdaptiveProjectionFamilies S:=by
 intro D i hi hproper
 apply (terminalAdaptiveProjectionFamiliesOfSupport_of_active_yz_caps
   ResidualSupportParameters.fixedMeetSupport S
   40 6 638 (1+67*131071) (11*131071)
   (by omega) hflagS (by omega)
   (by norm_num [meetProfile,ResidualSupportParameters.fixedMeetSupport])
   (by norm_num [meetProfile,ResidualSupportParameters.fixedMeetSupport])
   (by norm_num [prime]) (by norm_num [prime])) D i hi hproper
def frontierMeetSupport182688:ResidualSupportParameters where
 s:=7
 ys:=36
 total:=683
 one_le_s:=by norm_num
 s_le_ys:=by norm_num
 ys_le_total:=by norm_num
 two_le_ys:=by norm_num
theorem frontierMeet182688_parameters:
   26*182688=4749888∧(4749888-1)/131071=36∧
     frontierMeetSupport182688.agreementDirection=⟨1294,58,13⟩:=by
 norm_num [frontierMeetSupport182688,
   ResidualSupportParameters.agreementDirection]
theorem frontierMeet182688TerminalAdaptiveProjectionFamilies_of_active_yz
   [CharP Omega prime]
   {e:ℕ} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime e flag 131071
     frontierMeetSupport182688)
   (hflagZ:flag.zOnly ≤ 676)
   (hflagY:flag.yz ≤ 36)
   (hflagS:flag.all ≤ 7):
   TerminalAdaptiveProjectionFamiliesOfSupport frontierMeetSupport182688 S:=by
 apply terminalAdaptiveProjectionFamiliesOfSupport_of_active_yz_caps
   frontierMeetSupport182688 S
   43 7 719 (1+71*131071) (13*131071)
 · omega
 · exact hflagS
 · omega
 · norm_num [frontierMeetSupport182688]
 · norm_num [frontierMeetSupport182688]
 · norm_num [prime]
 · norm_num [prime]
theorem frontierMeet182688TerminalAdaptiveProjectionFamiliesYZ_of_active_yz
   [CharP Omega prime]
   {e:ℕ} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x prime e flag 131071
     frontierMeetSupport182688)
   (hflagZ:flag.zOnly ≤ 676)
   (hflagY:flag.yz ≤ 36)
   (hflagS:flag.all ≤ 7):
   TerminalAdaptiveProjectionFamiliesYZOfSupport frontierMeetSupport182688 S:=by
 apply terminalAdaptiveProjectionFamiliesYZOfSupport_of_active_yz_caps
   frontierMeetSupport182688 S
   43 7 719 (1+71*131071) (13*131071)
 · omega
 · exact hflagS
 · omega
 · norm_num [frontierMeetSupport182688]
 · norm_num [frontierMeetSupport182688]
 · norm_num [prime]
 · norm_num [prime]
end
end ProximityPrize.SubmissionLower.RCN316
end PackedLegacy_GP

/-! Packed from ProximityPrize.SubmissionLower.FR. -/
section PackedLegacy_FR
namespace ProximityPrize.SubmissionLower.RCN241
open scoped Classical
open RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN095 RCN159 RCN151 RCN148 RCN150 RCN156 RCN158 RCN154 RCN237 RCN234 RCN275 RCN276 RCN240 RCN046 RCN265 RCN316
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem terminal_outer_fiber_bound_of_prime_flag_budget_profile_z_yz
   (hphi:Function.Injective phi)
   (p:Profile) (support:ResidualSupportParameters)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar p.errors flag p.w support)
   (hnodes:S.nodes.card=p.n)
   (hagreement:∀ gamma∈Gamma,
     p.agreements ≤ (S.agreementFiber gamma).card)
   (hwa:p.w < p.agreements) (_han:p.agreements ≤ p.n)
   (hdegreeGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap*(p.w-k) ≤
       p.degreeIncidence*(p.agreements-k))
   (hunitGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap ≤ p.unitIncidence*(p.agreements-k))
   (D:S.TerminalDescendant) (i:Iota) (_hi:i∈D.stage.nodes)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (support.residualAgreementFlag D.degree))
   (hzyzPositive:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),1 ≤ B.zCost C+B.yzCost C):
   (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*p.gap ≤
     D.degree*factorDegreeCostYZ p support.agreementDirection flag+
       factorUnitCostYZ p support.agreementDirection flag:=by
 classical
 let GammaI:=Gamma.filter (fun gamma↦D.stage.Agrees gamma i)
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let aD:=p.agreements-(p.w-D.degree)
 have hTflag:PolynomialInFlag
     (support.residualAgreementFlag D.degree) T:=by
   exact surfaceMap_agreement_in_flag_of_support support
     D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
     D.stage.surface_total_weight D.degree
     (fun j↦(j.factorial:K)⁻¹)
     (x i) (D.stage.u0 i) (D.stage.u1 i)
 have hsub:GammaI ⊆ Gamma:=Finset.filter_subset _ _
 have hTpoint:∀ gamma∈GammaI,
     MvPolynomial.eval (selectedPoint phi D.stage.selected gamma) T=0:=by
   intro gamma hgamma
   obtain ⟨hGamma,hagree⟩:=Finset.mem_filter.mp hgamma
   exact (selected_agreement_zero_iff phi D.stage.F D.stage.selected
     pchar D.degree D.stage.characteristic_bound gamma
     (D.stage.degree_le gamma hGamma) (D.stage.solution gamma hGamma)
     (D.stage.regular gamma hGamma)
     (x i) (D.stage.u0 i) (D.stage.u1 i)).mpr hagree
 have hinnerAgreement:∀ gamma∈GammaI,
     aD ≤ (D.stage.nodes.filter (fun j↦
       (D.stage.selected gamma).eval (x j)=
         D.stage.u0 j+gamma*D.stage.u1 j)).card:=by
   intro gamma hgamma
   have hGamma:=hsub hgamma
   have h0:=Nat.sub_le_sub_right (hagreement gamma hGamma)
     (p.w-D.degree)
   exact h0.trans (by
     simpa only [aD,ResidualStage.agreementFiber,
       ResidualStage.Agrees] using D.agreement_card gamma hGamma)
 have hda:D.degree < aD:=by
   have hD:=D.degree_le
   dsimp only [aD]
   omega
 have hdegree:∀ k ≤ D.degree,
     (D.stage.nodes.card-k)*(aD-D.degree)*(D.degree-k) ≤
       p.degreeIncidence*(aD-k):=by
   intro k hk
   have hDle:D.degree ≤ p.w:=D.degree_le
   let total:=(p.w-D.degree)+k
   have htotal:total ≤ p.w:=by
     dsimp only [total]
     omega
   have h:=hdegreeGlobal total htotal
   have hnodesD:=D.nodes_card
   rw [hnodes] at hnodesD
   have hgap:aD-D.degree=p.gap:=by
     dsimp only [aD,Profile.gap]
     omega
   have hn:p.n-total=D.stage.nodes.card-k:=by
     rw [hnodesD]
     dsimp only [total]
     omega
   have hw:p.w-total=D.degree-k:=by
     dsimp only [total]
     omega
   have ha:p.agreements-total=aD-k:=by
     dsimp only [total,aD]
     omega
   rw [hgap]
   rw [hn,hw,ha] at h
   exact h
 have hunit:∀ k ≤ D.degree,
     (D.stage.nodes.card-k)*(aD-D.degree) ≤
       p.unitIncidence*(aD-k):=by
   intro k hk
   have hDle:D.degree ≤ p.w:=D.degree_le
   let total:=(p.w-D.degree)+k
   have htotal:total ≤ p.w:=by
     dsimp only [total]
     omega
   have h:=hunitGlobal total htotal
   have hnodesD:=D.nodes_card
   rw [hnodes] at hnodesD
   have hgap:aD-D.degree=p.gap:=by
     dsimp only [aD,Profile.gap]
     omega
   have hn:p.n-total=D.stage.nodes.card-k:=by
     rw [hnodesD]
     dsimp only [total]
     omega
   have ha:p.agreements-total=aD-k:=by
     dsimp only [total,aD]
     omega
   rw [hgap]
   rw [hn,ha] at h
   exact h
 have hbound:=
   proper_cut_seed_bound_of_recursive_prime_flag_budget_z_yz_of_direction
     hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
     x D.stage.u0 D.stage.u1 pchar p.errors D.degree aD
     p.degreeIncidence p.unitIncidence flag
     (support.residualAgreementFlag D.degree) support
     support.agreementDirection D.stage.G_dvd_surface D.stage.flag_support
     hTflag D.stage.surface_s_weight D.stage.surface_ys_weight
     D.stage.surface_total_weight D.stage.x_injective
     (fun gamma hgamma↦D.stage.degree_le gamma (hsub hgamma))
     (fun gamma hgamma↦D.stage.solution gamma (hsub hgamma))
     (fun gamma hgamma↦D.stage.regular gamma (hsub hgamma))
     (fun gamma hgamma↦D.stage.on_component gamma (hsub hgamma))
     hTpoint hinnerAgreement
     (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
       D.degree p.errors hsub D.stage.no_large_pencil)
     D.stage.characteristic_bound hda B
     (fun C t↦B.weightedCost_supportResidualAgreementFlag support C t)
     (by simpa only [T] using hzyzPositive) hdegree hunit
 have hgapEq:aD-D.degree=p.gap:=by
   have:=D.degree_le
   dsimp only [aD,Profile.gap]
   omega
 rw [hgapEq] at hbound
 rw [flagMixed_supportResidualAgreement_direction,
   flagMixed_supportResidualAgreement_unit,
   flagMixed_supportResidualAgreement_z] at hbound
 have hyz:=flagMixed_supportResidualAgreement_unit flag support D.degree
 dsimp only [GammaI] at hbound
 simp only [factorDegreeCostYZ,factorUnitCostYZ]
 calc
   _ ≤ _:=hbound
   _=_:=by ring
theorem recursive_scaled_factorYZ_of_adaptive_projection_families
   (hphi:Function.Injective phi)
   (p:Profile) (support:ResidualSupportParameters)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar p.errors flag p.w support)
   (hnodes:S.nodes.card=p.n)
   (hagreement:∀ gamma∈Gamma,
     p.agreements ≤ (S.agreementFiber gamma).card)
   (halign:support.agreementDirection=p.agreementDirection)
   (hwa:p.w < p.agreements) (han:p.agreements ≤ p.n)
   (hdegreeGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap*(p.w-k) ≤
       p.degreeIncidence*(p.agreements-k))
   (hunitGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap ≤ p.unitIncidence*(p.agreements-k))
   (hprojection:TerminalAdaptiveProjectionFamiliesYZOfSupport support S):
   Gamma.card*p.gap^2 ≤ factorRegularLedgerYZ p flag:=by
 change Gamma.card*p.gap^2 ≤
   factorRegularLedgerYZForDirection p p.agreementDirection flag
 rw [←halign]
 apply recursive_scaled_factorYZ hphi p support support.agreementDirection S
   hwa hagreement
 · intro D i hi hproper
   obtain ⟨base,⟨P⟩⟩:=hprojection D i hi hproper
   exact terminal_outer_fiber_bound_of_prime_flag_budget_profile_z_yz
     hphi p support S hnodes hagreement hwa han hdegreeGlobal hunitGlobal
     D i hi P.family.toPrimeFlagBudgetFamily
     (fun C↦P.one_le_zCost_add_yzCost phi D.stage.F rfl
       D.stage.G_dvd_surface C)
 · intro k hk
   simpa only [hnodes] using hdegreeGlobal k hk
 · intro k hk
   simpa only [hnodes] using hunitGlobal k hk
end
end ProximityPrize.SubmissionLower.RCN241
end PackedLegacy_FR

/-! Packed from ProximityPrize.SubmissionLower.P3. -/
section PackedLegacy_P3
namespace ProximityPrize.SubmissionLower.RCN288
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN065 RCN173 RCN095 RCN159 RCN151 RCN151.CurveResidualStage RCN152 RCN148 RCN150 RCN156 RCN158 RCN165 RCN154 RCN237 RCN234 RCN275 RCN276 RCN287 RCN240 RCN316 RCN216 RCN213 RCN272 RCN305 RCN046 RCN265 RCN037 RCN038 RCN040 RCN041 RCN341 RCN277 RCN274 RCN315
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar:ℕ} [CharP Omega pchar]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem recursive_curve_stratified_incidence_of_prime_flag_budget_for_cuts
   {e d a:ℕ} {surfaceFlag cutFlag:FlagDegree}
   {support:ResidualSupportParameters}
   (hphi:Function.Injective phi)
   (S:CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag d support)
   (cutAt:ℕ → FlagDegree) (cost:FlagDegree → ℕ)
   (B:PrimeFlagZeroBudget S.primeIdeal cost)
   (degreeCost unitCost U V zCharge:ℕ)
   (hcost:∀ t:ℕ,cost (cutAt t)=t*degreeCost+unitCost)
   (hcut:∀ D:S.TerminalDescendant,D.stage.identities=∅ →
     ∀ i∈D.stage.nodes,
       PolynomialInFlag (cutAt D.degree)
         (agreementPolynomial phi D.stage.F D.degree
           (x i) (D.stage.u0 i) (D.stage.u1 i)))
   (hda:d < a)
   (hagreement:∀ gamma∈Gamma,a ≤ (S.agreementFiber gamma).card)
   (hlarge:∀ D:S.TerminalDescendant,
     D.degree < D.stage.identities.card →
       Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
   (hdegree:∀ k ≤ d,
     (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
 classical
 let Inv:∀ n,CurveResidualStage phi Gamma x pchar e
     surfaceFlag cutFlag n support → Prop:=
   fun _ A↦PrimeFlagZeroBudget A.primeIdeal cost
 have htransport:∀ {n m}
     {A:CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag n support}
     {Anext:CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag m support},
     A.ResidualTransition Anext → Inv n A → Inv m Anext:=by
   intro n m A Anext htransition hbudget
   obtain ⟨aY,v,bY,aS,bS,cS,hv,_,_,hprime⟩:=htransition
   dsimp only [Inv] at hbudget ⊢
   rw [hprime]
   exact hbudget.mapResidual aY v bY aS bS cS hv
 obtain ⟨D,hDBudget⟩:=S.exists_terminal_descendant_with_invariant
   hphi Inv htransport B
 rcases D.terminal with hproper | hpencil
 · let k:=d-D.degree
   have hk:k ≤ d:=Nat.sub_le d D.degree
   have hDle:D.degree ≤ d:=D.degree_le
   have hdegreeEq:D.degree=d-k:=by
     dsimp only [k]
     omega
   have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
     simpa only [k] using D.nodes_card
   have hterminalAgreement:∀ gamma∈Gamma,
       a-k ≤ (D.stage.agreementFiber gamma).card:=by
     intro gamma hgamma
     exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
       (by simpa only [k] using D.agreement_card gamma hgamma)
   have hterminalFiber:∀ i∈D.stage.nodes,
       (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
         D.degree*degreeCost+unitCost:=by
     intro i hi
     have hflag:=hcut D hproper i hi
     have hzero:=hDBudget.zero_le (cutAt D.degree)
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       hflag (D.stage.proper_agreement_of_terminal hproper hi)
     rw [hcost D.degree] at hzero
     exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
       D.stage.F D.stage.selected Gamma pchar D.degree
       D.stage.characteristic_bound D.stage.degree_le D.stage.solution
       D.stage.regular D.stage.on_prime
       (x i) (D.stage.u0 i) (D.stage.u1 i)
       (D.degree*degreeCost+unitCost) hzero
   have hrawTerminal:=incidence_after_exempt_nodes
     (fun gamma i↦D.stage.Agrees gamma i)
     Gamma D.stage.nodes ∅ (a-k)
       (D.degree*degreeCost+unitCost)
     (by simp) hterminalAgreement (by
       intro i hi
       exact hterminalFiber i (by simpa using hi))
   have hraw:Gamma.card*(a-k) ≤
       (S.nodes.card-k)*((d-k)*degreeCost+unitCost):=by
     simpa only [Finset.card_empty,Nat.sub_zero,hnodeEq,hdegreeEq] using
       hrawTerminal
   have hmain:Gamma.card*(a-d) ≤ U*degreeCost+V*unitCost:=
     stratified_incidence_linear Gamma.card S.nodes.card a d k
       degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
   exact hmain.trans (Nat.le_add_right _ _)
 · have htail:=hlarge D hpencil.1
   exact htail.trans (Nat.le_add_left _ _)
theorem recursive_curve_stratified_incidence_of_sharp_prime_flag_budget
   {e d a:ℕ} {surfaceFlag cutFlag:FlagDegree}
   {support:ResidualSupportParameters}
   (hsy:support.s < support.ys)
   (hphi:Function.Injective phi)
   (S:CurveResidualStage phi Gamma x pchar e surfaceFlag cutFlag d support)
   (cost:FlagDegree → ℕ)
   (B:PrimeFlagZeroBudget S.primeIdeal cost)
   (degreeCost unitCost U V zCharge:ℕ)
   (hcost:∀ t:ℕ,
     cost (sharpResidualAgreementFlag support t)=
       t*degreeCost+unitCost)
   (hda:d < a)
   (hagreement:∀ gamma∈Gamma,a ≤ (S.agreementFiber gamma).card)
   (hlarge:∀ D:S.TerminalDescendant,
     D.degree < D.stage.identities.card →
       Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
   (hdegree:∀ k ≤ d,
     (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
 apply recursive_curve_stratified_incidence_of_prime_flag_budget_for_cuts
   hphi S (sharpResidualAgreementFlag support) cost B
   degreeCost unitCost U V zCharge hcost
 · intro D _hterminal i _hi
   exact surfaceMap_agreement_in_sharp_flag hsy (phi:=phi)
     ⟨D.stage.surface_s_weight,D.stage.surface_ys_weight,
       D.stage.surface_total_weight⟩
     D.degree (fun j:ℕ↦(j.factorial:K)⁻¹)
     (x i) (D.stage.u0 i) (D.stage.u1 i)
 · exact hda
 · exact hagreement
 · exact hlarge
 · exact hdegree
 · exact hunit
theorem weightedCost_sharpResidualAgreementFlag
   {G T H:MvPolynomial (Fin 3) Omega} {p q:FlagDegree}
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H) p q)
   (support:ResidualSupportParameters)
   (C:RegularComponent Omega G T H) (d:ℕ):
   B.weightedCost (sharpResidualAgreementFlag support d) C=
     d*B.weightedCost (sharpAgreementDirection support) C+
       B.weightedCost unitYZFlag C:=by
 simp only [sharpResidualAgreementFlag,sharpAgreementDirection,
   PrimeFlagBudgetFamily.weightedCost,unitYZFlag]
 ring
theorem flagMixed_sharpResidualAgreement_direction
   (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
   flagMixed p (sharpResidualAgreementFlag support d)
       (sharpAgreementDirection support)=
     d*flagMixed p (sharpAgreementDirection support)
         (sharpAgreementDirection support)+
       flagMixed p (sharpAgreementDirection support) unitYZFlag:=by
 simp [flagMixed,sharpResidualAgreementFlag,sharpAgreementDirection,
   unitYZFlag]
 ring
theorem flagMixed_sharpResidualAgreement_unit
   (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
   flagMixed p (sharpResidualAgreementFlag support d) unitYZFlag=
     d*flagMixed p (sharpAgreementDirection support) unitYZFlag+
       flagMixed p unitYZFlag unitYZFlag:=by
 simp [flagMixed,sharpResidualAgreementFlag,sharpAgreementDirection,
   unitYZFlag]
 ring
theorem flagMixed_sharpResidualAgreement_z
   (p:FlagDegree) (support:ResidualSupportParameters) (d:ℕ):
   flagMixed p (sharpResidualAgreementFlag support d) unitZFlag=
     d*flagMixed p (sharpAgreementDirection support) unitZFlag+
       flagMixed p unitYZFlag unitZFlag:=by
 simp [flagMixed,sharpResidualAgreementFlag,sharpAgreementDirection,
   unitYZFlag,unitZFlag]
 ring
theorem proper_cut_seed_bound_of_recursive_prime_flag_budget_sharp_z_yz
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G T:MvPolynomial (Fin 3) Omega)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (p e d a U V:ℕ) [CharP Omega p]
   (surfaceFlag:FlagDegree)
   (support:ResidualSupportParameters)
   (hsy:support.s < support.ys)
   (hdiv:G∣surfaceMap phi F)
   (hGflag:PolynomialInFlag surfaceFlag G)
   (hTflag:PolynomialInFlag (sharpResidualAgreementFlag support d) T)
   (hFs:wt residualSWeights F ≤ support.s)
   (hFys:wt residualYSWeights F ≤ support.ys)
   (hFtotal:wt residualTotalWeights F ≤ support.total)
   (hinj:Set.InjOn x nodes)
   (hdegreeSelected:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ d)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma F=0)
   (hregular:∀ gamma∈Gamma,
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) (selected gamma) gamma
         (phi Polynomial.X))
       (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) G=0)
   (hTpoint:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) T=0)
   (hagreement:∀ gamma∈Gamma,
     a ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma d e)
   (hchar:d < p) (hda:d < a)
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T)
     (H:=regularitySurface phi F) surfaceFlag
     (sharpResidualAgreementFlag support d))
   (hzyzPositive:∀ C:RegularComponent Omega G T
     (regularitySurface phi F),1 ≤ B.zCost C+B.yzCost C)
   (hdegree:∀ k ≤ d,
     (nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
   (hunit:∀ k ≤ d,
     (nodes.card-k)*(a-d) ≤ V*(a-k)):
   Gamma.card*(a-d) ≤
     U*flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
         (sharpAgreementDirection support)+
       V*flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
         unitYZFlag+
       (e+1)*(a-d)*
         (flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
             unitZFlag+
           flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
             unitYZFlag):=by
 classical
 let H:=regularitySurface phi F
 have hHp:∀ gamma∈Gamma,
     MvPolynomial.eval (selectedPoint phi selected gamma) H≠0:=by
   intro gamma hgamma
   change MvPolynomial.eval (selectedPoint phi selected gamma)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [selectedPoint_evaluation]
   exact hregular gamma hgamma
 let degreeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost (sharpAgreementDirection support) C
 let unitCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.weightedCost unitYZFlag C
 let largeCost:RegularComponent Omega G T H → ℕ:=
   fun C↦B.zCost C+B.yzCost C
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma
         (selectedPoint phi selected) C).card*(a-d) ≤
       U*degreeCost C+V*unitCost C+
         (e+1)*(a-d)*largeCost C:=by
   intro C
   let GammaC:=componentSeeds Omega G T H Gamma
     (selectedPoint phi selected) C
   let S:=regularComponentCurveStageOfSupport support F G T selected Gamma
     nodes x u0 u1 p e d surfaceFlag
     (sharpResidualAgreementFlag support d) hdiv hGflag hTflag
     hFs hFys hFtotal hinj hdegreeSelected hsolution hregular hnoPencil hchar C
   have hsub:GammaC ⊆ Gamma:=componentSeeds_subset Omega G T H Gamma
     (selectedPoint phi selected) C
   apply recursive_curve_stratified_incidence_of_sharp_prime_flag_budget
     hsy hphi S (fun r↦B.weightedCost r C) (B.primeBudget C)
     (degreeCost C) (unitCost C) U V (largeCost C)
   · intro t
     simpa only [degreeCost,unitCost] using
       weightedCost_sharpResidualAgreementFlag B support C t
   · exact hda
   · intro gamma hgamma
     exact hagreement gamma (hsub hgamma)
   · intro D hmany
     have hcard:GammaC.card ≤ e+1:=
       D.stage.card_le_pencil_of_many_identities hmany
     have hscaled:GammaC.card*(a-d) ≤ (e+1)*(a-d):=
       Nat.mul_le_mul_right (a-d) hcard
     have hcharged:(e+1)*(a-d) ≤
         (e+1)*(a-d)*largeCost C:=by
       have hmul:=Nat.mul_le_mul_left ((e+1)*(a-d))
         (hzyzPositive C)
       simpa only [largeCost,Nat.mul_one] using hmul
     exact hscaled.trans hcharged
   · simpa only [S,regularComponentCurveStageOfSupport] using hdegree
   · simpa only [S,regularComponentCurveStageOfSupport] using hunit
 have hlargeSum:(∑ C:RegularComponent Omega G T H,largeCost C) ≤
     flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitZFlag+
       flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
         unitYZFlag:=by
   calc
     (∑ C:RegularComponent Omega G T H,largeCost C)=
         (∑ C:RegularComponent Omega G T H,B.zCost C)+
           ∑ C:RegularComponent Omega G T H,B.yzCost C:=by
       simp only [largeCost,Finset.sum_add_distrib]
     _ ≤ _:=Nat.add_le_add B.sum_zCost_le B.sum_yzCost_le
 exact aggregate_component_stratified_incidence G T H Gamma
   (selectedPoint phi selected) hGpoint hTpoint hHp (a-d) U V (e+1)
   (flagMixed surfaceFlag (sharpResidualAgreementFlag support d)
     (sharpAgreementDirection support))
   (flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitYZFlag)
   (flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitZFlag+
     flagMixed surfaceFlag (sharpResidualAgreementFlag support d) unitYZFlag)
   degreeCost unitCost largeCost hcomponent
   (by simpa only [degreeCost] using
     B.sum_weightedCost_le (sharpAgreementDirection support))
   (by simpa only [unitCost] using B.sum_weightedCost_le unitYZFlag)
   hlargeSum
def TerminalAdaptiveProjectionFamiliesSharpYZ
   {e w:ℕ} {flag:FlagDegree}
   (support:ResidualSupportParameters)
   (S:ResidualStage phi Gamma x pchar e flag w support):Prop:=
 ∀ (D:S.TerminalDescendant) (i:Iota),
   i∈D.stage.nodes →
   ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i) →
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag support D.degree))
theorem terminalAdaptiveProjectionAtSharpCutYZ_of_active_yz_gates
   {e w:ℕ} {support:ResidualSupportParameters} {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (D:S.TerminalDescendant) (i:Iota)
   (hproper:¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
     (x i) (D.stage.u0 i) (D.stage.u1 i))
   (hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar)
   (hmixedZ:coordinateMixedDegree Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i)) 2 < pchar)
   (hGflag:PolynomialInFlag flag D.stage.G)
   (hTflag:PolynomialInFlag (sharpResidualAgreementFlag support D.degree)
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))):
   ∃ base:∀ C:RegularComponent Omega D.stage.G
       (agreementPolynomial phi D.stage.F D.degree
         (x i) (D.stage.u0 i) (D.stage.u1 i))
       (regularitySurface phi D.stage.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag support D.degree)):=by
 classical
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let H:=regularitySurface phi D.stage.F
 let choiceData:∀ C:RegularComponent Omega D.stage.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C↦regularComponent_exists_separableLiteralCoordinate6630
     phi D.stage.F D.stage.G T pchar D.stage.G_dvd_surface
     D.stage.irreducible_G hproper D.stage.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega D.stage.G T H,
     SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega D.stage.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega D.stage.G T H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0)≠0∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Omega D.stage.G T H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar D.stage.G T D.stage.irreducible_G
     (regularComponent_G_mem Omega D.stage.G T H C)
     (regularComponent_T_mem Omega D.stage.G T H C)
     hproper hGdegree hmixedZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag support D.degree)
   base hactive hZ (residualStage_pderiv_one_ne_zero_of_support D.stage)
   D.stage.irreducible_G hproper
   ((support_subset_flagSupport_iff flag D.stage.G).2 hGflag)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag support D.degree) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
theorem terminalAdaptiveProjectionFamiliesSharpYZ_of_active_yz_caps
   {e w:ℕ} {flag:FlagDegree}
   (support:ResidualSupportParameters) (hsy:support.s < support.ys)
   (S:ResidualStage phi Gamma x pchar e flag w support)
   (surfaceY surfaceS surfaceZ cutY cutS:ℕ)
   (hflagY:flag.yz+flag.all ≤ surfaceY)
   (hflagS:flag.all ≤ surfaceS)
   (hflagZ:flag.zOnly+flag.yz+flag.all ≤ surfaceZ)
   (hcutY:1+w*(2*support.ys-2) ≤ cutY)
   (hcutS:(2*support.s-1)*w ≤ cutS)
   (hsurfaceChar:surfaceY < pchar∧surfaceS < pchar∧
     surfaceZ < pchar)
   (hmixedZ:cutY*surfaceS+surfaceY*cutS < pchar):
   TerminalAdaptiveProjectionFamiliesSharpYZ support S:=by
 intro D i _hi hproper
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 have hGflag:PolynomialInFlag flag D.stage.G:=D.stage.flag_support
 have hTflag:PolynomialInFlag
     (sharpResidualAgreementFlag support D.degree) T:=
   surfaceMap_agreement_in_sharp_flag hsy (phi:=phi)
     ⟨D.stage.surface_s_weight,D.stage.surface_ys_weight,
       D.stage.surface_total_weight⟩
     D.degree (fun j:ℕ↦(j.factorial:K)⁻¹)
     (x i) (D.stage.u0 i) (D.stage.u1 i)
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY,hTS,_hTZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hD:D.degree ≤ w:=D.degree_le
 have hGY':D.stage.G.degreeOf 0 ≤ surfaceY:=hGY.trans hflagY
 have hGS':D.stage.G.degreeOf 1 ≤ surfaceS:=hGS.trans hflagS
 have hGZ':D.stage.G.degreeOf 2 ≤ surfaceZ:=hGZ.trans hflagZ
 have hTY':T.degreeOf 0 ≤ cutY:=by
   calc
     T.degreeOf 0 ≤
         (sharpResidualAgreementFlag support D.degree).yz+
           (sharpResidualAgreementFlag support D.degree).all:=hTY
     _=1+D.degree*(2*support.ys-2):=
       sharpResidualAgreementFlag_ys support hsy D.degree
     _ ≤ 1+w*(2*support.ys-2):=
       Nat.add_le_add_left
         (Nat.mul_le_mul_right (2*support.ys-2) hD) 1
     _ ≤ cutY:=hcutY
 have hTS':T.degreeOf 1 ≤ cutS:=by
   calc
     T.degreeOf 1 ≤ (sharpResidualAgreementFlag support D.degree).all:=hTS
     _=(2*support.s-1)*D.degree:=by
       simp only [sharpResidualAgreementFlag,sharpAgreementDirection]
     _ ≤ (2*support.s-1)*w:=
       Nat.mul_le_mul_left (2*support.s-1) hD
     _ ≤ cutS:=hcutS
 have hGdegree:∀ j:Fin 3,D.stage.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY'.trans_lt hsurfaceChar.1
   · exact hGS'.trans_lt hsurfaceChar.2.1
   · exact hGZ'.trans_lt hsurfaceChar.2.2
 have hmixedZ':coordinateMixedDegree Omega D.stage.G T 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add
     (Nat.mul_le_mul hTY' hGS')
     (Nat.mul_le_mul hGY' hTS')).trans_lt hmixedZ
 exact terminalAdaptiveProjectionAtSharpCutYZ_of_active_yz_gates
   S D i hproper hGdegree hmixedZ' hGflag hTflag
theorem terminal_outer_fiber_bound_of_prime_flag_budget_profile_sharp_z_yz
   (hphi:Function.Injective phi)
   (p:Profile) (support:ResidualSupportParameters)
   (hsy:support.s < support.ys)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar p.errors flag p.w support)
   (hnodes:S.nodes.card=p.n)
   (hagreement:∀ gamma∈Gamma,
     p.agreements ≤ (S.agreementFiber gamma).card)
   (hwa:p.w < p.agreements) (_han:p.agreements ≤ p.n)
   (hdegreeGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap*(p.w-k) ≤
       p.degreeIncidence*(p.agreements-k))
   (hunitGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap ≤ p.unitIncidence*(p.agreements-k))
   (D:S.TerminalDescendant) (i:Iota) (_hi:i∈D.stage.nodes)
   (B:PrimeFlagBudgetFamily
     (G:=D.stage.G)
     (T:=agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (H:=regularitySurface phi D.stage.F)
     flag (sharpResidualAgreementFlag support D.degree))
   (hzyzPositive:∀ C:RegularComponent Omega D.stage.G
     (agreementPolynomial phi D.stage.F D.degree
       (x i) (D.stage.u0 i) (D.stage.u1 i))
     (regularitySurface phi D.stage.F),1 ≤ B.zCost C+B.yzCost C):
   (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*p.gap ≤
     D.degree*factorDegreeCostYZ p (sharpAgreementDirection support) flag+
       factorUnitCostYZ p (sharpAgreementDirection support) flag:=by
 classical
 let GammaI:=Gamma.filter (fun gamma↦D.stage.Agrees gamma i)
 let T:=agreementPolynomial phi D.stage.F D.degree
   (x i) (D.stage.u0 i) (D.stage.u1 i)
 let aD:=p.agreements-(p.w-D.degree)
 have hTflag:PolynomialInFlag
     (sharpResidualAgreementFlag support D.degree) T:=by
   exact surfaceMap_agreement_in_sharp_flag hsy (phi:=phi)
     ⟨D.stage.surface_s_weight,D.stage.surface_ys_weight,
       D.stage.surface_total_weight⟩
     D.degree (fun j:ℕ↦(j.factorial:K)⁻¹)
     (x i) (D.stage.u0 i) (D.stage.u1 i)
 have hsub:GammaI ⊆ Gamma:=Finset.filter_subset _ _
 have hTpoint:∀ gamma∈GammaI,
     MvPolynomial.eval (selectedPoint phi D.stage.selected gamma) T=0:=by
   intro gamma hgamma
   obtain ⟨hGamma,hagree⟩:=Finset.mem_filter.mp hgamma
   exact (selected_agreement_zero_iff phi D.stage.F D.stage.selected
     pchar D.degree D.stage.characteristic_bound gamma
     (D.stage.degree_le gamma hGamma) (D.stage.solution gamma hGamma)
     (D.stage.regular gamma hGamma)
     (x i) (D.stage.u0 i) (D.stage.u1 i)).mpr hagree
 have hinnerAgreement:∀ gamma∈GammaI,
     aD ≤ (D.stage.nodes.filter (fun j↦
       (D.stage.selected gamma).eval (x j)=
         D.stage.u0 j+gamma*D.stage.u1 j)).card:=by
   intro gamma hgamma
   have hGamma:=hsub hgamma
   have h0:=Nat.sub_le_sub_right (hagreement gamma hGamma)
     (p.w-D.degree)
   exact h0.trans (by
     simpa only [aD,ResidualStage.agreementFiber,
       ResidualStage.Agrees] using D.agreement_card gamma hGamma)
 have hda:D.degree < aD:=by
   have hD:=D.degree_le
   dsimp only [aD]
   omega
 have hdegree:∀ k ≤ D.degree,
     (D.stage.nodes.card-k)*(aD-D.degree)*(D.degree-k) ≤
       p.degreeIncidence*(aD-k):=by
   intro k hk
   have hDle:D.degree ≤ p.w:=D.degree_le
   let total:=(p.w-D.degree)+k
   have htotal:total ≤ p.w:=by
     dsimp only [total]
     omega
   have h:=hdegreeGlobal total htotal
   have hnodesD:=D.nodes_card
   rw [hnodes] at hnodesD
   have hgap:aD-D.degree=p.gap:=by
     dsimp only [aD,Profile.gap]
     omega
   have hn:p.n-total=D.stage.nodes.card-k:=by
     rw [hnodesD]
     dsimp only [total]
     omega
   have hw:p.w-total=D.degree-k:=by
     dsimp only [total]
     omega
   have ha:p.agreements-total=aD-k:=by
     dsimp only [total,aD]
     omega
   rw [hgap]
   rw [hn,hw,ha] at h
   exact h
 have hunit:∀ k ≤ D.degree,
     (D.stage.nodes.card-k)*(aD-D.degree) ≤
       p.unitIncidence*(aD-k):=by
   intro k hk
   have hDle:D.degree ≤ p.w:=D.degree_le
   let total:=(p.w-D.degree)+k
   have htotal:total ≤ p.w:=by
     dsimp only [total]
     omega
   have h:=hunitGlobal total htotal
   have hnodesD:=D.nodes_card
   rw [hnodes] at hnodesD
   have hgap:aD-D.degree=p.gap:=by
     dsimp only [aD,Profile.gap]
     omega
   have hn:p.n-total=D.stage.nodes.card-k:=by
     rw [hnodesD]
     dsimp only [total]
     omega
   have ha:p.agreements-total=aD-k:=by
     dsimp only [total,aD]
     omega
   rw [hgap]
   rw [hn,ha] at h
   exact h
 have hbound:=
   proper_cut_seed_bound_of_recursive_prime_flag_budget_sharp_z_yz
     hphi D.stage.F D.stage.G T D.stage.selected GammaI D.stage.nodes
     x D.stage.u0 D.stage.u1 pchar p.errors D.degree aD
     p.degreeIncidence p.unitIncidence flag support hsy
     D.stage.G_dvd_surface D.stage.flag_support hTflag
     D.stage.surface_s_weight D.stage.surface_ys_weight
     D.stage.surface_total_weight D.stage.x_injective
     (fun gamma hgamma↦D.stage.degree_le gamma (hsub hgamma))
     (fun gamma hgamma↦D.stage.solution gamma (hsub hgamma))
     (fun gamma hgamma↦D.stage.regular gamma (hsub hgamma))
     (fun gamma hgamma↦D.stage.on_component gamma (hsub hgamma))
     hTpoint hinnerAgreement
     (noLargeSelectedPencil_mono D.stage.selected Gamma GammaI
       D.degree p.errors hsub D.stage.no_large_pencil)
     D.stage.characteristic_bound hda B (by simpa only [T] using hzyzPositive)
     hdegree hunit
 have hgapEq:aD-D.degree=p.gap:=by
   have:=D.degree_le
   dsimp only [aD,Profile.gap]
   omega
 rw [hgapEq] at hbound
 rw [flagMixed_sharpResidualAgreement_direction,
   flagMixed_sharpResidualAgreement_unit,
   flagMixed_sharpResidualAgreement_z] at hbound
 simp only [factorDegreeCostYZ,factorUnitCostYZ]
 calc
   _ ≤ _:=hbound
   _=_:=by ring
theorem recursive_scaled_factorSharpYZ_of_adaptive_projection_families
   (hphi:Function.Injective phi)
   (p:Profile) (support:ResidualSupportParameters)
   (hsy:support.s < support.ys)
   {flag:FlagDegree}
   (S:ResidualStage phi Gamma x pchar p.errors flag p.w support)
   (hnodes:S.nodes.card=p.n)
   (hagreement:∀ gamma∈Gamma,
     p.agreements ≤ (S.agreementFiber gamma).card)
   (hwa:p.w < p.agreements) (han:p.agreements ≤ p.n)
   (hdegreeGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap*(p.w-k) ≤
       p.degreeIncidence*(p.agreements-k))
   (hunitGlobal:∀ k ≤ p.w,
     (p.n-k)*p.gap ≤ p.unitIncidence*(p.agreements-k))
   (hprojection:TerminalAdaptiveProjectionFamiliesSharpYZ support S):
   Gamma.card*p.gap^2 ≤
     factorRegularLedgerYZForDirection p
       (sharpAgreementDirection support) flag:=by
 apply recursive_scaled_factorYZ hphi p support
   (sharpAgreementDirection support) S hwa hagreement
 · intro D i hi hproper
   obtain ⟨base,⟨P⟩⟩:=hprojection D i hi hproper
   exact terminal_outer_fiber_bound_of_prime_flag_budget_profile_sharp_z_yz
     hphi p support hsy S hnodes hagreement hwa han
     hdegreeGlobal hunitGlobal D i hi P.family.toPrimeFlagBudgetFamily
     (fun C↦P.one_le_zCost_add_yzCost phi D.stage.F rfl
       D.stage.G_dvd_surface C)
 · intro k hk
   simpa only [hnodes] using hdegreeGlobal k hk
 · intro k hk
   simpa only [hnodes] using hunitGlobal k hk
end
end ProximityPrize.SubmissionLower.RCN288
end PackedLegacy_P3

/-! Packed from ProximityPrize.SubmissionLower.B6. -/
section PackedLegacy_B6
namespace ProximityPrize.SubmissionLower.RCN088
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN086
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem firstTail_in_sharp_flag
   (S:ResidualStage phi Gamma x pchar e flag w
     (RCN198.support a b s)):
   PolynomialInFlag
     (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))
     (globalTailCut phi S.F (w+1)):=by
 let Hsupport:ResidualSupportData
     (RCN198.support a b s) S.F:=
   ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
 exact globalTailCut_in_sharp_flag phi a b s S.F
   Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight Hsupport.total_weight (w+1)
theorem exists_firstTail_projection
   (S:ResidualStage phi Gamma x pchar e flag w
     (RCN198.support a b s))
   (hproper:¬ S.G∣globalTailCut phi S.F (w+1))
   (hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar)
   (hmixedZ:coordinateMixedDegree Omega S.G (globalTailCut phi S.F (w+1)) 2 < pchar):
   ∃ base:∀ C:RegularComponent Omega S.G
       (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))):=by
 classical
 let T:=globalTailCut phi S.F (w+1)
 let H:=regularitySurface phi S.F
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 have hTflag:=firstTail_in_sharp_flag S
 let choiceData:∀ C:RegularComponent Omega S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C↦regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G T pchar S.G_dvd_surface
     S.irreducible_G hproper S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G T H,
     SeparableLiteralCoordinate C.1:=fun C↦(choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G T H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0)≠0∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Omega S.G T H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G T S.irreducible_G
     (regularComponent_G_mem Omega S.G T H C)
     (regularComponent_T_mem Omega S.G T H C)
     hproper hGdegree hmixedZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))
   base hactive hZ (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 hGflag)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (RCN198.support a b s) (w+1)) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
theorem exists_firstTail_projection_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w
     (RCN198.support a b s))
   (hproper:¬ S.G∣globalTailCut phi S.F (w+1))
   (hflagChar:flag.yz+flag.all < pchar∧flag.all < pchar∧
     flag.zOnly+flag.yz+flag.all < pchar)
   (hmixed:(1+(w+1)*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*(w+1)) < pchar):
   ∃ base:∀ C:RegularComponent Omega S.G
       (globalTailCut phi S.F (w+1)) (regularitySurface phi S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (RCN198.support a b s) (w+1))):=by
 let T:=globalTailCut phi S.F (w+1)
 let supp:=RCN198.support a b s
 have hsy:supp.s < supp.ys:=by
   change s+2 < b+s+3
   omega
 have hTflag:PolynomialInFlag (sharpResidualAgreementFlag supp (w+1)) T:=
   firstTail_in_sharp_flag S
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag S.flag_support
 obtain ⟨hTY,hTS,_⟩:=
   RCN314.degree_bounds_of_polynomialInFlag hTflag
 have hTY':T.degreeOf 0 ≤ 1+(w+1)*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact sharpResidualAgreementFlag_ys supp hsy (w+1)
 have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*(w+1):=by
   apply hTS.trans_eq
   simp only [sharpResidualAgreementFlag,sharpAgreementDirection,supp,
     RCN198.support]
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixZ:coordinateMixedDegree Omega S.G T 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 exact exists_firstTail_projection S hproper hGdegree hmixZ
end
end ProximityPrize.SubmissionLower.RCN088
end PackedLegacy_B6

/-! Packed from ProximityPrize.SubmissionLower.B7. -/
section PackedLegacy_B7
namespace ProximityPrize.SubmissionLower.RCN089
open RCN136 RCN313 RCN238 RCN275 RCN095 RCN198 RCN086 RCN262 RCN263
noncomputable section
variable {K Omega:Type} [Field K] [Field Omega]
def reducedGlobalTailCut (phi:Polynomial K →+* Omega)
   (support:ResidualSupportParameters) (F:MvPolynomial (Fin 4) K)
   (d:ℕ):MvPolynomial (Fin 3) Omega :=
 surfaceMap phi
   (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
theorem globalTailCut_sub_reduced_dvd
   (phi:Polynomial K →+* Omega) (support:ResidualSupportParameters)
   (F:MvPolynomial (Fin 4) K) (d:ℕ) :
   surfaceMap phi F ∣ globalTailCut phi F d -
     reducedGlobalTailCut phi support F d:=by
 change surfaceMap phi F ∣
   surfaceMap phi (agreementNumerator F d (tailSelector d) 0 0 0) -
     surfaceMap phi
       (reducedAgreementNumerator F support.s d (tailSelector d) 0 0 0)
 rw [← map_sub]
 exact map_dvd (surfaceMap phi)
   (agreementNumerator_sub_reduced_dvd F support.s d
     (tailSelector d) 0 0 0)
theorem reducedGlobalTailCut_in_flag
   (phi:Polynomial K →+* Omega) (support:ResidualSupportParameters)
   {F:MvPolynomial (Fin 4) K} (H:ResidualSupportData support F)
   (d:ℕ) :
   PolynomialInFlag (reducedResidualAgreementFlag support d)
     (reducedGlobalTailCut phi support F d):=by
 exact surfaceMap_reducedAgreement_in_flag phi support H d
   (tailSelector d) 0 0 0
end
end ProximityPrize.SubmissionLower.RCN089
end PackedLegacy_B7

/-! Packed from ProximityPrize.SubmissionLower.J5. -/
section PackedLegacy_J5
namespace ProximityPrize.SubmissionLower.RCN090
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN040 RCN041 RCN265 RCN274 RCN198 RCN086 RCN263 RCN089
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+* Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar e w a b s:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem exists_reduced_firstTail_projection_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
   ∃ base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (reducedResidualAgreementFlag (support a b s) (w + 1))):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans
     (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T,Tred,sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY,hGS,hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY,hTS,_hTZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hTY':Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2):=by
   apply hTY.trans_eq
   exact reducedResidualAgreementFlag_ys supp (w + 1)
 have hTS':Tred.degreeOf 1 ≤ (2 * (s + 2) - 2) * (w + 1):=by
   apply hTS.trans_eq
   rfl
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixedZ:coordinateMixedDegree Omega S.G Tred 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index = 0 ∨ B.index = 2 :=
   fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G Tred pchar S.G_dvd_surface S.irreducible_G hproperRed
     S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Omega S.G Tred H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G Tred S.irreducible_G
     (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C)
     hproperRed hGdegree hmixedZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (reducedResidualAgreementFlag supp (w + 1)) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproperRed
   ((support_subset_flagSupport_iff flag S.G).2 hGflag)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag supp (w + 1)) Tred).2 hTflag)
 exact ⟨base,⟨P⟩⟩
theorem exists_reduced_firstTail_activeNestedData_of_caps
   (S:ResidualStage phi Gamma x pchar e flag w (support a b s))
   (hproper:¬ S.G ∣ globalTailCut phi S.F (w + 1))
   (hflagChar:flag.yz + flag.all < pchar ∧ flag.all < pchar ∧
     flag.zOnly + flag.yz + flag.all < pchar)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < pchar) :
   ∃ (base:∀ C:RegularComponent Omega S.G
       (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
       (regularitySurface phi S.F), SeparableLiteralCoordinate C.1),
     ∃ (hactive:∀ C:RegularComponent Omega S.G
         (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
         (regularitySurface phi S.F),
         KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 0) ≠ 0 ∨
           KaehlerDifferential.D Omega (CoordinateField Omega C.1)
             (coordinate Omega C.1 2) ≠ 0),
       ∃ (hZ:∀ C:RegularComponent Omega S.G
           (reducedGlobalTailCut phi (support a b s) S.F (w + 1))
           (regularitySurface phi S.F), LiteralProjectionGate C 2),
         Nonempty (AdaptiveNestedProjectionDataActive base hactive
           (RCN315.residualStage_pderiv_one_ne_zero_of_support S)):=by
 classical
 let supp:=support a b s
 let T:=globalTailCut phi S.F (w + 1)
 let Tred:=reducedGlobalTailCut phi supp S.F (w + 1)
 let H:=regularitySurface phi S.F
 have hd:S.G ∣ T - Tred :=
   S.G_dvd_surface.trans (globalTailCut_sub_reduced_dvd phi supp S.F (w + 1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hproper
   have:=hd.add hr
   simpa only [T, Tred, sub_add_cancel] using this
 have hGflag:PolynomialInFlag flag S.G:=S.flag_support
 let Hsupport:ResidualSupportData supp S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hTflag:PolynomialInFlag
     (reducedResidualAgreementFlag supp (w + 1)) Tred :=
   reducedGlobalTailCut_in_flag phi supp Hsupport (w + 1)
 obtain ⟨hGY, hGS, hGZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hGflag
 obtain ⟨hTY, hTS, _hTZ⟩ :=
   RCN314.degree_bounds_of_polynomialInFlag
     hTflag
 have hTY':Tred.degreeOf 0 ≤ 1 + (w + 1) * (2 * (b + s + 3) - 2):=by
   apply hTY.trans_eq
   exact reducedResidualAgreementFlag_ys supp (w + 1)
 have hTS':Tred.degreeOf 1 ≤ (2 * (s + 2) - 2) * (w + 1):=by
   apply hTS.trans_eq
   rfl
 have hGdegree:∀ j:Fin 3, S.G.degreeOf j < pchar:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixedZ:coordinateMixedDegree Omega S.G Tred 2 < pchar:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Omega S.G Tred H,
     ∃ B:SeparableLiteralCoordinate C.1, B.index = 0 ∨ B.index = 2 :=
   fun C ↦ regularComponent_exists_separableLiteralCoordinate6630
     phi S.F S.G Tred pchar S.G_dvd_surface S.irreducible_G hproperRed
     S.y_dependent hGdegree hmixedZ C
 let base:∀ C:RegularComponent Omega S.G Tred H,
     SeparableLiteralCoordinate C.1:=fun C ↦ (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Omega S.G Tred H,
     (base C).index = 0 ∨ (base C).index = 2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Omega S.G Tred H,
     KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 0) ≠ 0 ∨
       KaehlerDifferential.D Omega (CoordinateField Omega C.1)
         (coordinate Omega C.1 2) ≠ 0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left
     simpa only [hidx] using hb
   · right
     simpa only [hidx] using hb
 have hZ:∀ C:RegularComponent Omega S.G Tred H,
     LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Omega C.1 2 htr
     pchar S.G Tred S.irreducible_G
     (regularComponent_G_mem Omega S.G Tred H C)
     (regularComponent_T_mem Omega S.G Tred H C)
     hproperRed hGdegree hmixedZ
 exact ⟨base, hactive, hZ,
   exists_adaptiveNestedProjectionDataActive base hactive
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S)⟩
end
end ProximityPrize.SubmissionLower.RCN090
end PackedLegacy_J5

/-! Packed from ProximityPrize.SubmissionLower.CK. -/
section PackedLegacy_CK
namespace ProximityPrize.SubmissionLower.RCN337
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
variable {K:Type} [Field K] [DecidableEq K]
theorem sum_pairwise_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqMonic:∀ i,(q i).Monic)
   (hqCoprime:Pairwise fun i j↦IsCoprime (q i) (q j))
   (hpow:∀ i,q i^multiplicity i∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 classical
 have hpowersCoprime:Pairwise fun i j↦
     IsCoprime ((q i)^multiplicity i) ((q j)^multiplicity j):=by
   intro i j hij
   exact (hqCoprime hij).pow
 have hprodDvd:(∏ i,(q i)^multiplicity i)∣R:=
   Fintype.prod_dvd_of_coprime hpowersCoprime hpow
 have hdegree:(∏ i,(q i)^multiplicity i).natDegree=
     ∑ i,multiplicity i*(q i).natDegree:=by
   rw [Polynomial.natDegree_prod_of_monic
     (s:=Finset.univ) (f:=fun i↦(q i)^multiplicity i)
     (fun i _↦(hqMonic i).pow _)]
   apply Finset.sum_congr rfl
   intro i _
   exact Polynomial.natDegree_pow (q i) (multiplicity i)
 rw [←hdegree]
 exact Polynomial.natDegree_le_of_dvd hprodDvd hR
theorem sum_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqIrreducible:∀ i,Irreducible (q i))
   (hqMonic:∀ i,(q i).Monic)
   (hqInjective:Function.Injective q)
   (hpow:∀ i,q i^multiplicity i∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 apply sum_pairwise_power_factor_degrees_le R q multiplicity hR hqMonic
 · intro i j hij
   apply (hqIrreducible i).coprime_iff_not_dvd.mpr
   intro hdvd
   have hassociated:=
     (hqIrreducible i).associated_of_dvd (hqIrreducible j) hdvd
   have heq:q i=q j:=Polynomial.eq_of_monic_of_associated
     (hqMonic i) (hqMonic j) hassociated
   exact hij (hqInjective heq)
 · exact hpow
theorem sum_power_factor_degrees_le_resultant_bidegree
   {I:Type*} [Fintype I]
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hqIrreducible:∀ i,Irreducible (q i))
   (hqMonic:∀ i,(q i).Monic)
   (hqInjective:Function.Injective q)
   (hpow:∀ i,
     q i^multiplicity i∣Polynomial.resultant P Q m n):
   (∑ i,multiplicity i*(q i).natDegree) ≤
     n*Polynomial.Bivariate.degreeX P+
       m*Polynomial.Bivariate.degreeX Q:=by
 exact (sum_power_factor_degrees_le
   (Polynomial.resultant P Q m n) q multiplicity hresultant
     hqIrreducible hqMonic hqInjective hpow).trans
   (bivariate_resultant_natDegree_le (F:=K) P Q m n)
theorem sum_grouped_power_factor_degrees_le
   {I:Type*} [Fintype I]
   (R:Polynomial K) (q:I → Polynomial K) (multiplicity:I → ℕ)
   (hR:R≠0)
   (hqIrreducible:∀ i,Irreducible (q i))
   (hqMonic:∀ i,(q i).Monic)
   (hpow:∀ f∈Finset.univ.image q,
     f^(∑ i with q i=f,multiplicity i)∣R):
   (∑ i,multiplicity i*(q i).natDegree) ≤ R.natDegree:=by
 classical
 let roots:Finset (Polynomial K):=Finset.univ.image q
 let grouped:roots → ℕ:=fun f↦∑ i with q i=f.1,multiplicity i
 have hrootsMonic:∀ f:roots,f.1.Monic:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hqMonic i
 have hrootsIrreducible:∀ f:roots,Irreducible f.1:=by
   intro f
   obtain ⟨i,_,hi⟩:=Finset.mem_image.mp f.2
   simpa only [hi] using hqIrreducible i
 have hrootsPow:∀ f:roots,f.1^grouped f∣R:=by
   intro f
   exact hpow f.1 f.2
 have hbound:=sum_power_factor_degrees_le R
   (fun f:roots↦f.1) grouped hR hrootsIrreducible hrootsMonic
     Subtype.val_injective hrootsPow
 have hregroup:
     (∑ f:roots,grouped f*f.1.natDegree)=
       ∑ i,multiplicity i*(q i).natDegree:=by
   change (∑ f:roots,
     (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=_
   have hattach:
       (∑ f:roots,
         (∑ i with q i=f.1,multiplicity i)*f.1.natDegree)=
       ∑ f∈roots,
         (∑ i with q i=f,multiplicity i)*f.natDegree:=by
     rw [show (Finset.univ:Finset roots)=roots.attach from
       Finset.univ_eq_attach roots]
     exact Finset.sum_attach roots (fun f:Polynomial K↦
       (∑ i with q i=f,multiplicity i)*f.natDegree)
   rw [hattach]
   simp_rw [Finset.sum_mul]
   calc
     (∑ f∈roots,∑ i with q i=f,
         multiplicity i*f.natDegree)=
         ∑ f∈roots,∑ i with q i=f,
           multiplicity i*(q i).natDegree:=by
       apply Finset.sum_congr rfl
       intro f _
       apply Finset.sum_congr rfl
       intro i hi
       rw [(Finset.mem_filter.mp hi).2]
     _=∑ i∈(Finset.univ:Finset I),
         multiplicity i*(q i).natDegree:=
       Finset.sum_fiberwise_of_maps_to
         (s:=Finset.univ) (t:=roots) (g:=q)
         (fun i _↦Finset.mem_image_of_mem q (Finset.mem_univ i)) _
     _=_:=by rfl
 rw [←hregroup]
 exact hbound
end
end ProximityPrize.SubmissionLower.RCN337
end PackedLegacy_CK

/-! Packed from ProximityPrize.SubmissionLower.GY. -/
section PackedLegacy_GY
namespace ProximityPrize.SubmissionLower.RCN328
open scoped Classical BigOperators
open RCN264 RCN095 RCN272 RCN237 RCN039 RCN046 RCN037 RCN341 RCN121
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega Seed:Type} [Field Omega]
 {G T1 T2 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1 tailFlag2:FlagDegree}
def properSecondTailComponents:
   Finset (RegularComponent Omega G T1 H):=by
 classical
 exact Finset.univ.filter fun C => T2∉C.1
theorem component_secondTail_card_le
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (C:RegularComponent Omega G T1 H)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlag tailFlag2 T2) (hproper:T2∉C.1)
   (hzero:∀ gamma∈componentSeeds Omega G T1 H S point C,
     MvPolynomial.aeval (point gamma) T2=0):
   (componentSeeds Omega G T1 H S point C).card ≤
     B.weightedCost tailFlag2 C:=by
 classical
 let component:=componentSeeds Omega G T1 H S point C
 let points:=component.image point
 have hpointsPrime:∀ v∈points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact componentSeeds_on_prime Omega G T1 H S point C gamma hgamma
 have hpointsZero:∀ v∈points,MvPolynomial.aeval v T2=0:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact hzero gamma hgamma
 have hbound:=(B.primeBudget C).zero_le tailFlag2 T2 hT2flag hproper
   points hpointsPrime hpointsZero
 have hcard:points.card=component.card:=
   Finset.card_image_of_injective component hpoint_injective
 simpa only [points,component,hcard,
   PrimeFlagBudgetFamily.weightedCost] using hbound
theorem properSecondTail_component_sum_le
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlag tailFlag2 T2)
   (hzero:∀ gamma∈S,MvPolynomial.aeval (point gamma) T2=0):
   (∑ C∈properSecondTailComponents (G:=G) (T1:=T1) (T2:=T2) (H:=H),
       (componentSeeds Omega G T1 H S point C).card) ≤
     flagMixed flag tailFlag1 tailFlag2:=by
 classical
 calc
   _ ≤ ∑ C∈properSecondTailComponents (G:=G) (T1:=T1) (T2:=T2) (H:=H),
       B.weightedCost tailFlag2 C:=by
     apply Finset.sum_le_sum
     intro C hC
     apply component_secondTail_card_le B C S point hpoint_injective hT2flag
     · exact (Finset.mem_filter.mp hC).2
     · intro gamma hgamma
       exact hzero gamma (componentSeeds_subset Omega G T1 H S point C hgamma)
   _ ≤ ∑ C:RegularComponent Omega G T1 H,B.weightedCost tailFlag2 C:=by
     exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=B.sum_weightedCost_le tailFlag2
variable [IsAlgClosed Omega]
theorem properSecondTail_component_sum_le_flagMixed
   (base:∀ C:RegularComponent Omega G T1 H,
     SeparableLiteralCoordinate C.1)
   (hY:∀ C:RegularComponent Omega G T1 H,LiteralProjectionGate C 0)
   (hZ:∀ C:RegularComponent Omega G T1 H,LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
   (hGirreducible:Irreducible G) (hT1proper:¬ G∣T1)
   (hGflag:PolynomialInFlag flag G)
   (hT1flag:PolynomialInFlag tailFlag1 T1)
   (hT2flag:PolynomialInFlag tailFlag2 T2)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hzero:∀ gamma∈S,MvPolynomial.aeval (point gamma) T2=0):
   (∑ C∈properSecondTailComponents (G:=G) (T1:=T1) (T2:=T2) (H:=H),
       (componentSeeds Omega G T1 H S point C).card) ≤
     flagMixed flag tailFlag1 tailFlag2:=by
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamily_of_nested
   flag tailFlag1 base hY hZ hSderiv hGirreducible hT1proper
   ((support_subset_flagSupport_iff flag G).mpr hGflag)
   ((support_subset_flagSupport_iff tailFlag1 T1).mpr hT1flag)
 exact properSecondTail_component_sum_le P.toPrimeFlagBudgetFamily
   S point hpoint_injective hT2flag hzero
end
end ProximityPrize.SubmissionLower.RCN328
end PackedLegacy_GY

/-! Packed from ProximityPrize.SubmissionLower.GX. -/
section PackedLegacy_GX
namespace ProximityPrize.SubmissionLower.RCN325
open scoped Classical BigOperators
open RCN264 RCN095 RCN237
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega Seed:Type} [Field Omega]
 {G T1 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1 tailFlag2:FlagDegree}
def delayedComponents
   (active:RegularComponent Omega G T1 H → Prop):
   Finset (RegularComponent Omega G T1 H):=by
 classical
 exact Finset.univ.filter active
structure DelayedBranchFlagBudget
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop) where
 multiplicity:RegularComponent Omega G T1 H → ℕ
 cost:RegularComponent Omega G T1 H → ℕ
 cost_le:∀ C,active C →
   cost C ≤ multiplicity C*B.weightedCost tailFlag2 C
 divisor_le:
   (∑ C∈delayedComponents active,
     multiplicity C*B.weightedCost tailFlag2 C) ≤
       flagMixed flag tailFlag1 tailFlag2
theorem delayed_component_sum_le_flagMixed
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop)
   (D:DelayedBranchFlagBudget (tailFlag2:=tailFlag2) B active)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hcomponent:∀ C,active C →
     (componentSeeds Omega G T1 H S point C).card ≤ D.cost C):
   (∑ C∈delayedComponents active,
     (componentSeeds Omega G T1 H S point C).card) ≤
       flagMixed flag tailFlag1 tailFlag2:=by
 classical
 calc
   _ ≤ ∑ C∈delayedComponents active,D.cost C:=by
     apply Finset.sum_le_sum
     intro C hC
     exact hcomponent C (Finset.mem_filter.mp hC).2
   _ ≤ ∑ C∈delayedComponents active,
       D.multiplicity C*B.weightedCost tailFlag2 C:=by
     apply Finset.sum_le_sum
     intro C hC
     exact D.cost_le C (Finset.mem_filter.mp hC).2
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=D.divisor_le
theorem delayed_seed_union_card_le_flagMixed
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop)
   (D:DelayedBranchFlagBudget (tailFlag2:=tailFlag2) B active)
   [DecidableEq Seed]
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hcomponent:∀ C,active C →
     (componentSeeds Omega G T1 H S point C).card ≤ D.cost C):
   ((delayedComponents active).biUnion
     (componentSeeds Omega G T1 H S point)).card ≤
       flagMixed flag tailFlag1 tailFlag2:=by
 classical
 exact Finset.card_biUnion_le.trans
   (delayed_component_sum_le_flagMixed B active D S point hcomponent)
def DelayedBranchFlagBudget.immediate
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (active:RegularComponent Omega G T1 H → Prop):
   DelayedBranchFlagBudget (tailFlag2:=tailFlag2) B active where
 multiplicity:=fun _ => 1
 cost:=fun C => B.weightedCost tailFlag2 C
 cost_le:=by simp
 divisor_le:=by
   calc
     (∑ C∈delayedComponents active,
         1*B.weightedCost tailFlag2 C)=
         ∑ C∈delayedComponents active,
           B.weightedCost tailFlag2 C:=by simp
     _ ≤
         ∑ C:RegularComponent Omega G T1 H,
           B.weightedCost tailFlag2 C:=by
       exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
     _ ≤ flagMixed flag tailFlag1 tailFlag2:=
       B.sum_weightedCost_le tailFlag2
end
end ProximityPrize.SubmissionLower.RCN325
end PackedLegacy_GX

/-! Packed from ProximityPrize.SubmissionLower.P7. -/
section PackedLegacy_P7
namespace ProximityPrize.SubmissionLower.RCN330
open scoped Classical
open RCN313 RCN231 RCN136 RCN238 RCN086 RCN055 RCN264 RCN243
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
variable {K Ω:Type} [Field K] [Field Ω]
theorem selected_globalTailCut_zero_of_lt
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (γ:K) (w d:ℕ)
   (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0)
   (hwd:w < d):
   MvPolynomial.aeval (selectedPoint φ selected γ)
     (globalTailCut φ F d)=0:=by
 rw [globalTailCut_eq,map_mul]
 have hzero:MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (numerator K F d))=0:=by
   rw [eval_surfaceMap]
   have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
       polynomialPoint (φ.comp Polynomial.C) (selected γ) γ
         (φ Polynomial.X):=by
     funext i
     fin_cases i <;> rfl
   rw [hv]
   exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F
     (selected γ) γ (φ Polynomial.X) hsolution d
     (hdegree.trans_lt hwd)
 change MvPolynomial.eval (selectedPoint φ selected γ)
     (surfaceMap φ (numerator K F d))*_=0
 rw [hzero,zero_mul]
theorem selected_secondTail_zero
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (γ:K) (w:ℕ)
   (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ)
     (globalTailCut φ F (w+2))=0:=by
 exact selected_globalTailCut_zero_of_lt φ F selected γ w (w+2)
   hdegree hsolution (by omega)
theorem surface_numerator_succ
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K) (b:ℕ):
   surfaceMap φ (numerator K F (b+1))=
     surfaceMap φ (polyH K F)*
         surfaceMap φ (baseDerivation F (numerator K F b))-
       (2*b:MvPolynomial (Fin 3) Ω)*
         surfaceMap φ (numerator K F b)*
         surfaceMap φ (baseDerivation F (polyH K F)):=by
 rw [numerator_succ,numeratorStep_eq]
 simp only [map_sub,map_mul,map_natCast]
 push_cast
 rfl
theorem mapped_baseDerivation_mem_of_two_numerators
   (φ:Polynomial K →+*Ω) (F:MvPolynomial (Fin 4) K) (b:ℕ)
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (hH:surfaceMap φ (polyH K F)∉P)
   (hN:surfaceMap φ (numerator K F b)∈P)
   (hNnext:surfaceMap φ (numerator K F (b+1))∈P):
   surfaceMap φ (baseDerivation F (numerator K F b))∈P:=by
 have hsecond:(2*b:MvPolynomial (Fin 3) Ω)*
     surfaceMap φ (numerator K F b)*
     surfaceMap φ (baseDerivation F (polyH K F))∈P:=by
   exact P.mul_mem_right _ (P.mul_mem_left _ hN)
 rw [surface_numerator_succ φ F b] at hNnext
 have hfirst:surfaceMap φ (polyH K F)*
     surfaceMap φ (baseDerivation F (numerator K F b))∈P:=by
   have:=P.add_mem hNnext hsecond
   simpa only [sub_add_cancel] using this
 exact (((inferInstance:P.IsPrime).mem_or_mem hfirst).resolve_left hH)
theorem globalTailCut_mem_iff
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (d:ℕ)
   (P:Ideal (MvPolynomial (Fin 3) Ω)):
   globalTailCut φ F d∈P ↔ surfaceMap φ (numerator K F d)∈P:=by
 rw [globalTailCut_eq]
 have hc:(-φ Polynomial.X)^d≠0:=tail_scalar_ne_zero φ hφ d
 have hu:IsUnit
     (MvPolynomial.C ((-φ Polynomial.X)^d):MvPolynomial (Fin 3) Ω):=
   (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
 exact P.mul_unit_mem_iff_mem hu
theorem mapped_baseDerivation_mem_of_two_globalTails
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (b:ℕ)
   (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
   (hH:surfaceMap φ (polyH K F)∉P)
   (hT:globalTailCut φ F b∈P)
   (hTnext:globalTailCut φ F (b+1)∈P):
   surfaceMap φ (baseDerivation F (numerator K F b))∈P:=by
 apply mapped_baseDerivation_mem_of_two_numerators φ F b P hH
 · exact (globalTailCut_mem_iff φ hφ F b P).mp hT
 · exact (globalTailCut_mem_iff φ hφ F (b+1) P).mp hTnext
theorem regularComponent_two_tail_dichotomy
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Ω) (w:ℕ)
   (C:RegularComponent Ω G (globalTailCut φ F (w+1))
     (regularitySurface φ F)):
   globalTailCut φ F (w+2)∉C.1∨
     (globalTailCut φ F (w+2)∈C.1∧
       surfaceMap φ
         (baseDerivation F (numerator K F (w+1)))∈C.1):=by
 by_cases hT2:globalTailCut φ F (w+2)∈C.1
 · right
   refine ⟨hT2,?_⟩
   apply mapped_baseDerivation_mem_of_two_globalTails φ hφ F (w+1) C.1
   · exact regularComponent_H_not_mem Ω G
       (globalTailCut φ F (w+1)) (regularitySurface φ F) C
   · exact regularComponent_T_mem Ω G
       (globalTailCut φ F (w+1)) (regularitySurface φ F) C
   · simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hT2
 · exact Or.inl hT2
end
end ProximityPrize.SubmissionLower.RCN330
end PackedLegacy_P7

/-! Packed from ProximityPrize.SubmissionLower.B3. -/
section PackedLegacy_B3
namespace ProximityPrize.SubmissionLower.RCN074
open scoped Classical BigOperators
open RCN159 RCN136 RCN238 RCN264 RCN243 RCN086 RCN095 RCN237 RCN325
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
 {pchar errors w:ℕ} [CharP Omega pchar]
 {flag tailFlag1 tailFlag2:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
abbrev FirstTailComponent
   (S:ResidualStage phi Gamma x pchar errors flag w support):=
 RegularComponent Omega S.G (globalTailCut phi S.F (w+1))
   (regularitySurface phi S.F)
structure DelayedTailMultiplicityProvider
   (S:ResidualStage phi Gamma x pchar errors flag w support) where
 budgetFamily:PrimeFlagBudgetFamily
   (G:=S.G) (T:=globalTailCut phi S.F (w+1))
   (H:=regularitySurface phi S.F) flag tailFlag1
 multiplicity:FirstTailComponent S → ℕ
 cost:FirstTailComponent S → ℕ
 one_le_multiplicity:∀ C,1 ≤ multiplicity C
 tangentYZGate:errors+1 ≤ tailFlag2.yz
 cost_le:∀ C,
   cost C ≤ multiplicity C*budgetFamily.weightedCost tailFlag2 C
 divisor_le:
   (∑ C,multiplicity C*budgetFamily.weightedCost tailFlag2 C) ≤
     flagMixed flag tailFlag1 tailFlag2
 componentBound:∀ C,
   (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
     (regularitySurface phi S.F) Gamma
     (selectedPoint phi S.selected) C).card ≤ cost C
 dichotomy:∀ C,
   (∃ delay,1 ≤ delay∧delay ≤ multiplicity C∧
     globalTailCut phi S.F (w+1+delay)∉C.1)∨
   ((∀ delay,globalTailCut phi S.F (w+1+delay)∈C.1)∧
     (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
       (regularitySurface phi S.F) Gamma
       (selectedPoint phi S.selected) C).card ≤
         (errors+1)*budgetFamily.yzCost C)
theorem stage_card_le_flagMixed
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (P:DelayedTailMultiplicityProvider
     (tailFlag1:=tailFlag1) (tailFlag2:=tailFlag2) S):
   Gamma.card ≤ flagMixed flag tailFlag1 tailFlag2:=by
 classical
 let T1:=globalTailCut phi S.F (w+1)
 let H:=regularitySurface phi S.F
 let point:=selectedPoint phi S.selected
 have hG:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) S.G=0:=S.on_component
 have hT1:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) T1=0:=by
   intro gamma hgamma
   exact selected_globalTailCut_zero phi S.F S.selected gamma w
     (S.degree_le gamma hgamma) (S.solution gamma hgamma)
 have hH:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) H≠0:=by
   intro gamma hgamma
   exact selectedPoint_evaluation phi S.selected gamma
     (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
 have hcover:Gamma.card ≤
     ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=
   card_le_sum_componentSeeds Omega S.G T1 H Gamma point hG hT1 hH
 calc
   Gamma.card ≤ ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=hcover
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,P.cost C:=
     Finset.sum_le_sum (fun C _↦P.componentBound C)
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,
       P.multiplicity C*P.budgetFamily.weightedCost tailFlag2 C:=
     Finset.sum_le_sum (fun C _↦P.cost_le C)
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=P.divisor_le
end
end ProximityPrize.SubmissionLower.RCN074
end PackedLegacy_B3

/-! Packed from ProximityPrize.SubmissionLower.AM. -/
section PackedLegacy_AM
namespace ProximityPrize.SubmissionLower.RCN338
open scoped Classical BigOperators
open RCN095 RCN264 RCN237 RCN121 RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
structure RegularComponentWeightedInertiaResultantCertificate
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ) where
 z:(∑ C,multiplicity C*B.zCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitZFlag
 yz:(∑ C,multiplicity C*B.yzCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitYZFlag
 all:(∑ C,multiplicity C*B.allCost C) ≤
   flagMixed surfaceFlag firstTailFlag unitAllFlag
theorem RegularComponentWeightedInertiaResultantCertificate.divisor_le
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   (C:RegularComponentWeightedInertiaResultantCertificate B multiplicity):
   (∑ component,
     multiplicity component*B.weightedCost secondTailFlag component) ≤
       flagMixed surfaceFlag firstTailFlag secondTailFlag:=by
 have hz:=C.z
 have hyz:=C.yz
 have hall:=C.all
 calc
   (∑ component,
       multiplicity component*B.weightedCost secondTailFlag component)=
     secondTailFlag.zOnly*
         (∑ component,multiplicity component*B.zCost component)+
       secondTailFlag.yz*
         (∑ component,multiplicity component*B.yzCost component)+
       secondTailFlag.all*
         (∑ component,multiplicity component*B.allCost component):=by
     simp only [PrimeFlagBudgetFamily.weightedCost,
       Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,
       Nat.mul_left_comm]
   _ ≤ secondTailFlag.zOnly*
         flagMixed surfaceFlag firstTailFlag unitZFlag+
       secondTailFlag.yz*
         flagMixed surfaceFlag firstTailFlag unitYZFlag+
       secondTailFlag.all*
         flagMixed surfaceFlag firstTailFlag unitAllFlag:=
     Nat.add_le_add
       (Nat.add_le_add
         (Nat.mul_le_mul_left secondTailFlag.zOnly hz)
         (Nat.mul_le_mul_left secondTailFlag.yz hyz))
       (Nat.mul_le_mul_left secondTailFlag.all hall)
   _=flagMixed surfaceFlag firstTailFlag secondTailFlag:=
     (flagMixed_projection_decomposition
       surfaceFlag firstTailFlag secondTailFlag).symm
end
end ProximityPrize.SubmissionLower.RCN338
end PackedLegacy_AM

/-! Packed from ProximityPrize.SubmissionLower.Q3. -/
section PackedLegacy_Q3
namespace ProximityPrize.SubmissionLower.RCN336
open scoped Classical BigOperators
open RCN264 RCN095 RCN237 RCN066 RCN338
noncomputable section
set_option autoImplicit false
variable {Omega Seed:Type} [Field Omega]
 {G T T' T2 H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag secondTailFlag:FlagDegree}
theorem component_secondTail_card_le_mod
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T) (H:=H)
     surfaceFlag firstTailFlag)
   (C:RegularComponent Omega G T H)
   (S:Finset Seed) (point:Seed → Fin 3 → Omega)
   (hpoint_injective:Function.Injective point)
   (hT2flag:PolynomialInFlagMod C.1 secondTailFlag T2)
   (hproper:T2 ∉ C.1)
   (hzero:∀ gamma ∈ componentSeeds Omega G T H S point C,
     MvPolynomial.aeval (point gamma) T2 = 0) :
   (componentSeeds Omega G T H S point C).card ≤
     B.weightedCost secondTailFlag C:=by
 classical
 let component:=componentSeeds Omega G T H S point C
 let points:=component.image point
 have hpointsPrime:∀ v ∈ points,
     C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact componentSeeds_on_prime Omega G T H S point C gamma hgamma
 have hpointsZero:∀ v ∈ points,MvPolynomial.aeval v T2 = 0:=by
   intro v hv
   obtain ⟨gamma,hgamma,rfl⟩:=Finset.mem_image.mp hv
   exact hzero gamma hgamma
 have hbound :=
   RCN066.PrimeFlagZeroBudget.zero_le_congr
     (B.primeBudget C) secondTailFlag T2 hT2flag hproper
     points hpointsPrime hpointsZero
 have hcard:points.card = component.card :=
   Finset.card_image_of_injective component hpoint_injective
 simpa only [points,component,hcard,
   PrimeFlagBudgetFamily.weightedCost] using hbound
def transportedMultiplicity
   (h:G ∣ T - T')
   (multiplicity:RegularComponent Omega G T H → ℕ) :
   RegularComponent Omega G T' H → ℕ :=
 fun C => multiplicity ((regularComponentEquiv h).symm C)
theorem weightedCertificate_of_congruentCut
   (h:G ∣ T - T')
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T') (H:=H)
     surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   (C:RegularComponentWeightedInertiaResultantCertificate B
     (transportedMultiplicity h multiplicity)) :
   RegularComponentWeightedInertiaResultantCertificate
     (PrimeFlagBudgetFamily.ofCongruentCut h B) multiplicity where
 z:=by
   have hz:=C.z
   dsimp only [transportedMultiplicity] at hz
   rw [← (regularComponentEquiv h).sum_comp] at hz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hz
 yz:=by
   have hyz:=C.yz
   dsimp only [transportedMultiplicity] at hyz
   rw [← (regularComponentEquiv h).sum_comp] at hyz
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hyz
 all:=by
   have hall:=C.all
   dsimp only [transportedMultiplicity] at hall
   rw [← (regularComponentEquiv h).sum_comp] at hall
   simpa only [PrimeFlagBudgetFamily.ofCongruentCut,
     Equiv.symm_apply_apply] using hall
end
end ProximityPrize.SubmissionLower.RCN336
end PackedLegacy_Q3

/-! Packed from ProximityPrize.SubmissionLower.X6. -/
section PackedLegacy_X6
namespace ProximityPrize.SubmissionLower.RCN014
open RCN002 RCN005 RCN011 RCN010
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
 (order:Fin 3 ≃ Fin 3)
variable (P:Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
 (ht:Transcendental K (coordinate K P (order 0)))
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
end PackedLegacy_X6

/-! Packed from ProximityPrize.SubmissionLower.FJ. -/
section PackedLegacy_FJ
namespace ProximityPrize.SubmissionLower.RCN226
open RCN011 RCN021 RCN022 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoefficientRing:=Polynomial (RatFunc K)
def projectedFactor:Polynomial (RatFunc K):=
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))
theorem planeEvaluation_comp_C:
   (planeEvaluation K L order e ht).comp
     (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
       Polynomial.eval₂RingHom
         (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
         (e (MvPolynomial.X (order 2))):=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 apply Polynomial.ringHom_ext
 · intro c
   change planeEvaluation K L order e ht
       (Polynomial.C (Polynomial.C c))=
     Polynomial.aeval (e (MvPolynomial.X (order 2))) (Polynomial.C c)
   rw [planeEvaluation_C_C,Polynomial.aeval_C]
   rfl
 · change planeEvaluation K L order e ht (Polynomial.C Polynomial.X)=
     Polynomial.aeval (e (MvPolynomial.X (order 2))) Polynomial.X
   rw [planeEvaluation_C_X,Polynomial.aeval_X]
theorem relationKernel_comap_C:
   (relationKernel K L order e ht).comap
     (Polynomial.C:CoefficientRing K →+*PlaneRing K)=
       Ideal.span {projectedFactor K L order e ht}:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 rw [relationKernel,RingHom.comap_ker,planeEvaluation_comp_C,
   show Polynomial.eval₂RingHom
     (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom
     (e (MvPolynomial.X (order 2)))=
       (Polynomial.aeval (e (MvPolynomial.X (order 2)))).toRingHom from rfl]
 change RingHom.ker (Polynomial.aeval (e (MvPolynomial.X (order 2))))=
   Ideal.span {minpoly (RatFunc K) (e (MvPolynomial.X (order 2)))}
 rw [minpoly.ker_aeval_eq_span_minpoly]
theorem projectedFactor_monic
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (projectedFactor K L order e ht).Monic:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 exact minpoly.monic (IsIntegral.of_finite _ _)
theorem projectedFactor_irreducible
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Irreducible (projectedFactor K L order e ht):=
 by
   letI:Algebra (RatFunc K) L:=
     (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
   letI:FiniteDimensional (RatFunc K) L:=hfinite
   exact minpoly.irreducible (IsIntegral.of_finite _ _)
theorem relationKernel_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (relationKernel K L order e ht).IsMaximal:=by
 letI:Algebra (RatFunc K) L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional (RatFunc K) L:=hfinite
 apply RingHom.ker_isMaximal_of_surjective
 exact planeEvaluation_surjective_of_finite_generatingPair
   (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
end
end ProximityPrize.SubmissionLower.RCN226
end PackedLegacy_FJ

/-! Packed from ProximityPrize.SubmissionLower.C7. -/
section PackedLegacy_C7
namespace ProximityPrize.SubmissionLower.RCN191
open RCN011 RCN021 RCN022 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
abbrev CoeffPrime:Ideal (Polynomial (RatFunc K)):=
 Ideal.span {projectedFactor K L order e ht}
theorem coeffPrime_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (CoeffPrime K L order e ht).IsMaximal:=
 PrincipalIdealRing.isMaximal_of_irreducible
   (projectedFactor_irreducible K L order e ht hfinite)
abbrev LocalCoefficient
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 @Localization.AtPrime (Polynomial (RatFunc K)) _
   (CoeffPrime K L order e ht)
   (coeffPrime_isMaximal K L order e ht hfinite).isPrime
local instance localCoefficientSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (LocalCoefficient K L order e ht hfinite):=
 (inferInstance:CommRing
   (LocalCoefficient K L order e ht hfinite)).toSemiring
local instance localizedPlaneSemiring
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Semiring (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 (inferInstance:CommRing
   (Polynomial (LocalCoefficient K L order e ht hfinite))).toSemiring
def localizePlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   PlaneRing K →+*Polynomial (LocalCoefficient K L order e ht hfinite):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))
def localizedRelation
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Ideal (Polynomial (LocalCoefficient K L order e ht hfinite)):=
 Ideal.map (localizePlane K L order e ht hfinite)
   (relationKernel K L order e ht)
theorem localizedRelation_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (localizedRelation K L order e ht hfinite).IsMaximal:=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 have hJmax:J.IsMaximal:=
   relationKernel_isMaximal K L order e ht hfinite hgen
 letI:J.IsPrime:=hJmax.isPrime
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K))
       (J:Set (PlaneRing K)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   apply hr
   have hrJ:r∈J.comap c:=haJ
   have hcomap:J.comap c=p:=by
     simpa only [J,c,p] using
       relationKernel_comap_C K L order e ht
   rwa [hcomap] at hrJ
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra (PlaneRing K) (Polynomial Rp):=
   Polynomial.algebra (Polynomial (RatFunc K)) Rp
 have hf:f=algebraMap (PlaneRing K) (Polynomial Rp):=rfl
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
     (Polynomial Rp):=by
   exact Polynomial.isLocalization p.primeCompl Rp
 have hunder:(localizedRelation K L order e ht hfinite).under
     (PlaneRing K)=J:=by
   change (Ideal.map f J).under (PlaneRing K)=J
   rw [hf]
   exact IsLocalization.under_map_of_isPrime_disjoint
     (I:=J) (p.primeCompl.map c.toMonoidHom) (Polynomial Rp)
       hJmax.isPrime hdisjoint
 letI:((localizedRelation K L order e ht hfinite).under
     (PlaneRing K)).IsMaximal:=
   hunder ▸ hJmax
 have hunder':(Ideal.map
     (algebraMap (PlaneRing K) (Polynomial Rp)) J).under (PlaneRing K)=J:=by
   rw [←hf]
   exact hunder
 letI:((Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).under
     (PlaneRing K)).IsMaximal:=hunder'.symm ▸ hJmax
 change (Ideal.map f J).IsMaximal
 rw [hf]
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
abbrev LocalizedPlane
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):=
 Polynomial (LocalCoefficient K L order e ht hfinite)
abbrev LocalizedSurfaceQuotient
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface:PlaneRing K):=
 Polynomial (LocalCoefficient K L order e ht hfinite) ⧸
   Ideal.span {localizePlane K L order e ht hfinite surface}
def localizedRelationBar
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface:PlaneRing K):
   Ideal (LocalizedSurfaceQuotient K L order e ht hfinite surface):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {localizePlane K L order e ht hfinite surface}))
     (localizedRelation K L order e ht hfinite)
theorem localizedRelationBar_isMaximal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤)
   (surface:PlaneRing K)
   (hsurface:surface∈relationKernel K L order e ht):
   (localizedRelationBar K L order e ht hfinite surface).IsMaximal:=by
 let J:=localizedRelation K L order e ht hfinite
 let q:=Ideal.Quotient.mk
   (Ideal.span {localizePlane K L order e ht hfinite surface})
 have hJmax:J.IsMaximal:=
   localizedRelation_isMaximal K L order e ht hfinite hgen
 letI:J.IsMaximal:=hJmax
 apply Ideal.IsMaximal.map_of_surjective_of_ker_le
   (f:=q) Ideal.Quotient.mk_surjective
 rw [Ideal.mk_ker,Ideal.span_le]
 intro x hx
 rw [Set.mem_singleton_iff] at hx
 subst x
 exact Ideal.mem_map_of_mem (localizePlane K L order e ht hfinite) hsurface
theorem localizedRelationBar_ne_bot
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (surface tail:PlaneRing K)
   (htail:tail∈relationKernel K L order e ht)
   (hproper:localizePlane K L order e ht hfinite tail∉
     Ideal.span {localizePlane K L order e ht hfinite surface}):
   localizedRelationBar K L order e ht hfinite surface≠⊥:=by
 intro hbot
 have hbar:Ideal.Quotient.mk
     (Ideal.span {localizePlane K L order e ht hfinite surface})
     (localizePlane K L order e ht hfinite tail)∈
       localizedRelationBar K L order e ht hfinite surface:=
   Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ htail)
 rw [hbot,Ideal.mem_bot] at hbar
 exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hbar)
end
end ProximityPrize.SubmissionLower.RCN191
end PackedLegacy_C7

/-! Packed from ProximityPrize.SubmissionLower.DM. -/
section PackedLegacy_DM
namespace ProximityPrize.SubmissionLower.RCN034
open RCN002 RCN005 RCN011 RCN010 RCN371
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K:Type) [Field K]
def planeDenominators (order:Fin 3 ≃ Fin 3):Submonoid (Original K):=
 (coefficientDenominators K).comap (collect K order).toMonoidHom
@[reducible] def rationalPolynomialAlgebra (order:Fin 3 ≃ Fin 3):
   Algebra (Original K) (RationalPolynomials K):=
 (rationalMap K order).toAlgebra
@[reducible] def planeAlgebra (order:Fin 3 ≃ Fin 3):
   Algebra (Original K) (PlaneRing K):=
 (planeMap K order).toAlgebra
theorem rationalPolynomialLocalization (order:Fin 3 ≃ Fin 3):
   letI:=rationalPolynomialAlgebra K order
   IsLocalization (planeDenominators K order) (RationalPolynomials K):=by
 letI:=rationalPolynomialAlgebra K order
 letI:Algebra (Collected K) (RationalPolynomials K):=
   MvPolynomial.algebraMvPolynomial
 letI:IsLocalization (coefficientDenominators K) (RationalPolynomials K):=
   MvPolynomial.isLocalization (nonZeroDivisors (Polynomial K)) (RatFunc K)
 apply IsLocalization.of_ringEquiv_left
   (R:=Original K) (S:=Collected K) (K:=RationalPolynomials K)
   (M₁:=coefficientDenominators K) (M₂:=planeDenominators K order)
   (collect K order).toRingEquiv
 · exact Submonoid.map_comap_eq_of_surjective
     (collect K order).surjective (coefficientDenominators K)
 · intro F
   rfl
theorem planeRingLocalization (order:Fin 3 ≃ Fin 3):
   letI:=planeAlgebra K order
   IsLocalization (planeDenominators K order) (PlaneRing K):=by
 letI:=rationalPolynomialAlgebra K order
 let aPlane:=planeAlgebra K order
 letI:Algebra (Original K) (PlaneRing K):=aPlane
 letI:SMul (Original K) (PlaneRing K):=aPlane.toSMul
 letI:IsLocalization (planeDenominators K order) (RationalPolynomials K):=
   rationalPolynomialLocalization K order
 let e:RationalPolynomials K ≃ₐ[Original K] PlaneRing K:={
   bivariateEquiv (RatFunc K) with
   commutes':=fun F => rfl}
 exact IsLocalization.isLocalization_of_algEquiv
   (planeDenominators K order) e
end
end ProximityPrize.SubmissionLower.RCN034
end PackedLegacy_DM

/-! Packed from ProximityPrize.SubmissionLower.L7. -/
section PackedLegacy_L7
namespace ProximityPrize.SubmissionLower.RCN189
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A B:Type*} [CommRing A] [CommRing B]
 (M:Submonoid A) [Algebra A B] [IsLocalization M B]
@[reducible] def quotientAlgebra
   (I:Ideal A) (J:Ideal B) (hIJ:I ≤ J.comap (algebraMap A B)):
   Algebra (A ⧸ I) (B ⧸ J):=
 (Ideal.quotientMap J (algebraMap A B) hIJ).toAlgebra'
   (fun _ _ => mul_comm _ _)
theorem quotient_isLocalization
   (I:Ideal A) (J:Ideal B)
   (hJ:J=I.map (algebraMap A B)):
   let hIJ:I ≤ J.comap (algebraMap A B):=by
     rw [hJ]
     exact Ideal.le_comap_map
   letI:=quotientAlgebra I J hIJ
   IsLocalization (M.map (Ideal.Quotient.mk I)) (B ⧸ J):=by
 let hIJ:I ≤ J.comap (algebraMap A B):=by
   rw [hJ]
   exact Ideal.le_comap_map
 letI:=quotientAlgebra I J hIJ
 let qA:A →+*A ⧸ I:=Ideal.Quotient.mk I
 let qB:B →+*B ⧸ J:=Ideal.Quotient.mk J
 constructor
 constructor
 · rintro ⟨_,⟨m,hm,rfl⟩⟩
   change IsUnit (qB (algebraMap A B m))
   exact (IsLocalization.map_units B ⟨m,hm⟩).map qB
 · intro y
   obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective y
   obtain ⟨⟨a,m⟩,hb⟩:=IsLocalization.surj M b
   let mbar:M.map qA:=⟨qA m,⟨m,m.property,rfl⟩⟩
   refine ⟨⟨qA a,mbar⟩,?_⟩
   change qB b*qB (algebraMap A B m)=qB (algebraMap A B a)
   simpa only [map_mul] using congrArg qB hb
 · intro x y hxy
   obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x
   obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective y
   change qB (algebraMap A B a)=qB (algebraMap A B b) at hxy
   have hmem:algebraMap A B (a-b)∈J:=by
     rw [←Ideal.Quotient.eq_zero_iff_mem]
     rw [map_sub]
     change qB (algebraMap A B a-algebraMap A B b)=0
     rw [map_sub,hxy,sub_self]
   rw [hJ,IsLocalization.algebraMap_mem_map_algebraMap_iff M B] at hmem
   obtain ⟨m,hmM,hmI⟩:=hmem
   let mbar:M.map qA:=⟨qA m,⟨m,hmM,rfl⟩⟩
   refine ⟨mbar,?_⟩
   change qA m*qA a=qA m*qA b
   rw [←map_mul, ←map_mul, ←sub_eq_zero, ←map_sub,
     Ideal.Quotient.eq_zero_iff_mem]
   simpa only [mul_sub] using hmI
end
end ProximityPrize.SubmissionLower.RCN189
end PackedLegacy_L7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier20 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.L8. -/
section PackedLegacy_L8
namespace ProximityPrize.SubmissionLower.RCN190
open RCN189
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A B:Type*} [CommRing A] [CommRing B]
 (M:Submonoid A) [Algebra A B] [IsLocalization M B]
def surfaceMap (I:Ideal A):
   (A ⧸ I) →+*(B ⧸ I.map (algebraMap A B)):=
 Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
   Ideal.le_comap_map
@[reducible] def surfaceAlgebra (I:Ideal A):
   Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=
 quotientAlgebra I (I.map (algebraMap A B)) Ideal.le_comap_map
def sourcePrime (I P:Ideal A):Ideal (A ⧸ I):=
 P.map (Ideal.Quotient.mk I)
def targetPrime (I:Ideal A) (J:Ideal B):
   Ideal (B ⧸ I.map (algebraMap A B)):=
 J.map (Ideal.Quotient.mk (I.map (algebraMap A B)))
theorem sourcePrime_isPrime
   (I P:Ideal A) [P.IsPrime] (hIP:I ≤ P):
   (sourcePrime I P).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using hIP
theorem map_ideal_le_relation
   (I P:Ideal A) (J:Ideal B)
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   I.map (algebraMap A B) ≤ J:=by
 rw [Ideal.map_le_iff_le_comap,hcontract]
 exact hIP
theorem targetPrime_isPrime
   (I P:Ideal A) (J:Ideal B) [J.IsPrime]
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   (targetPrime I J).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using
   map_ideal_le_relation I P J hIP hcontract
theorem targetPrime_contract
   (I P:Ideal A) (J:Ideal B)
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   (targetPrime I J).comap (surfaceMap I)=sourcePrime I P:=by
 let qA:A →+*A ⧸ I:=Ideal.Quotient.mk I
 let qB:B →+*B ⧸ I.map (algebraMap A B):=
   Ideal.Quotient.mk (I.map (algebraMap A B))
 apply Ideal.comap_injective_of_surjective qA Ideal.Quotient.mk_surjective
 change Ideal.comap qA
     (Ideal.comap (surfaceMap I) (Ideal.map qB J))=
   Ideal.comap qA (Ideal.map qA P)
 rw [Ideal.comap_comap]
 have hcomp:(surfaceMap I).comp qA=
     qB.comp (algebraMap A B):=by
   apply DFunLike.ext _ _
   intro a
   rfl
 rw [hcomp, ←Ideal.comap_comap,
   Ideal.comap_map_of_surjective' qB Ideal.Quotient.mk_surjective,
   Ideal.mk_ker,
   sup_eq_left.mpr (map_ideal_le_relation I P J hIP hcontract),
   hcontract,
   Ideal.comap_map_of_surjective' qA Ideal.Quotient.mk_surjective,
   Ideal.mk_ker,sup_eq_left.mpr hIP]
theorem surface_isLocalization (I:Ideal A):
   letI:=surfaceAlgebra (A:=A) (B:=B) I
   IsLocalization (M.map (Ideal.Quotient.mk I))
     (B ⧸ I.map (algebraMap A B)):=by
 letI:=surfaceAlgebra (A:=A) (B:=B) I
 exact quotient_isLocalization M I (I.map (algebraMap A B)) rfl
noncomputable abbrev SourceLocal
   (I P:Ideal A) [P.IsPrime] (hIP:I ≤ P):=
 @Localization.AtPrime (A ⧸ I) _ (sourcePrime I P)
   (sourcePrime_isPrime I P hIP)
noncomputable abbrev TargetLocal
   (I P:Ideal A) (J:Ideal B) [J.IsPrime]
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):=
 @Localization.AtPrime (B ⧸ I.map (algebraMap A B)) _ (targetPrime I J)
   (targetPrime_isPrime I P J hIP hcontract)
noncomputable def surfaceLocalEquiv
   (I P:Ideal A) [P.IsPrime] (J:Ideal B) [J.IsPrime]
   (hIP:I ≤ P) (hcontract:J.comap (algebraMap A B)=P):
   SourceLocal I P hIP ≃+*TargetLocal I P J hIP hcontract:=by
 let p:=sourcePrime I P
 let q:=targetPrime I J
 letI:p.IsPrime:=sourcePrime_isPrime I P hIP
 letI:q.IsPrime:=targetPrime_isPrime I P J hIP hcontract
 let aSurface:=surfaceAlgebra (A:=A) (B:=B) I
 letI:Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=aSurface
 letI:SMul (A ⧸ I) (B ⧸ I.map (algebraMap A B)):=aSurface.toSMul
 letI:IsLocalization (M.map (Ideal.Quotient.mk I))
     (B ⧸ I.map (algebraMap A B)):=surface_isLocalization M I
 let aLocal:Algebra (A ⧸ I) (Localization.AtPrime q):=
   ((algebraMap (B ⧸ I.map (algebraMap A B)) (Localization.AtPrime q)).comp
     (surfaceMap I)).toAlgebra' (fun _ _ => mul_comm _ _)
 letI:Algebra (A ⧸ I) (Localization.AtPrime q):=aLocal
 letI:SMul (A ⧸ I) (Localization.AtPrime q):=aLocal.toSMul
 let targetAlgebra:Algebra (B ⧸ I.map (algebraMap A B))
     (Localization.AtPrime q):=inferInstance
 letI:SMul (B ⧸ I.map (algebraMap A B)) (Localization.AtPrime q):=
   targetAlgebra.toSMul
 letI:IsScalarTower (A ⧸ I) (B ⧸ I.map (algebraMap A B))
     (Localization.AtPrime q):=IsScalarTower.of_algebraMap_eq' rfl
 have hloc:IsLocalization.AtPrime (Localization.AtPrime q) p:=by
   convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
     (M.map (Ideal.Quotient.mk I)) (Localization.AtPrime q) q
   exact (targetPrime_contract I P J hIP hcontract).symm
 letI:IsLocalization.AtPrime (Localization.AtPrime q) p:=hloc
 exact (IsLocalization.algEquiv p.primeCompl _ _).toRingEquiv
end
end ProximityPrize.SubmissionLower.RCN190
end PackedLegacy_L8

/-! Packed from ProximityPrize.SubmissionLower.EC. -/
section PackedLegacy_EC
namespace ProximityPrize.SubmissionLower.RCN113
open RCN002 RCN011 RCN371 RCN021 RCN125 RCN093 RCN034 RCN190
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K:Type) [Field K]
def flagPlaneMap (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Original K →+*PlaneRing K:=
 (planeMap K order).comp (flagAlgHom lam mu nu).toRingHom
def flagPlaneDenominators (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Submonoid (Original K):=
 (planeDenominators K order).map (flagEquiv lam mu nu).symm.toMonoidHom
@[reducible] def flagPlaneAlgebra
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Algebra (Original K) (PlaneRing K):=
 (flagPlaneMap K lam mu nu order).toAlgebra
theorem flagPlaneRingLocalization
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   letI:=flagPlaneAlgebra K lam mu nu order
   IsLocalization (flagPlaneDenominators K lam mu nu order) (PlaneRing K):=by
 letI:=planeAlgebra K order
 letI:IsLocalization (planeDenominators K order) (PlaneRing K):=
   planeRingLocalization K order
 exact IsLocalization.isLocalization_of_base_ringEquiv
   (planeDenominators K order) (PlaneRing K)
     (flagEquiv lam mu nu).symm.toRingEquiv
def flagRelationKernel
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=
 relationKernel K (CoordinateField K P) order
   (flagEvaluation K P lam mu nu) ht
theorem flagRelationKernel_contract
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   letI:=flagPlaneAlgebra K lam mu nu order
   (flagRelationKernel K P lam mu nu order ht).comap
     (algebraMap (Original K) (PlaneRing K))=P:=by
 letI:=flagPlaneAlgebra K lam mu nu order
 change (flagRelationKernel K P lam mu nu order ht).comap
     ((planeMap K order).comp (flagAlgHom lam mu nu).toRingHom)=P
 rw [←Ideal.comap_comap,flagRelationKernel,relationKernel_contract,
   flagEvaluation_kernel_contract]
theorem flag_map_surfaceIdeal
   (G:Original K) (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   letI:=flagPlaneAlgebra K lam mu nu order
   Ideal.map (algebraMap (Original K) (PlaneRing K)) (Ideal.span {G})=
     Ideal.span {planeMap K order (flagAlgHom lam mu nu G)}:=by
 letI:=flagPlaneAlgebra K lam mu nu order
 rw [Ideal.map_span]
 simp only [Set.image_singleton]
 rfl
noncomputable def flagSurfaceComponentToPlaneLocalEquiv
   (G:Original K) (P:Ideal (Original K)) [P.IsPrime]
   (hGmem:G∈P) (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   letI:=flagPlaneAlgebra K lam mu nu order
   letI:(flagRelationKernel K P lam mu nu order ht).IsPrime:=
     RingHom.ker_isPrime _
   SourceLocal (Ideal.span {G}) P
       (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem) ≃+*
     TargetLocal (Ideal.span {G}) P
       (flagRelationKernel K P lam mu nu order ht)
       (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem)
       (flagRelationKernel_contract K P lam mu nu order ht):=by
 letI:=flagPlaneAlgebra K lam mu nu order
 letI:IsLocalization (flagPlaneDenominators K lam mu nu order)
     (PlaneRing K):=flagPlaneRingLocalization K lam mu nu order
 letI:(flagRelationKernel K P lam mu nu order ht).IsPrime:=
   RingHom.ker_isPrime _
 exact surfaceLocalEquiv (flagPlaneDenominators K lam mu nu order)
   (Ideal.span {G}) P (flagRelationKernel K P lam mu nu order ht)
   (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem)
   (flagRelationKernel_contract K P lam mu nu order ht)
end
end ProximityPrize.SubmissionLower.RCN113
end PackedLegacy_EC

/-! Packed from ProximityPrize.SubmissionLower.Z1. -/
section PackedLegacy_Z1
namespace ProximityPrize.SubmissionLower.RCN120
open RCN002 RCN011 RCN371 RCN021 RCN022 RCN125 RCN093
noncomputable section
set_option autoImplicit false
@[reducible] def residueAlgebra
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   (q:Polynomial F) (J:Ideal B)
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   Algebra (AdjoinRoot q) (B ⧸ J):=
 (Ideal.quotientMap J (algebraMap (Polynomial F) B) (by rw [hcontract])).toAlgebra'
   (fun _ _ => mul_comm _ _)
theorem quotient_finrank_eq_natDegree_mul_residue_finrank
   {F B:Type*} [Field F] [CommRing B]
   [Algebra F B] [Algebra (Polynomial F) B]
   [IsScalarTower F (Polynomial F) B]
   (q:Polynomial F) (hq:Irreducible q)
   (J:Ideal B) [J.IsMaximal]
   (hcontract:J.comap (algebraMap (Polynomial F) B)=Ideal.span {q}):
   letI:=residueAlgebra q J hcontract
   Module.finrank F (B ⧸ J)=
     q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
 letI:Fact (Irreducible q):=⟨hq⟩
 let aResidue:Algebra (AdjoinRoot q) (B ⧸ J):=
   residueAlgebra q J hcontract
 letI:Algebra (AdjoinRoot q) (B ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (B ⧸ J):=aResidue.toSMul
 let aBase:Algebra F (AdjoinRoot q):=inferInstance
 letI:SMul F (AdjoinRoot q):=aBase.toSMul
 let aTotal:Algebra F (B ⧸ J):=inferInstance
 letI:SMul F (B ⧸ J):=aTotal.toSMul
 letI:IsScalarTower F (AdjoinRoot q) (B ⧸ J):=
   IsScalarTower.of_algebraMap_eq (R:=F) (S:=AdjoinRoot q)
     (A:=B ⧸ J) fun c => by
       change Ideal.Quotient.mk J (algebraMap F B c)=
         Ideal.Quotient.mk J
           (algebraMap (Polynomial F) B (Polynomial.C c))
       apply congrArg (Ideal.Quotient.mk J)
       change algebraMap F B c=algebraMap (Polynomial F) B
         (algebraMap F (Polynomial F) c)
       exact IsScalarTower.algebraMap_apply F (Polynomial F) B c
 letI:Module.Free F (AdjoinRoot q):=
   Module.Free.of_divisionRing F (AdjoinRoot q)
 letI:Module.Free (AdjoinRoot q) (B ⧸ J):=
   Module.Free.of_divisionRing (AdjoinRoot q) (B ⧸ J)
 calc
   Module.finrank F (B ⧸ J)=
       Module.finrank F (AdjoinRoot q)*
         Module.finrank (AdjoinRoot q) (B ⧸ J):=
     (Module.finrank_mul_finrank F (AdjoinRoot q) (B ⧸ J)).symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (B ⧸ J):=by
     rw [show Module.finrank F (AdjoinRoot q)=q.natDegree by
       change Module.finrank F (Polynomial F ⧸ Ideal.span {q})=q.natDegree
       exact finrank_quotient_span_eq_natDegree]
variable (K:Type) [Field K]
@[reducible] def flagBaseAlgebra
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Algebra (RatFunc K) (CoordinateField K P):=
 (elementEmbedding K (CoordinateField K P)
   (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
end
end ProximityPrize.SubmissionLower.RCN120
end PackedLegacy_Z1

/-! Packed from ProximityPrize.SubmissionLower.S. -/
section PackedLegacy_S
namespace ProximityPrize.SubmissionLower.RCN225
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {A:Type*} [CommRing A]
theorem maximalIdeal_pow_succ_lt_pow_of_noetherian_domain
   {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
   [IsLocalRing S]
   (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
   IsLocalRing.maximalIdeal S^(n+1) <
     IsLocalRing.maximalIdeal S^n:=by
 let m:=IsLocalRing.maximalIdeal S
 have hle:m^(n+1) ≤ m^n:=Ideal.pow_le_pow_right n.le_succ
 refine lt_of_le_of_ne hle ?_
 intro heq
 have hfg:(m^n).FG:=IsNoetherian.noetherian _
 have hsmul:m^n ≤ m • (m^n):=by
   rw [Ideal.smul_eq_mul, ←pow_succ', ←heq]
 have hzero:m^n=⊥:=
   Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m (m^n) hfg hsmul
     (IsLocalRing.maximalIdeal_le_jacobson ⊥)
 obtain ⟨x,hx,hx0⟩:=SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hmax)
 have hxpow:x^n∈m^n:=Ideal.pow_mem_pow hx n
 rw [hzero,Ideal.mem_bot] at hxpow
 exact pow_ne_zero n (by simpa only [Ideal.mem_bot] using hx0) hxpow
theorem exponent_le_length_local_maximal_pow_of_noetherian_domain
   {S:Type*} [CommRing S] [IsDomain S] [IsNoetherianRing S]
   [IsLocalRing S]
   (hmax:IsLocalRing.maximalIdeal S≠⊥) (n:ℕ):
   (n:ℕ∞) ≤ Module.length S
     (S ⧸ IsLocalRing.maximalIdeal S^n):=by
 rw [Module.length_quotient]
 induction n with
 | zero => simp
 | succ n ih =>
     calc
       ((n+1:ℕ):ℕ∞)=(n:ℕ∞)+1:=by simp
       _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^n)+1:=
         add_le_add_left ih 1
       _ ≤ Order.coheight (IsLocalRing.maximalIdeal S^(n+1)):=
         Order.coheight_add_one_le
           (maximalIdeal_pow_succ_lt_pow_of_noetherian_domain hmax n)
theorem exponent_mul_residueDegree_le_length_quotient_maximal_pow
   {R S:Type*} [CommRing R] [IsLocalRing R]
   [CommRing S] [IsDomain S] [IsNoetherianRing S] [Algebra R S]
   (p:Ideal S) [p.IsMaximal] (hp:p≠⊥)
   [IsLocalHom (algebraMap R (Localization.AtPrime p))]
   [FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime p))] (n:ℕ):
   ((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime p)):ℕ):ℕ∞) ≤
       Module.length R (S ⧸ p^n):=by
 let L:=Localization.AtPrime p
 let M:=L ⧸ IsLocalRing.maximalIdeal L^n
 have hmaxL:IsLocalRing.maximalIdeal L≠⊥:=by
   intro hbot
   apply hp
   rw [←IsLocalization.AtPrime.under_maximalIdeal L p,hbot]
   exact Ideal.comap_bot_of_injective (algebraMap S L)
     (IsLocalization.injective L p.primeCompl_le_nonZeroDivisors)
 have hlocal:(n:ℕ∞) ≤ Module.length L M:=
   exponent_le_length_local_maximal_pow_of_noetherian_domain hmaxL n
 have hresidue:Module.length (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L)=
       Module.finrank (IsLocalRing.ResidueField R)
         (IsLocalRing.ResidueField L):=Module.length_eq_finrank _ _
 have hweighted:((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L):ℕ):ℕ∞) ≤ Module.length R M:=by
   rw [Nat.cast_mul, ←hresidue,
     IsLocalRing.length_restrictScalars R L M]
   exact mul_le_mul_right' hlocal _
 let e:=IsLocalization.AtPrime.equivQuotMaximalIdealPow p L n
 have heq:Module.length R (S ⧸ p^n)=Module.length R M:=
   (e.toLinearEquiv.restrictScalars R).length_eq
 exact hweighted.trans_eq heq.symm
abbrev SurfaceQuotient (surface:A):=A ⧸ Ideal.span {surface}
theorem exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
   {R:Type*} [CommRing R] [IsLocalRing R] [Algebra R A]
   (surface:A)
   (relation:Ideal A)
   (relationBar:Ideal (SurfaceQuotient surface)) [relationBar.IsMaximal]
   (hrelationBar:relationBar=
     Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) relation)
   [IsDomain (SurfaceQuotient surface)]
   [IsNoetherianRing (SurfaceQuotient surface)]
   (hrelationBarNe:relationBar≠⊥)
   [IsLocalHom (algebraMap R (Localization.AtPrime relationBar))]
   [FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime relationBar))]
   (n:ℕ):
   ((n*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime relationBar)):ℕ):ℕ∞) ≤
     Module.length R (A ⧸ (Ideal.span {surface} ⊔ relation^n)):=by
 let I:Ideal A:=Ideal.span {surface}
 let q:A →ₐ[R] A ⧸ I:=Ideal.Quotient.mkₐ R I
 have hpow:relationBar^n=Ideal.map q (relation^n):=by
   rw [hrelationBar,Ideal.map_pow]
   rfl
 let e₁:(SurfaceQuotient surface ⧸ relationBar^n) ≃ₐ[R]
     (SurfaceQuotient surface ⧸ Ideal.map q (relation^n)):=
   Ideal.quotientEquivAlgOfEq R hpow
 let e₂:(SurfaceQuotient surface ⧸ Ideal.map q (relation^n)) ≃ₐ[R]
     (A ⧸ (I ⊔ relation^n)):=
   DoubleQuot.quotQuotEquivQuotSupₐ R I (relation^n)
 have hlocal:=
   exponent_mul_residueDegree_le_length_quotient_maximal_pow
     (R:=R) relationBar hrelationBarNe n
 exact hlocal.trans_eq (e₁.trans e₂).toLinearEquiv.length_eq
end
end ProximityPrize.SubmissionLower.RCN225
end PackedLegacy_S

/-! Packed from ProximityPrize.SubmissionLower.N. -/
section PackedLegacy_N
namespace ProximityPrize.SubmissionLower.RCN102
open RCN011
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
abbrev FiberCoefficient
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):=
 @Localization.AtPrime (Polynomial (RatFunc Omega)) _ (Ideal.span {q})
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
@[reducible] instance fiberLocalizedPlaneSemiring
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Semiring (Polynomial (FiberCoefficient q hq)):=
 Polynomial.commSemiring.toSemiring
def fiberLocalizePlane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   PlaneRing Omega →+*Polynomial (FiberCoefficient q hq):=
 Polynomial.mapRingHom
   (algebraMap (Polynomial (RatFunc Omega)) (FiberCoefficient q hq))
end
end ProximityPrize.SubmissionLower.RCN102
end PackedLegacy_N

/-! Packed from ProximityPrize.SubmissionLower.Y9. -/
section PackedLegacy_Y9
namespace ProximityPrize.SubmissionLower.RCN106
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN120 RCN102 RCN014 RCN226 RCN225 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
def indexedComponentFactor (a:A):Polynomial (RatFunc Omega):=
 projectedFactor Omega (CoordinateField Omega (component a).1) order
   (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
abbrev IndexedFactorFiber (q:Polynomial (RatFunc Omega)):=
 {a:A//q=indexedComponentFactor component lam mu nu order ht a}
def indexedFiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (Polynomial (FiberCoefficient q hq)):=
 Ideal.map (fiberLocalizePlane q hq)
   (relationKernel Omega (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
def indexedFiberRelationBar
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   Ideal (SurfaceQuotient (fiberLocalizePlane q hq surface)):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {fiberLocalizePlane q hq surface}))
     (indexedFiberRelation component lam mu nu order ht q hq a)
theorem indexedFiberRelation_under
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).comap
     (fiberLocalizePlane q hq)=
       relationKernel Omega (CoordinateField Omega (component a.1).1) order
         (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let f:=fiberLocalizePlane q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) a.property.symm
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing Omega))
       (J:Set (PlaneRing Omega)):=by
   rw [Set.disjoint_left]
   intro x hx hxJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
   exact hr (hcomap ▸ hxJ)
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R)) J).comap
   (algebraMap (PlaneRing Omega) (Polynomial R))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R) hJprime hdisjoint
include hfinite hgen in
theorem indexedFiberRelation_isMaximal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hJmax:J.IsMaximal:=relationKernel_isMaximal Omega
   (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (hfinite a.1) (hgen a.1)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hunder:=indexedFiberRelation_under component lam mu nu order ht q hq a
 letI:((indexedFiberRelation component lam mu nu order ht q hq a).under
     (PlaneRing Omega)).IsMaximal:=by
   change ((indexedFiberRelation component lam mu nu order ht q hq a).comap
     (algebraMap (PlaneRing Omega) (Polynomial R))).IsMaximal
   simpa only [fiberLocalizePlane] using hunder ▸ hJmax
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
include hcomponent in
theorem indexedFiberRelation_injective
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Function.Injective
     (indexedFiberRelation component lam mu nu order ht q hq):=by
 intro a b hab
 have hunder:=congrArg (Ideal.comap (fiberLocalizePlane q hq)) hab
 rw [indexedFiberRelation_under component lam mu nu order ht q hq a,
   indexedFiberRelation_under component lam mu nu order ht q hq b] at hunder
 have heval:=congrArg (Ideal.comap (planeMap Omega order)) hunder
 rw [relationKernel_contract,relationKernel_contract] at heval
 have hprime:=congrArg (Ideal.comap (flagAlgHom lam mu nu).toRingHom) heval
 rw [flagEvaluation_kernel_contract,flagEvaluation_kernel_contract] at hprime
 have hcomp:component a.1=component b.1:=Subtype.ext hprime
 exact Subtype.ext (hcomponent hcomp)
include hcomponent hfinite hgen in
theorem indexedFiberRelation_pairwise_coprime
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Pairwise fun a b:IndexedFactorFiber component lam mu nu order ht q =>
     IsCoprime (indexedFiberRelation component lam mu nu order ht q hq a)
       (indexedFiberRelation component lam mu nu order ht q hq b):=by
 intro a b hab
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
   q hq a).coprime_of_ne
     (indexedFiberRelation_isMaximal component lam mu nu order ht hfinite hgen
       q hq b)
     (fun heq => hab (indexedFiberRelation_injective
       component hcomponent lam mu nu order ht q hq heq))
end
end ProximityPrize.SubmissionLower.RCN106
end PackedLegacy_Y9

/-! Packed from ProximityPrize.SubmissionLower.C8. -/
section PackedLegacy_C8
namespace ProximityPrize.SubmissionLower.RCN193
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN120
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_under
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (localizedRelation K L order e ht hfinite).comap
     (localizePlane K L order e ht hfinite)=
     relationKernel K L order e ht:=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*PlaneRing K:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra (PlaneRing K) (Polynomial Rp):=
   Polynomial.algebra (Polynomial (RatFunc K)) Rp
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom)
     (Polynomial Rp):=Polynomial.isLocalization p.primeCompl Rp
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing K)) (J:Set (PlaneRing K)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   apply hr
   have hrJ:r∈J.comap c:=haJ
   have hcomap:J.comap c=p:=by
     simpa only [J,c,p] using relationKernel_comap_C K L order e ht
   rwa [hcomap] at hrJ
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing K) (Polynomial Rp)) J).comap
   (algebraMap (PlaneRing K) (Polynomial Rp))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial Rp) hJprime hdisjoint
noncomputable def planeResidueEquiv
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   (PlaneRing K ⧸ relationKernel K L order e ht) ≃+*
     (LocalizedPlane K L order e ht hfinite ⧸
       localizedRelation K L order e ht hfinite):=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let f:=localizePlane K L order e ht hfinite
 let c:Polynomial (RatFunc K) →+*S:=Polynomial.C
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 have hJmax:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 letI:J.IsPrime:=hJmax.isPrime
 have hJPmax:JP.IsMaximal:=localizedRelation_isMaximal
   K L order e ht hfinite hgen
 letI:JP.IsPrime:=hJPmax.isPrime
 letI:Algebra (Polynomial (RatFunc K)) Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 letI:Algebra S Sp:=Polynomial.algebra (Polynomial (RatFunc K)) Rp
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) Sp:=
   Polynomial.isLocalization p.primeCompl Rp
 have hunder:JP.comap f=J:=localizedRelation_under K L order e ht hfinite
 have hf:f=algebraMap S Sp:=rfl
 have hunderAlg:JP.under S=J:=by
   change JP.comap (algebraMap S Sp)=J
   rw [←hf]
   exact hunder
 let g:(S ⧸ J) →+*(Sp ⧸ JP):=
   Ideal.quotientMap JP (algebraMap S Sp) hunderAlg.ge
 refine RingEquiv.ofBijective g ⟨?_,?_⟩
 · exact Ideal.quotientMap_injective' hunderAlg.le
 · exact IsLocalization.surjective_quotientMap_of_maximal_of_localization
     (p.primeCompl.map c.toMonoidHom) Sp (J:=J) (I:=JP)
       (H:=hunderAlg.ge) (hunderAlg ▸ hJmax)
@[simp] theorem planeResidueEquiv_mk
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤)
   (x:PlaneRing K):
   planeResidueEquiv K L order e ht hfinite hgen
       (Ideal.Quotient.mk (relationKernel K L order e ht) x)=
     Ideal.Quotient.mk (localizedRelation K L order e ht hfinite)
       (localizePlane K L order e ht hfinite x):=rfl
theorem maximalIdeal_le_localizedRelation_comap_C
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite) ≤
     (localizedRelation K L order e ht hfinite).comap Polynomial.C:=by
 let C:=Polynomial (RatFunc K)
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let a:C →+*Rp:=algebraMap C Rp
 let c:C →+*S:=Polynomial.C
 let cL:Rp →+*Sp:=Polynomial.C
 let f:S →+*Sp:=localizePlane K L order e ht hfinite
 have hpmax:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 letI:p.IsPrime:=hpmax.isPrime
 letI:Algebra C Rp:=inferInstance
 letI:IsLocalization p.primeCompl Rp:=inferInstance
 have hcontract:J.comap c=p:=by
   simpa only [J,c,p] using relationKernel_comap_C K L order e ht
 have hsquare:cL.comp a=f.comp c:=by
   apply DFunLike.ext _ _
   intro x
   change Polynomial.C (a x)=Polynomial.map a (Polynomial.C x)
   rw [Polynomial.map_C]
 rw [←IsLocalization.AtPrime.map_eq_maximalIdeal p Rp,
   ←Ideal.map_le_iff_le_comap]
 calc
   Ideal.map cL (Ideal.map a p)=Ideal.map (cL.comp a) p:=
     Ideal.map_map a cL
   _=Ideal.map (f.comp c) p:=by
     rw [hsquare]
   _=Ideal.map f (Ideal.map c p):=(Ideal.map_map c f).symm
   _ ≤ Ideal.map f J:=Ideal.map_mono
     (Ideal.map_le_iff_le_comap.mpr hcontract.ge)
   _=JP:=rfl
@[reducible] def localizedResidueAlgebra
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   Algebra
     (LocalCoefficient K L order e ht hfinite ⧸
       IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
     (LocalizedPlane K L order e ht hfinite ⧸
       localizedRelation K L order e ht hfinite):=
 Ideal.Quotient.algebraQuotientOfLEComap
   (maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite)
noncomputable def coefficientResidueEquiv
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   AdjoinRoot (projectedFactor K L order e ht) ≃+*
     (LocalCoefficient K L order e ht hfinite ⧸
       IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite)):=by
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 letI:p.IsMaximal:=coeffPrime_isMaximal K L order e ht hfinite
 change (Polynomial (RatFunc K) ⧸ p) ≃+*
   (Rp ⧸ IsLocalRing.maximalIdeal Rp)
 exact IsLocalization.AtPrime.equivQuotMaximalIdeal p Rp
@[simp] theorem coefficientResidueEquiv_mk
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (x:Polynomial (RatFunc K)):
   coefficientResidueEquiv K L order e ht hfinite
       (AdjoinRoot.mk (projectedFactor K L order e ht) x)=
     Ideal.Quotient.mk
       (IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite))
       (algebraMap (Polynomial (RatFunc K))
         (LocalCoefficient K L order e ht hfinite) x):=rfl
end
end ProximityPrize.SubmissionLower.RCN193
end PackedLegacy_C8

/-! Packed from ProximityPrize.SubmissionLower.M0. -/
section PackedLegacy_M0
namespace ProximityPrize.SubmissionLower.RCN194
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN120 RCN193
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localized_residue_finrank_eq
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let q:=projectedFactor K L order e ht
   let J:=relationKernel K L order e ht
   let JP:=localizedRelation K L order e ht hfinite
   let a₀:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
   letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a₀
   letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a₀.toSMul
   let s₀:Semiring (PlaneRing K ⧸ J):=inferInstance
   letI:AddCommMonoid (PlaneRing K ⧸ J):=s₀.toAddCommMonoid
   letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
   let a₁:=localizedResidueAlgebra K L order e ht hfinite
   let Rp:=LocalCoefficient K L order e ht hfinite
   let Sp:=LocalizedPlane K L order e ht hfinite
   letI:Algebra (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁
   letI:SMul (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁.toSMul
   let r₁:CommRing (Rp ⧸ IsLocalRing.maximalIdeal Rp):=inferInstance
   letI:Semiring (Rp ⧸ IsLocalRing.maximalIdeal Rp):=r₁.toSemiring
   let s₁:Semiring (Sp ⧸ JP):=inferInstance
   letI:AddCommMonoid (Sp ⧸ JP):=s₁.toAddCommMonoid
   letI:Module (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=Algebra.toModule
   Module.finrank (AdjoinRoot q) (PlaneRing K ⧸ J)=
     Module.finrank (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=by
 let q:=projectedFactor K L order e ht
 let p:=CoeffPrime K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let S:=PlaneRing K
 let Sp:=LocalizedPlane K L order e ht hfinite
 let J:=relationKernel K L order e ht
 let JP:=localizedRelation K L order e ht hfinite
 let a₀:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (S ⧸ J):=a₀
 letI:SMul (AdjoinRoot q) (S ⧸ J):=a₀.toSMul
 let sr₀:Semiring (S ⧸ J):=inferInstance
 letI:AddCommMonoid (S ⧸ J):=sr₀.toAddCommMonoid
 letI:Module (AdjoinRoot q) (S ⧸ J):=Algebra.toModule
 let a₁:=localizedResidueAlgebra K L order e ht hfinite
 letI:Algebra (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁
 letI:SMul (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=a₁.toSMul
 let r₁:CommRing (Rp ⧸ IsLocalRing.maximalIdeal Rp):=inferInstance
 letI:Semiring (Rp ⧸ IsLocalRing.maximalIdeal Rp):=r₁.toSemiring
 let sr₁:Semiring (Sp ⧸ JP):=inferInstance
 letI:AddCommMonoid (Sp ⧸ JP):=sr₁.toAddCommMonoid
 letI:Module (Rp ⧸ IsLocalRing.maximalIdeal Rp) (Sp ⧸ JP):=Algebra.toModule
 let i:=coefficientResidueEquiv K L order e ht hfinite
 let j:=planeResidueEquiv K L order e ht hfinite hgen
 apply Algebra.finrank_eq_of_equiv_equiv i j
 apply DFunLike.ext _ _
 intro x
 obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
 change Ideal.Quotient.mk JP
     (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
   Ideal.Quotient.mk JP
     (localizePlane K L order e ht hfinite (Polynomial.C x))
 apply congrArg (Ideal.Quotient.mk JP)
 change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
   Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
 rw [Polynomial.map_C]
end
end ProximityPrize.SubmissionLower.RCN194
end PackedLegacy_M0

/-! Packed from ProximityPrize.SubmissionLower.D7. -/
section PackedLegacy_D7
open LinearMap Pointwise Ideal WithZero
variable {R:Type*} {M:Type*} [AddCommMonoid M]
namespace Ring
variable (R) [Ring R]
noncomputable def ord (x:R):ℕ∞:=Module.length R (R ⧸ Ideal.span {x})
@[simp] lemma ord_one:ord R 1=0:=by
 simp_all [ord,Ideal.span_singleton_one,Submodule.Quotient.subsingleton_iff]
end Ring
variable [CommRing R] [Module R M]
def Ideal.mulQuot (a:R) (I:Ideal R):
   R ⧸ I →ₗ[R] R ⧸ (a • I):=
 Submodule.mapQ _ _ (LinearMap.mul R R a) (Submodule.le_comap_map _ _)
lemma Ideal.mulQuot_injective {a:R} (I:Ideal R) (ha:a∈nonZeroDivisors R):
   Function.Injective (Ideal.mulQuot a I):=by
 simp only [mulQuot,Submodule.mapQ, ←ker_eq_bot]
 apply Submodule.ker_liftQ_eq_bot'
 apply le_antisymm
 · have:Submodule.map (mul R R a) I=a • I:=rfl
   rw [le_ker_iff_map,Submodule.map_comp,this,Submodule.mkQ_map_self]
 · have m:I=Submodule.comap (mul R R a) (a • I):=by
     ext b
     exact (Submodule.mul_mem_smul_iff ha).symm
   simp [←m,ker_comp]
def Ideal.quotOfMul (a:R) (I:Ideal R):
   (R ⧸ a • I) →ₗ[R] (R ⧸ Ideal.span {a}):=
 Submodule.factor <| Submodule.singleton_set_smul I a ▸ Submodule.smul_le_span {a} I
lemma Ideal.quotOfMul_surjective {a:R} (I:Ideal R):
   Function.Surjective (Ideal.quotOfMul a I):=by
 simp only [Ideal.quotOfMul]
 exact Submodule.factor_surjective <|
   Submodule.singleton_set_smul I a ▸ Submodule.smul_le_span {a} I
lemma Ideal.exact_mulQuot_quotOfMul {a:R} (I:Ideal R):
   Function.Exact (Ideal.mulQuot a I) (Ideal.quotOfMul a I):=by
 simp only [exact_iff]
 have:ker (Ideal.quotOfMul a I)=a • ⊤:=by
   simp only [←submodule_span_eq,quotOfMul,Submodule.factor,Submodule.mapQ,comp_id,
     Submodule.ker_liftQ,Submodule.ker_mkQ,Submodule.map_span,Submodule.mkQ_apply,
     Quotient.mk_eq_mk,Set.image_singleton,Quotient.smul_top]
 simp [this,Ideal.mulQuot,Submodule.mapQ.eq_1,Submodule.range_liftQ,
   range_comp,Ideal.Quotient.smul_top, ←Ideal.submodule_span_eq,LinearMap.map_span]
namespace Ring
variable (R)
theorem ord_mul {a b:R} (hb:b∈nonZeroDivisors R):
   ord R (a*b)=ord R a+ord R b:=by
 have hlen:=Module.length_eq_add_of_exact (Ideal.mulQuot b (Ideal.span {a}))
     (Ideal.quotOfMul b (Ideal.span {a}))
     (Ideal.mulQuot_injective (Ideal.span {a}) hb)
     (Ideal.quotOfMul_surjective (Ideal.span {a}))
     (Ideal.exact_mulQuot_quotOfMul (Ideal.span {a}))
 simp only [Ring.ord, ←hlen]
 have lem:(({b}:Set R) • Ideal.span {a})=Ideal.span {b*a}:=by
   simp [←Ideal.submodule_span_eq,Submodule.set_smul_span]
 have hs:(({b}:Set R) • Ideal.span {a})=b • Ideal.span {a}:=
   Submodule.singleton_set_smul (Ideal.span {a}) b
 rw [hs] at lem
 rw [lem,mul_comm]
lemma ord_mul' {a b:R} (ha:a∈nonZeroDivisors R):
   ord R (a*b)=ord R a+ord R b:=by
 rw [mul_comm,ord_mul R ha,add_comm]
variable {R}
@[simp] theorem ord_pow {x:R} (hx:x∈nonZeroDivisors R) (n:ℕ):
   ord R (x^n)=n • ord R x:=by
 induction n with
 | zero => simp
 | succ n ih =>
   rw [pow_succ,ord_mul,ih,succ_nsmul]
   exact hx
@[simp] lemma ord_mul_of_isUnit_left {a:R} (h:IsUnit a) (x:R):
   ord R (a*x)=ord R x:=by
 rw [ord,ord,Ideal.span_singleton_mul_left_unit h x]
@[simp] lemma ord_mul_of_isUnit_right {a:R} (h:IsUnit a) (x:R):
   ord R (x*a)=ord R x:=by
 rw [ord,ord,Ideal.span_singleton_mul_right_unit h x]
lemma ord_eq_of_associated {x y:R} (h:Associated x y):ord R x=ord R y:=by
 obtain ⟨a,rfl⟩:=h
 simp
@[simp] lemma ord_smul_of_isUnit {S:Type*} [CommRing S] [Algebra S R]
   {a:S} (h:IsUnit a) (x:R):ord R (a • x)=ord R x:=by
 rw [Algebra.smul_def a x]
 exact ord_mul_of_isUnit_left (RingHom.isUnit_map (algebraMap S R) h) x
@[simp] lemma ord_of_isUnit {x:R} (hx:IsUnit x):ord R x=0:=by
 simpa using ord_smul_of_isUnit hx (1:R)
section IsPrincipalIdealRing
variable [IsPrincipalIdealRing R]
theorem ord_of_irreducible {ϖ:R} (hϖ:Irreducible ϖ):ord R ϖ=1:=by
 rw [Ring.ord,Module.length_eq_one_iff]
 have:(Ideal.span {ϖ}).IsMaximal:=
   PrincipalIdealRing.isMaximal_of_irreducible hϖ
 rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
   (S:=R ⧸ Ideal.span {ϖ}) Ideal.Quotient.mk_surjective]
 letI:=Ideal.Quotient.field (Ideal.span {ϖ})
 exact instIsSimpleModule _
end IsPrincipalIdealRing
end Ring
end PackedLegacy_D7

/-! Packed from ProximityPrize.SubmissionLower.M2. -/
section PackedLegacy_M2
namespace ProximityPrize.SubmissionLower.RCN196
open scoped Classical BigOperators
open Module
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R M ι:Type*}
 [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
private theorem ord_finset_prod
   (a:ι → R) (ha:∀ i,a i≠0):
   Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=by
 classical
 let s:Finset ι:=Finset.univ
 change Ring.ord R (∏ i∈s,a i)=∑ i∈s,Ring.ord R (a i)
 induction s using Finset.induction_on with
 | empty => simp
 | @insert i s hi ih =>
     rw [Finset.prod_insert hi,Finset.sum_insert hi,
       Ring.ord_mul' (R:=R)
         (mem_nonZeroDivisors_iff_ne_zero.mpr (ha i)),ih]
theorem associated_det_prod_smithRange
   (b:Basis ι R M) (f:M →ₗ[R] M) (hinj:Function.Injective f):
   Associated (LinearMap.det f)
     (∏ i,(LinearMap.range f).smithNormalFormCoeffs b
       (f.finrank_range_of_inj hinj) i):=by
 classical
 let N:Submodule R M:=LinearMap.range f
 let hrank:Module.finrank R N=Module.finrank R M:=
   f.finrank_range_of_inj hinj
 let bM:Basis ι R M:=N.smithNormalFormTopBasis b hrank
 let bN:Basis ι R N:=N.smithNormalFormBotBasis b hrank
 let a:ι → R:=N.smithNormalFormCoeffs b hrank
 let eActual:M ≃ₗ[R] N:=LinearEquiv.ofInjective f hinj
 let eSmith:M ≃ₗ[R] N:=bM.equiv bN (Equiv.refl ι)
 let g:M →ₗ[R] M:=N.subtype.comp eSmith.toLinearMap
 have hmatrix:LinearMap.toMatrix bM bM g=Matrix.diagonal a:=by
   ext i j
   simp only [LinearMap.toMatrix_apply,g,LinearMap.comp_apply,
     LinearEquiv.coe_coe,eSmith,Basis.equiv_apply,Equiv.refl_apply]
   have hsnf:((bN j:N):M)=a j • bM j:=by
     exact N.smithNormalFormBotBasis_def b hrank j
   change bM.repr ((bN j:N):M) i=
     if i=j then a i else 0
   rw [hsnf,map_smul,Basis.repr_self,Finsupp.smul_single]
   by_cases hij:i=j
   · subst j
     simp
   · simp [Finsupp.single_apply,hij]
 have hdetg:LinearMap.det g=∏ i,a i:=by
   calc
     LinearMap.det g=(LinearMap.toMatrix bM bM g).det:=
       (LinearMap.det_toMatrix bM g).symm
     _=(Matrix.diagonal a).det:=by rw [hmatrix]
     _=∏ i,a i:=Matrix.det_diagonal
 have hassoc:Associated (LinearMap.det f) (LinearMap.det g):=by
   have h:=LinearMap.associated_det_comp_equiv N.subtype eActual eSmith
   have heActual:N.subtype.comp eActual.toLinearMap=f:=by
     ext z
     exact LinearEquiv.ofInjective_apply (h:=hinj) f z
   rw [heActual] at h
   exact h
 simpa only [N,hrank,a,hdetg] using hassoc
theorem length_coker_eq_ord_det
   (b:Basis ι R M) (f:M →ₗ[R] M)
   (hinj:Function.Injective f):
   Module.length R (M ⧸ LinearMap.range f)=Ring.ord R (LinearMap.det f):=by
 classical
 let N:Submodule R M:=LinearMap.range f
 let hrank:Module.finrank R N=Module.finrank R M:=
   f.finrank_range_of_inj hinj
 let a:ι → R:=N.smithNormalFormCoeffs b hrank
 have ha:∀ i,a i≠0:=fun i => N.smithNormalFormCoeffs_ne_zero b hrank i
 have hdecomp:Module.length R (M ⧸ N)=
     ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=by
   rw [(N.quotientEquivPiSpan b hrank).length_eq,
     Module.length_pi_of_fintype R]
 have hprod:Ring.ord R (∏ i,a i)=∑ i,Ring.ord R (a i):=
   ord_finset_prod a ha
 have hassoc:Associated (LinearMap.det f) (∏ i,a i):=by
   simpa only [N,hrank,a] using associated_det_prod_smithRange b f hinj
 change Module.length R (M ⧸ N)=_
 calc
   Module.length R (M ⧸ N)=
       ∑ i,Module.length R (R ⧸ Ideal.span ({a i}:Set R)):=hdecomp
   _=∑ i,Ring.ord R (a i):=rfl
   _=Ring.ord R (∏ i,a i):=hprod.symm
   _=Ring.ord R (LinearMap.det f):=
     (Ring.ord_eq_of_associated hassoc).symm
section TwoModules
variable {N:Type*} [AddCommGroup N] [Module R N]
theorem length_coker_eq_ord_toMatrix_det
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M →ₗ[R] N) (hinj:Function.Injective f):
   Module.length R (N ⧸ LinearMap.range f)=
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 classical
 let e:N ≃ₗ[R] M:=bN.equiv bM (Equiv.refl ι)
 let g:N →ₗ[R] N:=f.comp e.toLinearMap
 have hginj:Function.Injective g:=hinj.comp e.injective
 have hrange:LinearMap.range g=LinearMap.range f:=by
   change LinearMap.range (f.comp e.toLinearMap)=LinearMap.range f
   rw [LinearMap.range_comp_of_range_eq_top f e.range]
 have hmatrix:LinearMap.toMatrix bN bN g=
     LinearMap.toMatrix bM bN f:=by
   change LinearMap.toMatrix bN bN (f.comp e.toLinearMap)=_
   rw [LinearMap.toMatrix_comp bN bM bN,
     LinearMap.toMatrix_basis_equiv,Matrix.mul_one]
 calc
   Module.length R (N ⧸ LinearMap.range f)=
       Module.length R (N ⧸ LinearMap.range g):=by rw [hrange]
   _=Ring.ord R (LinearMap.det g):=length_coker_eq_ord_det bN g hginj
   _=Ring.ord R (LinearMap.toMatrix bN bN g).det:=by
     rw [LinearMap.det_toMatrix]
   _=Ring.ord R (LinearMap.toMatrix bM bN f).det:=by rw [hmatrix]
theorem sum_multiplicities_le_ord_toMatrix_det_of_surjective
   {J:Type*} [Fintype J]
   (bM:Basis ι R M) (bN:Basis ι R N)
   (f:M →ₗ[R] N) (hinj:Function.Injective f)
   (pieces:J → Type*)
   [∀ j,AddCommGroup (pieces j)] [∀ j,Module R (pieces j)]
   (multiplicity:J → ℕ)
   (hlength:∀ j,(multiplicity j:ℕ∞) ≤ Module.length R (pieces j))
   (project:(N ⧸ LinearMap.range f) →ₗ[R] (∀ j,pieces j))
   (hsurj:Function.Surjective project):
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
     Ring.ord R (LinearMap.toMatrix bM bN f).det:=by
 rw [←length_coker_eq_ord_toMatrix_det bM bN f hinj]
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞)=
       ∑ j,(multiplicity j:ℕ∞):=by simp
   _ ≤ ∑ j,Module.length R (pieces j):=
     Finset.sum_le_sum (fun j _ => hlength j)
   _=Module.length R (∀ j,pieces j):=
     (Module.length_pi_of_fintype R pieces).symm
   _ ≤ Module.length R (N ⧸ LinearMap.range f):=
     Module.length_le_of_surjective project hsurj
end TwoModules
end
end ProximityPrize.SubmissionLower.RCN196
end PackedLegacy_M2

/-! Packed from ProximityPrize.SubmissionLower.CE. -/
section PackedLegacy_CE
namespace ProximityPrize.SubmissionLower.RCN307
noncomputable section
set_option autoImplicit false
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
def intersectionIdeal (P Q:Polynomial R):Ideal (Polynomial R):=
 Ideal.span {P,Q}
structure PrimaryPiecesCertificate
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (multiplicity:J → ℕ) where
 pieces:J → Ideal (Polynomial R)
 coprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j)
 contains:∀ j,intersectionIdeal P Q ≤ pieces j
 length_le:∀ j,(multiplicity j:ℕ∞) ≤
   Module.length R (Polynomial R ⧸ pieces j)
end
end ProximityPrize.SubmissionLower.RCN307
end PackedLegacy_CE

/-! Packed from ProximityPrize.SubmissionLower.CF. -/
section PackedLegacy_CF
namespace ProximityPrize.SubmissionLower.RCN309
open scoped Classical BigOperators
open Module RCN196 RCN307
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
theorem moduleFinite_quotient_of_monic_mem
   (I:Ideal (Polynomial R)) (M:Polynomial R)
   (hMMonic:M.Monic) (hMmem:M∈I):
   Module.Finite R (Polynomial R ⧸ I):=by
 let hle:Ideal.span {M} ≤ I:=Ideal.span_le.mpr (by simpa)
 let f:(Polynomial R ⧸ Ideal.span {M}) →ₐ[R]
     (Polynomial R ⧸ I):=Ideal.Quotient.factorₐ R hle
 letI:Module.Finite R (Polynomial R ⧸ Ideal.span {M}):=
   hMMonic.finite_quotient
 exact Module.Finite.of_surjective f.toLinearMap
   (Ideal.Quotient.factor_surjective hle)
def rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R)):
   Polynomial.degreeLT R (m+n) →ₗ[R]
     (∀ j,Polynomial R ⧸ pieces j):=
 LinearMap.pi fun j↦
   ((Submodule.mkQ (pieces j)).restrictScalars R).comp
     (Submodule.subtype (Polynomial.degreeLT R (m+n)))
theorem range_sylvesterMap_le_ker_rawPiecesMap
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap) ≤
     LinearMap.ker (rawPiecesMap P Q m n pieces):=by
 rintro y ⟨v,rfl⟩
 rw [LinearMap.mem_ker]
 funext j
 apply Ideal.Quotient.eq_zero_iff_mem.mpr
 apply hcontains j
 change P*(v.2:Polynomial R)+Q*(v.1:Polynomial R)∈
   intersectionIdeal P Q
 exact Ideal.add_mem _
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert P {Q})))
   (Ideal.mul_mem_right _ _
     (Ideal.subset_span (Set.mem_insert_of_mem P (Set.mem_singleton Q))))
def cokerToPieces
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j):
   (Polynomial.degreeLT R (m+n) ⧸
     LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)) →ₗ[R]
       (∀ j,Polynomial R ⧸ pieces j):=
 (LinearMap.range (Polynomial.sylvesterMap P Q hPcap hQcap)).liftQ
   (rawPiecesMap P Q m n pieces)
   (range_sylvesterMap_le_ker_rawPiecesMap
     P Q m n hPcap hQcap pieces hcontains)
theorem cokerToPieces_surjective_of_modMax
   [IsLocalRing R]
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces))):
   Function.Surjective
     (cokerToPieces P Q m n hPcap hQcap pieces hcontains):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hraw:Function.Surjective (rawPiecesMap P Q m n pieces):=by
   apply LinearMap.surjective_of_surjective_comp_mkQ
     (rawPiecesMap P Q m n pieces) (IsLocalRing.maximalIdeal R)
     (IsLocalRing.maximalIdeal_le_jacobson ⊥)
   exact hmod
 intro y
 obtain ⟨v,hv⟩:=hraw y
 refine ⟨Submodule.Quotient.mk v,?_⟩
 change rawPiecesMap P Q m n pieces v=y
 exact hv
end
end ProximityPrize.SubmissionLower.RCN309
end PackedLegacy_CF

/-! Packed from ProximityPrize.SubmissionLower.C9. -/
section PackedLegacy_C9
namespace ProximityPrize.SubmissionLower.RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [IsLocalRing R]
@[reducible] def relationResidueAlgebra
   (J:Ideal (Polynomial R))
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R):
   Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
 (Ideal.quotientMap J (Polynomial.C:R →+*Polynomial R) (by
   rw [hcontract])).toAlgebra' (fun _ _ => mul_comm _ _)
theorem exists_monic_mem_maximal_relation
   (J:Ideal (Polynomial R)) [J.IsMaximal]
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hfinite:
     letI:=relationResidueAlgebra J hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ J)):
   ∃ H:Polynomial R,H.Monic∧H∈J:=by
 let k:=IsLocalRing.ResidueField R
 let E:=Polynomial R ⧸ J
 let qR:R →+*k:=Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
 let qB:Polynomial R →+*E:=Ideal.Quotient.mk J
 let aResidue:=relationResidueAlgebra J hcontract
 letI:Algebra k E:=aResidue
 let phi:k →+*E:=algebraMap k E
 letI:FiniteDimensional k E:=hfinite
 let y:E:=qB Polynomial.X
 let hbar:Polynomial k:=minpoly k y
 have hbarMonic:hbar.Monic:=
   minpoly.monic (IsIntegral.of_finite k y)
 have hbarLift:hbar∈Polynomial.lifts qR:=
   Polynomial.mem_lifts_of_surjective Ideal.Quotient.mk_surjective hbar
 obtain ⟨H,hmap,hdegree,hHMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hbarLift hbarMonic
 have hcomp:(Polynomial.eval₂RingHom phi y).comp
     (Polynomial.mapRingHom qR)=qB:=by
   apply Polynomial.ringHom_ext
   · intro r
     simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_C,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
     change Ideal.Quotient.mk J (Polynomial.C r)=qB (Polynomial.C r)
     rfl
   · simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,
       Polynomial.map_X,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
     rfl
 have hHmem:H∈J:=by
   apply Ideal.Quotient.eq_zero_iff_mem.mp
   change qB H=0
   rw [←hcomp]
   change Polynomial.eval₂ phi y (H.map qR)=0
   rw [hmap]
   change Polynomial.aeval y hbar=0
   exact minpoly.aeval k y
 exact ⟨H,hHMonic,hHmem⟩
theorem moduleFinite_primary_piece_of_maximal_relation
   (J:Ideal (Polynomial R)) [J.IsMaximal]
   (hcontract:J.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hfinite:
     letI:=relationResidueAlgebra J hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ J))
   (piece:Ideal (Polynomial R)) (mu:ℕ)
   (hpow:J^mu ≤ piece):
   Module.Finite R (Polynomial R ⧸ piece):=by
 obtain ⟨H,hHMonic,hHJ⟩:=
   exists_monic_mem_maximal_relation J hcontract hfinite
 exact RCN309.moduleFinite_quotient_of_monic_mem
   piece (H^mu) (hHMonic.pow mu) (hpow (Ideal.pow_mem_pow hHJ mu))
end
end ProximityPrize.SubmissionLower.RCN197
end PackedLegacy_C9

/-! Packed from ProximityPrize.SubmissionLower.L9. -/
section PackedLegacy_L9
namespace ProximityPrize.SubmissionLower.RCN192
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN193 RCN120 RCN014 RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localizedRelation_comap_C_eq_maximalIdeal
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L):
   (localizedRelation K L order e ht hfinite).comap Polynomial.C=
     IsLocalRing.maximalIdeal (LocalCoefficient K L order e ht hfinite):=by
 apply le_antisymm
 · apply IsLocalRing.le_maximalIdeal
   apply Ideal.comap_ne_top
   intro htop
   have hunder:=localizedRelation_under K L order e ht hfinite
   have hJne:relationKernel K L order e ht≠⊤:=RingHom.ker_ne_top _
   apply hJne
   rw [←hunder,htop,Ideal.comap_top]
 · exact maximalIdeal_le_localizedRelation_comap_C K L order e ht hfinite
theorem localizedRelationResidue_finite
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=
     targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   FiniteDimensional (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=by
 let F:=RatFunc K
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:Algebra F L:=
   (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
 letI:FiniteDimensional F L:=hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let quotientSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=quotientSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 let phi:PlaneRing K →ₐ[F] L:={
   toRingHom:=planeEvaluation K L order e ht
   commutes':=fun a => by
     change planeEvaluation K L order e ht
       (Polynomial.C (Polynomial.C a))=algebraMap F L a
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) hgen
 let eqv0:(PlaneRing K ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing K ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 letI:Module.Finite F (PlaneRing K ⧸ J):=
   Module.Finite.equiv eqv0.toLinearEquiv.symm
 letI:IsScalarTower F (AdjoinRoot q) (PlaneRing K ⧸ J):=
   IsScalarTower.of_algebraMap_eq fun c => by
     change Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))=
       Ideal.Quotient.mk J (Polynomial.C (Polynomial.C c))
     rfl
 letI:Module.Finite (AdjoinRoot q) (PlaneRing K ⧸ J):=
   Module.Finite.of_restrictScalars_finite F _ _
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 refine Module.Finite.of_equiv_equiv
   (A₁:=AdjoinRoot q) (B₁:=PlaneRing K ⧸ J)
   (A₂:=IsLocalRing.ResidueField Rp)
   (B₂:=LocalizedPlane K L order e ht hfinite ⧸ JP) e1 e2 ?_
 apply RingHom.ext
 intro x
 obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
 change Ideal.Quotient.mk JP
     (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
   Ideal.Quotient.mk JP
     (localizePlane K L order e ht hfinite (Polynomial.C x))
 apply congrArg (Ideal.Quotient.mk JP)
 change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
   Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
 rw [Polynomial.map_C]
theorem localizedRelationResidue_finrank_eq_unlocalized
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (hgen:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     IntermediateField.adjoin (RatFunc K)
       ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤):
   let q:=projectedFactor K L order e ht
   let J:=relationKernel K L order e ht
   let Rp:=LocalCoefficient K L order e ht hfinite
   let JP:=localizedRelation K L order e ht hfinite
   let hcontract:=localizedRelation_comap_C_eq_maximalIdeal
     K L order e ht hfinite
   let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
   letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
   letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
   let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
   letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
   letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
   let a1:=relationResidueAlgebra JP hcontract
   letI:Algebra (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
   letI:SMul (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
   let targetSemiring:Semiring
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
   letI:AddCommMonoid
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
   Module.finrank (IsLocalRing.ResidueField Rp)
       (LocalizedPlane K L order e ht hfinite ⧸ JP)=
     Module.finrank (AdjoinRoot q) (PlaneRing K ⧸ J):=by
 let q:=projectedFactor K L order e ht
 let J:=relationKernel K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let JP:=localizedRelation K L order e ht hfinite
 letI:J.IsMaximal:=relationKernel_isMaximal K L order e ht hfinite hgen
 let a0:=residueAlgebra q J (relationKernel_comap_C K L order e ht)
 letI:Algebra (AdjoinRoot q) (PlaneRing K ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing K ⧸ J):=a0.toSMul
 let sourceSemiring:Semiring (PlaneRing K ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing K ⧸ J):=sourceSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing K ⧸ J):=Algebra.toModule
 have hcontract:=localizedRelation_comap_C_eq_maximalIdeal
   K L order e ht hfinite
 let a1:=relationResidueAlgebra JP hcontract
 letI:Algebra (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1
 letI:SMul (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=a1.toSMul
 let targetSemiring:Semiring
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=inferInstance
 letI:AddCommMonoid (LocalizedPlane K L order e ht hfinite ⧸ JP):=
   targetSemiring.toAddCommMonoid
 letI:Module (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP):=Algebra.toModule
 let e1:=coefficientResidueEquiv K L order e ht hfinite
 let e2:=planeResidueEquiv K L order e ht hfinite hgen
 have hcompat:(algebraMap (IsLocalRing.ResidueField Rp)
     (LocalizedPlane K L order e ht hfinite ⧸ JP)).comp e1.toRingHom=
     e2.toRingHom.comp (algebraMap (AdjoinRoot q) (PlaneRing K ⧸ J)):=by
   apply RingHom.ext
   intro x
   obtain ⟨x,rfl⟩:=AdjoinRoot.mk_surjective x
   change Ideal.Quotient.mk JP
       (Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x))=
     Ideal.Quotient.mk JP
       (localizePlane K L order e ht hfinite (Polynomial.C x))
   apply congrArg (Ideal.Quotient.mk JP)
   change Polynomial.C (algebraMap (Polynomial (RatFunc K)) Rp x)=
     Polynomial.map (algebraMap (Polynomial (RatFunc K)) Rp) (Polynomial.C x)
   rw [Polynomial.map_C]
 exact (Algebra.finrank_eq_of_equiv_equiv e1 e2 hcompat).symm
end
end ProximityPrize.SubmissionLower.RCN192
end PackedLegacy_L9

/-! Packed from ProximityPrize.SubmissionLower.FP. -/
section PackedLegacy_FP
namespace ProximityPrize.SubmissionLower.RCN236
open RCN014 RCN225 RCN307
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 {J:Type*} [Fintype J]
noncomputable def primaryPiecesCertificateOfMembershipWeighted
   [IsLocalRing R]
   (surface tail:Polynomial R)
   [hSurfacePrime:(Ideal.span {surface}).IsPrime]
   (relation:J → Ideal (Polynomial R))
   (relationBar:J → Ideal (SurfaceQuotient surface))
   [∀ j,(relationBar j).IsMaximal]
   [IsNoetherianRing (SurfaceQuotient surface)]
   (hrelationBar:∀ j,relationBar j=
     Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) (relation j))
   (hrelationBarNe:∀ j,relationBar j≠⊥)
   [∀ j,IsLocalHom
     (algebraMap R (Localization.AtPrime (relationBar j)))]
   [∀ j,FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))]
   (mu:J → ℕ)
   (htail:∀ j,tail∈Ideal.span {surface} ⊔ relation j^mu j)
   (hcoprime:Pairwise fun i j↦IsCoprime (relation i) (relation j)):
   PrimaryPiecesCertificate surface tail (fun j↦
     mu j*Module.finrank (IsLocalRing.ResidueField R)
       (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j)))) where
 pieces j:=mappedPrimaryPiece (RingHom.id (Polynomial R)) relation
   surface mu j
 coprime:=mappedPrimaryPiece_pairwise_coprime
   (RingHom.id (Polynomial R)) relation hcoprime surface mu
 contains j:=by
   apply span_pair_le_mappedPrimaryPiece
     (RingHom.id (Polynomial R)) relation surface tail mu j
   simpa only [mappedPrimaryPiece,Ideal.map_id] using htail j
 length_le j:=by
   have hmap:Ideal.map (RingHom.id (Polynomial R)) (relation j)=relation j:=
     Ideal.map_id (relation j)
   have hbound:=
     exponent_mul_residueDegree_le_length_span_surface_sup_relation_pow
       (R:=R) surface (relation j) (relationBar j)
         (hrelationBar j) (hrelationBarNe j) (mu j)
   change ((mu j*Module.finrank (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField (Localization.AtPrime (relationBar j))):ℕ):ℕ∞) ≤
       Module.length R (Polynomial R ⧸ (Ideal.span {surface} ⊔
         Ideal.map (RingHom.id (Polynomial R)) (relation j)^mu j))
   rw [hmap]
   exact hbound
end
end ProximityPrize.SubmissionLower.RCN236
end PackedLegacy_FP

/-! Packed from ProximityPrize.SubmissionLower.C3. -/
section PackedLegacy_C3
namespace ProximityPrize.SubmissionLower.RCN107
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN120 RCN102 RCN106 RCN192 RCN197 RCN236 RCN307 RCN225 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
abbrev indexedFiberSurface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega):Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq surface
abbrev indexedFiberTail
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (tail:PlaneRing Omega):Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq tail
include hfinite hgen in
theorem indexedFiberRelationBar_isMaximal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=by
 let J:=indexedFiberRelation component lam mu nu order ht q hq a
 let quotientMap:=Ideal.Quotient.mk
   (Ideal.span {indexedFiberSurface q hq surface})
 letI:J.IsMaximal:=indexedFiberRelation_isMaximal
   component lam mu nu order ht hfinite hgen q hq a
 apply Ideal.IsMaximal.map_of_surjective_of_ker_le
   (f:=quotientMap) Ideal.Quotient.mk_surjective
 rw [Ideal.mk_ker,Ideal.span_le]
 intro x hx
 rw [Set.mem_singleton_iff] at hx
 subst x
 exact Ideal.mem_map_of_mem (fiberLocalizePlane q hq) (hsurface a)
theorem indexedFiberRelationBar_ne_bot
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface tail:PlaneRing Omega)
   (htailRoot:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     tail∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hproper:indexedFiberTail q hq tail∉
     Ideal.span {indexedFiberSurface q hq surface})
   (a:IndexedFactorFiber component lam mu nu order ht q):
   indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥:=by
 let quotientMap:Polynomial (FiberCoefficient q hq) →+*
     SurfaceQuotient (indexedFiberSurface q hq surface):=
   Ideal.Quotient.mk (Ideal.span {indexedFiberSurface q hq surface})
 intro hbot
 have hmem:quotientMap (indexedFiberTail q hq tail)∈
     indexedFiberRelationBar component lam mu nu order ht q hq surface a:=
   Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (htailRoot a))
 have hzero:quotientMap (indexedFiberTail q hq tail)=0:=by
   apply Ideal.mem_bot.mp
   rw [←hbot]
   exact hmem
 exact hproper (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
include hfinite in
theorem indexedFiberRelation_comap_C_eq_maximalIdeal
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (indexedFiberRelation component lam mu nu order ht q hq a).comap
       Polynomial.C=IsLocalRing.maximalIdeal (FiberCoefficient q hq):=by
 cases a with
 | mk a hqeq =>
   subst q
   exact localizedRelation_comap_C_eq_maximalIdeal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
include hfinite hgen in
theorem exists_monic_mem_indexedFiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   ∃ M:Polynomial (FiberCoefficient q hq),M.Monic∧
     M∈indexedFiberRelation component lam mu nu order ht q hq a:=by
 cases a with
 | mk a hqeq =>
   subst q
   let J:=localizedRelation Omega (CoordinateField Omega (component a).1) order
     (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   letI:J.IsMaximal:=localizedRelation_isMaximal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
         (hfinite a) (hgen a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hfin:=localizedRelationResidue_finite Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a)
         (hfinite a) (hgen a)
   exact exists_monic_mem_maximal_relation J hcontract hfin
noncomputable def indexedWeightedFiberPrimaryPieces
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface tail:PlaneRing Omega)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   (hbarne:∀ a,indexedFiberRelationBar component lam mu nu order ht
     q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   [hlocal:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]:
   PrimaryPiecesCertificate (indexedFiberSurface q hq surface)
     (indexedFiberTail q hq tail) (fun a => multiplicity a*
       Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
         (IsLocalRing.ResidueField (Localization.AtPrime
           (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))):=by
 exact primaryPiecesCertificateOfMembershipWeighted
   (indexedFiberSurface q hq surface) (indexedFiberTail q hq tail)
   (indexedFiberRelation component lam mu nu order ht q hq)
   (indexedFiberRelationBar component lam mu nu order ht q hq surface)
   (fun _ => rfl) hbarne multiplicity htail
   (indexedFiberRelation_pairwise_coprime component hcomponent lam mu nu order
     ht hfinite hgen q hq)
end
end ProximityPrize.SubmissionLower.RCN107
end PackedLegacy_C3

/-! Packed from ProximityPrize.SubmissionLower.I6. -/
section PackedLegacy_I6
namespace ProximityPrize.SubmissionLower.RCN073
open RCN324
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {K R:Type} [Field K] [CommRing R] [IsDomain R]
 [Algebra K R] [IsDiscreteValuationRing R]
private theorem derivation_preserves_char_pow
   (D:Derivation K R R) (pi:R) (p:ℕ) [CharP R p]
   (_hp:1 ≤ p) (f:R) (hf:pi^p∣f):pi^p∣D f:=by
 obtain ⟨u,rfl⟩:=hf
 rw [D.leibniz,Derivation.leibniz_pow]
 simp only [nsmul_eq_mul,smul_eq_mul,CharP.cast_eq_zero R p,zero_mul,
   mul_zero,add_zero]
 exact ⟨D u,rfl⟩
private theorem recurrence_preserves_dvd
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (a:R) (j:ℕ) (hN:a∣N j) (hDN:a∣D (N j)):
   a∣N (j+1):=by
 obtain ⟨u,hu⟩:=hN
 obtain ⟨v,hv⟩:=hDN
 refine ⟨H*v-c j*u*DH,?_⟩
 rw [hrec j,hv,hu]
 ring
private theorem tangent_chain
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi a:R) (htangent:D pi=pi*a)
   (hN0:pi∣N 0):∀ j,pi∣N j:=by
 intro j
 induction j with
 | zero => exact hN0
 | succ j ih =>
     apply recurrence_preserves_dvd D H DH c N hrec pi j ih
     simpa only [pow_one] using
       tangent_preserves_divisibility D pi a 1 (by simp) htangent
         (N j) (by simpa only [pow_one] using ih)
private theorem char_pow_chain
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (pi:R) (p:ℕ) [CharP R p] (hp:1 ≤ p)
   (hN0:pi^p∣N 0):∀ j,pi^p∣N j:=by
 intro j
 induction j with
 | zero => exact hN0
 | succ j ih =>
     apply recurrence_preserves_dvd D H DH c N hrec (pi^p) j ih
     exact derivation_preserves_char_pow D pi p hp (N j) ih
private theorem addVal_derivation_eq_pred
   (D:Derivation K R R) (pi:R) (hpi:Irreducible pi)
   (htrans:IsUnit (D pi)) (p k:ℕ) [CharP R p]
   (hp:p.Prime) (hkpos:1 ≤ k) (hkp:k < p)
   (x:R) (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R (D x)=k-1:=by
 have h:=addVal_iterate_eq_sub_of_transverse D pi (u:R) k 1 p hp hkp
   hkpos hpi u.isUnit htrans
 rw [hx,mul_comm]
 simpa using h
private theorem transverse_recurrence_step
   (D:Derivation K R R) (H DH c x next pi:R)
   (hrec:next=H*D x-c*x*DH)
   (hH:IsUnit H) (hpi:Irreducible pi) (htrans:IsUnit (D pi))
   (p k:ℕ) [CharP R p] (hp:p.Prime) (hkpos:1 ≤ k) (hkp:k < p)
   (u:Rˣ) (hx:x=(u:R)*pi^k):
   IsDiscreteValuationRing.addVal R next=k-1:=by
 let v:=IsDiscreteValuationRing.addVal R
 have hDx:v (D x)=k-1:=
   addVal_derivation_eq_pred D pi hpi htrans p k hp hkpos hkp x u hx
 have hxv:v x=k:=IsDiscreteValuationRing.addVal_def x u hpi k hx
 have hfirst:v (H*D x)=k-1:=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hH,zero_add,hDx]
 have hsecond:k ≤ v (c*x*DH):=by
   rw [IsDiscreteValuationRing.addVal_mul,
     IsDiscreteValuationRing.addVal_mul,hxv]
   exact le_add_right (le_add_left (le_refl (k:ℕ∞)))
 have hlt:v (H*D x) < v (c*x*DH):=by
   rw [hfirst]
   exact (ENat.coe_lt_coe.mpr (Nat.pred_lt (Nat.ne_zero_of_lt hkpos))).trans_le hsecond
 rw [hrec,v.map_sub_eq_of_lt_left hlt,hfirst]
theorem recurrence_unit_or_persistent
   (D:Derivation K R R) (H DH:R) (c:ℕ → R) (N:ℕ → R)
   (p:ℕ) [CharP R p] (hp:p.Prime)
   (hrec:∀ j,N (j+1)=H*D (N j)-c j*N j*DH)
   (hH:IsUnit H) (hN0ne:N 0≠0) (hN0nonunit:¬ IsUnit (N 0)):
   let mu:=(IsDiscreteValuationRing.addVal R (N 0)).toNat
   1 ≤ mu∧
     ((∃ delay,1 ≤ delay∧delay ≤ mu∧IsUnit (N delay))∨
       (∀ delay,¬ IsUnit (N delay))):=by
 classical
 let v:=IsDiscreteValuationRing.addVal R
 obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
 obtain ⟨mu,u,hN0⟩:=
   IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hN0ne hpi
 have hv0:v (N 0)=mu:=IsDiscreteValuationRing.addVal_def (N 0) u hpi mu hN0
 have hmuDef:(v (N 0)).toNat=mu:=by rw [hv0];simp
 have hmuPos:1 ≤ mu:=by
   by_contra h
   have hz:mu=0:=Nat.eq_zero_of_not_pos h
   apply hN0nonunit
   apply IsDiscreteValuationRing.addVal_eq_zero_iff.mp
   change v (N 0)=0
   rw [hv0,hz]
   simp
 rw [hmuDef]
 refine ⟨hmuPos,?_⟩
 letI:Decidable (IsUnit (D pi)):=Classical.propDecidable _
 by_cases htrans:IsUnit (D pi)
 · by_cases hmup:mu < p
   · left
     refine ⟨mu,hmuPos,le_rfl,?_⟩
     have horders:∀ j ≤ mu,v (N j)=mu-j:=by
       intro j hj
       induction j with
       | zero => simpa using hv0
       | succ j ih =>
           have hjlt:j < mu:=by omega
           have hord:=ih hjlt.le
           have hNjNe:N j≠0:=by
             intro hz
             rw [hz,IsDiscreteValuationRing.addVal_zero] at hord
             exact ENat.top_ne_coe (mu-j) hord
           obtain ⟨k,uj,hNj⟩:=
             IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hNjNe hpi
           have hkv:v (N j)=k:=
             IsDiscreteValuationRing.addVal_def (N j) uj hpi k hNj
           have hk:k=mu-j:=by
             exact ENat.coe_inj.mp (hkv.symm.trans hord)
           have hkpos:1 ≤ k:=by omega
           have hkp:k < p:=by omega
           have hstep:=transverse_recurrence_step D H DH (c j) (N j)
             (N (j+1)) pi (hrec j) hH hpi htrans p k hp hkpos hkp uj hNj
           rw [hstep,hk]
           exact_mod_cast (show mu-j-1=mu-(j+1) by omega)
     exact IsDiscreteValuationRing.addVal_eq_zero_iff.mp (by
       simpa using horders mu le_rfl)
   · right
     have hpLe:p ≤ mu:=Nat.le_of_not_gt hmup
     have hpPos:1 ≤ p:=hp.one_le
     have hpow:pi^p∣N 0:=by
       rw [hN0]
       refine ⟨(u:R)*pi^(mu-p),?_⟩
       have hpowEq:pi^mu=pi^p*pi^(mu-p):=by
         rw [←pow_add,Nat.add_sub_of_le hpLe]
       rw [hpowEq]
       ring
     have hall:=char_pow_chain D H DH c N hrec pi p hpPos hpow
     intro j hunit
     apply hpi.not_isUnit
     apply isUnit_of_dvd_one
     exact (dvd_pow_self pi (Nat.ne_of_gt hpPos)).trans
       ((hall j).trans (isUnit_iff_dvd_one.mp hunit))
 · right
   have hDmem:D pi∈IsLocalRing.maximalIdeal R:=
     (IsLocalRing.mem_maximalIdeal (D pi)).2 htrans
   obtain ⟨a,ha⟩:∃ a,D pi=pi*a:=by
     have hmax:=(IsDiscreteValuationRing.irreducible_iff_uniformizer pi).mp hpi
     rw [hmax,Ideal.mem_span_singleton'] at hDmem
     obtain ⟨a,ha⟩:=hDmem
     exact ⟨a,by simpa [mul_comm] using ha.symm⟩
   have hpiDvd:pi∣N 0:=by
     rw [hN0]
     refine ⟨(u:R)*pi^(mu-1),?_⟩
     have hpowEq:pi^mu=pi*pi^(mu-1):=by
       calc
         pi^mu=pi^(1+(mu-1)):=by
           rw [Nat.add_sub_of_le hmuPos]
         _=pi^1*pi^(mu-1):=pow_add pi 1 (mu-1)
         _=pi*pi^(mu-1):=by rw [pow_one]
     rw [hpowEq]
     ring
   have hall:=tangent_chain D H DH c N hrec pi a ha hpiDvd
   intro j hunit
   exact hpi.not_isUnit (isUnit_of_dvd_one
     ((hall j).trans (isUnit_iff_dvd_one.mp hunit)))
end
end ProximityPrize.SubmissionLower.RCN073
end PackedLegacy_I6

/-! Packed from ProximityPrize.SubmissionLower.O2. -/
section PackedLegacy_O2
namespace ProximityPrize.SubmissionLower.RCN270
open IsLocalRing Ideal
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {A:Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
private theorem exists_pair_generator_of_not_mem_sq
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2):
   ∃ g∈maximalIdeal A,maximalIdeal A=Ideal.span {f,g}:=by
 classical
 let m:=maximalIdeal A
 have hfg:m.FG:=m.fg_of_isNoetherianRing
 have hrank:m.spanFinrank=2:=by
   have hreg:=(isRegularLocalRing_iff A).mp (inferInstance:IsRegularLocalRing A)
   rw [hdim] at hreg
   exact_mod_cast hreg
 have hcard:m.generators.ncard=2:=by
   rw [Submodule.FG.generators_ncard hfg,hrank]
 obtain ⟨a,b,hab,hgen⟩:=Set.ncard_eq_two.mp hcard
 have hspan:Ideal.span {a,b}=m:=by
   simpa [hgen] using m.span_generators
 have ha:a∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hb:b∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hfm:f∈m:=by simpa [m] using hf
 have hfspan:f∈Ideal.span ({a,b}:Set A):=by rwa [hspan]
 obtain ⟨r,s,hrs⟩:=Ideal.mem_span_pair.mp hfspan
 have hunit:IsUnit r∨IsUnit s:=by
   letI:Decidable (IsUnit r):=Classical.propDecidable _
   letI:Decidable (IsUnit s):=Classical.propDecidable _
   by_cases hr:IsUnit r
   · exact Or.inl hr
   by_cases hs:IsUnit s
   · exact Or.inr hs
   · exfalso
     have hrm:r∈m:=(IsLocalRing.mem_maximalIdeal r).mpr hr
     have hsm:s∈m:=(IsLocalRing.mem_maximalIdeal s).mpr hs
     apply hf2
     rw [pow_two, ←hrs]
     exact (m*m).add_mem (Ideal.mul_mem_mul hrm ha) (Ideal.mul_mem_mul hsm hb)
 rcases hunit with hr | hs
 · refine ⟨b,hb,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,b}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       obtain ⟨u,rfl⟩:=hr
       have hfmem:f∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have hbmem:b∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have heq:a=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*s*b:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           a=((↑(u⁻¹):A)*(↑u:A))*a:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*((↑u:A)*a+s*b)-
               (↑(u⁻¹):A)*s*b:=by ring
       rw [heq]
       exact (Ideal.span ({f,b}:Set A)).sub_mem
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hbmem)
     · rw [hx]
       exact Ideal.subset_span (by simp)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
 · refine ⟨a,ha,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,a}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       exact Ideal.subset_span (by simp)
     · rw [hx]
       obtain ⟨u,rfl⟩:=hs
       have hfmem:f∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have hamem:a∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have heq:b=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*r*a:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           b=((↑(u⁻¹):A)*(↑u:A))*b:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*(r*a+(↑u:A)*b)-
               (↑(u⁻¹):A)*r*a:=by ring
       rw [heq]
       exact (Ideal.span ({f,a}:Set A)).sub_mem
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hamem)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
theorem quotient_span_singleton_isRegularLocalRing
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2)
   (hdimQ:ringKrullDim (A ⧸ Ideal.span {f})=1):
   IsRegularLocalRing (A ⧸ Ideal.span {f}):=by
 obtain ⟨g,hg,hmg⟩:=exists_pair_generator_of_not_mem_sq f hf hf2 hdim
 have hspanProper:Ideal.span ({f}:Set A)≠⊤:=by
   apply ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
   exact Ideal.span_le.2 (by simpa using hf)
 letI:Nontrivial (A ⧸ Ideal.span {f}):=
   Ideal.Quotient.nontrivial_iff.mpr hspanProper
 letI:IsLocalRing (A ⧸ Ideal.span {f}):=
   IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
     Ideal.Quotient.mk_surjective
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 rw [hdimQ]
 have hmax:maximalIdeal (A ⧸ Ideal.span {f})=
     Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:=by
   rw [←IsLocalRing.map_maximalIdeal_of_surjective
     (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective,hmg,
     Ideal.map_span]
   simp [Set.image_insert_eq,Set.image_singleton]
 rw [hmax]
 have hle:(Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:
     Ideal (A ⧸ Ideal.span {f})).spanFinrank ≤ 1:=by
   exact (Submodule.spanFinrank_span_le_ncard_of_finite
     (Set.finite_singleton _)).trans (by simp)
 exact_mod_cast hle
end ProximityPrize.SubmissionLower.RCN270
end PackedLegacy_O2

/-! Packed from ProximityPrize.SubmissionLower.L5. -/
section PackedLegacy_L5
namespace ProximityPrize.SubmissionLower.RCN186
variable {A:Type*} [CommRing A]
noncomputable def quotientPrime (I p:Ideal A):Ideal (A ⧸ I):=
 p.map (Ideal.Quotient.mk I)
theorem quotientPrime_isPrime (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):(quotientPrime I p).IsPrime:=by
 apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
 simpa only [Ideal.mk_ker] using hIp
noncomputable abbrev LocalizedQuotient (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):Type _:=
 @Localization.AtPrime (A ⧸ I) _ (quotientPrime I p)
   (quotientPrime_isPrime I p hIp)
theorem quotientPrime_comap_quotientMk (I p:Ideal A) [p.IsPrime]
   (hIp:I ≤ p):
   (quotientPrime I p).comap (Ideal.Quotient.mk I)=p:=by
 rw [quotientPrime,Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
 change p ⊔ RingHom.ker (Ideal.Quotient.mk I)=p
 rw [Ideal.mk_ker,sup_eq_left]
 exact hIp
theorem quotientMk_map_primeCompl (I p:Ideal A) [p.IsPrime]
   [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Submonoid.map (Ideal.Quotient.mk I) p.primeCompl=
     (quotientPrime I p).primeCompl:=by
 apply SetLike.ext
 intro x
 constructor
 · rintro ⟨s,hs,rfl⟩
   intro hmem
   exact hs ((quotientPrime_comap_quotientMk I p hIp).symm ▸ hmem)
 · intro hx
   obtain ⟨s,rfl⟩:=Ideal.Quotient.mk_surjective x
   refine ⟨s,?_,rfl⟩
   intro hs
   apply hx
   change s∈(quotientPrime I p).comap (Ideal.Quotient.mk I)
   rw [quotientPrime_comap_quotientMk I p hIp]
   exact hs
noncomputable def ambientToLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Localization.AtPrime p →+*LocalizedQuotient I p hIp:=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 exact IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
   p.primeCompl.le_comap_map
theorem ambientToLocalizedQuotient_surjective
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   Function.Surjective (ambientToLocalizedQuotient I p hIp):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 letI:IsLocalization (Submonoid.map (Ideal.Quotient.mk I) p.primeCompl)
     (LocalizedQuotient I p hIp):=hM.symm ▸ inferInstance
 simpa only [ambientToLocalizedQuotient] using
   (IsLocalization.map_surjective_of_surjective p.primeCompl (Localization.AtPrime p)
     (LocalizedQuotient I p hIp) Ideal.Quotient.mk_surjective)
theorem ambientToLocalizedQuotient_ker
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   RingHom.ker (ambientToLocalizedQuotient I p hIp)=
     I.map (algebraMap A (Localization.AtPrime p)):=by
 have hM:=quotientMk_map_primeCompl I p hIp
 have hk:=IsLocalization.ker_map (S:=Localization.AtPrime p)
   (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I) hM
 let canonicalMap:Localization.AtPrime p →+*LocalizedQuotient I p hIp:=
   IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
     (hM.symm ▸ p.primeCompl.le_comap_map)
 have hmaps:ambientToLocalizedQuotient I p hIp=canonicalMap:=by
   apply IsLocalization.ringHom_ext p.primeCompl
   simp only [ambientToLocalizedQuotient,canonicalMap,IsLocalization.map_comp]
 rw [hmaps]
 change RingHom.ker canonicalMap=_
 calc
   RingHom.ker canonicalMap=RingHom.ker
       (IsLocalization.map (LocalizedQuotient I p hIp) (Ideal.Quotient.mk I)
         (hM.symm ▸ p.primeCompl.le_comap_map)):=by
     congr 1
   _=I.map (algebraMap A (Localization.AtPrime p)):=by
     simpa only [Ideal.mk_ker] using hk
noncomputable def quotientAmbientEquivLocalizedQuotient
   (I p:Ideal A) [p.IsPrime] [hquotientPrime:(quotientPrime I p).IsPrime]
   (hIp:I ≤ p):
   (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))) ≃+*
     LocalizedQuotient I p hIp:=
 (Ideal.quotEquivOfEq (ambientToLocalizedQuotient_ker I p hIp).symm).trans
   (RingHom.quotientKerEquivOfSurjective
     (ambientToLocalizedQuotient_surjective I p hIp))
end ProximityPrize.SubmissionLower.RCN186
end PackedLegacy_L5

/-! Packed from ProximityPrize.SubmissionLower.I8. -/
section PackedLegacy_I8
namespace ProximityPrize.SubmissionLower.RCN078
def DualNumber (R:Type*):=R × R
namespace DualNumber
variable {K R:Type*}
instance [Zero R]:Zero (DualNumber R):=inferInstanceAs (Zero (R × R))
instance [Add R]:Add (DualNumber R):=inferInstanceAs (Add (R × R))
instance [Neg R]:Neg (DualNumber R):=inferInstanceAs (Neg (R × R))
instance [Sub R]:Sub (DualNumber R):=inferInstanceAs (Sub (R × R))
instance [AddCommMonoid R]:AddCommMonoid (DualNumber R):=
 inferInstanceAs (AddCommMonoid (R × R))
instance [AddCommGroup R]:AddCommGroup (DualNumber R):=
 inferInstanceAs (AddCommGroup (R × R))
instance [SMul K R]:SMul K (DualNumber R):=inferInstanceAs (SMul K (R × R))
instance {L:Type*} [SMul L K] [SMul L R] [SMul K R] [IsScalarTower L K R]:
   IsScalarTower L K (DualNumber R):=
 inferInstanceAs (IsScalarTower L K (R × R))
instance [Semiring K] [AddCommMonoid R] [Module K R]:Module K (DualNumber R):=
 inferInstanceAs (Module K (R × R))
instance [One R] [Zero R]:One (DualNumber R):=⟨(1,0)⟩
instance [Mul R] [Add R]:Mul (DualNumber R):=
 ⟨fun x y => (x.1*y.1,x.1*y.2+x.2*y.1)⟩
@[ext]
theorem ext {x y:DualNumber R} (h₁:x.1=y.1) (h₂:x.2=y.2):x=y:=
 Prod.ext h₁ h₂
@[simp] theorem fst_zero [Zero R]:(0:DualNumber R).1=0:=rfl
@[simp] theorem snd_zero [Zero R]:(0:DualNumber R).2=0:=rfl
@[simp] theorem fst_add [Add R] (x y:DualNumber R):(x+y).1=x.1+y.1:=rfl
@[simp] theorem snd_add [Add R] (x y:DualNumber R):(x+y).2=x.2+y.2:=rfl
@[simp] theorem fst_one [One R] [Zero R]:(1:DualNumber R).1=1:=rfl
@[simp] theorem snd_one [One R] [Zero R]:(1:DualNumber R).2=0:=rfl
@[simp] theorem fst_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).1=x.1*y.1:=rfl
@[simp] theorem snd_mul [Mul R] [Add R] (x y:DualNumber R):
   (x*y).2=x.1*y.2+x.2*y.1:=rfl
instance [CommRing R]:CommRing (DualNumber R) where
 mul_assoc x y z:=by ext <;> simp [mul_assoc,mul_add,add_mul];ring
 one_mul x:=by ext <;> simp
 mul_one x:=by ext <;> simp
 left_distrib x y z:=by ext <;> simp [mul_add];ring
 right_distrib x y z:=by ext <;> simp [add_mul];ring
 zero_mul x:=by ext <;> simp
 mul_zero x:=by ext <;> simp
 mul_comm x y:=by ext <;> simp [mul_comm,add_comm]
def inlRingHom [CommRing R]:R →+*DualNumber R where
 toFun r:=(r,0)
 map_one':=rfl
 map_mul' _ _:=by ext <;> simp
 map_zero':=rfl
 map_add' _ _:=by ext <;> simp
instance [CommRing K] [CommRing R] [Algebra K R]:Algebra K (DualNumber R) where
 algebraMap:=inlRingHom.comp (algebraMap K R)
 commutes' k x:=by ext <;> simp [mul_comm]
 smul_def' k x:=by
   apply Prod.ext
   · change k • x.1=algebraMap K R k*x.1
     exact Algebra.smul_def k x.1
   · change k • x.2=algebraMap K R k*x.2+0*x.1
     simp [Algebra.smul_def]
@[simp]
theorem algebraMap_apply [CommRing K] [CommRing R] [Algebra K R] (k:K):
   algebraMap K (DualNumber R) k=(algebraMap K R k,0):=rfl
def fstHom [CommRing K] [CommRing R] [Algebra K R]:DualNumber R →ₐ[K] R where
 toFun x:=x.1
 map_one':=rfl
 map_mul' _ _:=rfl
 map_zero':=rfl
 map_add' _ _:=rfl
 commutes' _:=rfl
def sndHom [CommRing R]:DualNumber R →ₗ[R] R where
 toFun x:=x.2
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
theorem isUnit_of_isUnit_fst [CommRing R] {x:DualNumber R} (hx:IsUnit x.1):
   IsUnit x:=by
 rcases x with ⟨a,b⟩
 rcases hx with ⟨u,hu⟩
 change (u:R)=a at hu
 subst a
 refine ⟨{
   val:=((u:R),b)
   inv:=((↑u⁻¹:R), -((↑u⁻¹:R)*b*(↑u⁻¹:R)))
   val_inv:=?_
   inv_val:=?_},rfl⟩
 · ext <;> simp [mul_assoc]
 · ext <;> simp [mul_assoc]
end DualNumber
end ProximityPrize.SubmissionLower.RCN078
end PackedLegacy_I8

/-! Packed from ProximityPrize.SubmissionLower.L6. -/
section PackedLegacy_L6
namespace ProximityPrize.SubmissionLower.RCN188
open RCN078
variable {K R S:Type*} [CommRing K] [CommRing R] [CommRing S]
 [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
 (M:Submonoid R) [IsLocalization M S]
def derivationDualAlgHom (D:Derivation K R R):R →ₐ[K] DualNumber S where
 toFun r:=(algebraMap R S r,algebraMap R S (D r))
 map_one':=by
   apply DualNumber.ext <;> simp
 map_mul' x y:=by
   apply DualNumber.ext
   · simp
   · simp [D.leibniz]
     exact mul_comm _ _
 map_zero':=by
   apply DualNumber.ext <;> simp
 map_add' x y:=by
   apply DualNumber.ext <;> simp
 commutes' k:=by
   apply DualNumber.ext
   · exact (IsScalarTower.algebraMap_apply K R S k).symm
   · simp
theorem derivationDualAlgHom_isUnit (D:Derivation K R R) (y:M):
   IsUnit (derivationDualAlgHom (S:=S) D y):=by
 apply DualNumber.isUnit_of_isUnit_fst
 simpa [derivationDualAlgHom] using IsLocalization.map_units S y
noncomputable def localizedDualAlgHom (D:Derivation K R R):
   S →ₐ[K] DualNumber S:=
 IsLocalization.liftAlgHom (derivationDualAlgHom_isUnit M D)
@[simp]
theorem localizedDualAlgHom_algebraMap (D:Derivation K R R) (r:R):
   localizedDualAlgHom M D (algebraMap R S r)=
     (algebraMap R S r,algebraMap R S (D r)):=by
 simp [localizedDualAlgHom,derivationDualAlgHom]
theorem localizedDualAlgHom_fst (D:Derivation K R R) (x:S):
   (localizedDualAlgHom M D x).fst=x:=by
 have hhom:
     (DualNumber.fstHom (K:=K) (R:=S)).comp
       (localizedDualAlgHom M D)=AlgHom.id K S:=by
   have hr:
       ((DualNumber.fstHom (K:=K) (R:=S)).comp
         (localizedDualAlgHom M D)).toRingHom=
         (AlgHom.id K S).toRingHom:=by
     apply IsLocalization.ringHom_ext M
     ext r
     simp [DualNumber.fstHom]
   exact AlgHom.ext fun x => RingHom.congr_fun hr x
 exact AlgHom.congr_fun hhom x
noncomputable def localizationDerivation (D:Derivation K R R):Derivation K S S:=
 Derivation.mk'
   ((DualNumber.sndHom (R:=S)).restrictScalars K |>.comp
     (localizedDualAlgHom M D).toLinearMap)
   (by
     intro x y
     change (localizedDualAlgHom M D (x*y)).snd=
       x*(localizedDualAlgHom M D y).snd+
         y*(localizedDualAlgHom M D x).snd
     rw [map_mul,DualNumber.snd_mul,
       localizedDualAlgHom_fst M D x,localizedDualAlgHom_fst M D y]
     simp
     ring)
@[simp]
theorem localizationDerivation_algebraMap (D:Derivation K R R) (r:R):
   localizationDerivation M D (algebraMap R S r)=algebraMap R S (D r):=by
 change (localizedDualAlgHom M D (algebraMap R S r)).snd=_
 rw [localizedDualAlgHom_algebraMap]
end ProximityPrize.SubmissionLower.RCN188
end PackedLegacy_L6

/-! Packed from ProximityPrize.SubmissionLower.FM. -/
section PackedLegacy_FM
namespace ProximityPrize.SubmissionLower.RCN230
open IsLocalRing Polynomial Ideal
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000
variable (R:Type*) [CommRing R]
theorem exists_monic_span_compat {k:Type*} [Field k]
   (I:Ideal k[X]) (hne:I≠⊥):
   ∃ f,f.Monic∧I=Ideal.span {f}:=by
 classical
 letI:DecidableEq k:=Classical.decEq k
 obtain ⟨x,h,spanx⟩:=Ideal.exists_normalized_span_of_isPrincipal I
 refine ⟨x,(Polynomial.normalize_eq_self_iff_monic ?_).mp h,spanx⟩
 by_contra eq0
 simp [eq0,spanx] at hne
theorem exists_monic_span_sup_map_eq_compat
   (p:Ideal R[X]) (hmax:(p.comap Polynomial.C).IsMaximal)
   (hne:p≠(p.comap Polynomial.C).map Polynomial.C):
   ∃ f:R[X],f.Monic∧
     p=(p.comap Polynomial.C).map Polynomial.C ⊔ Ideal.span {f}:=by
 let q:=p.comap Polynomial.C
 letI:Field (R ⧸ q):=Ideal.Quotient.field q
 have hne':Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk q)) p≠⊥:=by
   simp only [ne_eq,Ideal.map_eq_bot_iff_le_ker,
     Polynomial.ker_mapRingHom,q,Ideal.mk_ker]
   exact not_le_of_gt (lt_of_le_of_ne Ideal.map_comap_le hne.symm)
 rcases exists_monic_span_compat
     (Ideal.map (Polynomial.mapRingHom (Ideal.Quotient.mk q)) p) hne' with
   ⟨y,mony,hy⟩
 have hyLift:y∈Polynomial.lifts (Ideal.Quotient.mk q):=
   Polynomial.map_surjective _ Ideal.Quotient.mk_surjective _
 rcases Polynomial.lifts_and_natDegree_eq_and_monic hyLift mony with
   ⟨f,hf,_deg,monf⟩
 refine ⟨f,monf,?_⟩
 trans Ideal.comap (Polynomial.mapRingHom (Ideal.Quotient.mk q))
   ((Ideal.span {f}).map (Polynomial.mapRingHom (Ideal.Quotient.mk q)))
 · rw [Ideal.map_span,Polynomial.coe_mapRingHom,Set.image_singleton,hf, ←hy,
     Ideal.comap_map_of_surjective' _
       (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)]
   simpa [Polynomial.ker_mapRingHom,q] using Ideal.map_comap_le
 · rw [Ideal.comap_map_of_surjective' _
     (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective),
     sup_comm,Polynomial.ker_mapRingHom,Ideal.mk_ker]
theorem height_map_C_compat [IsNoetherianRing R]
   (p:Ideal R) [p.IsMaximal]:
   (p.map Polynomial.C).height=p.height:=by
 have:(p.map Polynomial.C).LiesOver p:=
   ⟨Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' Ideal.le_comap_map⟩
 simp [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p]
theorem polynomial_localization_isRegularLocalRing_compat
   [IsRegularLocalRing R] (p:Ideal R[X]) [p.IsPrime]
   (hcomap:p.comap Polynomial.C=maximalIdeal R):
   IsRegularLocalRing (Localization.AtPrime p):=by
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 let q:=(maximalIdeal R).map Polynomial.C
 have qle:q ≤ p:=by simpa [q, ←hcomap] using Ideal.map_comap_le
 have hreg:=(isRegularLocalRing_iff R).mp (inferInstance:IsRegularLocalRing R)
 have hfg':=(maximalIdeal R).fg_of_isNoetherianRing
 have hfg:=Submodule.FG.finite_generators hfg'
 have ht:(maximalIdeal R).height ≤ q.height:=
   le_of_eq (height_map_C_compat R (maximalIdeal R)).symm
 by_cases heq:p=q
 · have ht1:(maximalIdeal R).height ≤ p.height:=by simpa [heq]
   have hspan:Ideal.span
       ((algebraMap R (Localization.AtPrime p)) ''
         (maximalIdeal R).generators)=maximalIdeal (Localization.AtPrime p):=by
     rw [IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime p),
       RingHom.coe_comp,Set.image_comp, ←Ideal.map_span, ←Ideal.map_span]
     simp only [Ideal.span,(maximalIdeal R).span_generators,algebraMap_eq,
       q, ←heq,Localization.AtPrime.map_eq_maximalIdeal]
   simp only [←maximalIdeal_height_eq_ringKrullDim,
     ←IsLocalization.height_under p.primeCompl,
     IsLocalization.AtPrime.under_maximalIdeal _ p,ge_iff_le]
   apply le_trans _ (WithBot.coe_le_coe.mpr ht1)
   simp only [maximalIdeal_height_eq_ringKrullDim, ←hreg,Nat.cast_le,
     ←hspan, ←Submodule.FG.generators_ncard hfg']
   exact (Submodule.spanFinrank_span_le_ncard_of_finite (hfg.image _)).trans
     (Set.ncard_image_le hfg)
 · have hlt:q < p:=lt_of_le_of_ne qle (Ne.symm heq)
   have hpmax:(p.comap Polynomial.C).IsMaximal:=by
     simpa [hcomap] using maximalIdeal.isMaximal R
   obtain ⟨y,_,hy⟩:=
     exists_monic_span_sup_map_eq_compat R p hpmax (by simpa [hcomap])
   have peq:p=Ideal.span
       (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}):=by
     simp only [Set.union_comm,Ideal.span_union, ←Ideal.map_span,
       algebraMap_eq,sup_comm]
     nth_rw 1 [hy,hcomap, ←(maximalIdeal R).span_generators]
   simp only [←Localization.AtPrime.map_eq_maximalIdeal,peq,Ideal.map_span]
   rw [←maximalIdeal_height_eq_ringKrullDim,
     ←IsLocalization.height_under p.primeCompl,
     IsLocalization.AtPrime.under_maximalIdeal _ p]
   apply le_trans _
     (WithBot.coe_le_coe.mpr (Ideal.height_add_one_le_of_lt_of_isPrime hlt))
   apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1))
   rw [WithBot.coe_add,maximalIdeal_height_eq_ringKrullDim,WithBot.coe_one,
     ←hreg, ←Nat.cast_one, ←Nat.cast_add,Nat.cast_le]
   have hfin:=(hfg.image (algebraMap R R[X])).union (Set.finite_singleton y)
   apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (hfin.image _))
   apply le_trans (Set.ncard_image_le hfin) (le_trans (Set.ncard_union_le _ _) _)
   rw [Set.ncard_singleton,add_le_add_iff_right,
     ←Submodule.FG.generators_ncard hfg']
   exact Set.ncard_image_le hfg
instance polynomial_isRegularRing_compat [IsRegularRing R]:
   IsRegularRing R[X]:=by
 apply isRegularRing_iff.mpr
 intro p hp
 let q:=p.comap Polynomial.C
 let S:=(Localization.AtPrime q)[X]
 let pc:=Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
 letI:Algebra R[X] S:=Polynomial.algebra R (Localization.AtPrime q)
 haveI:IsLocalization pc S:=Polynomial.isLocalization _ _
 let pS:=p.map (algebraMap R[X] S)
 have hdisj:Disjoint (pc:Set R[X]) (p:Set R[X]):=by
   apply Set.disjoint_left.mpr
   rintro _ ⟨b,hb,rfl⟩ hp
   exact hb hp
 haveI:pS.IsPrime:=
   IsLocalization.isPrime_of_isPrime_disjoint pc _ _ inferInstance hdisj
 haveI:IsLocalization.AtPrime (Localization.AtPrime pS) p:=by
   convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
     pc (Localization.AtPrime pS) pS
   exact (IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance hdisj).symm
 haveI:IsRegularLocalRing (Localization.AtPrime q):=
   IsRegularRing.isRegularLocalRing_localization q
 have hbase:pS.comap Polynomial.C=maximalIdeal (Localization.AtPrime q):=by
   rw [←IsLocalization.map_under q.primeCompl _ (pS.comap Polynomial.C),
     ←IsLocalization.map_under q.primeCompl _
       (maximalIdeal (Localization.AtPrime q))]
   simp only [Ideal.comap_comap,S,pS]
   rw [←Polynomial.algebraMap_eq (R:=Localization.AtPrime q),
     ←IsScalarTower.algebraMap_eq R (Localization.AtPrime q)
       (Localization.AtPrime q)[X],
     IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X],
     ←Ideal.comap_comap, ←Ideal.under_def R[X],
     IsLocalization.under_map_of_isPrime_disjoint pc _ inferInstance hdisj]
   simp [q,IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
 haveI:=polynomial_localization_isRegularLocalRing_compat
   (Localization.AtPrime q) pS hbase
 exact IsRegularLocalRing.of_ringEquiv (R:=Localization.AtPrime pS)
   (IsLocalization.algEquiv p.primeCompl
     (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv
instance mvPolynomial_isRegularRing_compat [IsRegularRing R]
   {ι:Type*} [Finite ι]:IsRegularRing (MvPolynomial ι R):=by
 induction ι using Finite.induction_empty_option with
 | of_equiv e H =>
     exact IsRegularRing.of_ringEquiv (MvPolynomial.renameEquiv _ e).toRingEquiv
 | h_empty =>
     exact IsRegularRing.of_ringEquiv (MvPolynomial.isEmptyRingEquiv R _).symm
 | h_option IH =>
     exact IsRegularRing.of_ringEquiv
       (MvPolynomial.optionEquivLeft _ _).toRingEquiv.symm
theorem mvPolynomial_atPrime_isRegularLocalRing
   {K:Type*} [Field K] {ι:Type*} [Finite ι]
   (p:Ideal (MvPolynomial ι K)) [p.IsPrime]:
   IsRegularLocalRing (Localization.AtPrime p):=by
 letI:IsRegularRing K:=inferInstance
 letI:IsRegularRing (MvPolynomial ι K):=
   mvPolynomial_isRegularRing_compat K
 infer_instance
end
end ProximityPrize.SubmissionLower.RCN230
end PackedLegacy_FM

/-! Packed from ProximityPrize.SubmissionLower.FF. -/
section PackedLegacy_FF
namespace ProximityPrize.SubmissionLower.RCN218
open RCN313 RCN077 RCN136 RCN055 RCN188 RCN270 RCN186 RCN230 IsLocalRing
variable {K:Type*} [Field K]
abbrev Poly:=MvPolynomial (Fin 4) K
noncomputable def factorIdeal (F:Poly (K:=K)):Ideal (Poly (K:=K)):=Ideal.span {F}
theorem factorIdeal_isPrime (F:Poly (K:=K)) (hF:Irreducible F):
   (factorIdeal F).IsPrime:=by
 exact (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
noncomputable def contractedPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega)):
   Ideal (Poly (K:=K)):=
 C.comap (surfaceMap phi)
instance contractedPrime_isPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega)) [C.IsPrime]:
   (contractedPrime phi C).IsPrime:=by
 exact Ideal.comap_isPrime (surfaceMap phi) C
theorem mem_contractedPrime_iff {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega))
   (A:Poly (K:=K)):
   A∈contractedPrime phi C ↔ surfaceMap phi A∈C:=
 Iff.rfl
theorem factorIdeal_le_contractedPrime {Omega:Type*} [Field Omega]
   (phi:Polynomial K →+*Omega) (C:Ideal (MvPolynomial (Fin 3) Omega))
   (F:Poly (K:=K)) (hF:surfaceMap phi F∈C):
   factorIdeal F ≤ contractedPrime phi C:=by
 apply Ideal.span_le.2
 intro A hA
 simpa only [Set.mem_singleton_iff] using hA ▸ hF
noncomputable abbrev FactorLocal
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   (hFp:factorIdeal F ≤ p):Type _:=
 LocalizedQuotient (factorIdeal F) p hFp
theorem derivation_mem_maximal_of_mem_sq
   {A:Type*} [CommRing A] [Algebra K A] [IsLocalRing A]
   (D:Derivation K A A) (x:A) (hx:x∈maximalIdeal A^2):
   D x∈maximalIdeal A:=by
 rw [pow_two] at hx
 refine Submodule.mul_induction_on hx ?_ ?_
 · intro a ha b hb
   rw [D.leibniz]
   simpa [Algebra.smul_def] using (maximalIdeal A).add_mem
     ((maximalIdeal A).mul_mem_right (D b) ha)
     ((maximalIdeal A).mul_mem_right (D a) hb)
 · intro a b ha hb
   simpa only [map_add] using (maximalIdeal A).add_mem ha hb
noncomputable def factorAmbientQuotientEquiv
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   (Localization.AtPrime p ⧸ Ideal.span {
     algebraMap (Poly (K:=K)) (Localization.AtPrime p) F}) ≃+*
     FactorLocal F p hFp:=
 (Ideal.quotEquivOfEq (by
   simp only [factorIdeal,Ideal.map_span,Set.image_singleton])).trans
   (quotientAmbientEquivLocalizedQuotient (factorIdeal F) p hFp)
theorem factorLocal_isRegularLocalRing
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p)
   (hdimFactor:ringKrullDim (FactorLocal F p hFp)=1):
   IsRegularLocalRing (FactorLocal F p hFp):=by
 letI:IsRegularLocalRing (Localization.AtPrime p):=
   mvPolynomial_atPrime_isRegularLocalRing p
 let A:=Localization.AtPrime p
 let f:A:=algebraMap (Poly (K:=K)) A F
 have hdim:ringKrullDim A=2:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height p A,hheight]
   norm_num
 have hf:f∈maximalIdeal A:=by
   exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p F).mpr
     (hFp (Ideal.mem_span_singleton_self F))
 have hf2:f∉maximalIdeal A^2:=by
   intro hf2
   let D:Derivation K A A:=localizationDerivation p.primeCompl
     (MvPolynomial.pderiv (2:Fin 4):Derivation K (Poly (K:=K)) _)
   have hDmem:D f∈maximalIdeal A:=derivation_mem_maximal_of_mem_sq D f hf2
   have hD:D f=algebraMap (Poly (K:=K)) A (polyH K F):=by
     exact localizationDerivation_algebraMap p.primeCompl _ F
   rw [hD] at hDmem
   exact hH ((IsLocalization.AtPrime.to_map_mem_maximal_iff A p (polyH K F)).mp hDmem)
 haveI hsource:IsRegularLocalRing
     (Localization.AtPrime p ⧸ Ideal.span {
       algebraMap (Poly (K:=K)) (Localization.AtPrime p) F}):=by
   change IsRegularLocalRing (A ⧸ Ideal.span {f})
   apply quotient_span_singleton_isRegularLocalRing f hf hf2 hdim
   calc
     ringKrullDim (A ⧸ Ideal.span {f})=
         ringKrullDim (FactorLocal F p hFp):=
       ringKrullDim_eq_of_ringEquiv (factorAmbientQuotientEquiv F p hFp)
     _=1:=hdimFactor
 exact IsRegularLocalRing.of_ringEquiv (R:=
   Localization.AtPrime p ⧸ Ideal.span {
     algebraMap (Poly (K:=K)) (Localization.AtPrime p) F})
   (factorAmbientQuotientEquiv F p hFp)
theorem quotientPrime_height_eq_one
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p):
   (quotientPrime (factorIdeal F) p).height=1:=by
 let I:=factorIdeal F
 have hF0:F≠0:=by
   intro hzero
   subst F
   apply hH
   simp [polyH]
 have hFunit:¬ IsUnit F:=by
   intro hunit
   exact hfactorPrime.ne_top (by
     rw [factorIdeal,Ideal.span_singleton_eq_top]
     exact hunit)
 have hIheight:I.height=1:=by
   change (Ideal.span ({F}:Set (Poly (K:=K)))).height=1
   exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
     (by simpa [mem_nonZeroDivisors_iff_ne_zero] using hF0) hFunit
 have hIpne:I≠p:=by
   intro heq
   have:I.height=p.height:=congrArg Ideal.height heq
   rw [hIheight,hheight] at this
   norm_num at this
 have hIlt:I < p:=lt_of_le_of_ne hFp hIpne
 obtain ⟨x,hxp,hxI⟩:=SetLike.exists_of_lt hIlt
 have hmin:p∈(I ⊔ Ideal.span {x}).minimalPrimes:=by
   refine ⟨⟨inferInstance,sup_le hFp (Ideal.span_le.2 (by simpa))⟩,?_⟩
   intro r hr hrp
   rcases hr with ⟨hrprime,hJr⟩
   letI:r.IsPrime:=hrprime
   have hIr:I ≤ r:=le_sup_left.trans hJr
   have hIrne:I≠r:=by
     intro heq
     apply hxI
     rw [heq]
     exact hJr ((show Ideal.span {x} ≤ I ⊔ Ideal.span {x} from le_sup_right)
       (Ideal.mem_span_singleton_self x))
   have hIrlt:I < r:=lt_of_le_of_ne hIr hIrne
   have hrpEq:r=p:=by
     apply le_antisymm hrp
     by_contra hnot
     have hrlt:r < p:=lt_of_le_of_ne hrp (Ne.symm (ne_of_not_le hnot))
     have h1:=Ideal.height_add_one_le_of_lt_of_isPrime hIrlt
     have h2:=Ideal.height_add_one_le_of_lt_of_isPrime hrlt
     have hbad:(3:ℕ∞) ≤ p.height:=by
       calc
         3=I.height+1+1:=by rw [hIheight];norm_num
         _ ≤ r.height+1:=by
           simpa [add_comm,add_left_comm,add_assoc] using add_le_add_left h1 1
         _ ≤ p.height:=h2
     rw [hheight] at hbad
     norm_num at hbad
   exact hrpEq.ge
 apply le_antisymm
 · exact Ideal.map_height_le_one_of_mem_minimalPrimes hmin
 · rw [Order.one_le_iff_ne_zero]
   intro hz
   have hqbot:quotientPrime I p=⊥:=Ideal.height_eq_zero_iff_eq_bot.mp hz
   have hcomap:=quotientPrime_comap_quotientMk I p hFp
   rw [hqbot] at hcomap
   have hpI:p=I:=by
     change RingHom.ker (Ideal.Quotient.mk I)=p at hcomap
     rw [Ideal.mk_ker] at hcomap
     exact hcomap.symm
   exact hIpne hpI.symm
theorem factorLocal_isDiscreteValuationRing
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hfactorPrime:(factorIdeal F).IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hheight:p.height=2)
   (hH:polyH K F∉p):
   IsDiscreteValuationRing (FactorLocal F p hFp):=by
 have hdim:ringKrullDim (FactorLocal F p hFp)=1:=by
   rw [IsLocalization.AtPrime.ringKrullDim_eq_height
     (quotientPrime (factorIdeal F) p) (FactorLocal F p hFp)]
   exact_mod_cast quotientPrime_height_eq_one F p hFp hheight hH
 letI:IsRegularLocalRing (FactorLocal F p hFp):=
   factorLocal_isRegularLocalRing F p hFp hheight hH hdim
 exact RCN324.isDiscreteValuationRing_of_isRegularLocalRing_of_dimension_one hdim
private theorem baseDerivation_self (F:Poly (K:=K)):baseDerivation F F=0:=by
 rw [baseDerivation_apply]
 unfold polyG polyH
 ring
private theorem baseDerivation_stable_factor (F:Poly (K:=K)):
   ∀ P∈factorIdeal F,baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [factorIdeal,Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨baseDerivation F A,?_⟩
 rw [(baseDerivation F).leibniz,baseDerivation_self]
 simp
noncomputable def factorDerivation (F:Poly (K:=K)):
   Derivation K (Poly (K:=K) ⧸ factorIdeal F) (Poly (K:=K) ⧸ factorIdeal F):=
 quotientDerivation (baseDerivation F) (factorIdeal F) (baseDerivation_stable_factor F)
noncomputable def factorLocalDerivation
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   Derivation K (FactorLocal F p hFp) (FactorLocal F p hFp):=
 localizationDerivation (K:=K)
   (R:=Poly (K:=K) ⧸ factorIdeal F) (S:=FactorLocal F p hFp)
   (quotientPrime (factorIdeal F) p).primeCompl (factorDerivation F)
theorem factorLocalDerivation_mk
   (F P:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p):
   factorLocalDerivation F p hFp
       (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
         (Ideal.Quotient.mk (factorIdeal F) P))=
     algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
       (Ideal.Quotient.mk (factorIdeal F) (baseDerivation F P)):=by
 rw [factorLocalDerivation,localizationDerivation_algebraMap]
 have hq:=RCN077.quotientDerivation_mk
   (K:=K) (A:=Poly (K:=K)) (baseDerivation F) (factorIdeal F)
     (baseDerivation_stable_factor F) P
 exact congrArg
   (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp))
   (by simpa only [factorDerivation] using hq)
noncomputable def factorLocalImage
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (P:Poly (K:=K)):FactorLocal F p hFp:=
 algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
   (Ideal.Quotient.mk (factorIdeal F) P)
theorem factorLocal_numerator_succ
   (F:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (b:ℕ):
   factorLocalImage F p hFp (numerator K F (b+1))=
     factorLocalImage F p hFp (polyH K F)*
         factorLocalDerivation F p hFp
           (factorLocalImage F p hFp (numerator K F b))-
       (2*b:FactorLocal F p hFp)*
         factorLocalImage F p hFp (numerator K F b)*
         factorLocalDerivation F p hFp
           (factorLocalImage F p hFp (polyH K F)):=by
 rw [numerator_succ,numeratorStep_eq]
 simp only [factorLocalImage,map_sub,map_mul,map_natCast]
 rw [←factorLocalDerivation_mk F (numerator K F b) p hFp,
   ←factorLocalDerivation_mk F (polyH K F) p hFp]
 push_cast
 ring
theorem factorLocal_image_isUnit_of_not_mem
   (F A:Poly (K:=K)) (p:Ideal (Poly (K:=K))) [p.IsPrime]
   [hquotientPrime:(quotientPrime (factorIdeal F) p).IsPrime]
   (hFp:factorIdeal F ≤ p) (hA:A∉p):
   IsUnit (algebraMap (Poly (K:=K) ⧸ factorIdeal F) (FactorLocal F p hFp)
     (Ideal.Quotient.mk (factorIdeal F) A)):=by
 apply (IsLocalization.AtPrime.isUnit_to_map_iff (FactorLocal F p hFp)
   (quotientPrime (factorIdeal F) p) _).mpr
 intro hmem
 apply hA
 have hmem':A∈(quotientPrime (factorIdeal F) p).comap
     (Ideal.Quotient.mk (factorIdeal F)):=hmem
 rw [quotientPrime_comap_quotientMk (factorIdeal F) p hFp] at hmem'
 exact hmem'
end ProximityPrize.SubmissionLower.RCN218
end PackedLegacy_FF

/-! Packed from ProximityPrize.SubmissionLower.CJ. -/
section PackedLegacy_CJ
namespace ProximityPrize.SubmissionLower.RCN326
open ProximityPrize.Benchmark RCN095 RCN100 RCN119
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def score:ℕ:=6733
def errors:ℕ:=80092
def agreements:ℕ:=n-errors
def gap:ℕ:=agreements-w
def radiusNumerator:ℕ:=128*errors+127
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
structure Profile where
 multiplicity:ℕ
 totalCap:ℕ
 slopeCap:ℕ
 middleCap:ℕ
 coefficients:ℕ
 rank:ℕ
 deriving DecidableEq
namespace Profile
def nullity (P:Profile):ℕ:=P.coefficients-n*P.rank
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
def yCap (P:Profile):ℕ:=(P.weightedCap-1)/w
def totalRank (P:Profile):ℕ:=n*P.rank
def characteristicCap (P:Profile):ℕ:=
 (2*P.slopeCap-1)*P.weightedCap
end Profile
def profileA:Profile:=⟨41,19688,12,56,44579488339867,170057251⟩
def profileB:Profile:=⟨81,1242,25,112,20738895387938,79112293⟩
def profileC:Profile:=⟨43,624668,11,59,1477011414465277,5634351404⟩
def finalMeet:Profile:=⟨41,1242,11,56,0,0⟩
def fixedFlag:FlagDegree:=
 ⟨finalMeet.totalCap-finalMeet.middleCap,
   finalMeet.middleCap-finalMeet.slopeCap,
   finalMeet.slopeCap⟩
def direction:FlagDegree:=
 ⟨2*fixedFlag.zOnly,2*fixedFlag.yz-1,2*fixedFlag.all-1⟩
def tailFlag (d:ℕ):FlagDegree:=unitYZFlag+(d+1) • direction
def fixedRegularCost:ℕ:=flagMixed fixedFlag (tailFlag (w+1)) (tailFlag (w+2))
def fixedSingularCost:ℕ:=63020462332448
def firstResidualRegularCost:ℕ:=112248424128199
def firstResidualSingularCost:ℕ:=678257591819300
def secondResidualRegularCost:ℕ:=1127729807323574
def secondResidualSingularCost:ℕ:=75606965639647
def fixedCost:ℕ:=fixedRegularCost+fixedSingularCost
def firstResidualCeiling:ℕ:=
 firstResidualRegularCost+firstResidualSingularCost
def secondResidualCeiling:ℕ:=
 secondResidualRegularCost+secondResidualSingularCost
def totalCost:ℕ:=
 fixedRegularCost+fixedSingularCost+
   firstResidualRegularCost+firstResidualSingularCost+
   secondResidualRegularCost+secondResidualSingularCost
def seedlessListNumerator:ℕ:=43585392724533
def seedlessListCeiling:ℕ:=seedlessListNumerator/gap+1
def capacity:ℕ:=prime^6/2^128
def mcaBudget:ℕ:=capacity-seedlessListCeiling
def slack:ℕ:=mcaBudget-totalCost
abbrev scoreGate (e:ℕ):Prop:=
 (radiusDenominator-(128*e+127))^12800*2^score ≤
   radiusDenominator^12800
theorem radius_row_exact:
   errors=80092∧agreements=182052∧gap=50981∧
     radiusNumerator=10251903∧radiusDenominator=33554432:=by
 decide
theorem radius_cell_exact:scoreGate errors∧¬ scoreGate (errors-1):=by
 decide
theorem profile_values:
   profileA.nullity=333723∧profileB.nullity=82451746∧
     profileC.nullity=15101∧
     finalMeet=⟨41,1242,11,56,0,0⟩:=by
 decide
theorem profileA_coefficients_exact:
   coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap=
     profileA.coefficients:=by
 change coefficientCount (41*182052) 131071 19688 12=44579488339867
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   (41*182052) 131071 19688 12 57 (by decide) (by decide)]
 decide
theorem profileB_coefficients_exact:
   coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap=
     profileB.coefficients:=by
 change coefficientCount (81*182052) 131071 1242 25=20738895387938
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   (81*182052) 131071 1242 25 113 (by decide) (by decide)]
 decide
theorem profileC_coefficients_exact:
   coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap=
     profileC.coefficients:=by
 change coefficientCount (43*182052) 131071 624668 11=1477011414465277
 rw [RCN302.coefficientCount_eq_sum_range_of_weighted_cutoff
   (43*182052) 131071 624668 11 60 (by decide) (by decide)]
 decide
theorem profileA_rank_exact:
   localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap=
     profileA.rank:=by decide
theorem profileB_rank_exact:
   localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap=
     profileB.rank:=by decide
theorem profileC_rank_exact:
   localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap=
     profileC.rank:=by decide
theorem interpolation_gates:
   profileA.totalRank < profileA.coefficients∧
     profileB.totalRank < profileB.coefficients∧
     profileC.totalRank < profileC.coefficients:=by
 decide
theorem interpolation_gateA_exact:
   n*localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap <
     coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap:=by
 rw [profileA_coefficients_exact,profileA_rank_exact]
 decide
theorem interpolation_gateB_exact:
   n*localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap <
     coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap:=by
 rw [profileB_coefficients_exact,profileB_rank_exact]
 decide
theorem interpolation_gateC_exact:
   n*localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap <
     coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap:=by
 rw [profileC_coefficients_exact,profileC_rank_exact]
 decide
theorem profile_gates:
   profileA.characteristicCap < prime∧
     profileB.characteristicCap < prime∧
     profileC.characteristicCap < prime∧
     profileA.weightedCap+profileA.slopeCap ≤ w*(profileA.yCap+1)∧
     profileB.weightedCap+profileB.slopeCap ≤ w*(profileB.yCap+1)∧
     profileC.weightedCap+profileC.slopeCap ≤ w*(profileC.yCap+1)∧
     profileA.multiplicity-1+profileA.slopeCap ≤ profileA.yCap∧
     profileB.multiplicity-1+profileB.slopeCap ≤ profileB.yCap∧
     profileC.multiplicity-1+profileC.slopeCap ≤ profileC.yCap:=by
 decide
theorem profile_small_gates:
   (2*profileA.slopeCap-1)*profileA.totalCap < prime∧
     profileA.slopeCap < prime∧
     (2*profileB.slopeCap-1)*profileB.totalCap < prime∧
     profileB.slopeCap < prime∧
     (2*profileC.slopeCap-1)*profileC.totalCap < prime∧
     profileC.slopeCap < prime:=by
 decide
theorem fixed_flag_values:
   fixedFlag=⟨1186,45,11⟩∧direction=⟨2372,89,21⟩∧
     tailFlag (w+1)=⟨310905156,11665498,2752533⟩∧
     tailFlag (w+2)=⟨310907528,11665587,2752554⟩:=by
 decide
theorem six_cells_exact:
   fixedRegularCost=266307292786686640∧
     fixedSingularCost=63020462332448∧
     firstResidualRegularCost=112248424128199∧
     firstResidualSingularCost=678257591819300∧
     secondResidualRegularCost=1127729807323574∧
     secondResidualSingularCost=75606965639647:=by
 decide
theorem budget_and_slack_exact:
   seedlessListCeiling=854934049∧
     capacity=274980728111395087∧
     totalCost=268364156037929808∧
     mcaBudget=274980727256461038∧
     slack=6616571218531230∧totalCost < mcaBudget:=by
 decide
theorem cell_budget_strict:
   fixedCost+firstResidualCeiling+secondResidualCeiling < mcaBudget:=by
 decide
end
end ProximityPrize.SubmissionLower.RCN326
end PackedLegacy_CJ

/-! Packed from ProximityPrize.SubmissionLower.Q7. -/
section PackedLegacy_Q7
namespace ProximityPrize.SubmissionLower.RCN339
open RCN095 RCN237 RCN264 RCN326
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T1 H:MvPolynomial (Fin 3) Omega}
 {flag tailFlag1:FlagDegree}
theorem yzCost_mul_le_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (coefficient:ℕ) (hcoefficient:coefficient ≤ r.yz):
   coefficient*B.yzCost C ≤ B.weightedCost r C:=by
 unfold PrimeFlagBudgetFamily.weightedCost
 calc
   coefficient*B.yzCost C ≤ r.yz*B.yzCost C:=
     Nat.mul_le_mul_right (B.yzCost C) hcoefficient
   _ ≤ r.zOnly*B.zCost C+r.yz*B.yzCost C+r.all*B.allCost C:=by
     omega
theorem multiplicity_mul_yzCost_le_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (multiplicity coefficient:ℕ) (hcoefficient:coefficient ≤ r.yz):
   multiplicity*(coefficient*B.yzCost C) ≤
     multiplicity*B.weightedCost r C:=
 Nat.mul_le_mul_left multiplicity
   (yzCost_mul_le_weightedCost B r C coefficient hcoefficient)
theorem yzCost_le_multiplicity_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (r:FlagDegree) (C:RegularComponent Omega G T1 H)
   (multiplicity coefficient:ℕ) (hmultiplicity:1 ≤ multiplicity)
   (hcoefficient:coefficient ≤ r.yz):
   coefficient*B.yzCost C ≤ multiplicity*B.weightedCost r C:=by
 calc
   coefficient*B.yzCost C ≤ B.weightedCost r C:=
     yzCost_mul_le_weightedCost B r C coefficient hcoefficient
   _=1*B.weightedCost r C:=by simp
   _ ≤ multiplicity*B.weightedCost r C:=
     Nat.mul_le_mul_right (B.weightedCost r C) hmultiplicity
theorem errors_succ_le_secondTail_yz:
   errors+1 ≤ (tailFlag (w+2)).yz:=by
 decide
theorem tangentCost_le_secondTail_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (C:RegularComponent Omega G T1 H):
   (errors+1)*B.yzCost C ≤
     B.weightedCost (tailFlag (w+2)) C:=
 yzCost_mul_le_weightedCost B (tailFlag (w+2)) C (errors+1)
   errors_succ_le_secondTail_yz
theorem tangentCost_le_multiplicity_secondTail_weightedCost
   (B:PrimeFlagBudgetFamily (G:=G) (T:=T1) (H:=H) flag tailFlag1)
   (C:RegularComponent Omega G T1 H) (multiplicity:ℕ)
   (hmultiplicity:1 ≤ multiplicity):
   (errors+1)*B.yzCost C ≤
     multiplicity*B.weightedCost (tailFlag (w+2)) C:=
 yzCost_le_multiplicity_weightedCost B (tailFlag (w+2)) C
   multiplicity (errors+1) hmultiplicity errors_succ_le_secondTail_yz
end
end ProximityPrize.SubmissionLower.RCN339
end PackedLegacy_Q7

/-! Packed from ProximityPrize.SubmissionLower.FE. -/
section PackedLegacy_FE
namespace ProximityPrize.SubmissionLower.RCN217
open RCN077 RCN313
 RCN347 RCN055
noncomputable section
variable {K:Type*} [CommRing K]
private abbrev factorIdeal (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
private theorem baseDerivation_self (F:Poly4 K):baseDerivation F F=0:=by
 rw [baseDerivation_apply]
 unfold polyG polyH
 ring
private theorem baseDerivation_stable_factor (F:Poly4 K):
   ∀ P∈factorIdeal F,baseDerivation F P∈factorIdeal F:=by
 intro P hP
 rw [Ideal.mem_span_singleton] at hP ⊢
 obtain ⟨A,rfl⟩:=hP
 refine ⟨baseDerivation F A,?_⟩
 rw [leibniz_product,baseDerivation_self]
 ring
private def factorDerivation (F:Poly4 K):
   Derivation K (Poly4 K ⧸ factorIdeal F) (Poly4 K ⧸ factorIdeal F):=
 quotientDerivation (baseDerivation F) (factorIdeal F)
   (baseDerivation_stable_factor F)
private theorem factorDerivation_mk (F P:Poly4 K):
   factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P)=
     Ideal.Quotient.mk (factorIdeal F) (baseDerivation F P):=
 quotientDerivation_mk _ _ _ P
private theorem factor_zero (F:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) F=0:=
 Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
private theorem polyH_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul,factor_zero]
 ring
private theorem polyG_mul_factor_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyG K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*
       Ideal.Quotient.mk (factorIdeal F) (polyG K F):=by
 unfold polyG
 simp only [MvPolynomial.pderiv_mul,map_neg,map_add,map_mul,factor_zero]
 ring
private theorem baseDerivation_mul_factor_mod (F Q P:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (baseDerivation (F*Q) P)=
     Ideal.Quotient.mk (factorIdeal F) Q*
       factorDerivation F (Ideal.Quotient.mk (factorIdeal F) P):=by
 rw [factorDerivation_mk,baseDerivation_apply,baseDerivation_apply]
 simp only [map_add,map_mul]
 rw [polyH_mul_factor_mod,polyG_mul_factor_mod]
 ring
private theorem scaled_step_identity {A:Type*} [CommRing A] [Algebra K A]
   (D:Derivation K A A) (q h n nS:A) (b:ℕ)
   (hN:nS=q^(2*b)*n):
   q*h*(q*D nS)-(2*b:A)*nS*(q*D (q*h))=
     q^(2*(b+1))*(h*D n-(2*b:A)*n*D h):=by
 cases b with
 | zero =>
     simp only [hN,mul_zero,pow_zero,one_mul,Nat.cast_zero,
       zero_mul,sub_zero]
     ring
 | succ c =>
     rw [hN]
     simp only [leibniz_product,Derivation.leibniz_pow,nsmul_eq_mul,smul_eq_mul,
       Nat.cast_mul,Nat.cast_ofNat]
     have he:2*(c+1)=2*c+2:=by omega
     have hesub:2*c+2-1=2*c+1:=by omega
     have henext:2*(c+1+1)=2*c+4:=by omega
     rw [he,hesub,henext]
     have hp1:q^(2*c+1)=q^(2*c)*q:=by
       rw [pow_add,pow_one]
     have hp2:q^(2*c+2)=q^(2*c)*q^2:=by rw [pow_add]
     have hp4:q^(2*c+4)=q^(2*c)*q^4:=by rw [pow_add]
     rw [hp1,hp2,hp4]
     ring
private theorem numerator_scaling_mod (F Q:Poly4 K) (b:ℕ):
   Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*b)*
       Ideal.Quotient.mk (factorIdeal F) (numerator K F b):=by
 induction b with
 | zero => simp
 | succ b ih =>
   change Ideal.Quotient.mk (factorIdeal F)
       (numeratorStep K (F*Q) b (numerator K (F*Q) b))=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*(b+1))*
       Ideal.Quotient.mk (factorIdeal F)
         (numeratorStep K F b (numerator K F b))
   rw [numeratorStep_eq,numeratorStep_eq]
   simp only [map_sub,map_mul,map_natCast]
   rw [polyH_mul_factor_mod,
     baseDerivation_mul_factor_mod F Q (numerator K (F*Q) b),
     baseDerivation_mul_factor_mod F Q (polyH K (F*Q))]
   rw [←factorDerivation_mk F (numerator K F b),
     ←factorDerivation_mk F (polyH K F)]
   have hDH:=congrArg (factorDerivation F) (polyH_mul_factor_mod F Q)
   rw [hDH]
   simp only [Nat.cast_mul,Nat.cast_ofNat]
   apply scaled_step_identity (factorDerivation F)
     (Ideal.Quotient.mk (factorIdeal F) Q)
     (Ideal.Quotient.mk (factorIdeal F) (polyH K F))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K F b))
     (Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) b))
     b
   exact ih
theorem numerator_sub_factor_power_mem (F Q:Poly4 K) (b:ℕ):
   numerator K (F*Q) b-Q^(2*b)*numerator K F b∈
     Ideal.span ({F}:Set (Poly4 K)):=by
 rw [←Ideal.Quotient.mk_eq_mk_iff_sub_mem]
 simpa only [map_mul,map_pow] using numerator_scaling_mod F Q b
theorem factor_dvd_numerator_sub_power (F Q:Poly4 K) (b:ℕ):
   F∣numerator K (F*Q) b-Q^(2*b)*numerator K F b:=by
 exact Ideal.mem_span_singleton.mp (numerator_sub_factor_power_mem F Q b)
theorem factor_dvd_numerator_sub_power_of_eq (F Q S:Poly4 K)
   (hS:S=F*Q) (b:ℕ):
   F∣numerator K S b-Q^(2*b)*numerator K F b:=by
 subst S
 exact factor_dvd_numerator_sub_power F Q b
end
end ProximityPrize.SubmissionLower.RCN217
end PackedLegacy_FE

/-! Packed from ProximityPrize.SubmissionLower.A5. -/
section PackedLegacy_A5
namespace ProximityPrize.SubmissionLower.RCN048
open scoped BigOperators
open RCN077 RCN313 RCN217
noncomputable section
variable {K:Type*} [Field K]
private abbrev factorIdeal (F:Poly4 K):Ideal (Poly4 K):=Ideal.span {F}
private theorem H_scaling_mod (F Q:Poly4 K):
   Ideal.Quotient.mk (factorIdeal F) (polyH K (F*Q))=
     Ideal.Quotient.mk (factorIdeal F) Q*Ideal.Quotient.mk (factorIdeal F) (polyH K F):=by
 unfold polyH
 rw [MvPolynomial.pderiv_mul]
 simp only [map_add,map_mul]
 have hz:Ideal.Quotient.mk (factorIdeal F) F=0:=
   Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)
 rw [hz,zero_mul,add_zero]
 ring
private theorem numerator_scaling_mod (F Q:Poly4 K) (j:ℕ):
   Ideal.Quotient.mk (factorIdeal F) (numerator K (F*Q) j)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*j)*
       Ideal.Quotient.mk (factorIdeal F) (numerator K F j):=by
 have h:=numerator_sub_factor_power_mem F Q j
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,sub_eq_zero] at h
 exact h
private theorem commonTerm_scaling_mod (F Q:Poly4 K) (w j:ℕ) (hj:j≤w)
   (c:ℕ → K) (x:K):
   Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm (F*Q) w c x j)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F) (commonNumeratorTerm F w c x j):=by
 let ev:=Ideal.Quotient.mk (factorIdeal F)
 have he:2*j+2*(w-j)=2*w:=by omega
 unfold commonNumeratorTerm
 simp only [map_mul,map_pow,MvPolynomial.map_C]
 rw [numerator_scaling_mod,H_scaling_mod,mul_pow]
 calc
   _=ev Q^(2*j+2*(w-j))*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by
     rw [pow_add]
     ring
   _=ev Q^(2*w)*
       (ev (MvPolynomial.C (c j))*ev (numerator K F j)*
         ev (polyH K F)^(2*(w-j))*ev (MvPolynomial.C x-MvPolynomial.X 0)^j):=by rw [he]
   _=_:=by ring
private theorem seed_scaling_mod (F Q:Poly4 K) (w:ℕ) (u0 u1:K):
   Ideal.Quotient.mk (factorIdeal F)
       (affineSeedPolynomial u0 u1*polyH K (F*Q)^(2*w))=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F)
         (affineSeedPolynomial u0 u1*polyH K F^(2*w)):=by
 simp only [map_mul,map_pow]
 rw [H_scaling_mod,mul_pow]
 ring
theorem agreementNumerator_scaling_mod (F Q:Poly4 K) (w:ℕ)
   (c:ℕ → K) (x u0 u1:K):
   Ideal.Quotient.mk (factorIdeal F) (agreementNumerator (F*Q) w c x u0 u1)=
     Ideal.Quotient.mk (factorIdeal F) Q^(2*w)*
       Ideal.Quotient.mk (factorIdeal F) (agreementNumerator F w c x u0 u1):=by
 let ev:=Ideal.Quotient.mk (factorIdeal F)
 have hsum:ev (clearedTaylorNumerator (F*Q) w c x)=
     ev Q^(2*w)*ev (clearedTaylorNumerator F w c x):=by
   unfold clearedTaylorNumerator
   simp only [map_sum]
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j hj
   exact commonTerm_scaling_mod F Q w j (by have:=Finset.mem_range.mp hj;omega) c x
 unfold agreementNumerator
 rw [map_sub,map_sub,hsum,seed_scaling_mod]
 ring
theorem factor_dvd_agreement_sub_power (F Q:Poly4 K) (w:ℕ)
   (c:ℕ → K) (x u0 u1:K):
   F∣agreementNumerator (F*Q) w c x u0 u1-
     Q^(2*w)*agreementNumerator F w c x u0 u1:=by
 rw [←Ideal.mem_span_singleton]
 rw [←Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,map_pow,
   agreementNumerator_scaling_mod,sub_self]
end
end ProximityPrize.SubmissionLower.RCN048
end PackedLegacy_A5

/-! Packed from ProximityPrize.SubmissionLower.FH. -/
section PackedLegacy_FH
namespace ProximityPrize.SubmissionLower.RCN220
open RCN136 RCN135 RCN138 RCN137 RCN082 RCN350 RCN313 RCN159 RCN217 RCN002 RCN048 RCN095 RCN275 RCN065
noncomputable section
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
theorem exists_original_factor_with_first_tail
   {Γ:Finset K} {x:I → K} {p e:ℕ} [CharP (Ω K) p]
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1))):
   ∃ F0 Q:MvPolynomial (Fin 4) K,
     Irreducible F0∧0 < F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
     S.F=F0*Q∧S.G∣surfaceMap (polynomialEmbedding K) F0∧
     ¬ S.G∣surfaceMap (polynomialEmbedding K) Q∧
     ¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0)∧
     F0∣numerator K F0 (w+1):=by
 classical
 let P:=S.componentIdeal
 letI:P.IsPrime:=S.componentIdeal_isPrime
 have hFne:S.F≠0:=by
   intro hzero
   apply S.regular_proper
   rw [hzero]
   simp [polyH]
 let φC:Polynomial K →+*CoordinateField (Ω K) P:=
   (algebraMap (Ω K) (CoordinateField (Ω K) P)).comp (polynomialEmbedding K)
 let vC:Fin 3 → CoordinateField (Ω K) P:=
   fun i => componentPoint (polynomialEmbedding K) P i.succ
 have hsurfaceZero:MvPolynomial.eval vC (surfaceMap φC S.F)=0:=by
   rw [eval_surfaceMap]
   change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
     (componentPoint (polynomialEmbedding K) P) S.F=0
   rw [component_evaluation]
   rw [coordinateEvaluation_eq_aeval,aeval_coordinate_eq_quotient,
     Ideal.Quotient.eq_zero_iff_mem.mpr S.surface_mem_componentIdeal,map_zero]
 have hφC:Function.Injective φC:=
   (algebraMap (Ω K) (CoordinateField (Ω K) P)).injective.comp
     (polynomialEmbedding_injective K)
 obtain ⟨F0,hF0mem,hF0zero⟩:=exists_active_factor_of_surface_zero
   φC hφC S.F hFne vC hsurfaceZero
 have hF0spec:=activeFactors_spec S.F F0 hF0mem
 have hmapF0mem:surfaceMap (polynomialEmbedding K) F0∈P:=by
   rw [←coordinateEvaluation_ker (Ω K) P]
   rw [eval_surfaceMap] at hF0zero
   change MvPolynomial.eval₂Hom (componentCoefficients (polynomialEmbedding K) P)
     (componentPoint (polynomialEmbedding K) P) F0=0 at hF0zero
   rw [component_evaluation] at hF0zero
   exact hF0zero
 have hGdivF0:S.G∣surfaceMap (polynomialEmbedding K) F0:=
   Ideal.mem_span_singleton.mp hmapF0mem
 obtain ⟨Q,hprod⟩:=hF0spec.2.1
 have hQnot:¬ S.G∣surfaceMap (polynomialEmbedding K) Q:=by
   intro hGQ
   apply S.regular_proper
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_right hGQ _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hH0not:¬ S.G∣surfaceMap (polynomialEmbedding K) (polyH K F0):=by
   intro hGH
   apply S.regular_proper
   rw [hprod,MvPolynomial.pderiv_mul]
   simp only [polyH,map_add,map_mul]
   exact dvd_add (dvd_mul_of_dvd_left hGH _) (dvd_mul_of_dvd_left hGdivF0 _)
 have hscale:=factor_dvd_numerator_sub_power F0 Q (w+1)
 have hdiff:S.G∣surfaceMap (polynomialEmbedding K)
     (numerator K (F0*Q) (w+1)-Q^(2*(w+1))*numerator K F0 (w+1)):=
   hGdivF0.trans (map_dvd (surfaceMap (polynomialEmbedding K)) hscale)
 have htail':S.G∣surfaceMap (polynomialEmbedding K) (numerator K (F0*Q) (w+1)):=by
   simpa only [hprod] using hTail
 have hmul:S.G∣surfaceMap (polynomialEmbedding K)
     (Q^(2*(w+1))*numerator K F0 (w+1)):=by
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using dvd_sub htail' hdiff
 have hfactor:S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))∨
     S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
   have hmul':S.G∣surfaceMap (polynomialEmbedding K) Q^(2*(w+1))*
       surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
     rw [map_mul,map_pow] at hmul
     exact hmul
   exact S.irreducible_G.prime.dvd_or_dvd hmul'
 have hnum:S.G∣surfaceMap (polynomialEmbedding K) (numerator K F0 (w+1)):=by
   rcases hfactor with hpow | hnum
   · exact False.elim (hQnot (Prime.dvd_of_dvd_pow S.irreducible_G.prime
       (by simpa only [map_pow] using hpow)))
   · exact hnum
 have hbase:F0∣numerator K F0 (w+1):=
   (geometric_factor_dvd_iff K (Ω K) F0 (numerator K F0 (w+1))
     hF0spec.1 hF0spec.2.2 S.G S.irreducible_G
     (by simpa only [canonical_geometricSurfaceMap] using hGdivF0)).mp
     (by simpa only [canonical_geometricSurfaceMap] using hnum)
 exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGdivF0,hQnot,hH0not,hbase⟩
theorem original_factor_agreement_proper
   (φ:Polynomial K →+*Ω K) (F0 Q:MvPolynomial (Fin 4) K)
   (G:MvPolynomial (Fin 3) (Ω K))
   (hGdivF0:G∣surfaceMap φ F0)
   (w:ℕ) (c:ℕ → K) (x0 u0 u1:K)
   (hproper:¬G∣surfaceMap φ (agreementNumerator (F0*Q) w c x0 u0 u1)):
   ¬F0∣agreementNumerator F0 w c x0 u0 u1:=by
 intro hF0cut
 have hcut:G∣surfaceMap φ (agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ) hF0cut)
 have hscaled:G∣surfaceMap φ
     (Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=by
   have h:=dvd_mul_of_dvd_right hcut (surfaceMap φ Q^(2*w))
   simpa only [map_mul,map_pow,mul_comm] using h
 have hdiff:G∣surfaceMap φ
     (agreementNumerator (F0*Q) w c x0 u0 u1-
       Q^(2*w)*agreementNumerator F0 w c x0 u0 u1):=
   hGdivF0.trans (map_dvd (surfaceMap φ)
     (factor_dvd_agreement_sub_power F0 Q w c x0 u0 u1))
 apply hproper
 simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using dvd_add hdiff hscaled
end
end ProximityPrize.SubmissionLower.RCN220
end PackedLegacy_FH

/-! Packed from ProximityPrize.SubmissionLower.FL. -/
section PackedLegacy_FL
namespace ProximityPrize.SubmissionLower.RCN228
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347 RCN311 RCN174
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 30000
variable {K L M:Type} [Field K] [Field L] [Field M]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem map_reconstructedPolynomial
   (coefficients:K →+*L) (ψ:L →+*M) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hF':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i)) F=0)
   (hreg':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (reconstructedPolynomial coefficients F v hF hreg w).map ψ=
     reconstructedPolynomial (ψ.comp coefficients) F (fun i => ψ (v i)) hF' hreg' w:=by
 ext j
 simp only [Polynomial.coeff_map,reconstructedPolynomial,jetPolynomial_coeff]
 by_cases hj:j<w+1
 · simp only [if_pos hj]
   rw [jetCoefficient_eq_evaluated_numerator,jetCoefficient_eq_evaluated_numerator]
   simp only [map_div₀,map_mul,map_pow,map_inv₀,map_natCast,
     MvPolynomial.map_eval₂Hom]
 · simp only [if_neg hj,map_zero]
theorem map_globalPolynomial
   (coefficients:K →+*L) (ψ:L →+*M) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hF':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i)) F=0)
   (hreg':MvPolynomial.eval₂Hom (ψ.comp coefficients) (fun i => ψ (v i))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0) (w:ℕ):
   (globalPolynomial coefficients F v hF hreg w).map ψ=
     globalPolynomial (ψ.comp coefficients) F (fun i => ψ (v i)) hF' hreg' w:=by
 unfold globalPolynomial
 rw [Polynomial.map_taylor,
   map_reconstructedPolynomial coefficients ψ F v hF hreg hF' hreg' w,map_neg]
theorem globalPolynomial_congr_point
   (coefficients:K →+*L) (F:Poly4 K) {v v':Fin 4 → L} (hv:v=v')
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hF':MvPolynomial.eval₂Hom coefficients v' F=0)
   (hreg':MvPolynomial.eval₂Hom coefficients v' (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ):
   globalPolynomial coefficients F v hF hreg w=
     globalPolynomial coefficients F v' hF' hreg' w:=by
 cases hv
 rfl
theorem derivative_values_of_same_regular_jet
   (F:Poly4 K) (P Q:Polynomial K) (γ ξ:K)
   (hP:specialization K P γ F=0) (hQ:specialization K Q γ F=0)
   (hv:polynomialPoint (RingHom.id K) P γ ξ=polynomialPoint (RingHom.id K) Q γ ξ)
   (hreg:MvPolynomial.eval₂Hom (RingHom.id K) (polynomialPoint (RingHom.id K) P γ ξ)
     (polyH K F)≠0) (j:ℕ):
   (Polynomial.derivative^[j] P).eval ξ=(Polynomial.derivative^[j] Q).eval ξ:=by
 have hformula (A:Polynomial K) (hA:specialization K A γ F=0):
     MvPolynomial.eval₂Hom (RingHom.id K) (polynomialPoint (RingHom.id K) A γ ξ)
         (numerator K F j)=
       (MvPolynomial.eval₂Hom (RingHom.id K) (polynomialPoint (RingHom.id K) A γ ξ)
         (polyH K F))^(2*j)*(Polynomial.derivative^[j] A).eval ξ:=by
   simp only [eval_polynomialPoint_eq_specialization,Polynomial.eval₂_id]
   rw [specialization_numerator_eq K F A γ hA j,Polynomial.eval_mul,Polynomial.eval_pow]
 have hp:=hformula P hP
 have hq:=hformula Q hQ
 rw [←hv] at hq
 exact mul_left_cancel₀ (pow_ne_zero (2*j) hreg) (hp.symm.trans hq)
theorem canonical_polynomiality_of_first_tail
   (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom coefficients v F=0)
   (hreg:MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (p bound w seedCap slopeCap:ℕ) [CharP L p]
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hcaps:F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hdiv:F∣numerator K F (w+1)):
   specialization L (globalPolynomial coefficients F v hF hreg w) (v 3)
     (MvPolynomial.map coefficients F)=0:=by
 apply global_polynomiality_of_all_tails coefficients F v hF hreg
   p bound w seedCap slopeCap hw hshort hchar hcaps
 intro j hj _
 exact all_tail_jets_zero_of_first_tail_dvd coefficients F v hF hreg w hdiv j hj
end
end ProximityPrize.SubmissionLower.RCN228
end PackedLegacy_FL

/-! Packed from ProximityPrize.SubmissionLower.E4. -/
section PackedLegacy_E4
namespace ProximityPrize.SubmissionLower.RCN258
open RCN077 RCN269 RCN233 RCN313 RCN047 RCN231 RCN139 RCN229 RCN319 RCN347
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L M:Type*} [Field k] [Field L] [Field M]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
local instance:DecidableEq M:=Classical.decEq M
theorem mv_eval_mem (E:Subfield M) (c:k →+*M)
   (hc:∀ a,c a∈E) (v:Fin 4 → M) (hv:∀ i,v i∈E) (Q:Poly4 k):
   MvPolynomial.eval₂Hom c v Q∈E:=by
 induction Q using MvPolynomial.induction_on with
 | C a => simpa using hc a
 | add P Q hP hQ => simpa only [map_add] using E.add_mem hP hQ
 | mul_X P i hP =>
     simpa only [map_mul,MvPolynomial.eval₂Hom_X'] using E.mul_mem hP (hv i)
theorem polynomial_eval_mem (E:Subfield M) (c:L →+*M)
   (P:Polynomial L) (hP:∀ j,c (P.coeff j)∈E) (x:M) (hx:x∈E):
   P.eval₂ c x∈E:=by
 rw [Polynomial.eval₂_eq_sum_range]
 exact E.sum_mem fun j _ => E.mul_mem (hP j) (E.pow_mem hx j)
theorem taylor_coeff_mem (E:Subfield M) (P:Polynomial M)
   (hP:∀ j,P.coeff j∈E) (x:M) (hx:x∈E) (j:ℕ):
   (Polynomial.taylor x P).coeff j∈E:=by
 rw [Polynomial.taylor_coeff]
 apply polynomial_eval_mem E (RingHom.id M) (Polynomial.hasseDeriv j P) _ x hx
 intro n
 simp only [RingHom.id_apply,Polynomial.hasseDeriv_coeff]
 exact E.mul_mem (natCast_mem E _) (hP _)
theorem globalPolynomial_coeff_mem_of_evaluations
   (E:Subfield M) (c:k →+*M) (F:Poly4 k) (v:Fin 4 → M)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hreg:MvPolynomial.eval₂Hom c v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w:ℕ) (hv0:v 0∈E)
   (hnum:∀ j,MvPolynomial.eval₂Hom c v (numerator k F j)∈E)
   (hH:MvPolynomial.eval₂Hom c v (polyH k F)∈E) (j:ℕ):
   (globalPolynomial c F v hF hreg w).coeff j∈E:=by
 unfold globalPolynomial
 apply taylor_coeff_mem E _ _ _ (E.neg_mem hv0) j
 intro n
 simp only [reconstructedPolynomial,jetPolynomial_coeff]
 split_ifs with hn
 · rw [jetCoefficient_eq_evaluated_numerator]
   exact E.div_mem (E.mul_mem (hnum n) (E.pow_mem (E.inv_mem hH) _))
     (natCast_mem E _)
 · exact E.zero_mem
theorem globalPolynomial_coeff_mem
   (E:Subfield M) (c:k →+*M) (hc:∀ a,c a∈E)
   (F:Poly4 k) (v:Fin 4 → M) (hv:∀ i,v i∈E)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hreg:MvPolynomial.eval₂Hom c v (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (w j:ℕ):
   (globalPolynomial c F v hF hreg w).coeff j∈E:=
 globalPolynomial_coeff_mem_of_evaluations E c F v hF hreg w (hv 0)
   (fun n => mv_eval_mem E c hc v hv (numerator k F n))
   (mv_eval_mem E c hc v hv (polyH k F)) j
theorem map_numeratorStep (c:k →+*L) (F Q:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numeratorStep k F n Q)=
     numeratorStep L (MvPolynomial.map c F) n (MvPolynomial.map c Q):=by
 simp only [numeratorStep,clearedStep,polyH,polyG,MvPolynomial.pderiv_map,
   map_sub,map_add,map_mul,map_pow,map_natCast,map_neg,MvPolynomial.map_X]
theorem map_numerator (c:k →+*L) (F:Poly4 k) (n:ℕ):
   MvPolynomial.map c (numerator k F n)=numerator L (MvPolynomial.map c F) n:=by
 induction n with
 | zero => simp
 | succ n ih => rw [numerator_succ,map_numeratorStep,ih,numerator_succ]
theorem mapped_globalPolynomial_coeff_mem
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (v:Fin 4 → M)
   (hv:∀ i,v i∈E)
   (hF:MvPolynomial.eval₂Hom φ v (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ v
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (w j:ℕ):
   (globalPolynomial φ (MvPolynomial.map c F) v hF hreg w).coeff j∈E:=by
 apply globalPolynomial_coeff_mem_of_evaluations E φ (MvPolynomial.map c F)
   v hF hreg w (hv 0) _ _ j
 · intro n
   rw [←map_numerator c F n,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (numerator k F n)
 · unfold polyH
   rw [MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom]
   exact mv_eval_mem E (φ.comp c) hc v hv (MvPolynomial.pderiv (2:Fin 4) F)
theorem solution_coeff_mem_of_regular_point
   (E:Subfield M) (c:k →+*L) (φ:L →+*M)
   (hc:∀ a,φ (c a)∈E) (F:Poly4 k) (P:Polynomial L) (γ:L) (ξ:M)
   (hsolution:specialization L P γ (MvPolynomial.map c F)=0)
   (hreg:MvPolynomial.eval₂Hom φ (polynomialPoint φ P γ ξ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map c F))≠0)
   (hv:∀ i,polynomialPoint φ P γ ξ i∈E)
   (p w:ℕ) [CharP M p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   φ (P.coeff j)∈E:=by
 have hmem:=mapped_globalPolynomial_coeff_mem E c φ hc F
   (polynomialPoint φ P γ ξ) hv
   (polynomialPoint_relation φ (MvPolynomial.map c F) P γ ξ hsolution)
   hreg w j
 rw [globalPolynomial_eq_map_of_solution φ (MvPolynomial.map c F) P γ ξ
   hsolution hreg p w hw hP,Polynomial.coeff_map] at hmem
 exact hmem
end
end ProximityPrize.SubmissionLower.RCN258
end PackedLegacy_E4

/-! Packed from ProximityPrize.SubmissionLower.J2. -/
section PackedLegacy_J2
namespace ProximityPrize.SubmissionLower.RCN083
open RCN077 RCN313 RCN269 RCN233 RCN139 RCN347 RCN047 RCN217 RCN048 RCN136 RCN258
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 15000
variable {K L Ω:Type} [Field K] [Field L] [Field Ω]
theorem map_agreementNumerator_base
   (c:K →+*L) (F:Poly4 K) (w:ℕ) (a:ℕ → K) (x u0 u1:K):
   MvPolynomial.map c (agreementNumerator F w a x u0 u1)=
     agreementNumerator (MvPolynomial.map c F) w (fun j => c (a j))
       (c x) (c u0) (c u1):=by
 simp only [agreementNumerator,clearedTaylorNumerator,commonNumeratorTerm,
   affineSeedPolynomial,map_sub,map_sum,map_add,map_mul,map_pow,MvPolynomial.map_C,
   MvPolynomial.map_X,map_numerator,polyH,MvPolynomial.pderiv_map]
theorem globalPolynomial_mul_factor
   (c:K →+*L) (F Q:Poly4 K) (v:Fin 4 → L)
   (hF:MvPolynomial.eval₂Hom c v F=0)
   (hQ:MvPolynomial.eval₂Hom c v Q≠0)
   (hregF:MvPolynomial.eval₂Hom c v (polyH K F)≠0)
   (hprod:MvPolynomial.eval₂Hom c v (F*Q)=0)
   (hregprod:MvPolynomial.eval₂Hom c v (polyH K (F*Q))≠0)
   (w:ℕ):
   globalPolynomial c (F*Q) v hprod hregprod w=
     globalPolynomial c F v hF hregF w:=by
 let ev:=MvPolynomial.eval₂Hom c v
 change ev F=0 at hF
 change ev Q≠0 at hQ
 change ev (polyH K F)≠0 at hregF
 have hHscale:ev (polyH K (F*Q))=ev (polyH K F)*ev Q:=by
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul,hF,zero_mul,add_zero]
 have hNscale (j:ℕ):ev (numerator K (F*Q) j)=
     ev Q^(2*j)*ev (numerator K F j):=by
   obtain ⟨A,hA⟩:=factor_dvd_numerator_sub_power F Q j
   have h:=congrArg ev hA
   simp only [map_sub,map_mul,map_pow,hF,zero_mul] at h
   exact sub_eq_zero.mp h
 have hrecon:reconstructedPolynomial c (F*Q) v hprod hregprod w=
     reconstructedPolynomial c F v hF hregF w:=by
   ext j
   simp only [reconstructedPolynomial,jetPolynomial_coeff]
   by_cases hj:j<w+1
   · rw [if_pos hj,if_pos hj]
     rw [jetCoefficient_eq_evaluated_numerator,
       jetCoefficient_eq_evaluated_numerator]
     change ev (numerator K (F*Q) j)*(ev (polyH K (F*Q)))⁻¹^(2*j)/
         (j.factorial:L)=
       ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j)/
         (j.factorial:L)
     rw [hNscale,hHscale,mul_inv,mul_pow]
     have hcancel:ev Q^(2*j)*(ev Q)⁻¹^(2*j)=1:=by
       rw [←mul_pow,mul_inv_cancel₀ hQ,one_pow]
     calc
       _=(ev Q^(2*j)*(ev Q)⁻¹^(2*j))*
           (ev (numerator K F j)*(ev (polyH K F))⁻¹^(2*j))/
             (j.factorial:L):=by ring
       _=_:=by rw [hcancel,one_mul]
   · rw [if_neg hj,if_neg hj]
 unfold globalPolynomial
 rw [hrecon]
theorem original_factor_agreement_proper
   (φ:Polynomial K →+*Ω) (F Q:Poly4 K)
   (G:MvPolynomial (Fin 3) Ω)
   (hGF:G∣surfaceMap φ F)
   (w:ℕ) (c:ℕ → K) (x u0 u1:K)
   (hproper:¬G∣surfaceMap φ
     (agreementNumerator (F*Q) w c x u0 u1)):
   ¬F∣agreementNumerator F w c x u0 u1:=by
 intro hFcut
 have hcut:G∣surfaceMap φ
     (agreementNumerator F w c x u0 u1):=
   hGF.trans (map_dvd (surfaceMap φ) hFcut)
 have hscaled:G∣surfaceMap φ
     (Q^(2*w)*agreementNumerator F w c x u0 u1):=by
   have h:=dvd_mul_of_dvd_right hcut
     (surfaceMap φ Q^(2*w))
   simpa only [map_mul,map_pow,mul_comm] using h
 have hdiff:G∣surfaceMap φ
     (agreementNumerator (F*Q) w c x u0 u1-
       Q^(2*w)*agreementNumerator F w c x u0 u1):=
   hGF.trans (map_dvd (surfaceMap φ)
     (factor_dvd_agreement_sub_power F Q w c x u0 u1))
 apply hproper
 simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using dvd_add hdiff hscaled
end
end ProximityPrize.SubmissionLower.RCN083
end PackedLegacy_J2

/-! Packed from ProximityPrize.SubmissionLower.EF. -/
section PackedLegacy_EF
namespace ProximityPrize.SubmissionLower.RCN126
open RCN077 RCN231 RCN229 RCN139 RCN319 RCN258
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option synthInstance.maxHeartbeats 200000
variable {k L:Type*} [Field k] [Field L] [Algebra k L]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq L:=Classical.decEq L
def freshPoint (P:Polynomial L) (γ:L):Fin 4 → RatFunc L:=
 polynomialPoint (algebraMap L (RatFunc L)) P γ RatFunc.X
def jetField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k (Set.range (freshPoint P γ))
def coefficientField (P:Polynomial L) (γ:L):IntermediateField k (RatFunc L):=
 IntermediateField.adjoin k
   (insert RatFunc.X (insert (algebraMap L (RatFunc L) γ)
     (Set.range (fun j:ℕ => algebraMap L (RatFunc L) (P.coeff j)))))
@[simp] theorem freshPoint_X (P:Polynomial L) (γ:L):
   freshPoint P γ 0=RatFunc.X:=rfl
@[simp] theorem freshPoint_Z (P:Polynomial L) (γ:L):
   freshPoint P γ 3=algebraMap L (RatFunc L) γ:=rfl
theorem fresh_eval_eq (P:Polynomial L) (γ:L) (Q:Poly4 L):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ) Q=
     algebraMap (Polynomial L) (RatFunc L) (specialization L P γ Q):=by
 rw [freshPoint,eval_polynomialPoint_eq_specialization]
 exact RatFunc.aeval_X_left_eq_algebraMap _
theorem freshPoint_regular (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0):
   MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0:=by
 rw [fresh_eval_eq]
 exact RatFunc.algebraMap_ne_zero hreg
theorem coefficient_mem_of_freshPoint_mem
   (E:IntermediateField k (RatFunc L))
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (hv:∀ i,freshPoint P γ i∈E)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈E:=by
 apply solution_coeff_mem_of_regular_point E.toSubfield (algebraMap k L)
   (algebraMap L (RatFunc L)) _ F P γ RatFunc.X hsolution
   (freshPoint_regular F P γ hreg) hv p w hw hP j
 intro a
 change algebraMap k (RatFunc L) a∈E
 exact E.algebraMap_mem a
theorem coefficient_mem_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w) (j:ℕ):
   algebraMap L (RatFunc L) (P.coeff j)∈jetField (k:=k) P γ:=by
 apply coefficient_mem_of_freshPoint_mem (jetField (k:=k) P γ)
   F P γ hsolution hreg _ p w hw hP j
 intro i
 exact IntermediateField.subset_adjoin k _ ⟨i,rfl⟩
theorem jetField_le_coefficientField (P:Polynomial L) (γ:L):
   jetField (k:=k) P γ ≤ coefficientField (k:=k) P γ:=by
 let E:=coefficientField (k:=k) P γ
 have hX:(RatFunc.X:RatFunc L)∈E:=
   IntermediateField.subset_adjoin k _ (Or.inl rfl)
 have hγ:algebraMap L (RatFunc L) γ∈E:=
   IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 have hc:∀ j,algebraMap L (RatFunc L) (P.coeff j)∈E:=
   fun j => IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
 apply IntermediateField.adjoin_le_iff.mpr
 rintro x ⟨i,rfl⟩
 fin_cases i
 · exact hX
 · exact polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L)) P hc
     RatFunc.X hX
 · apply polynomial_eval_mem E.toSubfield (algebraMap L (RatFunc L))
     P.derivative _ RatFunc.X hX
   intro j
   rw [Polynomial.coeff_derivative,map_mul]
   exact E.mul_mem (hc _) (by simpa using E.natCast_mem (j+1))
 · exact hγ
theorem coefficientField_le_jetField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   coefficientField (k:=k) P γ ≤ jetField (k:=k) P γ:=by
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨0,rfl⟩
 rcases hx with rfl | hx
 · exact IntermediateField.subset_adjoin k _ ⟨3,rfl⟩
 obtain ⟨j,rfl⟩:=hx
 exact coefficient_mem_jetField F P γ hsolution hreg p w hw hP j
theorem fresh_jetField_eq_coefficientField
   (F:Poly4 k) (P:Polynomial L) (γ:L)
   (hsolution:specialization L P γ (MvPolynomial.map (algebraMap k L) F)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   jetField (k:=k) P γ=coefficientField (k:=k) P γ:=
 le_antisymm (jetField_le_coefficientField P γ)
   (coefficientField_le_jetField F P γ hsolution hreg p w hw hP)
end
end ProximityPrize.SubmissionLower.RCN126
end PackedLegacy_EF

/-! Packed from ProximityPrize.SubmissionLower.GS. -/
section PackedLegacy_GS
namespace ProximityPrize.SubmissionLower.RCN321
noncomputable section
variable {k B E:Type} [Field k] [Field B] [Field E]
 [Algebra k B] [Algebra B E] [Algebra k E] [IsScalarTower k B E]
theorem trdeg_le_one_of_tower
   (hE:Algebra.trdeg k E ≤ 2) (htrans:Algebra.Transcendental B E):
   Algebra.trdeg k B ≤ 1:=by
 letI:Algebra.Transcendental B E:=htrans
 have hb:0 < Algebra.trdeg B E:=trdeg_pos B E
 have hsum:Algebra.trdeg k B+Algebra.trdeg B E=Algebra.trdeg k E:=
   trdeg_add_eq k B
 have hab:Algebra.trdeg k B+Algebra.trdeg B E ≤ 2:=by
   rw [hsum]
   exact hE
 by_contra hnot
 have ha:(1:Cardinal) < Algebra.trdeg k B:=lt_of_not_ge hnot
 have htwo:(2:Cardinal) ≤ Algebra.trdeg k B:=by
   have h:=Cardinal.add_one_le_of_lt ha
   norm_num at h
   exact h
 have hbone:(1:Cardinal) ≤ Algebra.trdeg B E:=Cardinal.one_le_iff_pos.mpr hb
 have hthree:(3:Cardinal) ≤ Algebra.trdeg k B+Algebra.trdeg B E:=by
   calc
     (3:Cardinal)=2+1:=by norm_num
     _ ≤ _:=add_le_add htwo hbone
 have:(3:Cardinal) ≤ 2:=hthree.trans hab
 norm_num at this
section RationalExtension
variable {k L:Type} [Field k] [Field L] [Algebra k L]
theorem coefficient_trdeg_le_one_of_rational_extension
   (B:IntermediateField k L) (E:IntermediateField k (RatFunc L))
   (hmap:B.map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤ E)
   (hX:(RatFunc.X:RatFunc L)∈E)
   (hE:Algebra.trdeg k E ≤ 2):Algebra.trdeg k B ≤ 1:=by
 let f:L →ₐ[k] RatFunc L:=IsScalarTower.toAlgHom k L (RatFunc L)
 let bToE:B →ₐ[k] E:=
   (IntermediateField.inclusion hmap).comp (B.equivMap f).toAlgHom
 letI:Algebra B E:=bToE.toRingHom.toAlgebra
 letI:IsScalarTower k B E:=IsScalarTower.of_algebraMap_eq fun c => by
   change bToE (algebraMap k B c)=algebraMap k E c
   exact bToE.commutes c
 let xE:E:=⟨RatFunc.X,hX⟩
 have hcomp:RingHom.comp (algebraMap L (RatFunc L)) B.val=
     RingHom.comp E.val (algebraMap B E):=by
   ext b
   rfl
 have hxE:Transcendental B xE:=
   (show Transcendental L (RatFunc.X:RatFunc L) from RatFunc.transcendental_X).of_ringHom_of_comp_eq
     B.val E.val B.val.injective hcomp
 exact trdeg_le_one_of_tower hE ⟨xE,hxE⟩
end RationalExtension
end
end ProximityPrize.SubmissionLower.RCN321
end PackedLegacy_GS

/-! Packed from ProximityPrize.SubmissionLower.A7. -/
section PackedLegacy_A7
namespace ProximityPrize.SubmissionLower.RCN062
open RCN126
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
def baseCoefficientField (P:Polynomial L) (γ:L):IntermediateField k L:=
 IntermediateField.adjoin k
   (insert γ (Set.range (fun j:ℕ => P.coeff j)))
theorem baseCoefficientField_map_le (P:Polynomial L) (γ:L):
   (baseCoefficientField (k:=k) P γ).map (IsScalarTower.toAlgHom k L (RatFunc L)) ≤
     coefficientField (k:=k) P γ:=by
 rw [IntermediateField.map_le_iff_le_comap]
 apply IntermediateField.adjoin_le_iff.mpr
 intro x hx
 rcases hx with h | hx
 · rw [h]
   change algebraMap L (RatFunc L) γ∈coefficientField (k:=k) P γ
   exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inl rfl))
 obtain ⟨j,hj⟩:=hx
 rw [←hj]
 change algebraMap L (RatFunc L) (P.coeff j)∈coefficientField (k:=k) P γ
 exact IntermediateField.subset_adjoin k _ (Or.inr (Or.inr ⟨j,rfl⟩))
theorem baseCoefficientField_trdeg_le_one
   (P:Polynomial L) (γ:L)
   (hE:Algebra.trdeg k (coefficientField (k:=k) P γ) ≤ 2):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 apply RCN321.coefficient_trdeg_le_one_of_rational_extension
   (B:=baseCoefficientField (k:=k) P γ)
   (E:=coefficientField (k:=k) P γ)
   (baseCoefficientField_map_le P γ) _ hE
 exact IntermediateField.subset_adjoin k _ (Or.inl rfl)
end
end ProximityPrize.SubmissionLower.RCN062
end PackedLegacy_A7

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier21 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.EH. -/
section PackedLegacy_EH
namespace ProximityPrize.SubmissionLower.RCN129
noncomputable section
variable (K L:Type*) [Field K] [Field L] [Algebra K L]
 [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L]
 [FiniteDimensional (RatFunc K) L]
theorem trdeg_le_one_of_functionField:Algebra.trdeg K L ≤ 1:=by
 classical
 unfold Algebra.trdeg
 refine ciSup_le' fun s↦Cardinal.mk_le_one_iff_set_subsingleton.mpr ?_
 intro x hx y hy
 by_contra hxy
 let i:s.1:=⟨x,hx⟩
 let j:s.1:=⟨y,hy⟩
 have ht:Transcendental K x:=s.2.transcendental i
 letI:FiniteDimensional (IntermediateField.adjoin K ({x}:Set L)) L:=
   FunctionField.finiteDimensional_of_adjoin_transcendental ht
 have hyalg:IsAlgebraic (Algebra.adjoin K ({x}:Set L)) y:=
   IntermediateField.isAlgebraic_adjoin_iff.mp
     (Algebra.IsAlgebraic.isAlgebraic y)
 have hji:j∉({i}:Set s.1):=by
   simpa only [Set.mem_singleton_iff] using
     (show j≠i from fun h↦hxy (congrArg Subtype.val h).symm)
 have hytr:=s.2.transcendental_adjoin hji
 have himage:(fun z:s.1↦(z:L)) '' ({i}:Set s.1)={x}:=by
   simp [i]
 change Transcendental (Algebra.adjoin K
   ((fun z:s.1↦(z:L)) '' ({i}:Set s.1))) y at hytr
 rw [himage] at hytr
 exact hytr hyalg
end
end ProximityPrize.SubmissionLower.RCN129
end PackedLegacy_EH

/-! Packed from ProximityPrize.SubmissionLower.GT. -/
section PackedLegacy_GT
namespace ProximityPrize.SubmissionLower.RCN322
open RCN371 RCN011 RCN009
 RCN013
 RCN022 RCN021
 RCN024
 RCN129
noncomputable section
variable (K L:Type) [Field K] [Field L] [Algebra K L]
set_option maxHeartbeats 1000000
theorem trdeg_le_one_of_generated_relations
   (v:Fin 3 → L)
   (hgen:IntermediateField.adjoin K (Set.range v)=⊤)
   (F T:MvPolynomial (Fin 3) K)
   (hF:Irreducible F) (hproper:¬ F∣T)
   (hFzero:MvPolynomial.aeval v F=0)
   (hTzero:MvPolynomial.aeval v T=0):Algebra.trdeg K L ≤ 1:=by
 classical
 by_cases halg:∀ i,IsAlgebraic K (v i)
 · have hA:=IntermediateField.isAlgebraic_adjoin
     (K:=K) (L:=L) (S:=Set.range v) (by
       rintro x ⟨i,rfl⟩
       exact isAlgebraic_iff_isIntegral.mp (halg i))
   rw [hgen] at hA
   letI:=hA
   letI:Algebra.IsAlgebraic K L:=(IntermediateField.topEquiv).isAlgebraic
   exact (trdeg_eq_zero (R:=K) (A:=L)).trans_le zero_le
 push Not at halg
 obtain ⟨i,hi⟩:=halg
 let e:Original K →ₐ[K] L:=MvPolynomial.aeval v
 let initial:Fin 3 ≃ Fin 3:=Equiv.swap 0 i
 have hi0:initial 0=i:=Equiv.swap_apply_left _ _
 have ht0:Transcendental K (e (MvPolynomial.X (initial 0))):=by
   simpa [e,hi0] using (show Transcendental K (v i) from hi)
 have hex:∃ order:Fin 3 ≃ Fin 3,
     Transcendental K (e (MvPolynomial.X (order 0)))∧
     0 < (planeMap K order F).natDegree:=by
   have hirr:=rationalMap_irreducible_of_evaluation K L initial e F hF hFzero ht0
   rcases positive_degree_of_irreducible (rationalMap K initial F) hirr with h0 | h1
   · refine ⟨initial,ht0,?_⟩
     change 0 < (bivariateEquiv (RatFunc K) (rationalMap K initial F)).natDegree
     rwa [bivariateEquiv_natDegree]
   · exact ⟨swapOtherOrder initial,by simpa only [swapOtherOrder_zero] using ht0,
       by rwa [swapped_outer_degree]⟩
 obtain ⟨order,ht,hpositive⟩:=hex
 let base:=elementEmbedding K L (e (MvPolynomial.X (order 0))) ht
 letI:Algebra (RatFunc K) L:=base.toRingHom.toAlgebra
 letI:IsScalarTower K (RatFunc K) L:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hpair:IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)=⊤:=by
   let S:=IntermediateField.adjoin (RatFunc K)
     ({e (MvPolynomial.X (order 2)),e (MvPolynomial.X (order 1))}:Set L)
   have hcoords:Set.range v ⊆ S.restrictScalars K:=by
     rintro x ⟨l,rfl⟩
     obtain ⟨j,rfl⟩:=order.surjective l
     have hj:j=0∨j=1∨j=2:=by omega
     rcases hj with rfl | rfl | rfl
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)
       change elementEmbedding K L _ ht _∈S at hm
       rw [elementEmbedding_variable] at hm
       simpa [e] using hm
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_right (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
     · simpa [S,e] using IntermediateField.mem_adjoin_pair_left (RatFunc K)
         (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   have htop:S.restrictScalars K=⊤:=by
     apply top_unique
     rw [←hgen]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=K)).mp htop
 have hroot (G:Original K) (hG:e G=0):
     Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (RatFunc K) L)
       (e (MvPolynomial.X (order 2))))
       (e (MvPolynomial.X (order 1))) (planeMap K order G)=0:=by
   rw [←RCN365.planeEval_eq_eval₂]
   change planeEvaluation K L order e ht (planeMap K order G)=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   exact hG
 have hirr:=planeMap_irreducible_of_evaluation K L order e F hF hFzero ht
 have hproperPlane:¬ planeMap K order F∣planeMap K order T:=by
   intro h
   exact hproper ((planeMap_dvd_iff_of_evaluation K L order e F T hF hFzero ht).mp h)
 letI:FiniteDimensional (RatFunc K) L:=finite_of_proper_plane_roots
   (planeMap K order F) (planeMap K order T) hirr hpositive hproperPlane
   (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1)))
   (hroot F hFzero) (hroot T hTzero) hpair
 exact trdeg_le_one_of_functionField K L
theorem trdeg_adjoin_le_one_of_irreducible_proper_relations
   (v:Fin 3 → L) (F T:MvPolynomial (Fin 3) K)
   (hF:Irreducible F) (hproper:¬ F∣T)
   (hFzero:MvPolynomial.aeval v F=0)
   (hTzero:MvPolynomial.aeval v T=0):
   Algebra.trdeg K (IntermediateField.adjoin K (Set.range v)) ≤ 1:=by
 classical
 let E:=IntermediateField.adjoin K (Set.range v)
 let vE:Fin 3 → E:=fun i↦⟨v i,IntermediateField.subset_adjoin K _ ⟨i,rfl⟩⟩
 have hgen:IntermediateField.adjoin K (Set.range vE)=⊤:=by
   apply IntermediateField.map_injective E.val
   rw [IntermediateField.adjoin_map, ←AlgHom.fieldRange_eq_map,
     IntermediateField.fieldRange_val]
   have himage:E.val '' Set.range vE=Set.range v:=by
     ext x
     simp [vE]
   rw [himage]
 have heval:E.val.comp (MvPolynomial.aeval vE)=MvPolynomial.aeval v:=by
   ext i
   simp [vE]
 have hroot (G:MvPolynomial (Fin 3) K) (hG:MvPolynomial.aeval v G=0):
     MvPolynomial.aeval vE G=0:=by
   apply E.val.injective
   change (E.val.comp (MvPolynomial.aeval vE)) G=E.val 0
   rw [heval,hG,map_zero]
 exact trdeg_le_one_of_generated_relations K E vE hgen F T hF hproper
   (hroot F hFzero) (hroot T hTzero)
end
end ProximityPrize.SubmissionLower.RCN322
end PackedLegacy_GT

/-! Packed from ProximityPrize.SubmissionLower.EG. -/
section PackedLegacy_EG
namespace ProximityPrize.SubmissionLower.RCN127
open RCN077 RCN319 RCN136
 RCN132 RCN126
 RCN062
 RCN322 RCN129
 RCN022
noncomputable section
variable {k L:Type} [Field k] [Field L] [Algebra k L]
private def freshJet (P:Polynomial L) (γ:L) (i:Fin 4):
   jetField (k:=k) P γ:=
 ⟨freshPoint P γ i,IntermediateField.subset_adjoin k _ ⟨i,rfl⟩⟩
@[simp] private theorem freshJet_val (P:Polynomial L) (γ:L) (i:Fin 4):
   ((freshJet (k:=k) P γ i:jetField (k:=k) P γ):RatFunc L)=
     freshPoint P γ i:=rfl
private def freshOtherJet (P:Polynomial L) (γ:L) (i:Fin 3):
   jetField (k:=k) P γ:=freshJet (k:=k) P γ i.succ
private theorem freshTau_transcendental (P:Polynomial L) (γ:L):
   Transcendental k (freshJet (k:=k) P γ 0):=by
 intro h
 have h':IsAlgebraic k (RatFunc.X:RatFunc L):=by
   exact IntermediateField.isAlgebraic_iff.mp h
 exact (RatFunc.transcendental_X.restrictScalars
   (algebraMap k L).injective) h'
set_option maxHeartbeats 1000000 in
theorem baseCoefficientField_trdeg_le_one_of_fresh_proper_relations
   (F T:Poly4 k) (P:Polynomial L) (γ:L)
   (hF:Irreducible F)
   (hpos:0 < F.degreeOf 1+F.degreeOf 2+F.degreeOf 3)
   (hproper:¬ F∣T)
   (hFsolution:specialization L P γ
     (MvPolynomial.map (algebraMap k L) F)=0)
   (hTsolution:specialization L P γ
     (MvPolynomial.map (algebraMap k L) T)=0)
   (hreg:specialization L P γ
     (MvPolynomial.pderiv (2:Fin 4)
       (MvPolynomial.map (algebraMap k L) F))≠0)
   (p w:ℕ) [CharP L p] (hw:w < p) (hP:P.natDegree ≤ w):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 classical
 let E:=jetField (k:=k) P γ
 let full:Fin 4 → E:=freshJet (k:=k) P γ
 let v:Fin 3 → E:=freshOtherJet (k:=k) P γ
 let τ:E:=freshJet (k:=k) P γ 0
 have hτ:Transcendental k τ:=freshTau_transcendental P γ
 let rawEquiv:=FractionRing.algEquiv (Polynomial k) (RatFunc k)
 let coeffEquiv:RationalCoefficients k ≃ₐ[k] RatFunc k:=rawEquiv.restrictScalars k
 let baseRat:RatFunc k →ₐ[k] E:=elementEmbedding k E τ hτ
 let base:RationalCoefficients k →ₐ[k] E:=baseRat.comp coeffEquiv.toAlgHom
 letI:Algebra (RationalCoefficients k) E:=base.toRingHom.toAlgebra
 letI:IsScalarTower k (RationalCoefficients k) E:=
   IsScalarTower.of_algebraMap_eq fun c↦(base.commutes c).symm
 have hbaseX:base
     (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=τ:=by
   change baseRat (rawEquiv
     (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X))=τ
   rw [rawEquiv.commutes,elementEmbedding_variable]
 have hfull:IntermediateField.adjoin k (Set.range full)=⊤:=by
   apply IntermediateField.map_injective E.val
   rw [IntermediateField.adjoin_map, ←AlgHom.fieldRange_eq_map,
     IntermediateField.fieldRange_val]
   have himage:E.val '' Set.range full=Set.range (freshPoint P γ):=by
     ext x
     simp [full,freshJet]
   rw [himage]
   rfl
 have hgen:IntermediateField.adjoin (RationalCoefficients k) (Set.range v)=⊤:=by
   let S:=IntermediateField.adjoin (RationalCoefficients k) (Set.range v)
   have hcoords:Set.range full ⊆ S.restrictScalars k:=by
     rintro x ⟨i,rfl⟩
     refine Fin.cases ?_ (fun j↦?_) i
     · have hm:=S.algebraMap_mem
         (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)
       change base
         (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)∈S at hm
       rw [hbaseX] at hm
       exact hm
     · exact IntermediateField.subset_adjoin (RationalCoefficients k) _ ⟨j,rfl⟩
   have htop:S.restrictScalars k=⊤:=by
     apply top_unique
     rw [←hfull]
     exact IntermediateField.adjoin_le_iff.mpr hcoords
   exact (IntermediateField.restrictScalars_eq_top_iff (K:=k)).mp htop
 have hsurface:∀ G:Poly4 k,
     MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
         (rationalSurfaceMap k G)=
       MvPolynomial.eval₂Hom (algebraMap k E) full G:=by
   intro G
   have heq:(MvPolynomial.eval₂Hom
         (algebraMap (RationalCoefficients k) E) v).comp (rationalSurfaceMap k)=
       MvPolynomial.eval₂Hom (algebraMap k E) full:=by
     apply MvPolynomial.ringHom_ext
     · intro a
       simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_C,
         MvPolynomial.eval₂Hom_C]
       change base
         (algebraMap (Polynomial k) (RationalCoefficients k) (Polynomial.C a))=
           algebraMap k E a
       calc
         _=base (algebraMap k (RationalCoefficients k) a):=by
           congr 1
         _=algebraMap k E a:=base.commutes a
     · intro i
       refine Fin.cases ?_ (fun j↦?_) i
       · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_zero,
           MvPolynomial.eval₂Hom_C,
           MvPolynomial.eval₂Hom_X']
         change base
           (algebraMap (Polynomial k) (RationalCoefficients k) Polynomial.X)=full 0
         exact hbaseX
       · simp only [RingHom.comp_apply,rationalSurfaceMap,surfaceMap_X_succ,
           MvPolynomial.eval₂Hom_X']
         rfl
   exact RingHom.congr_fun heq G
 have hcoeffcomp:E.val.toRingHom.comp
       (MvPolynomial.eval₂Hom (algebraMap k E) full)=
     (MvPolynomial.eval₂Hom (algebraMap L (RatFunc L)) (freshPoint P γ)).comp
       (MvPolynomial.map (algebraMap k L)):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_C,
       MvPolynomial.map_C]
     change algebraMap k (RatFunc L) a=
       algebraMap L (RatFunc L) (algebraMap k L a)
     exact IsScalarTower.algebraMap_apply k L (RatFunc L) a
   · intro i
     simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
       MvPolynomial.eval₂Hom_X',
       MvPolynomial.map_X]
     change E.val (full i)=freshPoint P γ i
     rfl
 have hfullroot (G:Poly4 k)
     (hG:specialization L P γ (MvPolynomial.map (algebraMap k L) G)=0):
     MvPolynomial.eval₂Hom (algebraMap k E) full G=0:=by
   apply E.val.injective
   change (E.val.toRingHom.comp
     (MvPolynomial.eval₂Hom (algebraMap k E) full)) G=E.val 0
   rw [hcoeffcomp,RingHom.comp_apply,fresh_eval_eq,hG,map_zero,map_zero]
 have hFroot:MvPolynomial.aeval v (rationalSurfaceMap k F)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
     (rationalSurfaceMap k F)=0
   rw [hsurface]
   exact hfullroot F hFsolution
 have hTroot:MvPolynomial.aeval v (rationalSurfaceMap k T)=0:=by
   change MvPolynomial.eval₂Hom (algebraMap (RationalCoefficients k) E) v
     (rationalSurfaceMap k T)=0
   rw [hsurface]
   exact hfullroot T hTsolution
 have hirr:Irreducible (rationalSurfaceMap k F):=
   rationalSurfaceMap_irreducible k F hF hpos
 have hproperRat:¬ rationalSurfaceMap k F∣rationalSurfaceMap k T:=by
   intro h
   exact hproper ((rationalSurfaceMap_dvd_iff k F T hF hpos).mp h)
 have hrelative:Algebra.trdeg (RationalCoefficients k) E ≤ 1:=
   trdeg_le_one_of_generated_relations (RationalCoefficients k) E v hgen
     (rationalSurfaceMap k F) (rationalSurfaceMap k T)
     hirr hproperRat hFroot hTroot
 have hbaseRat:Algebra.trdeg k (RatFunc k) ≤ 1:=
   trdeg_le_one_of_functionField k (RatFunc k)
 have hbase:Algebra.trdeg k (RationalCoefficients k) ≤ 1:=by
   rw [coeffEquiv.trdeg_eq]
   exact hbaseRat
 have hsum:Algebra.trdeg k (RationalCoefficients k)+
     Algebra.trdeg (RationalCoefficients k) E=Algebra.trdeg k E:=
   trdeg_add_eq k (RationalCoefficients k)
 have hjet:Algebra.trdeg k E ≤ 2:=by
   rw [←hsum]
   exact (add_le_add hbase hrelative).trans_eq (by norm_num)
 have hfield:=fresh_jetField_eq_coefficientField F P γ hFsolution hreg p w hw hP
 change Algebra.trdeg k (jetField (k:=k) P γ) ≤ 2 at hjet
 rw [hfield] at hjet
 exact baseCoefficientField_trdeg_le_one P γ hjet
end
end ProximityPrize.SubmissionLower.RCN127
end PackedLegacy_EG

/-! Packed from ProximityPrize.SubmissionLower.H9. -/
section PackedLegacy_H9
namespace ProximityPrize.SubmissionLower.RCN059
open scoped BigOperators
noncomputable section
variable {k F L Γ:Type*} [Field k] [Field F] [Field L]
 [LinearOrderedCommGroupWithZero Γ]
local instance:DecidableEq F:=Classical.decEq F
def ResidueApprox (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F):Prop:=
 ∀ f:F,v (φ f) ≤ 1 → ∃ c:k,v (φ (f-κ c)) < 1
def ConstantPolynomialUnit (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (w:ℕ):Prop:=
 ∀ c:Fin (w+1) → k,(∃ i,c i≠0) →
   v (∑ i,φ (κ (c i))*x^(i:ℕ))=1
private theorem sum_eq_one_of_close {w:ℕ}
   (v:Valuation L Γ) (x:L) (hx:v x=1)
   (b c:Fin (w+1) → L)
   (hclose:∀ i,v (b i-c i) < 1)
   (hc:v (∑ i,c i*x^(i:ℕ))=1):
   v (∑ i,b i*x^(i:ℕ))=1:=by
 have herr:v (∑ i,(b i-c i)*x^(i:ℕ)) < 1:=by
   apply v.map_sum_lt (by simp)
   intro i _
   simpa only [map_mul,map_pow,hx,one_pow,mul_one] using hclose i
 have hsplit:(∑ i,b i*x^(i:ℕ))=
     (∑ i,c i*x^(i:ℕ))+
     (∑ i,(b i-c i)*x^(i:ℕ)):=by
   rw [←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl
   intro i _
   ring
 rw [hsplit,v.map_add_eq_of_lt_left (by simpa only [hc] using herr),hc]
theorem valuation_sum_eq_dominant_of_residueApprox {w:ℕ}
   (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (j:Fin (w+1)) (haj:a j≠0)
   (hmax:∀ i,v (φ (a i)) ≤ v (φ (a j))):
   v (∑ i,φ (a i)*x^(i:ℕ))=v (φ (a j)):=by
 have hφj:φ (a j)≠0:=by
   intro h
   apply haj
   apply φ.injective
   simpa using h
 have hvj:v (φ (a j))≠0:=(Valuation.ne_zero_iff v).mpr hφj
 have hnorm:∀ i,v (φ (a i/a j)) ≤ 1:=by
   intro i
   rw [map_div₀,map_div₀]
   exact (div_le_one₀ (zero_lt_iff.mpr hvj)).mpr (hmax i)
 choose c hc using fun i => hres (a i/a j) (hnorm i)
 have hcj:c j≠0:=by
   intro h
   have hbad:=hc j
   simpa [h,haj] using hbad
 have hsum:v (∑ i,φ (a i/a j)*x^(i:ℕ))=1:=by
   apply sum_eq_one_of_close v x hx
     (fun i => φ (a i/a j)) (fun i => φ (κ (c i)))
   · intro i
     simpa only [map_sub] using hc i
   · exact hunit c ⟨j,hcj⟩
 have hscale:(∑ i,φ (a i)*x^(i:ℕ))=
     φ (a j)*(∑ i,φ (a i/a j)*x^(i:ℕ)):=by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro i _
   rw [map_div₀]
   field_simp
 rw [hscale,map_mul,hsum,mul_one]
theorem valuation_coefficient_le_sum_of_residueApprox {w:ℕ}
   (v:Valuation L Γ) (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   v (φ (a i)) ≤ v (∑ j,φ (a j)*x^(j:ℕ)):=by
 classical
 by_cases hai:a i=0
 · simp [hai]
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 obtain ⟨j,_,hmax⟩:=
   Finset.exists_max_image Finset.univ (fun j:Fin (w+1) => v (φ (a j)))
     Finset.univ_nonempty
 have haj:a j≠0:=by
   intro h
   have hz:v (φ (a j))=0:=by simp [h]
   apply hvi
   apply le_antisymm
   · simpa only [hz] using hmax i (Finset.mem_univ i)
   · exact zero_le
 rw [valuation_sum_eq_dominant_of_residueApprox v φ κ x hx hres hunit a j haj
   (fun z => hmax z (Finset.mem_univ z))]
 exact hmax i (Finset.mem_univ i)
theorem coefficient_pole_le_generic_value_of_residueApprox {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ)))
   (φ:F →+*L) (κ:k →+*F)
   (x:L) (hx:v x=1)
   (hres:ResidueApprox v φ κ)
   (hunit:ConstantPolynomialUnit v φ κ x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 have hval:=valuation_coefficient_le_sum_of_residueApprox
   v φ κ x hx hres hunit a i
 by_cases hai:a i=0
 · simp only [hai,map_zero,RCN187.poleOrder,
     WithZero.log_zero,max_self]
   exact le_max_left _ _
 have hφi:φ (a i)≠0:=by
   intro h
   apply hai
   apply φ.injective
   simpa using h
 have hvi:v (φ (a i))≠0:=(Valuation.ne_zero_iff v).mpr hφi
 have hsum:v (∑ j,φ (a j)*x^(j:ℕ))≠0:=
   ne_of_gt ((zero_lt_iff.mpr hvi).trans_le hval)
 exact max_le_max_left 0 ((WithZero.log_le_log hvi hsum).mpr hval)
end
end ProximityPrize.SubmissionLower.RCN059
end PackedLegacy_H9

/-! Packed from ProximityPrize.SubmissionLower.I0. -/
section PackedLegacy_I0
namespace ProximityPrize.SubmissionLower.RCN060
open scoped BigOperators
open Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
variable {k F Γ:Type*} [Field k] [Field F] [Algebra k F]
 [LinearOrderedCommGroupWithZero Γ]
local instance:DecidableEq k:=Classical.decEq k
local instance:DecidableEq F:=Classical.decEq F
theorem polynomial_value_le_one
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,v (κ c) ≤ 1) (f:F) (hf:v f ≤ 1) (p:k[X]):
   v (p.eval₂ κ f) ≤ 1:=by
 rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
 apply v.map_sum_le
 intro i _
 rw [map_mul,map_pow]
 exact mul_le_one₀ (hκ _) zero_le (pow_le_one₀ zero_le hf)
theorem normalize_relation
   {R:Type*} [CommRing R] [IsDomain R] (κ:R →+*F)
   (u:F) (hu:u≠0) (p:R[X]) (hp:p≠0)
   (hev:p.eval₂ κ u=0):
   ∃ q:R[X],q.coeff 0≠0∧q.eval₂ κ u=0:=by
 classical
 induction hn:p.natDegree using Nat.strong_induction_on generalizing p with
 | h n ih =>
   by_cases hzero:p.coeff 0=0
   · obtain ⟨q,hpq⟩:=Polynomial.X_dvd_iff.mpr hzero
     have hq:q≠0:=by
       intro hz
       exact hp (by simp [hpq,hz])
     have hdeg:q.natDegree < n:=by
       rw [hpq,Polynomial.natDegree_X_mul hq] at hn
       omega
     have hqeval:q.eval₂ κ u=0:=by
       rw [hpq,Polynomial.eval₂_mul,Polynomial.eval₂_X] at hev
       exact (mul_eq_zero.mp hev).resolve_left hu
     exact ih q.natDegree hdeg q hq hqeval rfl
   · exact ⟨p,hzero,hev⟩
theorem exists_constant_close_of_small_polynomial [IsAlgClosed k]
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,c≠0 → v (κ c)=1)
   (f:F) (p:k[X]) (hp:p≠0) (hsmall:v (p.eval₂ κ f) < 1):
   ∃ c:k,v (f-κ c) < 1:=by
 classical
 by_contra h
 push_neg at h
 have hge:1 ≤ v (p.eval₂ κ f):=by
   rw [(IsAlgClosed.splits p).eq_prod_roots,Polynomial.eval₂_mul,
     Polynomial.eval₂_C,map_mul,hκ p.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hp),
     one_mul,Polynomial.eval₂_multiset_prod,map_multiset_prod]
   simp only [Multiset.map_map,Polynomial.eval₂_sub,Polynomial.eval₂_X,
     Polynomial.eval₂_C,Function.comp_def]
   exact Multiset.one_le_prod_map (fun c _ => h c)
 exact (not_lt_of_ge hge) hsmall
theorem constant_coefficient_value_lt_one
   (v:Valuation F Γ) (κ:k →+*F)
   (hκ:∀ c,v (κ c) ≤ 1)
   (u f:F) (hu:v u < 1) (hf:v f ≤ 1)
   (q:Polynomial (Polynomial k))
   (hq:q.eval₂ (Polynomial.eval₂RingHom κ f) u=0):
   v ((q.coeff 0).eval₂ κ f) < 1:=by
 have hcoeff:∀ p:k[X],v ((Polynomial.eval₂RingHom κ f) p) ≤ 1:=
   fun p => polynomial_value_le_one v κ hκ f hf p
 have htail:v (q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u) ≤ 1:=by
   rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def]
   apply v.map_sum_le
   intro i _
   rw [map_mul,map_pow]
   exact mul_le_one₀ (hcoeff _) zero_le (pow_le_one₀ zero_le hu.le)
 have hdecomp:=congrArg
   (fun p:Polynomial (Polynomial k) => p.eval₂ (Polynomial.eval₂RingHom κ f) u)
   (Polynomial.X_mul_divX_add q)
 simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_X,
   Polynomial.eval₂_C,hq,Polynomial.coe_eval₂RingHom] at hdecomp
 have heq:(q.coeff 0).eval₂ κ f=
     -(u*q.divX.eval₂ (Polynomial.eval₂RingHom κ f) u):=by
   rw [eq_neg_iff_add_eq_zero]
   simpa only [add_comm] using hdecomp
 rw [heq,v.map_neg,map_mul]
 exact (mul_le_mul' le_rfl htail).trans_lt (by simpa using hu)
theorem exists_bivariate_relation_of_trdeg_one
   (htrdeg:Algebra.trdeg k F=1) (u f:F):
   ∃ q:Polynomial (Polynomial k),q≠0∧
     q.eval₂ (Polynomial.eval₂RingHom (algebraMap k F) f) u=0:=by
 have hnot:¬ AlgebraicIndependent k ![f,u]:=by
   intro hi
   have hc:=hi.lift_cardinalMk_le_trdeg
   rw [htrdeg] at hc
   norm_num at hc
 rw [algebraicIndependent_iff] at hnot
 push_neg at hnot
 obtain ⟨p,hpval,hp⟩:=hnot
 let e:=Polynomial.Bivariate.equivMvPolynomial k
 let q:Polynomial (Polynomial k):=e.symm p
 have hq:q≠0:=by
   intro hz
   apply hp
   have:=congrArg e hz
   simpa [q] using this
 have hmaps:
     (Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom=
       MvPolynomial.aeval ![f,u]:=by
   ext i
   fin_cases i <;> simp [e,Polynomial.aevalAeval_C,
     Polynomial.aevalAeval_X,Polynomial.aevalAeval_Y]
 have hev:
     Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u=
       (Polynomial.aevalAeval (R:=k) f u).toRingHom:=by
   ext <;> simp [Polynomial.aevalAeval_C,Polynomial.aevalAeval_X,
     Polynomial.aevalAeval_Y]
 refine ⟨q,hq,?_⟩
 change (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap k F) f) u) q=0
 rw [hev]
 change ((Polynomial.aevalAeval (R:=k) f u).comp e.symm.toAlgHom) p=0
 rw [hmaps]
 exact hpval
theorem exists_constant_approx_of_trdeg_one [IsAlgClosed k]
   (v:Valuation F Γ) [v.IsTrivialOn k]
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v u < 1)
   (f:F) (hf:v f ≤ 1):
   ∃ c:k,v (f-algebraMap k F c) < 1:=by
 have hκ:∀ c:k,v (algebraMap k F c) ≤ 1:=by
   intro c
   by_cases hc:c=0
   · simp [hc]
   · exact (Valuation.IsTrivialOn.eq_one c hc).le
 obtain ⟨p,hp,hpval⟩:=exists_bivariate_relation_of_trdeg_one htrdeg u f
 obtain ⟨q,hq0,hqval⟩:=
   normalize_relation (Polynomial.eval₂RingHom (algebraMap k F) f) u hu0 p hp hpval
 exact exists_constant_close_of_small_polynomial v (algebraMap k F)
   (fun c hc => Valuation.IsTrivialOn.eq_one c hc) f (q.coeff 0) hq0
   (constant_coefficient_value_lt_one v (algebraMap k F) hκ u f hu hf q hqval)
variable {L:Type*} [Field L]
open ProximityPrize.SubmissionLower RCN059
theorem residueApprox_of_trdeg_one [IsAlgClosed k]
   (v:Valuation L Γ) (φ:F →+*L)
   (hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (u:F) (hu0:u≠0) (hu:v (φ u) < 1):
   ResidueApprox v φ (algebraMap k F):=by
 let vF:Valuation F Γ:=v.comap φ
 letI:vF.IsTrivialOn k:=⟨hconst⟩
 intro f hf
 exact exists_constant_approx_of_trdeg_one vF htrdeg u hu0 hu f hf
theorem coefficient_pole_le_of_trdeg_one [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) (φ:F →+*L)
   (hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1)
   (htrdeg:Algebra.trdeg k F=1)
   (x:L) (hx:v x=1)
   (hunit:ConstantPolynomialUnit v φ (algebraMap k F) x w)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v (∑ j,φ (a j)*x^(j:ℕ)):=by
 by_cases hi:v (φ (a i)) ≤ 1
 · have hz:RCN187.poleOrder v (φ (a i))=0:=by
     change max 0 (v (φ (a i))).log=0
     rw [←RCN187.log_max_one,max_eq_left hi,WithZero.log_one]
   rw [hz]
   exact le_max_left _ _
 have hbig:1 < v (φ (a i)):=lt_of_not_ge hi
 let vF:Valuation F (WithZero (Multiplicative ℤ)):=v.comap φ
 haveI:vF.IsNontrivial:=
   ⟨a i,ne_of_gt (zero_lt_one.trans hbig),hbig.ne'⟩
 obtain ⟨u,hu0,hu⟩:=Valuation.IsNontrivial.exists_lt_one (v:=vF)
 exact coefficient_pole_le_generic_value_of_residueApprox v φ (algebraMap k F)
   x hx (residueApprox_of_trdeg_one v φ hconst htrdeg u hu0 hu) hunit a i
theorem constantPolynomialUnit_of_base_constants
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] {w:ℕ}
   (v:Valuation L Γ) [v.IsTrivialOn Ω] (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (x:Ω) (htrans:Transcendental k x):
   ConstantPolynomialUnit v φ (algebraMap k F) (algebraMap Ω L x) w:=by
 classical
 intro c hc
 obtain ⟨i,hi⟩:=hc
 let q:k[X]:=∑ j:Fin (w+1),Polynomial.monomial (j:ℕ) (c j)
 have hcoef:q.coeff (i:ℕ)=c i:=by
   simp only [q,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial]
   rw [Finset.sum_eq_single i]
   · simp
   · intro j _ hji
     have hval:(j:ℕ)≠(i:ℕ):=fun h => hji (Fin.ext h)
     simp [hval]
   · simp
 have hq:q≠0:=by
   intro hzero
   apply hi
   have h:=congrArg (fun p:k[X] => p.coeff (i:ℕ)) hzero
   simpa only [hcoef,Polynomial.coeff_zero] using h
 have hneq:Polynomial.aeval x q≠0:=by
   intro hzero
   apply hq
   apply (transcendental_iff_injective.mp htrans)
   simpa only [map_zero] using hzero
 have hv:v (algebraMap Ω L (Polynomial.aeval x q))=1:=
   Valuation.IsTrivialOn.eq_one _ hneq
 simpa only [q,map_sum,Polynomial.aeval_monomial,map_mul,map_pow,
   ←hcompat] using hv
theorem coefficient_pole_le_generic_evaluation
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F=1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 have hconst:∀ c:k,c≠0 → v (φ (algebraMap k F c))=1:=by
   intro c hc
   rw [hcompat]
   apply Valuation.IsTrivialOn.eq_one
   intro hz
   apply hc
   apply (algebraMap k Ω).injective
   simpa using hz
 have hx0:x≠0:=by
   intro hz
   apply htrans
   rw [hz]
   exact isAlgebraic_zero
 have hx:v (algebraMap Ω L x)=1:=Valuation.IsTrivialOn.eq_one x hx0
 exact coefficient_pole_le_of_trdeg_one v φ hconst htrdeg (algebraMap Ω L x) hx
   (constantPolynomialUnit_of_base_constants v φ hcompat x htrans) a i
end
end ProximityPrize.SubmissionLower.RCN060
end PackedLegacy_I0

/-! Packed from ProximityPrize.SubmissionLower.I1. -/
section PackedLegacy_I1
namespace ProximityPrize.SubmissionLower.RCN061
open scoped BigOperators
open RCN060
noncomputable section
variable {k F L:Type*} [Field k] [Field F] [Field L] [Algebra k F]
theorem coefficient_pole_le_generic_evaluation_of_trdeg_le_one
   {Ω:Type*} [Field Ω] [Algebra k Ω] [Algebra Ω L] [IsAlgClosed k] {w:ℕ}
   (v:Valuation L (WithZero (Multiplicative ℤ))) [v.IsTrivialOn Ω]
   (φ:F →+*L)
   (hcompat:∀ c:k,φ (algebraMap k F c)=
     algebraMap Ω L (algebraMap k Ω c))
   (htrdeg:Algebra.trdeg k F ≤ 1)
   (x:Ω) (htrans:Transcendental k x)
   (a:Fin (w+1) → F) (i:Fin (w+1)):
   RCN187.poleOrder v (φ (a i)) ≤
     RCN187.poleOrder v
       (∑ j,φ (a j)*(algebraMap Ω L x)^(j:ℕ)):=by
 classical
 letI:Decidable (Algebra.trdeg k F=0):=Classical.propDecidable _
 by_cases hz:Algebra.trdeg k F=0
 · letI:Algebra.IsAlgebraic k F:=trdeg_eq_zero_iff.mp hz
   letI:Algebra.IsIntegral k F:=
     Algebra.isAlgebraic_iff_isIntegral.mp (inferInstance:Algebra.IsAlgebraic k F)
   obtain ⟨c,hc⟩:=
     (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=k)).2 (a i)
   have hφ:φ (a i)=algebraMap Ω L (algebraMap k Ω c):=by
     rw [←hc,hcompat]
   have hpole:RCN187.poleOrder v (φ (a i))=0:=by
     rw [hφ]
     change max 0 (v (algebraMap Ω L (algebraMap k Ω c))).log=0
     rw [←RCN187.log_max_one,
       max_eq_left (Valuation.IsTrivialOn.valuation_algebraMap_le_one v _),
       WithZero.log_one]
   rw [hpole]
   exact le_max_left _ _
 · have hone:(1:Cardinal) ≤ Algebra.trdeg k F:=
     Cardinal.one_le_iff_ne_zero.mpr hz
   have heq:Algebra.trdeg k F=1:=le_antisymm htrdeg hone
   exact coefficient_pole_le_generic_evaluation v φ hcompat heq x htrans a i
end
end ProximityPrize.SubmissionLower.RCN061
end PackedLegacy_I1

/-! Packed from ProximityPrize.SubmissionLower.D0. -/
section PackedLegacy_D0
namespace ProximityPrize.SubmissionLower.RCN205
open scoped Classical WithZero
open RCN187 RCN295 RCN095 RCN114 RCN162
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
variable {K L:Type} [Field K] [Field L] [Algebra K L]
abbrev DV (L:Type) [Field L]:=Valuation L (WithZero (Multiplicative ℤ))
def zPole (ν:DV L) (x:Fin 3 → L):ℤ:=poleOrder ν (x 2)
def yzPole (ν:DV L) (x:Fin 3 → L):ℤ:=
 max (poleOrder ν (x 0)) (poleOrder ν (x 2))
def allPole (ν:DV L) (x:Fin 3 → L):ℤ:=
 max (poleOrder ν (x 1)) (yzPole ν x)
def movingPole (ν:DV L) (x:Fin 3 → L) (W:L):ℤ:=
 max (2*allPole ν x) (yzPole ν x+poleOrder ν W)
private theorem pole_nonneg (ν:DV L) (x:L):0 ≤ poleOrder ν x:=
 le_max_left _ _
private theorem val_le_exp_pole (ν:DV L) (x:L):
   ν x ≤ WithZero.exp (poleOrder ν x):=by
 have hn:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 rw [poleOrder, ←log_max_one,WithZero.exp_log hn]
 exact le_max_right _ _
private theorem pole_le_of_val_le (ν:DV L) (x:L) (n:ℤ)
   (hn:0 ≤ n) (h:ν x ≤ WithZero.exp n):poleOrder ν x ≤ n:=by
 have h1:(1:WithZero (Multiplicative ℤ)) ≤ WithZero.exp n:=by
   rw [←WithZero.exp_zero,WithZero.exp_le_exp]
   exact hn
 have hnz:max 1 (ν x)≠0:=ne_of_gt
   (zero_lt_one.trans_le (le_max_left _ _))
 have hh:=(WithZero.log_le_log hnz WithZero.exp_ne_zero).2 (max_le h1 h)
 simpa only [log_max_one,WithZero.log_exp,poleOrder] using hh
theorem pole_add_le (ν:DV L) (x y:L):
   poleOrder ν (x+y) ≤ max (poleOrder ν x) (poleOrder ν y):=by
 apply pole_le_of_val_le ν _ _ ((pole_nonneg ν x).trans (le_max_left _ _))
 exact (ν.map_add x y).trans (max_le
   ((val_le_exp_pole ν x).trans ((WithZero.exp_le_exp).2 (le_max_left _ _)))
   ((val_le_exp_pole ν y).trans ((WithZero.exp_le_exp).2 (le_max_right _ _))))
theorem pole_const_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1) (c:K):
   poleOrder ν (algebraMap K L c) ≤ 0:=by
 apply pole_le_of_val_le ν _ _ le_rfl
 simpa using hν c
theorem pole_const_mul_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1) (c:K) (x:L):
   poleOrder ν (algebraMap K L c*x) ≤ poleOrder ν x:=by
 apply pole_le_of_val_le ν _ _ (pole_nonneg ν x)
 rw [map_mul]
 exact (mul_le_mul' (hν c) (val_le_exp_pole ν x)).trans_eq (one_mul _)
theorem pole_neg (ν:DV L) (x:L):poleOrder ν (-x)=poleOrder ν x:=by
 simp [poleOrder]
def forward (aY v bY aS bS cS:K) (x:Fin 3 → L):Fin 3 → L:=
 forwardResidualPoint (algebraMap K L aY) (algebraMap K L v)
   (algebraMap K L bY) (algebraMap K L aS) (algebraMap K L bS)
   (algebraMap K L cS) x
theorem forward_unit_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (x:Fin 3 → L):
   zPole ν (forward aY v bY aS bS cS x)=zPole ν x∧
   yzPole ν (forward aY v bY aS bS cS x) ≤ yzPole ν x∧
   allPole ν (forward aY v bY aS bS cS x) ≤ allPole ν x:=by
 let A:=algebraMap K L
 have hY:poleOrder ν (A aY+A v*x 0+A bY*x 2) ≤ yzPole ν x:=by
   have h0:=pole_add_le ν (A aY+A v*x 0) (A bY*x 2)
   have h1:=pole_add_le ν (A aY) (A v*x 0)
   have h2:=pole_const_le ν hν aY
   have h3:=pole_const_mul_le ν hν v (x 0)
   have h4:=pole_const_mul_le ν hν bY (x 2)
   have h5:=pole_nonneg ν (x 0)
   dsimp [A] at*
   unfold yzPole
   omega
 have hS:poleOrder ν (A aS+A v*x 1+A bS*x 0+A cS*x 2) ≤
     allPole ν x:=by
   have h0:=pole_add_le ν (A aS+A v*x 1+A bS*x 0) (A cS*x 2)
   have h1:=pole_add_le ν (A aS+A v*x 1) (A bS*x 0)
   have h2:=pole_add_le ν (A aS) (A v*x 1)
   have h3:=pole_const_le ν hν aS
   have h4:=pole_const_mul_le ν hν v (x 1)
   have h5:=pole_const_mul_le ν hν bS (x 0)
   have h6:=pole_const_mul_le ν hν cS (x 2)
   have h7:=pole_nonneg ν (x 1)
   dsimp [A] at*
   unfold allPole yzPole
   omega
 refine ⟨rfl,?_,?_⟩
 · change max (poleOrder ν (A aY+A v*x 0+A bY*x 2))
     (poleOrder ν (x 2)) ≤ yzPole ν x
   exact max_le hY (le_max_right _ _)
 · change max (poleOrder ν (A aS+A v*x 1+A bS*x 0+A cS*x 2))
     (max (poleOrder ν (A aY+A v*x 0+A bY*x 2))
       (poleOrder ν (x 2))) ≤ allPole ν x
   exact max_le hS ((max_le hY (le_max_right _ _)).trans (le_max_right _ _))
theorem forward_inverse (aY v bY aS bS cS:K) (hv:v≠0)
   (x:Fin 3 → L):
   forward (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
     (-v⁻¹*aS+v⁻¹*bS*v⁻¹*aY) (-v⁻¹*bS*v⁻¹)
     (v⁻¹*bS*v⁻¹*bY-v⁻¹*cS) (forward aY v bY aS bS cS x)=x:=by
 have hvL:algebraMap K L v≠0:=(map_ne_zero (algebraMap K L)).2 hv
 funext i
 fin_cases i <;> simp [forward,forwardResidualPoint,map_inv₀] <;>
   field_simp [hvL] <;> ring
theorem forward_unit_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L):
   zPole ν (forward aY v bY aS bS cS x)=zPole ν x∧
   yzPole ν (forward aY v bY aS bS cS x)=yzPole ν x∧
   allPole ν (forward aY v bY aS bS cS x)=allPole ν x:=by
 have h:=forward_unit_le ν hν aY v bY aS bS cS x
 have hi:=forward_unit_le ν hν (-v⁻¹*aY) v⁻¹ (-v⁻¹*bY)
   (-v⁻¹*aS+v⁻¹*bS*v⁻¹*aY) (-v⁻¹*bS*v⁻¹)
   (v⁻¹*bS*v⁻¹*bY-v⁻¹*cS) (forward aY v bY aS bS cS x)
 rw [forward_inverse aY v bY aS bS cS hv x] at hi
 exact ⟨h.1,le_antisymm h.2.1 hi.2.1,le_antisymm h.2.2 hi.2.2⟩
theorem unitAll_eval_pole_le (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (x:Fin 3 → L) (P:MvPolynomial (Fin 3) K)
   (hP:RCN125.PolynomialInFlag unitAllFlag P):
   poleOrder ν (MvPolynomial.eval₂Hom (algebraMap K L) x P) ≤ allPole ν x:=by
 have h:=(poleOrder_eval_le_support ν (algebraMap K L) hν x P).trans
   (supportPoleWeight_le_exponentSetPoleWeight ν x P (flagSupport unitAllFlag)
     ((support_subset_flagSupport_iff _ _).2 hP))
 simpa only [exponentSetPoleWeight_unitAll,allPole,yzPole] using h
theorem unit_flag_poles_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L):
   exponentSetPoleWeight ν (forward aY v bY aS bS cS x) (flagSupport unitZFlag)=
     exponentSetPoleWeight ν x (flagSupport unitZFlag)∧
   exponentSetPoleWeight ν (forward aY v bY aS bS cS x) (flagSupport unitYZFlag)=
     exponentSetPoleWeight ν x (flagSupport unitYZFlag)∧
   exponentSetPoleWeight ν (forward aY v bY aS bS cS x) (flagSupport unitAllFlag)=
     exponentSetPoleWeight ν x (flagSupport unitAllFlag):=by
 simpa only [exponentSetPoleWeight_unitZ,exponentSetPoleWeight_unitYZ,
   exponentSetPoleWeight_unitAll,zPole,yzPole,allPole] using
   forward_unit_invariant ν hν aY v bY aS bS cS hv x
theorem moving_pole_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L)
   (c:K) (hc:c≠0) (P:MvPolynomial (Fin 3) K)
   (hP:RCN125.PolynomialInFlag unitAllFlag P)
   (W W':L)
   (hW:W'=algebraMap K L c*W+
     MvPolynomial.eval₂Hom (algebraMap K L) x P):
   movingPole ν (forward aY v bY aS bS cS x) W'=movingPole ν x W:=by
 let t:=MvPolynomial.eval₂Hom (algebraMap K L) x P
 have ht:=unitAll_eval_pole_le ν hν x P hP
 have hplus:=pole_add_le ν (algebraMap K L c*W) t
 have hmul:=pole_const_mul_le ν hν c W
 have hcL:algebraMap K L c≠0:=(map_ne_zero (algebraMap K L)).2 hc
 have hinv:algebraMap K L c⁻¹*(W'-t)=W:=by
   rw [hW]
   simp [t,map_inv₀,hcL]
 have hback:=pole_const_mul_le ν hν c⁻¹ (W'-t)
 rw [hinv] at hback
 have hsub:=pole_add_le ν W' (-t)
 rw [pole_neg] at hsub
 have hu:=forward_unit_invariant ν hν aY v bY aS bS cS hv x
 unfold movingPole
 rw [hu.2.1,hu.2.2]
 have hab:yzPole ν x ≤ allPole ν x:=le_max_right _ _
 have hn:0 ≤ allPole ν x:=(pole_nonneg ν (x 1)).trans (le_max_left _ _)
 have hw:poleOrder ν W' ≤ max (poleOrder ν W) (poleOrder ν t):=by
   rw [hW]
   exact hplus.trans (max_le_max hmul le_rfl)
 change poleOrder ν t ≤ allPole ν x at ht
 rw [sub_eq_add_neg] at hback
 omega
theorem actual_forward_moving_pole_invariant (ν:DV L)
   (hν:∀ c:K,ν (algebraMap K L c) ≤ 1)
   (aY v bY aS bS cS:K) (hv:v≠0) (x:Fin 3 → L)
   (c:K) (hc:c≠0) (P:MvPolynomial (Fin 3) K)
   (hP:RCN125.PolynomialInFlag unitAllFlag P)
   (W W':L)
   (hW:W'=algebraMap K L c*W+
     MvPolynomial.eval₂Hom (algebraMap K L) x P):
   movingPole ν
     (forwardResidualPoint (algebraMap K L aY) (algebraMap K L v)
       (algebraMap K L bY) (algebraMap K L aS) (algebraMap K L bS)
       (algebraMap K L cS) x) W'=movingPole ν x W:=
 moving_pole_invariant ν hν aY v bY aS bS cS hv x c hc P hP W W' hW
end
end ProximityPrize.SubmissionLower.RCN205
end PackedLegacy_D0

/-! Packed from ProximityPrize.SubmissionLower.H8. -/
section PackedLegacy_H8
namespace ProximityPrize.SubmissionLower.RCN058
open RCN062 RCN061 RCN187 RCN205 RCN002
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
variable {K k L:Type} [Field K] [Field k] [Field L]
 [Algebra K k] [Algebra K L] [Algebra k L] [IsScalarTower K k L]
theorem baseCoefficientField_trdeg_le_one_of_algebraic_constants
   [Algebra.IsAlgebraic K k] (P:Polynomial L) (γ:L)
   (htr:Algebra.trdeg K (baseCoefficientField (k:=K) P γ) ≤ 1):
   Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1:=by
 let S:Set L:=insert γ (Set.range (fun j:ℕ => P.coeff j))
 let BK:IntermediateField K L:=baseCoefficientField (k:=K) P γ
 let Bk:IntermediateField k L:=baseCoefficientField (k:=k) P γ
 let BkK:IntermediateField K L:=Bk.restrictScalars K
 have hBK:BK ≤ BkK:=by
   change IntermediateField.adjoin K S ≤ BkK
   apply IntermediateField.adjoin_le_iff.mpr
   intro z hz
   change z∈Bk
   exact IntermediateField.subset_adjoin k S hz
 let inc:BK →ₐ[K] Bk:={
   toFun:=fun z => ⟨z,hBK z.2⟩
   map_one':=rfl
   map_mul':=fun _ _ => rfl
   map_zero':=rfl
   map_add':=fun _ _ => rfl
   commutes':=fun _ => rfl}
 letI:Algebra BK Bk:=inc.toRingHom.toAlgebra
 letI:IsScalarTower K BK Bk:=
   IsScalarTower.of_algebraMap_eq fun c => (inc.commutes c).symm
 letI:IsScalarTower BK Bk L:=
   IsScalarTower.of_algebraMap_eq fun _ => rfl
 let ACL:IntermediateField BK L:=algebraicClosure BK L
 have hkACL (c:k):algebraMap k L c∈ACL:=by
   apply mem_algebraicClosure_iff.mpr
   have hcK:IsAlgebraic K (algebraMap k L c):=
     (Algebra.IsAlgebraic.isAlgebraic c).algebraMap
   exact hcK.tower_top BK
 let ACLk:IntermediateField k L:=
   ACL.toSubfield.toIntermediateField hkACL
 have hBkACL:Bk ≤ ACLk:=by
   apply IntermediateField.adjoin_le_iff.mpr
   intro z hz
   change z∈ACL
   have hzBK:z∈BK:=IntermediateField.subset_adjoin K S hz
   simpa only [IntermediateField.algebraMap_apply] using
     ACL.algebraMap_mem (⟨z,hzBK⟩:BK)
 letI:Algebra.IsAlgebraic BK Bk:=⟨fun z => by
   apply (isAlgebraic_algHom_iff
     (IsScalarTower.toAlgHom BK Bk L) (algebraMap Bk L).injective).mp
   apply mem_algebraicClosure_iff.mp
   exact hBkACL z.2⟩
 have hzeroE:Algebra.trdeg BK Bk=0:=trdeg_eq_zero
 have hsumE:Algebra.trdeg K BK+Algebra.trdeg BK Bk=Algebra.trdeg K Bk:=
   trdeg_add_eq K BK
 have hKBk:Algebra.trdeg K Bk ≤ 1:=by
   rw [←hsumE,hzeroE,add_zero]
   exact htr
 have hzerok:Algebra.trdeg K k=0:=trdeg_eq_zero
 have hsumk:Algebra.trdeg K k+Algebra.trdeg k Bk=Algebra.trdeg K Bk:=
   trdeg_add_eq K k
 rw [hzerok,zero_add] at hsumk
 exact hsumk.symm ▸ hKBk
theorem coefficient_pole_le_of_trdeg_le_one
   {Ω:Type} [Field Ω] [IsAlgClosed k]
   [Algebra k Ω] [Algebra Ω L] [IsScalarTower k Ω L]
   (P:Polynomial L) (γ:L) (w:ℕ) (hP:P.natDegree ≤ w)
   (htr:Algebra.trdeg k (baseCoefficientField (k:=k) P γ) ≤ 1)
   (x:Ω) (hx:Transcendental k x) (y:L)
   (hy:P.eval (algebraMap Ω L x)=y)
   (v:RCN346.Place Ω L) (j:ℕ):
   poleOrder v.val (P.coeff j) ≤ poleOrder v.val y:=by
 letI:v.val.IsTrivialOn Ω:=v.property.2
 let B:IntermediateField k L:=baseCoefficientField (k:=k) P γ
 have hcoeff (n:ℕ):P.coeff n∈B:=by
   exact IntermediateField.subset_adjoin k _ (Or.inr ⟨n,rfl⟩)
 by_cases hj:j < w+1
 · let i:Fin (w+1):=⟨j,hj⟩
   let a:Fin (w+1) → B:=fun n => ⟨P.coeff n,hcoeff n⟩
   let φ:B →+*L:=B.val.toRingHom
   have hcompat:∀ c:k,φ (algebraMap k B c)=
       algebraMap Ω L (algebraMap k Ω c):=by
     intro c
     exact IsScalarTower.algebraMap_apply k Ω L c
   have hsum:(∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ))=
       P.eval (algebraMap Ω L x):=by
     rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
     rw [←Fin.sum_univ_eq_sum_range]
     change (∑ n:Fin (w+1),P.coeff (n:ℕ)*
       (algebraMap Ω L x)^(n:ℕ))=_
     rfl
   have hle:=coefficient_pole_le_generic_evaluation_of_trdeg_le_one
     v.val φ hcompat htr x hx a i
   change poleOrder v.val (P.coeff i) ≤
     poleOrder v.val (∑ n,φ (a n)*(algebraMap Ω L x)^(n:ℕ)) at hle
   rw [hsum,hy] at hle
   simpa only [i] using hle
 · have hz:P.coeff j=0:=Polynomial.coeff_eq_zero_of_natDegree_lt
     (hP.trans_lt (by omega))
   rw [hz]
   simp only [poleOrder,map_zero,WithZero.log_zero,max_self]
   exact le_max_left _ _
end
end ProximityPrize.SubmissionLower.RCN058
end PackedLegacy_H8

/-! Packed from ProximityPrize.SubmissionLower.A8. -/
section PackedLegacy_A8
namespace ProximityPrize.SubmissionLower.RCN063
open scoped Classical BigOperators WithZero
open RCN187 RCN205 RCN344 RCN002 RCN065 RCN136 RCN139 RCN047 RCN313 RCN233 RCN238 RCN341 RCN271 RCN257 RCN095 RCN114 RCN295
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {L:Type} [Field L]
def coefficientPoleWeight (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L):ℤ:=
 (insert (0:ℤ) (insert (poleOrder v z)
   (T.support.image (fun j↦poleOrder v (T.coeff j))))).max'
   ⟨0,Finset.mem_insert_self _ _⟩
theorem coefficientPoleWeight_nonneg (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L):0 ≤ coefficientPoleWeight v T z:=
 Finset.le_max' _ _ (Finset.mem_insert_self _ _)
theorem seedPole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L):poleOrder v z ≤ coefficientPoleWeight v T z:=
 Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
theorem coeffPole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z:L) (j:ℕ) (hj:j∈T.support):
   poleOrder v (T.coeff j) ≤ coefficientPoleWeight v T z:=by
 unfold coefficientPoleWeight
 apply Finset.le_max'
 exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
private theorem pole_le_of_exp (v:Valuation L (WithZero (Multiplicative ℤ)))
   (x:L) (q:ℤ) (hq:0 ≤ q) (hx:v x ≤ WithZero.exp q):poleOrder v x ≤ q:=by
 apply max_le hq
 by_cases hzero:v x=0
 · simpa [hzero] using hq
 · simpa only [WithZero.log_exp] using (WithZero.log_le_log hzero WithZero.exp_ne_zero).mpr hx
theorem eval_pole_le (v:Valuation L (WithZero (Multiplicative ℤ)))
   (T:Polynomial L) (z a:L) (ha:v a ≤ 1):
   poleOrder v (T.eval a) ≤ coefficientPoleWeight v T z:=by
 apply pole_le_of_exp _ _ _ (coefficientPoleWeight_nonneg v T z)
 rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
 apply v.map_sum_le
 intro j hj
 rw [map_mul,map_pow]
 have hc:v (T.coeff j) ≤ WithZero.exp (coefficientPoleWeight v T z):=
   WithZero.le_exp_of_log_le ((le_max_right _ _).trans (coeffPole_le v T z j hj))
 have hp:v a^j ≤ 1:=pow_le_one₀ zero_le ha
 simpa only [mul_one] using mul_le_mul' hc hp
theorem affine_eval_pole_le {Ω:Type} [Field Ω] [Algebra Ω L]
   (v:Place Ω L) (T:Polynomial L) (z:L) (a u0 u1:Ω):
   poleOrder v.val (T.eval (algebraMap Ω L a)-algebraMap Ω L u0-z*algebraMap Ω L u1) ≤
     coefficientPoleWeight v.val T z:=by
 have ht:=eval_pole_le v.val T z _ (constant_value_le_one Ω L v a)
 have h0:=pole_const_le v.val (constant_value_le_one Ω L v) u0
 have hz:=pole_const_mul_le v.val (constant_value_le_one Ω L v) u1 z
 have hseed:=seedPole_le v.val T z
 have hn:=coefficientPoleWeight_nonneg v.val T z
 have hsub (x y:L):poleOrder v.val (x-y) ≤ max (poleOrder v.val x) (poleOrder v.val y):=by
   simpa only [sub_eq_add_neg,pole_neg] using pole_add_le v.val x (-y)
 exact (hsub _ _).trans (max_le ((hsub _ _).trans (max_le ht (h0.trans hn)))
   (by simpa only [mul_comm] using hz.trans hseed))
variable {K Ω:Type} [Field K] [Field Ω]
variable (φ:Polynomial K →+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
def CoefficientPoleProfile (w cost:ℕ):Prop:=
 ∀ W:Finset (Place Ω (CoordinateField Ω P)),
   (∑ v∈W,coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w)
     (coordinate Ω P 2)) ≤ (cost:ℤ)
theorem coefficientPoleProfile_of_coordinate [IsAlgClosed Ω] (w:ℕ)
   (J:Coordinate Ω (CoordinateField Ω P))
   (hprofile:∀ v:Place Ω (CoordinateField Ω P),
     coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2) ≤
       RCN346.poleOrder Ω (CoordinateField Ω P) v
         (coordinateValue Ω (CoordinateField Ω P) J)):
   CoefficientPoleProfile φ P F hF hH w (coordinateDegree Ω (CoordinateField Ω P) J):=by
 intro W
 exact (Finset.sum_le_sum (fun v _↦hprofile v)).trans
   (finite_sum_coordinate_pole_le_degree Ω (CoordinateField Ω P) J W)
theorem coefficientPoleProfile_of_unitYZ_bound (w cost:ℕ)
   (hcoeff:∀ (v:Place Ω (CoordinateField Ω P)) (j:ℕ),
     poleOrder v.val ((truncatedPolynomial φ P F hF hH w).coeff j) ≤
       poleOrder v.val (coordinate Ω P 0))
   (hyz:∀ W:Finset (Place Ω (CoordinateField Ω P)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate Ω P) (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
   CoefficientPoleProfile φ P F hF hH w cost:=by
 have hp (v:Place Ω (CoordinateField Ω P)):
     coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2) ≤
       max (poleOrder v.val (coordinate Ω P 0)) (poleOrder v.val (coordinate Ω P 2)):=by
   unfold coefficientPoleWeight
   apply Finset.max'_le
   intro z hz
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact (le_max_left _ _).trans (le_max_left _ _)
   rcases Finset.mem_insert.mp hz with rfl | hz
   · exact le_max_right _ _
   obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hz
   exact (hcoeff v j).trans (le_max_left _ _)
 intro W
 exact (Finset.sum_le_sum (fun v _↦hp v)).trans
   (by simpa only [exponentSetPoleWeight_unitYZ] using hyz W)
theorem normalized_agreement_eq (w:ℕ) (x u0 u1:K):
   coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
     (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)=
   (truncatedPolynomial φ P F hF hH w).eval (componentCoefficients φ P x)-
     componentCoefficients φ P u0-coordinate Ω P 2*componentCoefficients φ P u1:=by
 have hclear:=eval_factorial_agreementNumerator (componentCoefficients φ P) F
   (componentPoint φ P) (component_relation φ P F hF) (component_regular φ P F hH)
   w x u0 u1
 rw [component_evaluation] at hclear
 have hbase:MvPolynomial.eval₂Hom (componentCoefficients φ P) (componentPoint φ P) (polyH K F)=
     coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)):=by
   exact component_evaluation φ P _
 rw [hbase,←globalPolynomial_eval] at hclear
 have hz:componentPoint φ P (3:Fin 4)=coordinate Ω P 2:=rfl
 rw [hz] at hclear
 have hne:coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0:=by
   rw [←component_evaluation]
   exact component_regular φ P F hH
 apply (div_eq_iff (pow_ne_zero _ hne)).mpr
 simpa only [agreementPolynomial,truncatedPolynomial,mul_comm] using hclear
include hH in
theorem normalized_agreement_ne_zero_iff (w:ℕ) (x u0 u1:K):
   coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
     (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)≠0 ↔
     agreementPolynomial φ F w x u0 u1∉P:=by
 have hn:coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))≠0:=by
   rw [←component_evaluation]
   exact component_regular φ P F hH
 constructor
 · intro h hmem
   apply h
   have hz:coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)=0:=by
     change agreementPolynomial φ F w x u0 u1∈RingHom.ker (coordinateEvaluation Ω P).toRingHom
     rwa [coordinateEvaluation_ker]
   rw [hz,zero_div]
 · intro h
   apply div_ne_zero _ (pow_ne_zero _ hn)
   intro hz
   apply h
   rw [←coordinateEvaluation_ker Ω P]
   exact hz
theorem agreement_regular_zero_le [IsAlgClosed Ω] (base:SeparableLiteralCoordinate P)
   (w cost:ℕ) (hprofile:CoefficientPoleProfile φ P F hF hH w cost)
   (x u0 u1:K) (hproper:agreementPolynomial φ F w x u0 u1∉P):
   FiniteRegularZeroSetBound P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
     (agreementPolynomial φ F w x u0 u1) cost:=by
 apply finite_regular_zero_bound_of_separator Ω P base _ _ (2*w) cost hproper hH
 intro W
 have hlocal (v:Place Ω (CoordinateField Ω P)):
     poleOrder v.val (coordinateEvaluation Ω P (agreementPolynomial φ F w x u0 u1)/
       (coordinateEvaluation Ω P (surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)))^(2*w)) ≤
     coefficientPoleWeight v.val (truncatedPolynomial φ P F hF hH w) (coordinate Ω P 2):=by
   rw [normalized_agreement_eq φ P F hF hH]
   exact affine_eval_pole_le v _ _ (φ (Polynomial.C x)) (φ (Polynomial.C u0)) (φ (Polynomial.C u1))
 simpa only [RCN346.poleOrder,coordinateEvaluation_eq_aeval] using
   (Finset.sum_le_sum (fun v _↦hlocal v)).trans (hprofile W)
end
end ProximityPrize.SubmissionLower.RCN063
end PackedLegacy_A8

/-! Packed from ProximityPrize.SubmissionLower.BK. -/
section PackedLegacy_BK
namespace ProximityPrize.SubmissionLower.RCN144
open scoped Classical BigOperators
open RCN135 RCN136 RCN313 RCN159 RCN220 RCN083 RCN228 RCN127 RCN058 RCN063 RCN065 RCN238 RCN243 RCN264 RCN231 RCN229 RCN126 RCN062 RCN047 RCN139 RCN174 RCN114 RCN295 RCN095 RCN275 RCN319 RCN002
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
variable {Γ:Finset K} {x:I → K} {p e:ℕ} [CharP (Ω K) p]
 {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
theorem stage_surface_mem
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (x0 u0 u1:K)
   (C:RegularComponent (Ω K) S.G
     (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
     (regularitySurface (polynomialEmbedding K) S.F)):
   surfaceMap (polynomialEmbedding K) S.F∈C.1:=by
 obtain ⟨A,hA⟩:=S.G_dvd_surface
 rw [hA]
 exact C.1.mul_mem_right A
   (regularComponent_G_mem (Ω K) S.G _ _ C)
theorem stage_regularity_not_mem
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (x0 u0 u1:K)
   (C:RegularComponent (Ω K) S.G
     (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
     (regularitySurface (polynomialEmbedding K) S.F)):
   surfaceMap (polynomialEmbedding K) (polyH K S.F)∉C.1:=
 regularComponent_H_not_mem (Ω K) S.G _ _ C
theorem coefficientPoleProfile_of_regular_agreement_curve
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w support)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
   (x0 u0 u1:K)
   (hproper:¬S.G∣agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
   (C:RegularComponent (Ω K) S.G
     (agreementPolynomial (polynomialEmbedding K) S.F w x0 u0 u1)
     (regularitySurface (polynomialEmbedding K) S.F))
   (bound seedCap slopeCap cost:ℕ)
   (hw:1≤w) (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hyz:∀ W:Finset (RCN346.Place (Ω K) (CoordinateField (Ω K) C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
       (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
   CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
     (stage_surface_mem S x0 u0 u1 C)
     (stage_regularity_not_mem S x0 u0 u1 C) w cost:=by
 classical
 let φ:=polynomialEmbedding K
 let Pcurve:=C.1
 let L:=CoordinateField (Ω K) Pcurve
 let κ:K →+*L:=componentCoefficients φ Pcurve
 let v0:Fin 4 → L:=componentPoint φ Pcurve
 letI:CharP L p:=
   charP_of_injective_algebraMap (algebraMap (Ω K) L).injective p
 have hFC:=stage_surface_mem S x0 u0 u1 C
 have hHC:=stage_regularity_not_mem S x0 u0 u1 C
 obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hGQ,hGH0,hTail0⟩:=
   exists_original_factor_with_first_tail S hTail
 have hF0mem:surfaceMap φ F0∈Pcurve:=by
   obtain ⟨A,hA⟩:=hGF0
   rw [hA]
   exact Pcurve.mul_mem_right A (regularComponent_G_mem (Ω K) S.G _ _ C)
 have hHdecomp:surfaceMap φ (polyH K S.F)=
     surfaceMap φ (polyH K F0)*surfaceMap φ Q+
       surfaceMap φ F0*surfaceMap φ (polyH K Q):=by
   rw [hprod]
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
 have hHQnot:surfaceMap φ (polyH K F0)*surfaceMap φ Q∉Pcurve:=by
   intro hm
   apply hHC
   rw [hHdecomp]
   exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0mem)
 have hQnot:surfaceMap φ Q∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_left _ h)
 have hH0not:surfaceMap φ (polyH K F0)∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_right _ h)
 have hF0rel:MvPolynomial.eval₂Hom κ v0 F0=0:=
   (component_evaluation_zero_iff φ Pcurve F0).mpr hF0mem
 have hF0reg:MvPolynomial.eval₂Hom κ v0 (polyH K F0)≠0:=
   (component_evaluation_zero_iff φ Pcurve (polyH K F0)).not.mpr hH0not
 have hQeval:MvPolynomial.eval₂Hom κ v0 Q≠0:=
   (component_evaluation_zero_iff φ Pcurve Q).not.mpr hQnot
 have hprodrel:MvPolynomial.eval₂Hom κ v0 (F0*Q)=0:=by
   rw [map_mul,hF0rel,zero_mul]
 have hprodreg:MvPolynomial.eval₂Hom κ v0 (polyH K (F0*Q))≠0:=by
   rw [←hprod]
   exact component_regular φ Pcurve S.F hHC
 let P0:Polynomial L:=globalPolynomial κ F0 v0 hF0rel hF0reg w
 have hP0deg:P0.natDegree≤w:=globalPolynomial_natDegree_le κ F0 v0 hF0rel hF0reg w
 have hSne:S.F≠0:=by
   intro hz
   apply S.regular_proper
   rw [hz]
   simp
 have hF0box:F0∈globalCoefficientBox K bound w seedCap slopeCap:=by
   apply RCN081.mem_globalCoefficientBox_of_dvd F0 S.F bound w seedCap slopeCap
     hSne ⟨Q,hprod⟩ hbox
 have hP0solution:specialization L P0 (v0 3) (MvPolynomial.map κ F0)=0:=
   canonical_polynomiality_of_first_tail κ F0 v0 hF0rel hF0reg
     p bound w seedCap slopeCap hw hshort hchar hF0box hTail0
 have hcanon:truncatedPolynomial φ Pcurve S.F hFC hHC w=P0:=by
   unfold truncatedPolynomial
   change globalPolynomial κ S.F v0 _ _ w=P0
   have hm:=globalPolynomial_mul_factor κ F0 Q v0 hF0rel hQeval hF0reg
     hprodrel hprodreg w
   simpa only [hprod,P0] using hm
 have hagree:P0.eval (κ x0)=κ u0+v0 3*κ u1:=by
   have hm:=regularComponent_T_mem (Ω K) S.G
     (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F) C
   have hv:=(agreement_mem_iff_truncated_value φ Pcurve S.F hFC hHC
     w x0 u0 u1).mp (by simpa only [agreementPolynomial] using hm)
   rw [hcanon] at hv
   change P0.eval (componentCoefficients φ Pcurve x0)=
     componentCoefficients φ Pcurve u0+
       coordinate (Ω K) Pcurve 2*componentCoefficients φ Pcurve u1 at hv
   change P0.eval (componentCoefficients φ Pcurve x0)=
     componentCoefficients φ Pcurve u0+
       coordinate (Ω K) Pcurve 2*componentCoefficients φ Pcurve u1
   exact hv
 let A0:=agreementNumerator F0 w (fun j => (j.factorial:K)⁻¹) x0 u0 u1
 have hA0proper:¬F0∣A0:=by
   apply RCN220.original_factor_agreement_proper
     φ F0 Q S.G hGF0 w _ x0 u0 u1
   simpa only [agreementPolynomial,hprod] using hproper
 have hvpoint:polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0:=by
   funext i
   fin_cases i
   · rfl
   · exact globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
   · exact globalPolynomial_initial_slope κ F0 v0 hF0rel hF0reg w hw
   · rfl
 have hregspec:specialization L P0 (v0 3)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
   have hmapped:MvPolynomial.eval₂Hom (RingHom.id L) v0
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
     simpa only [polyH,MvPolynomial.pderiv_map,MvPolynomial.eval₂Hom_map_hom,
       RingHom.id_comp] using hF0reg
   intro hz
   apply hmapped
   rw [←hvpoint]
   rw [eval_polynomialPoint_eq_specialization,hz]
   simp
 have hA0solution:specialization L P0 (v0 3) (MvPolynomial.map κ A0)=0:=by
   apply RatFunc.algebraMap_injective L
   rw [map_zero,←fresh_eval_eq]
   rw [map_agreementNumerator_base]
   have hfresh:MvPolynomial.eval₂Hom (algebraMap L (RatFunc L))
       (freshPoint P0 (v0 3))
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map κ F0))≠0:=by
     rw [fresh_eval_eq]
     exact RatFunc.algebraMap_ne_zero hregspec
   have heval:=(factorial_agreement_zero_iff_original_agreement
     (algebraMap L (RatFunc L)) (MvPolynomial.map κ F0) P0 (v0 3) RatFunc.X
     hP0solution hfresh p w S.characteristic_bound
     hP0deg (κ x0) (κ u0) (κ u1)).mpr hagree
   simpa only [freshPoint,map_inv₀,map_natCast] using heval
 have htrK:Algebra.trdeg K (baseCoefficientField (k:=K) P0 (v0 3))≤1:=
   baseCoefficientField_trdeg_le_one_of_fresh_proper_relations F0 A0 P0 (v0 3)
     hF0irr hF0pos hA0proper hP0solution hA0solution hregspec
     p w S.characteristic_bound hP0deg
 let k:=algebraicClosure K (Ω K)
 have htrk:Algebra.trdeg k (baseCoefficientField (k:=k) P0 (v0 3))≤1:=
   baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
 letI:IsAlgClosed k:=IsAlgClosure.isAlgClosed K
 have hxK:Transcendental K (initialCoordinate K):=by
   rw [transcendental_iff_injective]
   intro f g hfg
   apply polynomialEmbedding_injective K
   change f.eval₂ (coefficientEmbedding K) (initialCoordinate K)=
     g.eval₂ (coefficientEmbedding K) (initialCoordinate K) at hfg
   rw [generic_eval_eq,generic_eval_eq] at hfg
   exact hfg
 have hxk:Transcendental k (initialCoordinate K):=hxK.algebraicClosure
 apply coefficientPoleProfile_of_unitYZ_bound φ Pcurve S.F hFC hHC w cost
 · intro place j
   rw [hcanon]
   apply coefficient_pole_le_of_trdeg_le_one P0 (v0 3) w hP0deg htrk
     (initialCoordinate K) hxk (coordinate (Ω K) Pcurve 0)
   exact globalPolynomial_initial_value κ F0 v0 hF0rel hF0reg w
 · exact hyz
end
end ProximityPrize.SubmissionLower.RCN144
end PackedLegacy_BK

/-! Packed from ProximityPrize.SubmissionLower.BL. -/
section PackedLegacy_BL
namespace ProximityPrize.SubmissionLower.RCN145
open scoped Classical BigOperators
open RCN002 RCN136 RCN231 RCN319 RCN238 RCN065 RCN271 RCN063 RCN341 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
variable (φ:Polynomial K →+*Ω) (P:Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
 (F:MvPolynomial (Fin 4) K)
 (hF:surfaceMap φ F∈P)
 (hH:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P)
theorem prime_curve_card_le_of_coefficientPoleProfile
   (base:SeparableLiteralCoordinate P) (p w a e cost:ℕ) [CharP Ω p]
   (hchar:w < p) (hwa:w < a) (hcost:1 ≤ cost)
   (hprofile:CoefficientPoleProfile φ P F hF hH w cost)
   (selected:K → Polynomial K) (Γ:Finset K)
   {ι:Type*} (nodes:Finset ι) (x u0 u1:ι → K) (hinj:Set.InjOn x nodes)
   (hsize:nodes.card=a+e)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,a ≤ (nodes.filter (fun i↦
     (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e):Γ.card ≤ (e+1)*cost:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 let I:=identityNodes φ P F nodes x u0 u1 w
 let relation:K → ι → Prop:=fun γ i↦(selected γ).eval (x i)=u0 i+γ*u1 i
 by_cases hI:I.card ≤ w
 · have hfiber:∀ i∈nodes \ I,(Γ.filter (fun γ↦relation γ i)).card ≤ cost:=by
     intro i hi
     obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
     have hproper:agreementPolynomial φ F w (x i) (u0 i) (u1 i)∉P:=by
       intro hmem
       apply hnotI
       exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
     exact agreement_fiber_card_le_of_regular_zero_bound φ P F selected Γ p w hchar
       hdegree hsolution hregular hpoint (x i) (u0 i) (u1 i) cost
       (agreement_regular_zero_le φ P F hF hH base w cost hprofile _ _ _ hproper)
   have hcount:=RCN173.sharp_incidence_bound relation Γ nodes I a w cost
     (identityNodes_subset φ P F nodes x u0 u1 w) hI hwa (by omega) hagreement hfiber
   have hg:0 < a-w:=Nat.sub_pos_of_lt hwa
   have hu:nodes.card-w ≤ (e+1)*(a-w):=by
     have he:=Nat.mul_le_mul_left e (show 1 ≤ a-w by omega)
     calc
       nodes.card-w=(a-w)+e:=by omega
       _ ≤ (a-w)+e*(a-w):=by simpa only [Nat.mul_one] using Nat.add_le_add_left he (a-w)
       _=_:=by ring
   have hscaled:Γ.card*(a-w) ≤ ((e+1)*cost)*(a-w):=by
     calc
       _ ≤ (nodes.card-w)*cost:=hcount
       _ ≤ ((e+1)*(a-w))*cost:=Nat.mul_le_mul_right cost hu
       _=_:=by ring
   exact Nat.le_of_mul_le_mul_right hscaled hg
 · have hi:w < I.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈I →
       (selected t.1).eval (x i)=u0 i+t.1*u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ P F nodes x u0 u1 p w hchar
       (selected t.1) t.1 (hdegree t.1 t.2) (hsolution t.1 t.2)
       (hregular t.1 t.2) (hpoint t.1 t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=exists_common_pencil_of_many_identities
     φ P F hF hH nodes x u0 u1 w hinj hi
     (fun t:{γ:K//γ∈Γ}↦t.1) (fun t↦selected t.1)
     (fun t↦hdegree t.1 t.2) hvalues
   have hfilter:Γ.filter (fun γ↦selected γ=P0+Polynomial.C γ*P1)=Γ:=
     Finset.filter_eq_self.mpr (fun γ hγ↦hpencil ⟨γ,hγ⟩)
   have hsmall:Γ.card ≤ e+1:=by
     simpa only [hfilter] using hnoPencil P0 P1 h0 h1
   exact hsmall.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e+1) hcost)
theorem prime_curve_card_le_projection_degree
   (base:SeparableLiteralCoordinate P) (J:SeparableCoordinate Ω (CoordinateField Ω P))
   (p w a e:ℕ) [CharP Ω p] (hchar:w < p) (hwa:w < a)
   (hprofile:CoefficientPoleProfile φ P F hF hH w
     (SeparableCoordinate.degree Ω (CoordinateField Ω P) J))
   (selected:K → Polynomial K) (Γ:Finset K)
   {ι:Type*} (nodes:Finset ι) (x u0 u1:ι → K) (hinj:Set.InjOn x nodes)
   (hsize:nodes.card=a+e)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ γ∈Γ,P ≤ RingHom.ker (MvPolynomial.aeval (selectedPoint φ selected γ)).toRingHom)
   (hagreement:∀ γ∈Γ,a ≤ (nodes.filter (fun i↦
     (selected γ).eval (x i)=u0 i+γ*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e):
   Γ.card ≤ (e+1)*SeparableCoordinate.degree Ω (CoordinateField Ω P) J:=by
 have hcost:1 ≤ SeparableCoordinate.degree Ω (CoordinateField Ω P) J:=by
   letI:Algebra (RatFunc Ω) (CoordinateField Ω P):=J.embedding.toRingHom.toAlgebra
   letI:FiniteDimensional (RatFunc Ω) (CoordinateField Ω P):=J.finite
   exact Module.finrank_pos
 exact prime_curve_card_le_of_coefficientPoleProfile φ P F hF hH base p w a e _
   hchar hwa hcost hprofile selected Γ nodes x u0 u1 hinj hsize hdegree hsolution hregular
   hpoint hagreement hnoPencil
end
end ProximityPrize.SubmissionLower.RCN145
end PackedLegacy_BL

/-! Packed from ProximityPrize.SubmissionLower.GM. -/
section PackedLegacy_GM
namespace ProximityPrize.SubmissionLower.RCN312
open scoped Classical BigOperators
open RCN135 RCN136 RCN313 RCN159 RCN264 RCN074 RCN086 RCN330 RCN065 RCN238 RCN243 RCN231 RCN139 RCN047 RCN137 RCN082 RCN083 RCN258 RCN217 RCN127 RCN126 RCN062 RCN058 RCN063 RCN145 RCN339 RCN095 RCN237 RCN295 RCN174 RCN319 RCN341 RCN046 RCN042 RCN344 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Omega (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I → K} {p errors w:ℕ}
 [CharP (Omega K) p]
 {flag tailFlag1:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
theorem firstTailComponent_surface_mem
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K) S.F∈C.1:=by
 obtain ⟨Q,hQ⟩:=S.G_dvd_surface
 rw [hQ]
 exact C.1.mul_mem_right Q
   (regularComponent_G_mem (Omega K) S.G _ _ C)
theorem firstTailComponent_regularity_not_mem
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K) (polyH K S.F)∉C.1:=
 regularComponent_H_not_mem (Omega K) S.G _ _ C
theorem exists_original_factor_of_firstTailComponent
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S):
   ∃ F0 Q:MvPolynomial (Fin 4) K,
     Irreducible F0∧0 < F0.degreeOf 1+F0.degreeOf 2+F0.degreeOf 3∧
     S.F=F0*Q∧
     S.G∣surfaceMap (polynomialEmbedding K) F0∧
     surfaceMap (polynomialEmbedding K) F0∈C.1∧
     surfaceMap (polynomialEmbedding K) Q∉C.1∧
     surfaceMap (polynomialEmbedding K) (polyH K F0)∉C.1:=by
 classical
 let phi:=polynomialEmbedding K
 let Pcurve:=C.1
 let L:=CoordinateField (Omega K) Pcurve
 let phiC:Polynomial K →+*L:=
   (algebraMap (Omega K) L).comp phi
 let vC:Fin 3 → L:=fun i => componentPoint phi Pcurve i.succ
 have hSne:S.F≠0:=by
   intro hzero
   apply S.regular_proper
   rw [hzero]
   simp
 have hsurfaceZero:MvPolynomial.eval vC (surfaceMap phiC S.F)=0:=by
   rw [eval_surfaceMap]
   change MvPolynomial.eval₂Hom (componentCoefficients phi Pcurve)
     (componentPoint phi Pcurve) S.F=0
   exact (component_evaluation_zero_iff phi Pcurve S.F).mpr
     (firstTailComponent_surface_mem S C)
 have hphiC:Function.Injective phiC:=
   (algebraMap (Omega K) L).injective.comp (polynomialEmbedding_injective K)
 obtain ⟨F0,hF0mem,hF0zero⟩:=
   exists_active_factor_of_surface_zero phiC hphiC S.F hSne vC hsurfaceZero
 have hF0spec:=activeFactors_spec S.F F0 hF0mem
 obtain ⟨Q,hprod⟩:=hF0spec.2.1
 have hF0curve:surfaceMap phi F0∈Pcurve:=by
   rw [←coordinateEvaluation_ker (Omega K) Pcurve]
   rw [eval_surfaceMap] at hF0zero
   change MvPolynomial.eval₂Hom (componentCoefficients phi Pcurve)
     (componentPoint phi Pcurve) F0=0 at hF0zero
   rw [component_evaluation] at hF0zero
   exact hF0zero
 have hHdecomp:surfaceMap phi (polyH K S.F)=
     surfaceMap phi (polyH K F0)*surfaceMap phi Q+
       surfaceMap phi F0*surfaceMap phi (polyH K Q):=by
   rw [hprod]
   unfold polyH
   rw [MvPolynomial.pderiv_mul]
   simp only [map_add,map_mul]
 have hHQnot:surfaceMap phi (polyH K F0)*surfaceMap phi Q∉Pcurve:=by
   intro hm
   apply firstTailComponent_regularity_not_mem S C
   rw [hHdecomp]
   exact Pcurve.add_mem hm (Pcurve.mul_mem_right _ hF0curve)
 have hQnot:surfaceMap phi Q∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_left _ h)
 have hH0not:surfaceMap phi (polyH K F0)∉Pcurve:=
   fun h => hHQnot (Pcurve.mul_mem_right _ h)
 have hGprod:S.G∣surfaceMap phi F0*surfaceMap phi Q:=by
   simpa only [←map_mul, ←hprod] using S.G_dvd_surface
 have hGsplit:=S.irreducible_G.prime.dvd_or_dvd hGprod
 have hGQfalse:¬ S.G∣surfaceMap phi Q:=by
   intro hGQ
   apply hQnot
   exact Pcurve.mem_of_dvd hGQ
     (regularComponent_G_mem (Omega K) S.G _ _ C)
 have hGF0:S.G∣surfaceMap phi F0:=hGsplit.resolve_right hGQfalse
 exact ⟨F0,Q,hF0spec.1,hF0spec.2.2,hprod,hGF0,
   hF0curve,hQnot,hH0not⟩
theorem original_factor_firstTail_proper
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
   (F0 Q:MvPolynomial (Fin 4) K) (hprod:S.F=F0*Q)
   (hGF0:S.G∣surfaceMap (polynomialEmbedding K) F0):
   ¬ F0∣numerator K F0 (w+1):=by
 intro hdiv
 let phi:=polynomialEmbedding K
 have hscaled:S.G∣surfaceMap phi
     (Q^(2*(w+1))*numerator K F0 (w+1)):=by
   exact hGF0.trans (map_dvd (surfaceMap phi)
     (dvd_mul_of_dvd_right hdiv (Q^(2*(w+1)))))
 have hdiff:S.G∣surfaceMap phi
     (numerator K (F0*Q) (w+1)-
       Q^(2*(w+1))*numerator K F0 (w+1)):=
   hGF0.trans (map_dvd (surfaceMap phi)
     (factor_dvd_numerator_sub_power F0 Q (w+1)))
 have hwhole:S.G∣surfaceMap phi (numerator K S.F (w+1)):=by
   rw [hprod]
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using
     dvd_add hdiff hscaled
 apply hfirstProper
 exact (globalTailCut_dvd_iff phi (polynomialEmbedding_injective K)
   S.F (w+1) S.G).mpr hwhole
theorem tangent_truncatedPolynomial_solution
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S)
   (bound seedCap slopeCap:ℕ) (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hallTails:∀ delay,
     globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1):
   specialization (CoordinateField (Omega K) C.1)
     (truncatedPolynomial (polynomialEmbedding K) C.1 S.F
       (firstTailComponent_surface_mem S C)
       (firstTailComponent_regularity_not_mem S C) w)
     (coordinate (Omega K) C.1 2)
     (MvPolynomial.map (componentCoefficients (polynomialEmbedding K) C.1) S.F)=0:=by
 let phi:=polynomialEmbedding K
 let Pcurve:=C.1
 let coefficients:=componentCoefficients phi Pcurve
 let v:=componentPoint phi Pcurve
 let hF:=firstTailComponent_surface_mem S C
 let hH:=firstTailComponent_regularity_not_mem S C
 let hrel:=component_relation phi Pcurve S.F hF
 let hreg:=component_regular phi Pcurve S.F hH
 letI:CharP (CoordinateField (Omega K) Pcurve) p:=
   charP_of_injective_algebraMap
     (algebraMap (Omega K) (CoordinateField (Omega K) Pcurve)).injective p
 apply global_polynomiality_of_all_tails coefficients S.F v hrel hreg
   p bound w seedCap slopeCap hw hshort hchar hbox
 apply (all_tail_numerators_iff_all_tail_jets coefficients S.F v hrel hreg
   p bound w hchar).mp
 intro j hj _
 have hjbase:w+1 ≤ j:=by omega
 have hT:=hallTails (j-(w+1))
 have heq:w+1+(j-(w+1))=j:=Nat.add_sub_of_le hjbase
 rw [heq] at hT
 have hN:surfaceMap phi (numerator K S.F j)∈Pcurve:=
   (globalTailCut_mem_iff phi (polynomialEmbedding_injective K)
     S.F j Pcurve).mp hT
 exact (component_evaluation_zero_iff phi Pcurve _).mpr hN
theorem coefficientPoleProfile_of_tangent_firstTail
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣
     globalTailCut (polynomialEmbedding K) S.F (w+1))
   (bound seedCap slopeCap cost:ℕ) (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hallTails:∀ delay,
     globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1)
   (hyz:∀ W:Finset
     (RCN346.Place (Omega K) (CoordinateField (Omega K) C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Omega K) C.1)
       (flagSupport unitYZFlag)) ≤ (cost:ℤ)):
   CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
     (firstTailComponent_surface_mem S C)
     (firstTailComponent_regularity_not_mem S C) w cost:=by
 classical
 let phi:=polynomialEmbedding K
 let Pcurve:=C.1
 let L:=CoordinateField (Omega K) Pcurve
 let kappa:K →+*L:=componentCoefficients phi Pcurve
 let v0:Fin 4 → L:=componentPoint phi Pcurve
 let hFC:=firstTailComponent_surface_mem S C
 let hHC:=firstTailComponent_regularity_not_mem S C
 let P0:Polynomial L:=truncatedPolynomial phi Pcurve S.F hFC hHC w
 letI:CharP L p:=charP_of_injective_algebraMap
   (algebraMap (Omega K) L).injective p
 have hP0deg:P0.natDegree ≤ w:=
   truncatedPolynomial_natDegree_le phi Pcurve S.F hFC hHC w
 have hSsolution:specialization L P0 (v0 3)
     (MvPolynomial.map kappa S.F)=0:=
   tangent_truncatedPolynomial_solution S C bound seedCap slopeCap hw
     hshort hchar hbox hallTails
 obtain ⟨F0,Q,hF0irr,hF0pos,hprod,hGF0,hF0curve,hQnot,hH0not⟩:=
   exists_original_factor_of_firstTailComponent S C
 have hF0rel:MvPolynomial.eval₂Hom kappa v0 F0=0:=
   (component_evaluation_zero_iff phi Pcurve F0).mpr hF0curve
 have hF0regPoint:MvPolynomial.eval₂Hom kappa v0 (polyH K F0)≠0:=
   (component_evaluation_zero_iff phi Pcurve (polyH K F0)).not.mpr hH0not
 have hQeval:MvPolynomial.eval₂Hom kappa v0 Q≠0:=
   (component_evaluation_zero_iff phi Pcurve Q).not.mpr hQnot
 have hvpoint:polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0)=v0:=by
   funext i
   fin_cases i
   · rfl
   · exact truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
   · exact truncatedPolynomial_initial_slope phi Pcurve S.F hFC hHC w hw
   · rfl
 have hQsolution_ne:specialization L P0 (v0 3)
     (MvPolynomial.map kappa Q)≠0:=by
   intro hz
   apply hQeval
   calc
     MvPolynomial.eval₂Hom kappa v0 Q=
         MvPolynomial.eval₂Hom (RingHom.id L)
           (polynomialPoint (RingHom.id L) P0 (v0 3) (v0 0))
           (MvPolynomial.map kappa Q):=by
       rw [hvpoint,MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp]
     _=(specialization L P0 (v0 3)
         (MvPolynomial.map kappa Q)).eval (v0 0):=by
       simpa using eval_polynomialPoint_eq_specialization
         (RingHom.id L) P0 (v0 3) (v0 0) (MvPolynomial.map kappa Q)
     _=0:=by rw [hz];simp
 have hF0solution:specialization L P0 (v0 3)
     (MvPolynomial.map kappa F0)=0:=by
   have hmul:specialization L P0 (v0 3) (MvPolynomial.map kappa F0)*
       specialization L P0 (v0 3) (MvPolynomial.map kappa Q)=0:=by
     simpa only [hprod,map_mul] using hSsolution
   exact (mul_eq_zero.mp hmul).resolve_right hQsolution_ne
 have hF0reg:specialization L P0 (v0 3)
     (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
   have hmapped:MvPolynomial.eval₂Hom (RingHom.id L) v0
       (MvPolynomial.pderiv (2:Fin 4) (MvPolynomial.map kappa F0))≠0:=by
     simpa only [polyH,MvPolynomial.pderiv_map,
       MvPolynomial.eval₂Hom_map_hom,RingHom.id_comp] using hF0regPoint
   intro hz
   apply hmapped
   rw [←hvpoint,eval_polynomialPoint_eq_specialization,hz]
   simp
 have hTsolution:specialization L P0 (v0 3)
     (MvPolynomial.map kappa (numerator K F0 (w+1)))=0:=by
   rw [map_numerator]
   exact specialization_numerator_zero_of_degree L (MvPolynomial.map kappa F0)
     P0 (v0 3) hF0solution (w+1) (hP0deg.trans_lt (by omega))
 have hTproper:¬ F0∣numerator K F0 (w+1):=
   original_factor_firstTail_proper S hfirstProper F0 Q hprod hGF0
 have htrK:Algebra.trdeg K (baseCoefficientField (k:=K) P0 (v0 3)) ≤ 1:=
   baseCoefficientField_trdeg_le_one_of_fresh_proper_relations
     F0 (numerator K F0 (w+1)) P0 (v0 3)
     hF0irr hF0pos hTproper hF0solution hTsolution hF0reg
     p w S.characteristic_bound hP0deg
 let k:=algebraicClosure K (Omega K)
 have htrk:Algebra.trdeg k (baseCoefficientField (k:=k) P0 (v0 3)) ≤ 1:=
   baseCoefficientField_trdeg_le_one_of_algebraic_constants P0 (v0 3) htrK
 letI:IsAlgClosed k:=IsAlgClosure.isAlgClosed K
 have hxK:Transcendental K (initialCoordinate K):=by
   rw [transcendental_iff_injective]
   intro f g hfg
   apply polynomialEmbedding_injective K
   change f.eval₂ (coefficientEmbedding K) (initialCoordinate K)=
     g.eval₂ (coefficientEmbedding K) (initialCoordinate K) at hfg
   rw [generic_eval_eq,generic_eval_eq] at hfg
   exact hfg
 have hxk:Transcendental k (initialCoordinate K):=hxK.algebraicClosure
 apply coefficientPoleProfile_of_unitYZ_bound phi Pcurve S.F hFC hHC w cost
 · intro place j
   apply coefficient_pole_le_of_trdeg_le_one P0 (v0 3) w hP0deg htrk
     (initialCoordinate K) hxk (coordinate (Omega K) Pcurve 0)
   exact truncatedPolynomial_initial_value phi Pcurve S.F hFC hHC w
 · exact hyz
theorem tangent_component_card_le
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w support)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣
     globalTailCut (polynomialEmbedding K) S.F (w+1))
   (base:SeparableLiteralCoordinate C.1)
   (agreements bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card=agreements+errors)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ (S.agreementFiber gamma).card)
   (hwa:w < agreements) (hw:1 ≤ w)
   (hshort:w+1 ≤ bound) (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w+1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (hyzPositive:1 ≤ B.yzCost C)
   (hallTails:∀ delay,
     globalTailCut (polynomialEmbedding K) S.F (w+1+delay)∈C.1)
   (hyz:∀ W:Finset
     (RCN346.Place (Omega K) (CoordinateField (Omega K) C.1)),
     (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Omega K) C.1)
       (flagSupport unitYZFlag)) ≤ (B.yzCost C:ℤ)):
   (componentSeeds (Omega K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w+1))
     (regularitySurface (polynomialEmbedding K) S.F) Gamma
     (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
       (errors+1)*B.yzCost C:=by
 classical
 let T1:=globalTailCut (polynomialEmbedding K) S.F (w+1)
 let H:=regularitySurface (polynomialEmbedding K) S.F
 let Gc:=componentSeeds (Omega K) S.G T1 H Gamma
   (selectedPoint (polynomialEmbedding K) S.selected) C
 have hGcGamma:Gc ⊆ Gamma:=
   componentSeeds_subset (Omega K) S.G T1 H Gamma _ C
 have hprofile:=coefficientPoleProfile_of_tangent_firstTail
   S C hfirstProper bound seedCap slopeCap (B.yzCost C) hw hshort hchar
   hbox hallTails hyz
 apply prime_curve_card_le_of_coefficientPoleProfile
   (polynomialEmbedding K) C.1 S.F
   (firstTailComponent_surface_mem S C)
   (firstTailComponent_regularity_not_mem S C)
   base p w agreements errors (B.yzCost C)
   S.characteristic_bound hwa hyzPositive hprofile
   S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
 · intro gamma hgamma
   exact S.degree_le gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact S.solution gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact S.regular gamma (hGcGamma hgamma)
 · intro gamma hgamma
   exact componentSeeds_on_prime (Omega K) S.G T1 H Gamma
     (selectedPoint (polynomialEmbedding K) S.selected) C gamma hgamma
 · intro gamma hgamma
   have hGamma:=hGcGamma hgamma
   simpa only [ResidualStage.agreementFiber,ResidualStage.Agrees] using
     hagreement gamma hGamma
 · exact noLargeSelectedPencil_mono S.selected Gamma Gc w errors
     hGcGamma S.no_large_pencil
end
end ProximityPrize.SubmissionLower.RCN312
end PackedLegacy_GM

/-! Packed from ProximityPrize.SubmissionLower.GZ. -/
section PackedLegacy_GZ
namespace ProximityPrize.SubmissionLower.RCN329
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN046 RCN341 RCN002 RCN344 RCN312 RCN338 RCN174 RCN042 RCN339
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Omega (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I → K} {p:ℕ}
 [CharP (Omega K) p] {flag:FlagDegree}
 {support:RCN275.ResidualSupportParameters}
abbrev FixedStage
   (phi:Polynomial K →+*Omega K:=polynomialEmbedding K):=
 ResidualStage phi Gamma x p RCN326.errors
   flag RCN326.w support
structure ProperDelayedTailCertificate
   (S:FixedStage (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
     (support:=support))
   (B:PrimeFlagBudgetFamily
     (G:=S.G)
     (T:=globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag
     (RCN326.tailFlag
       (RCN326.w+1)))
   (multiplicity:FirstTailComponent S → ℕ) where
 branch:∀ C:FirstTailComponent S,
   (∃ delay,1 ≤ delay∧delay ≤ multiplicity C∧
     globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∉C.1∧
     (componentSeeds (Omega K) S.G
       (globalTailCut (polynomialEmbedding K) S.F
         (RCN326.w+1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         multiplicity C*B.weightedCost
           (RCN326.tailFlag
             (RCN326.w+2)) C)∨
   (∀ delay,globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1+delay)∈C.1)
theorem delayedTailMultiplicityProvider_of_certificates
   (S:FixedStage (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
     (support:=support))
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (baseFamily:∀ C:FirstTailComponent S,SeparableLiteralCoordinate C.1)
   (U:AdaptiveUnitProjectionFamily baseFamily flag
     (RCN326.tailFlag
       (RCN326.w+1)))
   (hyzTranscendental:∀ C:FirstTailComponent S,
     Transcendental (Omega K)
       (coordinateValue (Omega K) (CoordinateField (Omega K) C.1)
         (U.yzProjection C)))
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card=RCN326.agreements+
     RCN326.errors)
   (hagreement:∀ gamma∈Gamma,
     RCN326.agreements ≤
       (S.agreementFiber gamma).card)
   (hshort:RCN326.w+1 ≤ bound)
   (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound
     RCN326.w seedCap slopeCap)
   (multiplicity:FirstTailComponent S → ℕ)
   (hone:∀ C,1 ≤ multiplicity C)
   (proper:ProperDelayedTailCertificate S U.toPrimeFlagBudgetFamily multiplicity)
   (resultants:RegularComponentWeightedInertiaResultantCertificate
     U.toPrimeFlagBudgetFamily multiplicity):
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=RCN326.tailFlag
       (RCN326.w+1))
     (tailFlag2:=RCN326.tailFlag
       (RCN326.w+2)) S):=by
 let B:=U.toPrimeFlagBudgetFamily
 let secondTail:=RCN326.tailFlag
   (RCN326.w+2)
 let cost:FirstTailComponent S → ℕ:=
   fun C => multiplicity C*B.weightedCost secondTail C
 have hyzPositive (C:FirstTailComponent S):1 ≤ B.yzCost C:=by
   change 1 ≤ coordinateDegree (Omega K) (CoordinateField (Omega K) C.1)
     (U.yzProjection C)
   exact one_le_coordinateDegree_of_transcendental_value
     (U.yzProjection C) (hyzTranscendental C)
 have hyzPole (C:FirstTailComponent S):∀ W:Finset
     (RCN346.Place (Omega K) (CoordinateField (Omega K) C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight
       v.val (coordinate (Omega K) C.1)
       (RCN095.flagSupport
         RCN095.unitYZFlag)) ≤ (B.yzCost C:ℤ):=by
   exact U.toAdaptiveUnitPoleBudget.yzPole C
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay,globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∈C.1):
     (componentSeeds (Omega K) S.G
       (globalTailCut (polynomialEmbedding K) S.F
         (RCN326.w+1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (RCN326.errors+1)*B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper (baseFamily C)
     RCN326.agreements bound seedCap slopeCap
     hnodes hagreement (by decide) (by decide) hshort hchar hbox B
     (hyzPositive C) hall (hyzPole C)
 refine ⟨{
   budgetFamily:=B
   multiplicity:=multiplicity
   cost:=cost
   one_le_multiplicity:=hone
   tangentYZGate:=errors_succ_le_secondTail_yz
   cost_le:=fun C => le_rfl
   divisor_le:=resultants.divisor_le B multiplicity
   componentBound:=?_
   dichotomy:=?_}⟩
 · intro C
   rcases proper.branch C with hproper | htangent
   · exact hproper.choose_spec.2.2.2
   · exact (tangentCount C htangent).trans
       (tangentCost_le_multiplicity_secondTail_weightedCost
         B C (multiplicity C) (hone C))
 · intro C
   rcases proper.branch C with hproper | htangent
   · exact Or.inl ⟨hproper.choose,hproper.choose_spec.1,
       hproper.choose_spec.2.1,hproper.choose_spec.2.2.1⟩
   · exact Or.inr ⟨htangent,tangentCount C htangent⟩
end
end ProximityPrize.SubmissionLower.RCN329
end PackedLegacy_GZ

/-! Packed from ProximityPrize.SubmissionLower.FG. -/
section PackedLegacy_FG
namespace ProximityPrize.SubmissionLower.RCN219
open scoped Classical TensorProduct
open RCN135 RCN136 RCN072 RCN264
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K:Type} [Field K]
abbrev Omega (K:Type) [Field K]:=GenericField K
abbrev Poly4 (K:Type) [Field K]:=MvPolynomial (Fin 4) K
abbrev Collected (K:Type) [Field K]:=
 MvPolynomial (Fin 3) (Polynomial K)
abbrev GenericPoly3 (K:Type) [Field K]:=
 MvPolynomial (Fin 3) (Omega K)
local instance:Algebra (Polynomial K) (Omega K):=
 (polynomialEmbedding K).toAlgebra
local instance:Module.IsTorsionFree (Polynomial K) (Omega K):=
 (Module.isTorsionFree_iff_algebraMap_injective).2
   (polynomialEmbedding_injective K)
local instance:Module.Flat (Polynomial K) (Omega K):=inferInstance
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.rightAlgebra
local instance genericPolynomial_flat:
   Module.Flat (Collected K) (GenericPoly3 K):=by
 let E:=Algebra.IsPushout.equiv (Polynomial K) (Collected K)
   (Omega K) (GenericPoly3 K)
 letI:Module.Flat (Collected K)
     ((Collected K) ⊗[Polynomial K] Omega K):=inferInstance
 exact Module.Flat.of_linearEquiv E.symm.toLinearEquiv
def collectedPrime (P:Ideal (GenericPoly3 K)):Ideal (Collected K):=
 P.comap (algebraMap (Collected K) (GenericPoly3 K))
def originalPrime (P:Ideal (GenericPoly3 K)):Ideal (Poly4 K):=
 (collectedPrime P).comap (collectX K).toRingEquiv
theorem mem_originalPrime_iff
   (P:Ideal (GenericPoly3 K)) (A:Poly4 K):
   A∈originalPrime P ↔
     surfaceMap (polynomialEmbedding K) A∈P:=by
 rfl
instance collectedPrime_isPrime (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (collectedPrime P).IsPrime:=
 Ideal.IsPrime.comap (algebraMap (Collected K) (GenericPoly3 K))
instance originalPrime_isPrime (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (originalPrime P).IsPrime:=
 Ideal.IsPrime.comap (collectX K).toRingEquiv
theorem collectedPrime_height_le
   (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (collectedPrime P).height ≤ P.height:=by
 let p:=collectedPrime P
 letI:p.IsPrime:=inferInstance
 letI:P.LiesOver p:=⟨rfl⟩
 have h:=Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
 rw [h]
 exact le_add_right (le_refl _)
theorem originalPrime_height_le
   (P:Ideal (GenericPoly3 K)) [P.IsPrime]:
   (originalPrime P).height ≤ P.height:=by
 calc
   (originalPrime P).height=(collectedPrime P).height:=by
     simpa only [originalPrime] using
       RingEquiv.height_comap (collectX K).toRingEquiv (collectedPrime P)
   _ ≤ P.height:=collectedPrime_height_le P
theorem originalPrime_height_eq_two
   (P:Ideal (GenericPoly3 K)) [P.IsPrime]
   (hPheight:P.height ≤ 2)
   (F N:Poly4 K) (hF:Irreducible F)
   (hFmem:surfaceMap (polynomialEmbedding K) F∈P)
   (hNmem:surfaceMap (polynomialEmbedding K) N∈P)
   (hproper:¬ F∣N):
   (originalPrime P).height=2:=by
 let p:=originalPrime P
 let I:Ideal (Poly4 K):=Ideal.span {F}
 letI:p.IsPrime:=inferInstance
 letI:I.IsPrime:=Ideal.isPrime_span_singleton_of_prime hF.prime
 have hFmem':F∈p:=(mem_originalPrime_iff P F).2 hFmem
 have hNmem':N∈p:=(mem_originalPrime_iff P N).2 hNmem
 have hIp:I ≤ p:=by
   apply Ideal.span_le.2
   simpa using hFmem'
 have hNnot:N∉I:=by
   intro h
   exact hproper (Ideal.mem_span_singleton.mp h)
 have hIne:I≠p:=by
   intro h
   exact hNnot (h ▸ hNmem')
 have hIlt:I < p:=lt_of_le_of_ne hIp hIne
 have hIbot:I≠⊥:=by
   intro h
   have hzero:F=0:=by
     have:F∈(⊥:Ideal (Poly4 K)):=h ▸ Ideal.subset_span (by simp)
     simpa using this
   exact hF.ne_zero hzero
 have hbotlt:(⊥:Ideal (Poly4 K)) < I:=
   lt_of_le_of_ne bot_le hIbot.symm
 have hone:(1:ℕ∞) ≤ I.height:=by
   calc
     1=(0:ℕ∞)+1:=by simp
     _ ≤ (⊥:Ideal (Poly4 K)).height+1:=by gcongr;exact zero_le
     _ ≤ I.height:=Ideal.height_add_one_le_of_lt_of_isPrime hbotlt
 have htwo:(2:ℕ∞) ≤ p.height:=by
   calc
     2=(1:ℕ∞)+1:=by norm_num
     _ ≤ I.height+1:=by gcongr
     _ ≤ p.height:=Ideal.height_add_one_le_of_lt_of_isPrime hIlt
 exact le_antisymm ((originalPrime_height_le P).trans hPheight) htwo
abbrev AmbientLocal (P:Ideal (Poly4 K)) [P.IsPrime]:=
 Localization.AtPrime P
abbrev OriginalFactorLocalRing
   (P:Ideal (Poly4 K)) [P.IsPrime] (F:Poly4 K):=
 AmbientLocal P ⧸ Ideal.span
   {algebraMap (Poly4 K) (AmbientLocal P) F}
private theorem derivation_sq_mem_maximal
   {A:Type} [CommRing A] [IsLocalRing A]
   {k:Type} [CommRing k] [Algebra k A]
   (D:Derivation k A A) {f:A}
   (hf:f∈IsLocalRing.maximalIdeal A^2):
   D f∈IsLocalRing.maximalIdeal A:=by
 rw [pow_two] at hf
 refine Submodule.mul_induction_on hf ?_ ?_
 · intro x hx y hy
   rw [D.leibniz]
   exact (IsLocalRing.maximalIdeal A).add_mem
     ((IsLocalRing.maximalIdeal A).mul_mem_right (D y) hx)
     ((IsLocalRing.maximalIdeal A).mul_mem_right (D x) hy)
 · intro x y hx hy
   simpa only [map_add] using (IsLocalRing.maximalIdeal A).add_mem hx hy
end
end ProximityPrize.SubmissionLower.RCN219
end PackedLegacy_FG

/-! Packed from ProximityPrize.SubmissionLower.AL. -/
section PackedLegacy_AL
namespace ProximityPrize.SubmissionLower.RCN327
open ProximityPrize.Benchmark RCN095 RCN275 RCN198 RCN206 RCN263
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def score:ℕ:=6734
def errors:ℕ:=80102
def agreements:ℕ:=n - errors
def gap:ℕ:=agreements - w
def radiusNumerator:ℕ:=10253183
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
structure Profile where
 multiplicity:ℕ
 totalCap:ℕ
 slopeCap:ℕ
 middleCap:ℕ
 deriving DecidableEq
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity * agreements
end Profile
def profileA:Profile:=⟨42,84439,12,58⟩
def profileB:Profile:=⟨81,1262,25,112⟩
def profileC:Profile:=⟨41,41787,12,56⟩
def profileH:Profile:=⟨42,1261,12,55⟩
def supportYS:ResidualSupportParameters :=
 RCN198.support 1207 41 10
def supportS:ResidualSupportParameters :=
 RCN198.support 1206 43 9
def fixedFlagYS:FlagDegree:=surfaceFlag 1207 41 10
def fixedFlagS:FlagDegree:=surfaceFlag 1206 43 9
def firstTailYS:FlagDegree:=reducedResidualAgreementFlag supportYS (w + 1)
def secondTailYS:FlagDegree:=reducedResidualAgreementFlag supportYS (w + 2)
def firstTailS:FlagDegree:=reducedResidualAgreementFlag supportS (w + 1)
def secondTailS:FlagDegree:=reducedResidualAgreementFlag supportS (w + 2)
def fixedRegularCostYS:ℕ:=flagMixed fixedFlagYS firstTailYS secondTailYS
def fixedSingularCostYS:ℕ:=76778677599070
def firstResidualRegularCostYS:ℕ:=9644144290222
def firstResidualSingularCostYS:ℕ:=235470664
def secondResidualRegularCostYS:ℕ:=0
def secondResidualSingularCostYS:ℕ:=4646124
def fixedRegularCostS:ℕ:=flagMixed fixedFlagS firstTailS secondTailS
def fixedSingularCostS:ℕ:=63997115995699
def firstResidualRegularCostS:ℕ:=15868064433192
def firstResidualSingularCostS:ℕ:=235470664
def secondResidualRegularCostS:ℕ:=2376733763872
def secondResidualSingularCostS:ℕ:=4646124
def fixedCostYS:ℕ:=fixedRegularCostYS + fixedSingularCostYS
def firstResidualCeilingYS:ℕ :=
 firstResidualRegularCostYS + firstResidualSingularCostYS
def secondResidualCeilingYS:ℕ :=
 secondResidualRegularCostYS + secondResidualSingularCostYS
def totalCostYS:ℕ :=
 fixedCostYS + firstResidualCeilingYS + secondResidualCeilingYS
def fixedCostS:ℕ:=fixedRegularCostS + fixedSingularCostS
def firstResidualCeilingS:ℕ :=
 firstResidualRegularCostS + firstResidualSingularCostS
def secondResidualCeilingS:ℕ :=
 secondResidualRegularCostS + secondResidualSingularCostS
def totalCostS:ℕ :=
 fixedCostS + firstResidualCeilingS + secondResidualCeilingS
def capacity:ℕ:=prime ^ 6 / 2 ^ 128
def listBudget:ℕ:=1000000000
def mcaBudget:ℕ:=capacity - listBudget
theorem basic_values :
   agreements = 182042 ∧ gap = 50971 ∧
     profileA.weightedCap = 7645764 ∧
     profileB.weightedCap = 14745402 ∧
     profileC.weightedCap = 7463722:=by
 decide
theorem support_values :
   supportYS.s = 12 ∧ supportYS.ys = 54 ∧ supportYS.total = 1261 ∧
     supportS.s = 11 ∧ supportS.ys = 55 ∧ supportS.total = 1261:=by
 decide
theorem fixed_flag_values :
   fixedFlagYS = ⟨1207,42,12⟩ ∧
     fixedFlagS = ⟨1206,44,11⟩:=by
 decide
theorem exact_costs :
   fixedRegularCostYS = 274157428415717762 ∧
     totalCostYS = 274243851477723842 ∧
     fixedRegularCostS = 257774510141394427 ∧
     totalCostS = 257856752295703978:=by
 decide
theorem budget_values :
   capacity = 274980728111395087 ∧
     mcaBudget = 274980727111395087 ∧
     totalCostYS < mcaBudget ∧ totalCostS < mcaBudget:=by
 decide
theorem radius_floor :
   ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ = errors:=by
 norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
   errors, IRSProfile.Index]
theorem radius_admissible :
   radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
 constructor <;>
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
     IRSProfile.minRelativeDistance]
theorem score_root_integer:(2:ℕ) ^ 17 * 598 ^ 50 ≤ 757 ^ 50:=by
 decide
theorem score_radius_integer :
   (23301249:ℕ) ^ 128 * (2 ^ 67 * 757) ≤ 598 * 33554432 ^ 128:=by
 decide
theorem two_rpow_score_fraction_le :
   (2:ℝ≥0) ^ ((17:ℝ) / 50) ≤ (757:ℝ≥0) / 598:=by
 have hroot:((2:ℝ≥0) ^ (17:ℕ)) ^ ((50:ℝ)⁻¹) ≤
     (757:ℝ≥0) / 598:=by
   rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 50)]
   rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
   exact_mod_cast score_root_integer
 calc
   (2:ℝ≥0) ^ ((17:ℝ) / 50) =
       ((2:ℝ≥0) ^ (17:ℕ)) ^ ((50:ℝ)⁻¹):=by
     rw [← NNReal.rpow_natCast_mul]
     norm_num [div_eq_mul_inv]
   _ ≤ (757:ℝ≥0) / 598:=hroot
theorem radius_power_rational_bound :
   (1 - radius) ^ IRSProfile.repetitions ≤
     ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (598 / 757):=by
 have hsub:(1 - radius:ℝ≥0) = 23301249 / 33554432:=by
   have hr:radius ≤ 1:=by
     rw [← NNReal.coe_le_coe]
     norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
   apply NNReal.coe_injective
   rw [NNReal.coe_sub hr]
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
 change (1 - radius) ^ 128 ≤ ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (598 / 757)
 rw [hsub, div_pow, div_mul_div_comm, one_mul,
   div_le_div_iff₀ (by positivity) (by positivity)]
 exact_mod_cast score_radius_integer
theorem score_target_le :
   (1 - radius) ^ IRSProfile.repetitions ≤ claimedError score:=by
 have hscale:(598:ℝ≥0) / 757 ≤
     (2:ℝ≥0) ^ (-((17:ℝ) / 50)):=by
   calc
     (598:ℝ≥0) / 757 = 1 / ((757:ℝ≥0) / 598):=by norm_num
     _ ≤ 1 / ((2:ℝ≥0) ^ ((17:ℝ) / 50)) :=
       one_div_le_one_div_of_le (by positivity) two_rpow_score_fraction_le
     _ = (2:ℝ≥0) ^ (-((17:ℝ) / 50)):=by
       rw [one_div, NNReal.rpow_neg]
 calc
   (1 - radius) ^ IRSProfile.repetitions ≤
       ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (598 / 757) :=
     radius_power_rational_bound
   _ ≤ ((1:ℝ≥0) / 2 ^ (67:ℕ)) *
       (2:ℝ≥0) ^ (-((17:ℝ) / 50)) :=
     mul_le_mul_of_nonneg_left hscale (by positivity)
   _ = claimedError score:=by
     unfold claimedError score
     rw [show -((((6734:ℕ):ℝ) / 100)) =
         -((67:ℕ):ℝ) + -((17:ℝ) / 50) by norm_num,
       NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
     simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.RCN327
end PackedLegacy_AL

/-! Packed from ProximityPrize.SubmissionLower.FT. -/
section PackedLegacy_FT
namespace ProximityPrize.SubmissionLower.RCN244
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN329 RCN312 RCN219 RCN218 RCN073 RCN086 RCN330 RCN328 RCN237 RCN095 RCN198 RCN287 RCN313 RCN217 RCN243 RCN072 RCN238
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
abbrev fixedSupport:=support 1206 42 10
abbrev Stage (K I:Type) [Field K]
   (Gamma:Finset K) (x:I → K) (p:ℕ) [CharP (GenericField K) p]
   (flag:FlagDegree)
   (errorCap:ℕ:=RCN327.errors)
   (stageSupport:RCN275.ResidualSupportParameters:=fixedSupport):=
 ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag
   RCN326.w stageSupport
variable {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
structure OriginalData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S) where
 factor:MvPolynomial (Fin 4) K
 cofactor:MvPolynomial (Fin 4) K
 irreducible:Irreducible factor
 positive:0 < factor.degreeOf 1+factor.degreeOf 2+factor.degreeOf 3
 product:S.F=factor*cofactor
 factor_dvd:S.G∣surfaceMap (polynomialEmbedding K) factor
 factor_mem:surfaceMap (polynomialEmbedding K) factor∈C.1
 cofactor_not_mem:surfaceMap (polynomialEmbedding K) cofactor∉C.1
 regularity_not_mem:
   surfaceMap (polynomialEmbedding K) (polyH K factor)∉C.1
noncomputable def originalData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   OriginalData S C:=by
 let h:=exists_original_factor_of_firstTailComponent S C
 let factor:=h.choose
 let cofactor:=h.choose_spec.choose
 have hs:=h.choose_spec.choose_spec
 exact ⟨factor,cofactor,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,
   hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2⟩
abbrev componentPrime
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):=
 contractedPrime (polynomialEmbedding K) C.1
theorem factorLe
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   RCN218.factorIdeal (originalData S C).factor ≤ componentPrime S C:=
 RCN218.factorIdeal_le_contractedPrime (polynomialEmbedding K) C.1
   (originalData S C).factor (originalData S C).factor_mem
abbrev LocalRing
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):=
 FactorLocal (originalData S C).factor (componentPrime S C) (factorLe S C)
local instance factorIdealPrime
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   (RCN218.factorIdeal (originalData S C).factor).IsPrime:=
 RCN218.factorIdeal_isPrime _ (originalData S C).irreducible
local instance quotientPrimeInstance
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   (RCN186.quotientPrime
     (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)).IsPrime:=
 RCN186.quotientPrime_isPrime _ _ (factorLe S C)
noncomputable def localImage
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K):LocalRing S C:=
 factorLocalImage (originalData S C).factor (componentPrime S C)
   (factorLe S C) A
noncomputable def localDerivation
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   Derivation K (LocalRing S C) (LocalRing S C):=
 factorLocalDerivation (originalData S C).factor (componentPrime S C)
   (factorLe S C)
theorem original_firstNumerator_mem_component
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S):
   surfaceMap (polynomialEmbedding K)
     (numerator K (originalData S C).factor
       (RCN326.w+1))∈C.1:=by
 let phi:=polynomialEmbedding K
 let d:=originalData S C
 let b:=RCN326.w+1
 have hwhole:surfaceMap phi (numerator K S.F b)∈C.1:=by
   apply (globalTailCut_mem_iff phi (polynomialEmbedding_injective K)
     S.F b C.1).mp
   exact regularComponent_T_mem (GenericField K) S.G
     (globalTailCut phi S.F b) (regularitySurface phi S.F) C
 have hdiff:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
       d.product b)
 have hdiffMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   exact C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hdiff))
     d.factor_mem
 have hproduct:surfaceMap phi
     (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
   have:=C.1.sub_mem hwhole hdiffMap
   simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
 have hproduct':surfaceMap phi (d.cofactor^(2*b))*
     surfaceMap phi (numerator K d.factor b)∈C.1:=by
   simpa only [map_mul] using hproduct
 have hsplit:surfaceMap phi (d.cofactor^(2*b))∈C.1∨
     surfaceMap phi (numerator K d.factor b)∈C.1:=
   (inferInstance:C.1.IsPrime).mem_or_mem hproduct'
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.cofactor_not_mem
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rcases hsplit with hleft | hright
 · exact False.elim (hcofactorPow (by simpa only [map_pow] using hleft))
 · exact hright
theorem componentPrime_height_eq_two
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   (componentPrime S C).height=2:=by
 let d:=originalData S C
 let N:=numerator K d.factor (RCN326.w+1)
 have hproperN:¬ d.factor∣N:=
   original_factor_firstTail_proper S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hheightC:C.1.height ≤ 2:=
   component_height_le_two (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1)) C.1
     (regularComponent_mem (GenericField K) S.G _ _ C)
 have horiginal:=originalPrime_height_eq_two C.1 hheightC d.factor N
   d.irreducible d.factor_mem (original_firstNumerator_mem_component S C) hproperN
 have heq:componentPrime S C=originalPrime C.1:=by
   apply Ideal.ext
   intro A
   exact (mem_contractedPrime_iff (polynomialEmbedding K) C.1 A).trans
     (mem_originalPrime_iff C.1 A).symm
 rw [heq]
 exact horiginal
structure LocalDVRFamily (S:Stage K I Gamma x p flag errorCap stageSupport) where
 domain:∀ C:FirstTailComponent S,IsDomain (LocalRing S C)
 dvr:∀ C:FirstTailComponent S,
   @IsDiscreteValuationRing (LocalRing S C) _ (domain C)
theorem canonicalLocalDVRFamily
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   LocalDVRFamily S where
 domain:=fun C↦inferInstance
 dvr:=fun C↦by
   exact factorLocal_isDiscreteValuationRing
     (originalData S C).factor (componentPrime S C) (factorLe S C)
     (componentPrime_height_eq_two S C hfirstProper)
     (originalData S C).regularity_not_mem
noncomputable def localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport) (L:LocalDVRFamily S)
   (C:FirstTailComponent S):ℕ:=by
 letI:IsDomain (LocalRing S C):=L.domain C
 letI:IsDiscreteValuationRing (LocalRing S C):=L.dvr C
 exact (IsDiscreteValuationRing.addVal (LocalRing S C)
   (localImage S C (numerator K (originalData S C).factor
     (RCN326.w+1)))).toNat
theorem localImage_isUnit_iff_not_mem
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K):
   IsUnit (localImage S C A) ↔
     surfaceMap (polynomialEmbedding K) A∉C.1:=by
 constructor
 · intro hunit hmem
   have hnon:¬ IsUnit (localImage S C A):=by
     change ¬ IsUnit
       (factorLocalImage
         (originalData S C).factor (componentPrime S C) (factorLe S C) A)
     have hmax:=
       (IsLocalization.AtPrime.to_map_mem_maximal_iff
         (LocalRing S C)
         (RCN186.quotientPrime
           (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C))
         (Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor) A)).2 (by
           have:A∈
               (RCN186.quotientPrime
                 (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)).comap
                 (Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor)):=by
             rw [RCN186.quotientPrime_comap_quotientMk
               (RCN218.factorIdeal (originalData S C).factor) (componentPrime S C)
               (factorLe S C)]
             exact hmem
           exact this)
     simpa only [factorLocalImage,IsLocalRing.mem_maximalIdeal,
       mem_nonunits_iff] using hmax
   exact hnon hunit
 · intro hnot
   exact factorLocal_image_isUnit_of_not_mem
     (originalData S C).factor A (componentPrime S C) (factorLe S C) hnot
theorem tail_mem_iff_original_numerator_mem
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S) (b:ℕ):
   globalTailCut (polynomialEmbedding K) S.F b∈C.1 ↔
     surfaceMap (polynomialEmbedding K)
       (numerator K (originalData S C).factor b)∈C.1:=by
 let phi:=polynomialEmbedding K
 let d:=originalData S C
 have hscaled:numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b∈
       Ideal.span ({d.factor}:Set (MvPolynomial (Fin 4) K)):=by
   exact Ideal.mem_span_singleton.mpr
     (factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
       d.product b)
 have hscaledMap:surfaceMap phi (numerator K S.F b-
     d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=
   C.1.mem_of_dvd
     (map_dvd (surfaceMap phi) (Ideal.mem_span_singleton.mp hscaled))
     d.factor_mem
 have hcofactorPow:surfaceMap phi (d.cofactor^(2*b))∉C.1:=by
   intro hpow
   apply d.cofactor_not_mem
   exact (inferInstance:C.1.IsPrime).mem_of_pow_mem (2*b)
     (by simpa only [map_pow] using hpow)
 rw [globalTailCut_mem_iff phi (polynomialEmbedding_injective K) S.F b C.1]
 constructor
 · intro hwhole
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     have:=C.1.sub_mem hwhole hscaledMap
     simpa only [map_sub,map_mul,map_pow,sub_sub_cancel] using this
   have hproduct':surfaceMap phi (d.cofactor^(2*b))*
       surfaceMap phi (numerator K d.factor b)∈C.1:=by
     simpa only [map_mul] using hproduct
   exact ((inferInstance:C.1.IsPrime).mem_or_mem hproduct').resolve_left
     hcofactorPow
 · intro horiginal
   have hproduct:surfaceMap phi
       (d.cofactor^(2*b)*numerator K d.factor b)∈C.1:=by
     rw [map_mul]
     exact C.1.mul_mem_left _ horiginal
   have:=C.1.add_mem hscaledMap hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using this
private theorem chosenLocalImage_ne_zero_of_not_dvd
   (S:Stage K I Gamma x p flag errorCap stageSupport) (C:FirstTailComponent S)
   (A:MvPolynomial (Fin 4) K)
   (hA:¬ (originalData S C).factor∣A):
   localImage S C A≠0:=by
 intro hzero
 have hquot:Ideal.Quotient.mk (RCN218.factorIdeal (originalData S C).factor) A=0:=by
   apply (IsLocalization.injective (LocalRing S C)
     (RCN186.quotientPrime
       (RCN218.factorIdeal (originalData S C).factor)
       (componentPrime S C)).primeCompl_le_nonZeroDivisors)
   simpa only [localImage,factorLocalImage,map_zero] using hzero
 exact hA (Ideal.mem_span_singleton.mp
   (Ideal.Quotient.eq_zero_iff_mem.mp hquot))
theorem local_order_tail_dichotomy
   (S:Stage K I Gamma x p flag errorCap stageSupport) (L:LocalDVRFamily S)
   (C:FirstTailComponent S)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   1 ≤ localMultiplicity S L C∧
     ((∃ delay,1 ≤ delay∧delay ≤ localMultiplicity S L C∧
       globalTailCut (polynomialEmbedding K) S.F
         (RCN326.w+1+delay)∉C.1)∨
     (∀ delay,globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∈C.1)):=by
 let d:=originalData S C
 let p0:=componentPrime S C
 let hFp:=factorLe S C
 let R:=LocalRing S C
 let D:=localDerivation S C
 let H:R:=localImage S C (polyH K d.factor)
 let N:ℕ → R:=fun j↦localImage S C
   (numerator K d.factor (RCN326.w+1+j))
 let coeff:ℕ → R:=fun j↦
   (2*(RCN326.w+1+j):R)
 letI:IsDomain R:=L.domain C
 letI:IsDiscreteValuationRing R:=L.dvr C
 letI:CharP K p:=
   (coefficientEmbedding K).charP (coefficientEmbedding_injective K) p
 letI:CharP R p:=charP_of_injective_algebraMap
   (algebraMap K R).injective p
 have hpne:p≠0:=by
   have:=S.characteristic_bound
   dsimp only [RCN326.w] at this
   omega
 have hp:p.Prime:=CharP.char_prime_of_ne_zero (GenericField K) hpne
 have hproperN:¬ d.factor∣
     numerator K d.factor (RCN326.w+1):=
   original_factor_firstTail_proper S hfirstProper d.factor d.cofactor
     d.product d.factor_dvd
 have hN0ne:N 0≠0:=by
   exact chosenLocalImage_ne_zero_of_not_dvd S C _ hproperN
 have hN0nonunit:¬ IsUnit (N 0):=by
   have hmem:=original_firstNumerator_mem_component S C
   exact (localImage_isUnit_iff_not_mem S C _).not.mpr (not_not.mpr hmem)
 have hHunit:IsUnit H:=
   (localImage_isUnit_iff_not_mem S C _).2 d.regularity_not_mem
 have hrec:∀ j,N (j+1)=
     H*D (N j)-coeff j*N j*D H:=by
   intro j
   dsimp only [N,H,D,coeff,d,localImage,localDerivation]
   convert
     (factorLocal_numerator_succ
       (originalData S C).factor (componentPrime S C) (factorLe S C)
       (RCN326.w+1+j)) using 1 <;>
     push_cast <;> ring
 have hd:=recurrence_unit_or_persistent D H (D H) coeff N p hp
   hrec hHunit hN0ne hN0nonunit
 change 1 ≤ localMultiplicity S L C∧_
 change 1 ≤ (IsDiscreteValuationRing.addVal R (N 0)).toNat∧_ at hd
 refine ⟨hd.1,?_⟩
 rcases hd.2 with hproper | hpersistent
 · left
   obtain ⟨delay,hdelay1,hdelayMu,hunit⟩:=hproper
   refine ⟨delay,hdelay1,hdelayMu,?_⟩
   apply (tail_mem_iff_original_numerator_mem S C _).not.mpr
   exact (localImage_isUnit_iff_not_mem S C _).1 hunit
 · right
   intro delay
   by_contra hnot
   apply hpersistent delay
   apply (localImage_isUnit_iff_not_mem S C _).2
   exact (tail_mem_iff_original_numerator_mem S C _).not.mp hnot
theorem one_le_localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1)):
   ∀ C,1 ≤ localMultiplicity S
     (canonicalLocalDVRFamily S hfirstProper) C:=by
 intro C
 exact (local_order_tail_dichotomy S
   (canonicalLocalDVRFamily S hfirstProper) C hfirstProper).1
end
end ProximityPrize.SubmissionLower.RCN244
end PackedLegacy_FT

/-! Packed from ProximityPrize.SubmissionLower.GL. -/
section PackedLegacy_GL
namespace ProximityPrize.SubmissionLower.RCN310
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {A:Type*} [CommRing A]
theorem exists_multiplier_mem_sup_pow_of_localized_mem
   (I p:Ideal A) (hIp:I ≤ p)
   (pbar:Ideal (A ⧸ I)) [pbar.IsPrime]
   (hpbar:pbar=Ideal.map (Ideal.Quotient.mk I) p)
   (x:A) (n:ℕ)
   (hx:algebraMap (A ⧸ I) (Localization.AtPrime pbar)
     (Ideal.Quotient.mk I x)∈
       IsLocalRing.maximalIdeal (Localization.AtPrime pbar)^n):
   ∃ s:A,s∉p∧s*x∈I ⊔ p^n:=by
 let S:=A ⧸ I
 let L:=Localization.AtPrime pbar
 let q:A →+*S:=Ideal.Quotient.mk I
 have hxMap:algebraMap S L (q x)∈
     Ideal.map (algebraMap S L) (pbar^n):=by
   rw [Ideal.map_pow,IsLocalization.AtPrime.map_eq_maximalIdeal pbar L]
   exact hx
 rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
   pbar.primeCompl L] at hxMap
 obtain ⟨m,hmM,hmprod⟩:=hxMap
 obtain ⟨s,hs⟩:=Ideal.Quotient.mk_surjective m
 have hcomap:Ideal.comap q pbar=p:=by
   rw [hpbar,Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
     ←RingHom.ker_eq_comap_bot,Ideal.mk_ker,sup_eq_left.mpr hIp]
 have hsnot:s∉p:=by
   intro hsp
   have hqsp:q s∈pbar:=by
     change s∈Ideal.comap q pbar
     rwa [hcomap]
   exact hmM (hs ▸ hqsp)
 have hmprod':q (s*x)∈pbar^n:=by
   simpa only [q,map_mul,hs] using hmprod
 have hmapped:q (s*x)∈Ideal.map q (p^n):=by
   rw [Ideal.map_pow, ←hpbar]
   exact hmprod'
 have hcomapPow:s*x∈Ideal.comap q (Ideal.map q (p^n)):=hmapped
 rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
   ←RingHom.ker_eq_comap_bot,Ideal.mk_ker] at hcomapPow
 exact ⟨s,hsnot,by simpa only [sup_comm] using hcomapPow⟩
theorem isPrimary_of_maximal_power_le_le
   (J Q:Ideal A) [J.IsMaximal] (n:ℕ) (hn:1 ≤ n)
   (hpow:J^n ≤ Q) (hle:Q ≤ J):Q.IsPrimary:=by
 apply Ideal.isPrimary_of_isMaximal_radical
 have hrad:Ideal.radical Q=J:=by
   apply le_antisymm
   · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
   · intro x hx
     exact ⟨n,hpow (Ideal.pow_mem_pow hx n)⟩
 rw [hrad]
 exact inferInstance
theorem mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
   (surface x s:A) (J:Ideal A) [J.IsMaximal]
   (hsurface:surface∈J) (n:ℕ) (hn:1 ≤ n)
   (hs:s∉J)
   (hmul:s*x∈Ideal.span {surface} ⊔ J^n):
   x∈Ideal.span {surface} ⊔ J^n:=by
 let Q:=Ideal.span {surface} ⊔ J^n
 have hpow:J^n ≤ Q:=le_sup_right
 have hle:Q ≤ J:=by
   exact sup_le (Ideal.span_le.mpr (by simpa))
     (Ideal.pow_le_self (Nat.ne_of_gt hn))
 have hprimary:Q.IsPrimary:=
   isPrimary_of_maximal_power_le_le J Q n hn hpow hle
 have hcases:=(Ideal.isPrimary_iff.mp hprimary).2
   (by simpa only [mul_comm] using hmul)
 rcases hcases with hxQ | hsrad
 · exact hxQ
 · have hrad:Ideal.radical Q=J:=by
     apply le_antisymm
     · exact (inferInstance:J.IsPrime).radical_le_iff.mpr hle
     · intro y hy
       exact ⟨n,hpow (Ideal.pow_mem_pow hy n)⟩
   exact False.elim (hs (hrad ▸ hsrad))
theorem mapped_mem_span_sup_pow_of_localized_mem
   {B:Type*} [CommRing B]
   (I p:Ideal A) (hIp:I ≤ p)
   (pbar:Ideal (A ⧸ I)) [pbar.IsPrime]
   (hpbar:pbar=Ideal.map (Ideal.Quotient.mk I) p)
   (x:A) (n:ℕ) (hn:1 ≤ n)
   (hx:algebraMap (A ⧸ I) (Localization.AtPrime pbar)
     (Ideal.Quotient.mk I x)∈
       IsLocalRing.maximalIdeal (Localization.AtPrime pbar)^n)
   (f:A →+*B) (surface:B) (J:Ideal B) [J.IsMaximal]
   (hmapI:Ideal.map f I ≤ Ideal.span {surface})
   (hsurface:surface∈J)
   (hcontract:Ideal.comap f J=p):
   f x∈Ideal.span {surface} ⊔ J^n:=by
 obtain ⟨s,hsnot,hsx⟩:=
   exists_multiplier_mem_sup_pow_of_localized_mem
     I p hIp pbar hpbar x n hx
 have hmapP:Ideal.map f p ≤ J:=by
   rw [Ideal.map_le_iff_le_comap,hcontract]
 have hmapPow:Ideal.map f (p^n) ≤ J^n:=by
   rw [Ideal.map_pow]
   exact pow_le_pow_left' hmapP n
 have htarget:Ideal.map f (I ⊔ p^n) ≤
     Ideal.span {surface} ⊔ J^n:=by
   rw [Ideal.map_sup]
   exact sup_le (hmapI.trans le_sup_left) (hmapPow.trans le_sup_right)
 have hmul:f s*f x∈Ideal.span {surface} ⊔ J^n:=by
   rw [←map_mul]
   exact htarget (Ideal.mem_map_of_mem f hsx)
 have hfs:f s∉J:=by
   intro h
   apply hsnot
   rw [←hcontract]
   exact h
 exact mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
   surface (f x) (f s) J hsurface n hn hfs hmul
end
end ProximityPrize.SubmissionLower.RCN310
end PackedLegacy_GL

/-! Packed from ProximityPrize.SubmissionLower.FX. -/
section PackedLegacy_FX
namespace ProximityPrize.SubmissionLower.RCN248
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem exists_original_multiplier_for_localMultiplicity
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:FirstTailComponent S):
   let d:=originalData S C
   let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
   ∃ s:MvPolynomial (Fin 4) K,
     s∉componentPrime S C∧
     s*numerator K d.factor
       (RCN326.w+1)∈
         RCN218.factorIdeal d.factor ⊔ componentPrime S C^mu:=by
 let d:=originalData S C
 let family:=canonicalLocalDVRFamily S hfirstProper
 let mu:=localMultiplicity S family C
 let N:=numerator K d.factor
   (RCN326.w+1)
 let p0:=componentPrime S C
 let I0:=RCN218.factorIdeal d.factor
 let q0:=quotientPrime I0 p0
 let R:=LocalRing S C
 letI:IsDomain R:=family.domain C
 letI:IsDiscreteValuationRing R:=family.dvr C
 have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
 have horder:IsDiscreteValuationRing.addVal R (localImage S C N)=mu:=by
   change IsDiscreteValuationRing.addVal R (localImage S C N)=
     (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat
   apply (ENat.coe_toNat ?_).symm
   intro htop
   change 1 ≤ (IsDiscreteValuationRing.addVal R (localImage S C N)).toNat at hmuPos
   rw [htop] at hmuPos
   simp at hmuPos
 obtain ⟨uniformizer,hUniformizer⟩:=
   IsDiscreteValuationRing.exists_irreducible R
 have hdvd:uniformizer^mu∣localImage S C N:=by
   apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
   rw [hUniformizer.addVal_pow,horder]
 have hxMax:localImage S C N∈IsLocalRing.maximalIdeal R^mu:=by
   rw [hUniformizer.maximalIdeal_eq,Ideal.span_singleton_pow,
     Ideal.mem_span_singleton]
   exact hdvd
 haveI:I0.IsPrime:=RCN218.factorIdeal_isPrime d.factor d.irreducible
 haveI:q0.IsPrime:=quotientPrime_isPrime I0 p0 (factorLe S C)
 exact exists_multiplier_mem_sup_pow_of_localized_mem
   I0 p0 (factorLe S C) q0 rfl N mu hxMax
theorem proper_global_tail_mem_projected_primary
   {B:Type*} [CommRing B]
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (C:FirstTailComponent S)
   (f:MvPolynomial (Fin 4) K →+*B)
   (surface tail scalar:B) (J:Ideal B) [J.IsMaximal]
   (hfactor:f (originalData S C).factor∈Ideal.span {surface})
   (hsurface:surface∈J)
   (hcontract:Ideal.comap f J=componentPrime S C)
   (htail:tail=f (numerator K S.F
     (RCN326.w+1))*scalar):
   tail∈Ideal.span {surface} ⊔
     J^localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C:=by
 let d:=originalData S C
 let mu:=localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) C
 let b:=RCN326.w+1
 let Nfactor:=numerator K d.factor b
 let Q:=Ideal.span {surface} ⊔ J^mu
 obtain ⟨s,hsnot,hsN⟩:=
   exists_original_multiplier_for_localMultiplicity S hfirstProper C
 have hmapI:Ideal.map f (RCN218.factorIdeal d.factor) ≤ Ideal.span {surface}:=by
   rw [RCN218.factorIdeal,Ideal.map_span,Set.image_singleton,Ideal.span_le]
   exact Set.singleton_subset_iff.mpr hfactor
 have hmapP:Ideal.map f (componentPrime S C) ≤ J:=by
   rw [Ideal.map_le_iff_le_comap,hcontract]
 have hmapPow:Ideal.map f (componentPrime S C^mu) ≤ J^mu:=by
   rw [Ideal.map_pow]
   exact pow_le_pow_left' hmapP mu
 have htarget:Ideal.map f
     (RCN218.factorIdeal d.factor ⊔ componentPrime S C^mu) ≤ Q:=by
   rw [Ideal.map_sup]
   exact sup_le (hmapI.trans le_sup_left) (hmapPow.trans le_sup_right)
 have hmul:f s*f Nfactor∈Q:=by
   rw [←map_mul]
   exact htarget (Ideal.mem_map_of_mem f hsN)
 have hfs:f s∉J:=by
   intro hsJ
   apply hsnot
   rw [←hcontract]
   exact hsJ
 have hmuPos:1 ≤ mu:=one_le_localMultiplicity S hfirstProper C
 have hNfactor:f Nfactor∈Q:=
   mem_span_sup_pow_of_mul_mem_of_not_mem_maximal
     surface (f Nfactor) (f s) J hsurface mu hmuPos hfs hmul
 have hdiff:d.factor∣numerator K S.F b-
     d.cofactor^(2*b)*Nfactor:=
   factor_dvd_numerator_sub_power_of_eq d.factor d.cofactor S.F
     d.product b
 have hdiffMap:f (numerator K S.F b-
     d.cofactor^(2*b)*Nfactor)∈Ideal.span {surface}:=
   (Ideal.span {surface}).mem_of_dvd (map_dvd f hdiff) hfactor
 have hproduct:f (d.cofactor^(2*b)*Nfactor)∈Q:=by
   rw [map_mul]
   exact Q.mul_mem_left _ hNfactor
 have hwhole:f (numerator K S.F b)∈Q:=by
   have hdiffQ:f (numerator K S.F b-
       d.cofactor^(2*b)*Nfactor)∈Q:=
     (show Ideal.span {surface} ≤ Q from le_sup_left) hdiffMap
   have hadd:=Q.add_mem hdiffQ hproduct
   simpa only [map_sub,map_mul,map_pow,sub_add_cancel] using hadd
 rw [htail]
 exact Q.mul_mem_right scalar hwhole
end
end ProximityPrize.SubmissionLower.RCN248
end PackedLegacy_FX

/-! Packed from ProximityPrize.SubmissionLower.FU. -/
section PackedLegacy_FU
namespace ProximityPrize.SubmissionLower.RCN245
open RCN244 RCN135 RCN136 RCN074 RCN095 RCN102 RCN113 RCN120 RCN086 RCN313 RCN002 RCN011 RCN125
noncomputable section
set_option autoImplicit false
variable {K I:Type} [Field K]
 {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
abbrev StageComponent (S:Stage K I Gamma x p flag errorCap stageSupport):=FirstTailComponent S
def stageSurfacePlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order S.G
def stageTailPlane (S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3):
   PlaneRing (GenericField K):=
 flagPlaneMap (GenericField K) lam mu nu order
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
def stageFiberTargetMap (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   MvPolynomial (Fin 4) K →+*Polynomial (FiberCoefficient q hq):=
 ((fiberLocalizePlane q hq).comp
   (flagPlaneMap (GenericField K) lam mu nu order)).comp
     (surfaceMap (polynomialEmbedding K))
def stageFiberScalar (_S:Stage K I Gamma x p flag errorCap stageSupport)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q):
   Polynomial (FiberCoefficient q hq):=
 fiberLocalizePlane q hq
   (flagPlaneMap (GenericField K) lam mu nu order
     (MvPolynomial.C ((-polynomialEmbedding K Polynomial.X)^
       (RCN326.w+1))))
end
end ProximityPrize.SubmissionLower.RCN245
end PackedLegacy_FU

/-! Packed from ProximityPrize.SubmissionLower.FV. -/
section PackedLegacy_FV
namespace ProximityPrize.SubmissionLower.RCN246
open RCN244 RCN248 RCN135 RCN136 RCN095 RCN074 RCN106 RCN107 RCN102 RCN245 RCN113 RCN120 RCN086 RCN264 RCN218 RCN313 RCN002 RCN011 RCN021 RCN125 RCN093
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem indexedStageSurface_mem_relation
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   stageSurfacePlane S lam mu nu order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a).1) order
       (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 change planeEvaluation (GenericField K)
   (CoordinateField (GenericField K) (component a).1) order
     (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom lam mu nu S.G))=0
 rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom lam mu nu S.G)=0
 rw [flagEvaluation_flag]
 change S.G∈RingHom.ker
   (coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [coordinateEvaluation_ker]
 exact regularComponent_G_mem (GenericField K) S.G _ _ (component a)
theorem indexedStageTail_mem_relation
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0)))) (a:A):
   stageTailPlane S lam mu nu order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a).1) order
       (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a):=by
 let tail:=globalTailCut (polynomialEmbedding K) S.F
   (RCN326.w+1)
 change planeEvaluation (GenericField K)
   (CoordinateField (GenericField K) (component a).1) order
     (flagEvaluation (GenericField K) (component a).1 lam mu nu) (ht a)
       (planeMap (GenericField K) order (flagAlgHom lam mu nu tail))=0
 rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation (GenericField K) (component a).1 lam mu nu
   (flagAlgHom lam mu nu tail)=0
 rw [flagEvaluation_flag]
 change tail∈RingHom.ker
   (coordinateEvaluation (GenericField K) (component a).1).toRingHom
 rw [coordinateEvaluation_ker]
 exact regularComponent_T_mem (GenericField K) S.G tail _ (component a)
structure IndexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):Prop where
 relationMax:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal
 factor_mem:stageFiberTargetMap S lam mu nu order q hq
   (originalData S (component a.1)).factor∈
     Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)}
 surface_mem:indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)∈
   indexedFiberRelation component lam mu nu order ht q hq a
 contract:(indexedFiberRelation component lam mu nu order ht q hq a).comap
   (stageFiberTargetMap S lam mu nu order q hq)=componentPrime S (component a.1)
 tail_eq:indexedFiberTail q hq (stageTailPlane S lam mu nu order)=
   stageFiberTargetMap S lam mu nu order q hq
     (numerator K S.F (RCN326.w+1))*
       stageFiberScalar S lam mu nu order q hq
theorem indexedFiberProjectionData
   (S:Stage K I Gamma x p flag errorCap stageSupport) (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   IndexedFiberProjectionData S component lam mu nu order ht q hq a:=by
 let phi:=polynomialEmbedding K
 let plane:=flagPlaneMap (GenericField K) lam mu nu order
 let localize:=fiberLocalizePlane q hq
 let J:=indexedFiberRelation component lam mu nu order ht q hq a
 refine ⟨indexedFiberRelation_isMaximal component lam mu nu order ht
   hfinite hgen q hq a,?_,?_,?_,?_⟩
 · rw [Ideal.mem_span_singleton]
   exact map_dvd (localize.comp plane) (originalData S (component a.1)).factor_dvd
 · exact Ideal.mem_map_of_mem localize
     (indexedStageSurface_mem_relation S component lam mu nu order ht a.1)
 · have hplane:(relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap plane=(component a.1).1:=by
     change (relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu)
         (ht a.1)).comap
       ((planeMap (GenericField K) order).comp (flagAlgHom lam mu nu).toRingHom)=_
     rw [←Ideal.comap_comap,relationKernel_contract,
       flagEvaluation_kernel_contract]
   change J.comap ((localize.comp plane).comp (surfaceMap phi))=
     componentPrime S (component a.1)
   rw [←Ideal.comap_comap, ←Ideal.comap_comap,
     indexedFiberRelation_under,hplane]
   rfl
 · change localize (plane (globalTailCut phi S.F
     (RCN326.w+1)))=
     localize (plane (surfaceMap phi (numerator K S.F
       (RCN326.w+1))))*
       localize (plane (MvPolynomial.C
         ((-phi Polynomial.X)^(RCN326.w+1))))
   rw [globalTailCut_eq,map_mul,map_mul]
end
end ProximityPrize.SubmissionLower.RCN246
end PackedLegacy_FV

/-! Packed from ProximityPrize.SubmissionLower.FW. -/
section PackedLegacy_FW
namespace ProximityPrize.SubmissionLower.RCN247
open RCN244 RCN248 RCN074 RCN106 RCN107 RCN102 RCN245 RCN246 RCN120 RCN086 RCN218 RCN135 RCN313 RCN095 RCN093 RCN002 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem indexedFiberTail_mem_primary
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (component:A → StageComponent S)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a:A,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a:A,
     letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))}:
         Set (CoordinateField (GenericField K) (component a).1))=⊤)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   indexedFiberTail q hq (stageTailPlane S lam mu nu order)∈
     Ideal.span {indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order)} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^
         localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (component a.1):=by
 let D:=indexedFiberProjectionData S component lam mu nu order ht hfinite hgen q hq a
 letI:(indexedFiberRelation component lam mu nu order ht q hq a).IsMaximal:=
   D.relationMax
 have hfactor:=D.factor_mem
 have hsurface:=D.surface_mem
 have hcontract:=D.contract
 have htail:=D.tail_eq
 apply proper_global_tail_mem_projected_primary
   (K:=K) (I:=I) (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
   (B:=Polynomial (FiberCoefficient q hq))
   (S:=S) (hfirstProper:=hfirstProper) (C:=component a.1)
   (f:=stageFiberTargetMap S lam mu nu order q hq)
   (surface:=indexedFiberSurface q hq (stageSurfacePlane S lam mu nu order))
   (tail:=indexedFiberTail q hq (stageTailPlane S lam mu nu order))
   (scalar:=stageFiberScalar S lam mu nu order q hq)
   (J:=indexedFiberRelation component lam mu nu order ht q hq a)
 · exact hfactor
 · exact hsurface
 · exact hcontract
 · exact htail
end
end ProximityPrize.SubmissionLower.RCN247
end PackedLegacy_FW

/-! Packed from ProximityPrize.SubmissionLower.O. -/
section PackedLegacy_O
namespace ProximityPrize.SubmissionLower.RCN111
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN120 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
noncomputable def indexedPlaneResidueWeight (a:A):ℕ:=by
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Fact (Irreducible q):=
   ⟨projectedFactor_irreducible Omega L order e (ht a) (hfinite a)⟩
 let a0:=residueAlgebra q J (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=a0.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 exact Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J)
end
end ProximityPrize.SubmissionLower.RCN111
end PackedLegacy_O

/-! Packed from ProximityPrize.SubmissionLower.FY. -/
section PackedLegacy_FY
namespace ProximityPrize.SubmissionLower.RCN249
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN074 RCN245 RCN106 RCN111 RCN095 RCN120 RCN093 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) (A:Type) [Fintype A]
structure StageIndexedFlagFamily where
 component:A → StageComponent S
 injective:Function.Injective component
 lam:GenericField K
 mu:GenericField K
 nu:GenericField K
 order:Fin 3 ≃ Fin 3
 ht:∀ a,Transcendental (GenericField K)
   (flagEvaluation (GenericField K) (component a).1 lam mu nu
     (MvPolynomial.X (order 0)))
 finite:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   FiniteDimensional (RatFunc (GenericField K))
     (CoordinateField (GenericField K) (component a).1)
 generates:∀ a,
   letI:=flagBaseAlgebra (GenericField K) (component a).1 lam mu nu order (ht a)
   IntermediateField.adjoin (RatFunc (GenericField K))
     ({flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 2)),
       flagEvaluation (GenericField K) (component a).1 lam mu nu
         (MvPolynomial.X (order 1))}:
       Set (CoordinateField (GenericField K) (component a).1))=⊤
 positive:0 < (stageSurfacePlane S lam mu nu order).natDegree
structure StageIndexedFactor (F:StageIndexedFlagFamily S A) where
 q:Polynomial (RatFunc (GenericField K))
 irreducible:Irreducible q
 monic:q.Monic
 witness:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q
noncomputable def stageFamilyGroupedExponent
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):ℕ:=
 ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
   localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
     indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
       F.ht F.finite a.1
noncomputable def stageFamilyResultant (F:StageIndexedFlagFamily S A):
   Polynomial (RatFunc (GenericField K)):=
 Polynomial.resultant (stageSurfacePlane S F.lam F.mu F.nu F.order)
   (stageTailPlane S F.lam F.mu F.nu F.order)
   (stageSurfacePlane S F.lam F.mu F.nu F.order).natDegree
   (stageTailPlane S F.lam F.mu F.nu F.order).natDegree
@[simp] theorem stageFamilyGroupedExponent_eq
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (q):
   stageFamilyGroupedExponent S A hfirstProper F q=
     ∑ a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q,
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper) (F.component a.1)*
         indexedPlaneResidueWeight F.component F.lam F.mu F.nu F.order
           F.ht F.finite a.1:=rfl
end
end ProximityPrize.SubmissionLower.RCN249
end PackedLegacy_FY

/-! Packed from ProximityPrize.SubmissionLower.J9. -/
section PackedLegacy_J9
namespace ProximityPrize.SubmissionLower.RCN102
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN022 RCN264 RCN125 RCN093 RCN226 RCN191 RCN120 RCN113 RCN225 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
def componentFactor (C:RegularComponent Omega G T H):
   Polynomial (RatFunc Omega):=
 projectedFactor Omega (CoordinateField Omega C.1) order
   (flagEvaluation Omega C.1 lam mu nu) (ht C)
abbrev FactorFiber (q:Polynomial (RatFunc Omega)):=
 {C:RegularComponent Omega G T H//q=componentFactor lam mu nu order ht C}
def fiberRelation
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   Ideal (Polynomial (FiberCoefficient q hq)):=
 Ideal.map (fiberLocalizePlane q hq)
   (relationKernel Omega (CoordinateField Omega C.1.1) order
     (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1))
def fiberRelationBar
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (C:FactorFiber lam mu nu order ht q):
   Ideal (SurfaceQuotient (fiberLocalizePlane q hq surface)):=
 Ideal.map (Ideal.Quotient.mk
   (Ideal.span {fiberLocalizePlane q hq surface}))
     (fiberRelation lam mu nu order ht q hq C)
theorem fiberRelation_under
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   (fiberRelation lam mu nu order ht q hq C).comap
     (fiberLocalizePlane q hq)=
       relationKernel Omega (CoordinateField Omega C.1.1) order
         (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega C.1.1) order
   (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
 let f:=fiberLocalizePlane q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hJprime:J.IsPrime:=RingHom.ker_isPrime _
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) C.property.symm
 have hdisjoint:Disjoint
     ((p.primeCompl.map c.toMonoidHom):Set (PlaneRing Omega))
       (J:Set (PlaneRing Omega)):=by
   rw [Set.disjoint_left]
   intro a ha haJ
   obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
   exact hr (hcomap ▸ haJ)
 change (Ideal.map f J).comap f=J
 change (Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R)) J).comap
   (algebraMap (PlaneRing Omega) (Polynomial R))=J
 exact IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R) hJprime hdisjoint
theorem fiberRelation_isMaximal
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hgen:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 1))}:
         Set (CoordinateField Omega C.1))=⊤)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   (fiberRelation lam mu nu order ht q hq C).IsMaximal:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let J:=relationKernel Omega (CoordinateField Omega C.1.1) order
   (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hJmax:J.IsMaximal:=relationKernel_isMaximal Omega
   (CoordinateField Omega C.1.1) order
     (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
       (hfinite C.1) (hgen C.1)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hunder:=fiberRelation_under lam mu nu order ht q hq C
 letI:((fiberRelation lam mu nu order ht q hq C).under
     (PlaneRing Omega)).IsMaximal:=by
   change ((fiberRelation lam mu nu order ht q hq C).comap
     (algebraMap (PlaneRing Omega) (Polynomial R))).IsMaximal
   simpa only [fiberLocalizePlane] using hunder ▸ hJmax
 exact Ideal.IsMaximal.of_isLocalization_of_disjoint
   (p.primeCompl.map c.toMonoidHom)
theorem fiberRelation_injective
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Function.Injective (fiberRelation lam mu nu order ht q hq):=by
 intro C D hCD
 have hunder:=congrArg
   (Ideal.comap (fiberLocalizePlane q hq)) hCD
 rw [fiberRelation_under lam mu nu order ht q hq C,
   fiberRelation_under lam mu nu order ht q hq D] at hunder
 have heval:=congrArg (Ideal.comap (planeMap Omega order)) hunder
 rw [relationKernel_contract,relationKernel_contract] at heval
 have hprime:=congrArg
   (Ideal.comap (flagAlgHom lam mu nu).toRingHom) heval
 rw [flagEvaluation_kernel_contract,flagEvaluation_kernel_contract] at hprime
 apply Subtype.ext
 apply Subtype.ext
 exact hprime
theorem fiberRelation_pairwise_coprime
   (hfinite:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))
   (hgen:∀ C:RegularComponent Omega G T H,
     letI:=flagBaseAlgebra Omega C.1 lam mu nu order (ht C)
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 1))}:
         Set (CoordinateField Omega C.1))=⊤)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q):
   Pairwise fun C D:FactorFiber lam mu nu order ht q =>
     IsCoprime (fiberRelation lam mu nu order ht q hq C)
       (fiberRelation lam mu nu order ht q hq D):=by
 intro C D hne
 apply Ideal.isCoprime_iff_sup_eq.mpr
 exact (fiberRelation_isMaximal lam mu nu order ht hfinite hgen q hq C).coprime_of_ne
   (fiberRelation_isMaximal lam mu nu order ht hfinite hgen q hq D)
   (fun heq => hne (fiberRelation_injective lam mu nu order ht q hq heq))
end
end ProximityPrize.SubmissionLower.RCN102
end PackedLegacy_J9

/-! Packed from ProximityPrize.SubmissionLower.C5. -/
section PackedLegacy_C5
namespace ProximityPrize.SubmissionLower.RCN103
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
theorem transformedSurface_irreducible
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G)
   (C:RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   Irreducible (planeMap Omega order (flagAlgHom lam mu nu G)):=by
 let e:=flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom lam mu nu G)=0:=by
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C
 exact planeMap_irreducible_of_evaluation Omega (CoordinateField Omega C.1)
   order e (flagAlgHom lam mu nu G)
     ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC
theorem transformedSurface_not_dvd_tail
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (C:RegularComponent Omega G T H)
   (htC:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0)))):
   ¬ planeMap Omega order (flagAlgHom lam mu nu G)∣
     planeMap Omega order (flagAlgHom lam mu nu T):=by
 let e:=flagEvaluation Omega C.1 lam mu nu
 have hroot:e (flagAlgHom lam mu nu G)=0:=by
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C
 intro hdiv
 have hflagDvd:=(planeMap_dvd_iff_of_evaluation Omega
   (CoordinateField Omega C.1) order e
     (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
     ((flag_irreducible_iff lam mu nu G).mpr hG) hroot htC).mp hdiv
 exact hproper ((flag_dvd_iff lam mu nu G T).mp hflagDvd)
end
end ProximityPrize.SubmissionLower.RCN103
end PackedLegacy_C5

/-! Packed from ProximityPrize.SubmissionLower.K0. -/
section PackedLegacy_K0
namespace ProximityPrize.SubmissionLower.RCN103
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093 RCN120 RCN102 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ C:RegularComponent Omega G T H,
 Transcendental Omega
   (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
theorem fiber_denominators_disjoint_surface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   letI:(Ideal.span {q}).IsPrime:=
     (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
   Disjoint
     (((Ideal.span {q}).primeCompl.map
       (Polynomial.C:Polynomial (RatFunc Omega) →+*PlaneRing Omega).toMonoidHom):
       Set (PlaneRing Omega))
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)}:
       Set (PlaneRing Omega)):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let J:=relationKernel Omega (CoordinateField Omega C.1.1) order
   (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) C.property.symm
 have hsurface:planeMap Omega order (flagAlgHom lam mu nu G)∈J:=by
   change planeEvaluation Omega (CoordinateField Omega C.1.1) order
     (flagEvaluation Omega C.1.1 lam mu nu) (ht C.1)
       (planeMap Omega order (flagAlgHom lam mu nu G))=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   change flagEvaluation Omega C.1.1 lam mu nu (flagAlgHom lam mu nu G)=0
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega C.1.1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H C.1
 rw [Set.disjoint_left]
 intro a ha haSurface
 obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp ha
 apply hr
 have hJ:c r∈J:=J.mem_of_dvd
   (Ideal.mem_span_singleton.mp haSurface) hsurface
 have hrJ:r∈J.comap c:=hJ
 rw [hcomap] at hrJ
 exact hrJ
theorem fiberSurface_span_isPrime
   (hG:Irreducible G)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   (Ideal.span {fiberLocalizePlane q hq
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hglobal:(Ideal.span {planeMap Omega order
     (flagAlgHom lam mu nu G)}).IsPrime:=
   Ideal.isPrime_span_singleton_of_prime
     (transformedSurface_irreducible lam mu nu order hG C.1 (ht C.1)).prime
 have hmapped:=IsLocalization.isPrime_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)})
     hglobal (fiber_denominators_disjoint_surface lam mu nu order ht q hq C)
 change (@Ideal.span (Polynomial R) Polynomial.commSemiring.toSemiring
   {algebraMap (PlaneRing Omega) (Polynomial R)
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime
 simpa only [Ideal.map_span,Set.image_singleton] using hmapped
theorem fiberTail_not_mem_surface
   (hG:Irreducible G) (hproper:¬ G∣T)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (C:FactorFiber lam mu nu order ht q):
   fiberLocalizePlane q hq (planeMap Omega order (flagAlgHom lam mu nu T))∉
     Ideal.span {fiberLocalizePlane q hq
       (planeMap Omega order (flagAlgHom lam mu nu G))}:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 let f:PlaneRing Omega →+*Polynomial R:=fiberLocalizePlane q hq
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 intro hmem
 have hunder:=IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.isPrime_span_singleton_of_prime
       (transformedSurface_irreducible lam mu nu order hG C.1 (ht C.1)).prime)
     (fiber_denominators_disjoint_surface lam mu nu order ht q hq C)
 have hspanEq:Ideal.map f (Ideal.span {P})=Ideal.span {f P}:=by
   rw [Ideal.map_span]
   simp only [Set.image_singleton]
 have hmem':f Q∈Ideal.map f (Ideal.span {P}):=by
   rwa [hspanEq]
 have hglobal:Q∈Ideal.span {P}:=by
   have hx:Q∈(Ideal.map f (Ideal.span {P})).comap f:=hmem'
   change Q∈(Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R))
     (Ideal.span {P})).under (PlaneRing Omega) at hx
   rwa [hunder] at hx
 exact transformedSurface_not_dvd_tail lam mu nu order hG hproper C.1 (ht C.1)
   (Ideal.mem_span_singleton.mp hglobal)
end
end ProximityPrize.SubmissionLower.RCN103
end PackedLegacy_K0

/-! Packed from ProximityPrize.SubmissionLower.K3. -/
section PackedLegacy_K3
namespace ProximityPrize.SubmissionLower.RCN108
open RCN002 RCN011 RCN021 RCN264 RCN125 RCN093 RCN120 RCN102 RCN103 RCN106 RCN226
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
theorem indexed_denominators_disjoint_surface
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   letI:(Ideal.span {q}).IsPrime:=
     (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
   Disjoint (((Ideal.span {q}).primeCompl.map
     (Polynomial.C:Polynomial (RatFunc Omega) →+*PlaneRing Omega).toMonoidHom):
     Set (PlaneRing Omega))
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)}:
       Set (PlaneRing Omega)):=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let J:=relationKernel Omega (CoordinateField Omega (component a.1).1) order
   (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 have hcomap:J.comap c=p:=by
   rw [relationKernel_comap_C]
   exact congrArg (fun r => Ideal.span {r}) a.property.symm
 have hsurface:planeMap Omega order (flagAlgHom lam mu nu G)∈J:=by
   change planeEvaluation Omega (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1)
       (planeMap Omega order (flagAlgHom lam mu nu G))=0
   rw [←RingHom.comp_apply,planeEvaluation_comp_planeMap]
   change flagEvaluation Omega (component a.1).1 lam mu nu
     (flagAlgHom lam mu nu G)=0
   rw [flagEvaluation_flag]
   change G∈RingHom.ker (coordinateEvaluation Omega (component a.1).1).toRingHom
   rw [coordinateEvaluation_ker]
   exact regularComponent_G_mem Omega G T H (component a.1)
 rw [Set.disjoint_left]
 intro x hx hxSurface
 obtain ⟨r,hr,rfl⟩:=Submonoid.mem_map.mp hx
 apply hr
 have hJ:c r∈J:=J.mem_of_dvd
   (Ideal.mem_span_singleton.mp hxSurface) hsurface
 have hrJ:r∈J.comap c:=hJ
 rw [hcomap] at hrJ
 exact hrJ
theorem indexedFiberSurface_span_isPrime
   (hG:Irreducible G)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   (Ideal.span {fiberLocalizePlane q hq
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 have hglobal:(Ideal.span {planeMap Omega order
     (flagAlgHom lam mu nu G)}).IsPrime:=
   Ideal.isPrime_span_singleton_of_prime
     (transformedSurface_irreducible lam mu nu order hG
       (component a.1) (ht a.1)).prime
 have hmapped:=IsLocalization.isPrime_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.span {planeMap Omega order (flagAlgHom lam mu nu G)})
     hglobal (indexed_denominators_disjoint_surface
       component lam mu nu order ht q hq a)
 change (@Ideal.span (Polynomial R) Polynomial.commSemiring.toSemiring
   {algebraMap (PlaneRing Omega) (Polynomial R)
     (planeMap Omega order (flagAlgHom lam mu nu G))}).IsPrime
 simpa only [Ideal.map_span,Set.image_singleton] using hmapped
theorem indexedFiberTail_not_mem_surface
   (hG:Irreducible G) (hproper:¬ G∣T)
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (a:IndexedFactorFiber component lam mu nu order ht q):
   fiberLocalizePlane q hq (planeMap Omega order (flagAlgHom lam mu nu T))∉
     Ideal.span {fiberLocalizePlane q hq
       (planeMap Omega order (flagAlgHom lam mu nu G))}:=by
 let p:Ideal (Polynomial (RatFunc Omega)):=Ideal.span {q}
 let R:=FiberCoefficient q hq
 let c:Polynomial (RatFunc Omega) →+*PlaneRing Omega:=Polynomial.C
 let f:PlaneRing Omega →+*Polynomial R:=fiberLocalizePlane q hq
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 letI:p.IsPrime:=(PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 letI:Algebra (Polynomial (RatFunc Omega)) R:=inferInstance
 letI:IsLocalization p.primeCompl R:=inferInstance
 letI:Algebra (PlaneRing Omega) (Polynomial R):=
   Polynomial.algebra (Polynomial (RatFunc Omega)) R
 letI:IsLocalization (p.primeCompl.map c.toMonoidHom) (Polynomial R):=
   Polynomial.isLocalization p.primeCompl R
 intro hmem
 have hunder:=IsLocalization.under_map_of_isPrime_disjoint
   (p.primeCompl.map c.toMonoidHom) (Polynomial R)
     (Ideal.isPrime_span_singleton_of_prime
       (transformedSurface_irreducible lam mu nu order hG
         (component a.1) (ht a.1)).prime)
     (indexed_denominators_disjoint_surface component lam mu nu order ht q hq a)
 have hmem':f Q∈Ideal.map f (Ideal.span {P}):=by
   simpa only [Ideal.map_span,Set.image_singleton] using hmem
 have hglobal:Q∈Ideal.span {P}:=by
   have hx:Q∈(Ideal.map f (Ideal.span {P})).comap f:=hmem'
   change Q∈(Ideal.map (algebraMap (PlaneRing Omega) (Polynomial R))
     (Ideal.span {P})).under (PlaneRing Omega) at hx
   rwa [hunder] at hx
 exact transformedSurface_not_dvd_tail lam mu nu order hG hproper
   (component a.1) (ht a.1) (Ideal.mem_span_singleton.mp hglobal)
end
end ProximityPrize.SubmissionLower.RCN108
end PackedLegacy_K3

/-! Packed from ProximityPrize.SubmissionLower.FK. -/
section PackedLegacy_FK
namespace ProximityPrize.SubmissionLower.RCN227
open UniqueFactorizationMonoid
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K:Type} [Field K] [DecidableEq K]
theorem ord_algebraMap_eq_normalizedFactors_count
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic)
   (hr:r≠0):
   Ring.ord (Localization.AtPrime p)
     (algebraMap (Polynomial K) (Localization.AtPrime p) r)=
       ((normalizedFactors r).count q:ℕ∞):=by
 let R:=Localization.AtPrime p
 have hp0:p≠⊥:=by
   rw [hp,ne_eq,Ideal.span_singleton_eq_bot]
   exact hq.ne_zero
 letI:IsDiscreteValuationRing R:=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial K) hp0 R
 have hem:emultiplicity q r=((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 have hfinite:FiniteMultiplicity q r:=
   finiteMultiplicity_of_emultiplicity_eq_natCast hem
 let e:ℕ:=(normalizedFactors r).count q
 have hmult:multiplicity q r=e:=by
   rw [multiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 obtain ⟨s,hrs,hqNotDvd⟩:=hfinite.exists_eq_pow_mul_and_not_dvd
 rw [hmult] at hrs
 have hsNotMem:s∉p:=by
   simpa only [hp,Ideal.mem_span_singleton] using hqNotDvd
 have hsUnit:IsUnit (algebraMap (Polynomial K) R s):=
   (IsLocalization.AtPrime.isUnit_to_map_iff R p s).mpr hsNotMem
 have hqMapNe:algebraMap (Polynomial K) R q≠0:=
   by
     simpa only [map_zero] using
       (FaithfulSMul.algebraMap_injective (Polynomial K) R).ne hq.ne_zero
 have hmax:IsLocalRing.maximalIdeal R=
     Ideal.span {algebraMap (Polynomial K) R q}:=by
   calc
     IsLocalRing.maximalIdeal R=
         Ideal.map (algebraMap (Polynomial K) R) p:=by
       simpa only [R] using
         (Localization.AtPrime.map_eq_maximalIdeal (I:=p)).symm
     _=Ideal.map (algebraMap (Polynomial K) R) (Ideal.span {q}):=
       congrArg (Ideal.map (algebraMap (Polynomial K) R)) hp
     _=Ideal.span {algebraMap (Polynomial K) R q}:=by
       rw [Ideal.map_span]
       simp only [Set.image_singleton]
 have hqMapIrr:Irreducible (algebraMap (Polynomial K) R q):=
   IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
     _ hqMapNe hmax
 have hsNe:algebraMap (Polynomial K) R s≠0:=hsUnit.ne_zero
 have hrsMap:algebraMap (Polynomial K) R r=
     (algebraMap (Polynomial K) R q)^e*
       algebraMap (Polynomial K) R s:=by
   rw [hrs,map_mul,map_pow]
 change Ring.ord R (algebraMap (Polynomial K) R r)=_
 rw [hrsMap,
   Ring.ord_mul R (mem_nonZeroDivisors_iff_ne_zero.mpr hsNe),
   Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr hqMapNe),
   Ring.ord_of_irreducible hqMapIrr,Ring.ord_of_isUnit hsUnit]
 simp [e]
theorem pow_sum_dvd_of_sum_le_localized_ord
   {I:Type*} [Fintype I]
   (p:Ideal (Polynomial K)) [p.IsPrime]
   (q r:Polynomial K) (hp:p=Ideal.span {q})
   (hq:Irreducible q) (hqMonic:q.Monic) (hr:r≠0)
   (multiplicity:I → ℕ)
   (hle:((∑ i,multiplicity i:ℕ):ℕ∞) ≤
     Ring.ord (Localization.AtPrime p)
       (algebraMap (Polynomial K) (Localization.AtPrime p) r)):
   q^(∑ i,multiplicity i)∣r:=by
 rw [ord_algebraMap_eq_normalizedFactors_count p q r hp hq hqMonic hr] at hle
 have hcount:(∑ i,multiplicity i) ≤ (normalizedFactors r).count q:=by
   exact_mod_cast hle
 have hem:emultiplicity q r=
     ((normalizedFactors r).count q:ℕ∞):=by
   rw [emultiplicity_eq_count_normalizedFactors hq hr,
     hqMonic.normalize_eq_self]
 apply pow_dvd_of_le_emultiplicity
 rw [hem]
 exact_mod_cast hcount
end
end ProximityPrize.SubmissionLower.RCN227
end PackedLegacy_FK

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier22 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.GK. -/
section PackedLegacy_GK
namespace ProximityPrize.SubmissionLower.RCN308
open scoped Classical
open RCN307 RCN309
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {R:Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
 [IsLocalRing R]
def fullPiecesRingHom
   {J:Type*} [Fintype J]
   (pieces:J → Ideal (Polynomial R)):
   Polynomial R →+*(∀ j,Polynomial R ⧸ pieces j):=
 RingHom.pi fun j↦Ideal.Quotient.mk (pieces j)
def coefficientMaxIdeal:Ideal (Polynomial R):=
 Ideal.map (Polynomial.C:R →+*Polynomial R)
   (IsLocalRing.maximalIdeal R)
theorem rawPieces_modMax_surjective_of_monic_mod
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (pieces:J → Ideal (Polynomial R))
   (hcoprime:Pairwise fun i j↦IsCoprime (pieces i) (pieces j))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   (M:Polynomial R) (hMMonic:M.Monic)
   (hMmem:M∈intersectionIdeal P Q ⊔ coefficientMaxIdeal (R:=R))
   (hMdegree:M.natDegree ≤ m+n):
   Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)):=by
 let target:=∀ j,Polynomial R ⧸ pieces j
 let full:=fullPiecesRingHom pieces
 let maxTarget:=IsLocalRing.maximalIdeal R •
   (⊤:Submodule R target)
 have hfullC:full.comp (Polynomial.C:R →+*Polynomial R)=
     algebraMap R target:=by
   ext r j
   rfl
 have hcoeffMap:Ideal.map full (coefficientMaxIdeal (R:=R))=
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   rw [coefficientMaxIdeal,Ideal.map_map,hfullC]
 have hinterZero:∀ x∈intersectionIdeal P Q,full x=0:=by
   intro x hx
   funext j
   exact Ideal.Quotient.eq_zero_iff_mem.mpr (hcontains j hx)
 have hMmax:full M∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
   obtain ⟨a,ha,b,hb,hab⟩:=Submodule.mem_sup.mp hMmem
   have hfa:full a=0:=hinterZero a ha
   have hfb:full b∈
       Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=by
     rw [←hcoeffMap]
     exact Ideal.mem_map_of_mem full hb
   rw [←hab,map_add,hfa,zero_add]
   exact hfb
 intro ybar
 obtain ⟨y,rfl⟩:=Submodule.mkQ_surjective maxTarget ybar
 obtain ⟨A,hA⟩:=Ideal.pi_mkQ_surjective hcoprime y
 let rem:Polynomial R:=A %ₘ M
 have hremDegree:rem.degree < (m+n:ℕ):=by
   have hlt:=Polynomial.degree_modByMonic_lt A hMMonic
   rw [Polynomial.degree_eq_natDegree hMMonic.ne_zero] at hlt
   exact hlt.trans_le (by exact_mod_cast hMdegree)
 let v:Polynomial.degreeLT R (m+n):=
   ⟨rem,Polynomial.mem_degreeLT.mpr hremDegree⟩
 refine ⟨v,?_⟩
 change maxTarget.mkQ (rawPiecesMap P Q m n pieces v)=maxTarget.mkQ y
 rw [Submodule.mkQ_apply,Submodule.mkQ_apply,Submodule.Quotient.eq]
 have hraw:rawPiecesMap P Q m n pieces v=full rem:=by
   rfl
 have hfullA:full A=y:=hA
 rw [hraw, ←hfullA, ←map_sub]
 have hdiff:rem-A= -(M*(A/ₘ M)):=by
   dsimp only [rem]
   rw [Polynomial.modByMonic_eq_sub_mul_div]
   ring
 rw [hdiff,map_neg,map_mul]
 have hmul:full M*full (A/ₘ M)∈
     Ideal.map (algebraMap R target) (IsLocalRing.maximalIdeal R):=
   Ideal.mul_mem_right _ _ hMmax
 have hmul':full M*full (A/ₘ M)∈maxTarget:=by
   change full M*full (A/ₘ M)∈
     IsLocalRing.maximalIdeal R • (⊤:Submodule R target)
   rw [Ideal.smul_top_eq_map]
   exact hmul
 exact maxTarget.neg_mem hmul'
theorem sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
   {J:Type*} [Fintype J]
   (P Q:Polynomial R) (m n:ℕ)
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (pieces:J → Ideal (Polynomial R))
   (hcontains:∀ j,intersectionIdeal P Q ≤ pieces j)
   [Module.Finite R (∀ j,Polynomial R ⧸ pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal R •
         (⊤:Submodule R (∀ j,Polynomial R ⧸ pieces j))).mkQ).comp
       (rawPiecesMap P Q m n pieces)))
   (multiplicity:J → ℕ)
   (hlength:∀ j,(multiplicity j:ℕ∞) ≤
     Module.length R (Polynomial R ⧸ pieces j)):
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
     Ring.ord R (Polynomial.resultant P Q m n):=by
 classical
 letI:DecidableEq (Fin (m+n)):=Classical.decEq _
 let f:=Polynomial.sylvesterMap P Q hPcap hQcap
 have hinj:Function.Injective f:=by
   intro x y hxy
   apply sub_eq_zero.mp
   let z:=x-y
   have hfz:f z=0:=by simp [z,f,hxy]
   have hcomp:=LinearMap.congr_fun
     (Polynomial.adjSylvester_comp_sylveserMap P Q hPcap hQcap) z
   have hscalar:Polynomial.resultant P Q m n • z=0:=by
     rw [LinearMap.comp_apply,hfz,map_zero] at hcomp
     simpa using hcomp.symm
   exact (smul_eq_zero.mp hscalar).resolve_left hresultant
 have hbound:=
   RCN196.sum_multiplicities_le_ord_toMatrix_det_of_surjective
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f hinj
     (fun j↦Polynomial R ⧸ pieces j) multiplicity hlength
     (RCN309.cokerToPieces
       P Q m n hPcap hQcap pieces hcontains)
     (cokerToPieces_surjective_of_modMax P Q m n hPcap hQcap
       pieces hcontains hmod)
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd R m n)
     (Polynomial.degreeLT.basis R (m+n)) f=
       Polynomial.sylvester P Q m n:=by
   ext i j
   obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective j
   simpa [f,Polynomial.degreeLT.basisProd,LinearMap.toMatrix_apply] using
     congr($(Polynomial.toMatrix_sylvesterMap P Q hPcap hQcap) i j)
 calc
   ((∑ j,multiplicity j:ℕ):ℕ∞) ≤
       Ring.ord R (LinearMap.toMatrix
         (Polynomial.degreeLT.basisProd R m n)
         (Polynomial.degreeLT.basis R (m+n)) f).det:=hbound
   _=Ring.ord R (Polynomial.resultant P Q m n):=by
     rw [hmatrix]
     congr 1
     unfold Polynomial.resultant
     convert! rfl
end
end ProximityPrize.SubmissionLower.RCN308
end PackedLegacy_GK

/-! Packed from ProximityPrize.SubmissionLower.GB. -/
section PackedLegacy_GB
namespace ProximityPrize.SubmissionLower.RCN297
open RCN307 RCN308
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type*} [CommRing R] [IsLocalRing R]
theorem exists_specialized_monic_reducer
   (P:Polynomial R)
   (hPbar:P.map (IsLocalRing.residue R)≠0):
   ∃ M:Polynomial R,
     M.Monic∧
     M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)∧
     M.natDegree ≤ P.natDegree:=by
 let k:=IsLocalRing.ResidueField R
 let q:R →+*k:=IsLocalRing.residue R
 let Pbar:Polynomial k:=P.map q
 let Mbar:Polynomial k:=Pbar*Polynomial.C Pbar.leadingCoeff⁻¹
 have hMbarMonic:Mbar.Monic:=
   Polynomial.monic_mul_leadingCoeff_inv hPbar
 have hMbarLift:Mbar∈Polynomial.lifts q:=
   Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective) Mbar
 obtain ⟨M,hMmap,hMdegree,hMMonic⟩:=
   Polynomial.lifts_and_natDegree_eq_and_monic hMbarLift hMbarMonic
 obtain ⟨c,hc⟩:=IsLocalRing.residue_surjective Pbar.leadingCoeff⁻¹
 change q c=Pbar.leadingCoeff⁻¹ at hc
 let D:Polynomial R:=M-Polynomial.C c*P
 have hDmap:D.map q=0:=by
   dsimp only [D]
   rw [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
     hMmap,hc]
   dsimp only [Mbar]
   ring
 have hDcoeff:D∈coefficientMaxIdeal (R:=R):=by
   have hker:D∈RingHom.ker (Polynomial.mapRingHom q):=hDmap
   rw [Polynomial.ker_mapRingHom,IsLocalRing.ker_residue] at hker
   exact hker
 have hMmem:M∈Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=by
   have hfirst:Polynomial.C c*P∈Ideal.span {P}:=
     (Ideal.span {P}).mul_mem_left _
       (Ideal.subset_span (Set.mem_singleton P))
   have hfirst':Polynomial.C c*P∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show Ideal.span {P} ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_left) hfirst
   have hDcoeff':D∈
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R):=
     (show coefficientMaxIdeal (R:=R) ≤
       Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R) from le_sup_right) hDcoeff
   have hadd:=(Ideal.span {P} ⊔ coefficientMaxIdeal (R:=R)).add_mem
     hfirst' hDcoeff'
   convert hadd using 1 <;>
     simp only [D] <;> ring
 have hdegreeBar:Mbar.natDegree=Pbar.natDegree:=
   Polynomial.natDegree_mul_leadingCoeff_inv Pbar hPbar
 refine ⟨M,hMMonic,hMmem,?_⟩
 rw [hMdegree,hdegreeBar]
 exact Polynomial.natDegree_map_le
end
end ProximityPrize.SubmissionLower.RCN297
end PackedLegacy_GB

/-! Packed from ProximityPrize.SubmissionLower.EP. -/
section PackedLegacy_EP
namespace ProximityPrize.SubmissionLower.RCN143
open scoped Classical BigOperators
open RCN227 RCN307 RCN309 RCN308 RCN297
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Base:Type} [Field Base] [DecidableEq Base]
variable (primeIdeal:Ideal (Polynomial Base)) [primeIdeal.IsPrime]
 (factor:Polynomial Base)
abbrev LocalBase:=Localization.AtPrime primeIdeal
theorem grouped_resultant_power_dvd_of_primary_pieces_modMax
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]
   (hmod:Function.Surjective
     (((IsLocalRing.maximalIdeal (LocalBase primeIdeal) •
         (⊤:Submodule (LocalBase primeIdeal)
           (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j))).mkQ).comp
       (rawPiecesMap P Q m n C.pieces))):
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 have hp0:primeIdeal≠⊥:=by
   rw [hprime,ne_eq,Ideal.span_singleton_eq_bot]
   exact hfactor.ne_zero
 letI:IsDiscreteValuationRing (LocalBase primeIdeal):=
   IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
     (Polynomial Base) hp0 _
 have hmappedResultant:Polynomial.resultant P Q m n=
     algebraMap (Polynomial Base) (LocalBase primeIdeal)
       (Polynomial.resultant P₀ Q₀ m n):=by
   rw [hPmap,hQmap,Polynomial.resultant_map_map]
 have hmappedNe:Polynomial.resultant P Q m n≠0:=by
   rw [hmappedResultant]
   simpa only [map_zero] using
     (FaithfulSMul.algebraMap_injective
       (Polynomial Base) (LocalBase primeIdeal)).ne hresultant
 have hlocal:=
   sum_multiplicities_le_ord_resultant_of_primary_pieces_modMax
     P Q m n hPcap hQcap hmappedNe C.pieces C.contains hmod
       multiplicity C.length_le
 have hlocal':
     (((∑ j,multiplicity j:ℕ):ℕ∞)) ≤
       Ring.ord (LocalBase primeIdeal)
         (algebraMap (Polynomial Base) (LocalBase primeIdeal)
           (Polynomial.resultant P₀ Q₀ m n)):=by
   rw [←hmappedResultant]
   exact hlocal
 exact pow_sum_dvd_of_sum_le_localized_ord primeIdeal factor
   (Polynomial.resultant P₀ Q₀ m n) hprime hfactor hfactorMonic
     hresultant multiplicity hlocal'
theorem grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   {J:Type*} [Fintype J] (multiplicity:J → ℕ)
   (hprime:primeIdeal=Ideal.span {factor})
   (hfactor:Irreducible factor) (hfactorMonic:factor.Monic)
   (P₀ Q₀:Polynomial (Polynomial Base)) (m n:ℕ)
   (P Q:Polynomial (LocalBase primeIdeal))
   (hPmap:P=P₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hQmap:Q=Q₀.map
     (algebraMap (Polynomial Base) (LocalBase primeIdeal)))
   (hPcap:P.natDegree ≤ m) (hQcap:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P₀ Q₀ m n≠0)
   (hPbar:P.map (IsLocalRing.residue (LocalBase primeIdeal))≠0)
   (C:PrimaryPiecesCertificate P Q multiplicity)
   [Module.Finite (LocalBase primeIdeal)
     (∀ j,Polynomial (LocalBase primeIdeal) ⧸ C.pieces j)]:
   factor^(∑ j,multiplicity j)∣
     Polynomial.resultant P₀ Q₀ m n:=by
 obtain ⟨M,hMMonic,hMmem,hMdegreeP⟩:=
   exists_specialized_monic_reducer P hPbar
 have hspan:Ideal.span {P} ≤ intersectionIdeal P Q:=by
   rw [Ideal.span_le]
   intro x hx
   rw [Set.mem_singleton_iff] at hx
   subst x
   exact Ideal.subset_span (Set.mem_insert P {Q})
 have hMmem':M∈intersectionIdeal P Q ⊔
     coefficientMaxIdeal (R:=LocalBase primeIdeal):=
   (sup_le_sup hspan le_rfl) hMmem
 have hMdegree:M.natDegree ≤ m+n:=
   hMdegreeP.trans (hPcap.trans (Nat.le_add_right m n))
 have hmod:=rawPieces_modMax_surjective_of_monic_mod
   P Q m n C.pieces C.coprime C.contains M hMMonic hMmem' hMdegree
 exact grouped_resultant_power_dvd_of_primary_pieces_modMax
   primeIdeal factor multiplicity hprime hfactor hfactorMonic
     P₀ Q₀ m n P Q hPmap hQmap hPcap hQcap hresultant C hmod
end
end ProximityPrize.SubmissionLower.RCN143
end PackedLegacy_EP

/-! Packed from ProximityPrize.SubmissionLower.FN. -/
section PackedLegacy_FN
namespace ProximityPrize.SubmissionLower.RCN232
open RCN225 RCN197
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R:Type} [CommRing R] [IsLocalRing R]
def polynomialRelationBar (surface:Polynomial R)
   (relation:Ideal (Polynomial R)):Ideal (SurfaceQuotient surface):=
 Ideal.map (Ideal.Quotient.mk (Ideal.span {surface})) relation
@[implicit_reducible] noncomputable def polynomialSurfaceAtPrimeAlgebra
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   Algebra R (Localization.AtPrime (polynomialRelationBar surface relation)):=
 (((algebraMap (SurfaceQuotient surface)
     (Localization.AtPrime (polynomialRelationBar surface relation))).comp
   (Ideal.Quotient.mk (Ideal.span {surface}))).comp
     (Polynomial.C:R →+*Polynomial R)).toAlgebra' (fun _ _ => mul_comm _ _)
theorem polynomialSurfaceAtPrimeAlgebra_eq_natural
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   (inferInstance:Algebra R
     (Localization.AtPrime (polynomialRelationBar surface relation)))=
       polynomialSurfaceAtPrimeAlgebra surface relation:=by
 apply Algebra.algebra_ext
 intro r
 rfl
theorem polynomialSurfaceAtPrimeAlgebra_isLocalHom
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   letI:=polynomialSurfaceAtPrimeAlgebra surface relation
   IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let S:=SurfaceQuotient surface
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 let quotientMap:Polynomial R →+*S:=Ideal.Quotient.mk I
 letI:=polynomialSurfaceAtPrimeAlgebra surface relation
 refine ⟨fun r hrUnit => ?_⟩
 by_contra hrNonunit
 have hrMax:r∈IsLocalRing.maximalIdeal R:=
   (IsLocalRing.mem_maximalIdeal r).2 hrNonunit
 have hrRelation:Polynomial.C r∈relation:=by
   have:r∈relation.comap (Polynomial.C:R →+*Polynomial R):=
     hcontract.symm ▸ hrMax
   exact this
 have hrBar:quotientMap (Polynomial.C r)∈bar:=
   Ideal.mem_map_of_mem quotientMap hrRelation
 have hrTarget:algebraMap S L (quotientMap (Polynomial.C r))∈
     IsLocalRing.maximalIdeal L:=by
   rw [←IsLocalization.AtPrime.map_eq_maximalIdeal bar L]
   exact Ideal.mem_map_of_mem (algebraMap S L) hrBar
 have hscalar:algebraMap R L r=
     algebraMap S L (quotientMap (Polynomial.C r)):=rfl
 have:algebraMap R L r∈IsLocalRing.maximalIdeal L:=hscalar ▸ hrTarget
 exact (IsLocalRing.mem_maximalIdeal (algebraMap R L r)).mp this hrUnit
theorem polynomialSurfaceAtPrimeNatural_isLocalHom
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 let L:=Localization.AtPrime (polynomialRelationBar surface relation)
 let natural:Algebra R L:=inferInstance
 let custom:Algebra R L:=polynomialSurfaceAtPrimeAlgebra surface relation
 have halg:natural=custom:=
   polynomialSurfaceAtPrimeAlgebra_eq_natural surface relation
 have hcustom:IsLocalHom (@algebraMap R L _ _ custom):=by
   letI:Algebra R L:=custom
   exact polynomialSurfaceAtPrimeAlgebra_isLocalHom surface relation hcontract
 change IsLocalHom (@algebraMap R L _ _ natural)
 have hmap:@algebraMap R L _ _ natural=@algebraMap R L _ _ custom:=
   congrArg (fun A:Algebra R L => @algebraMap R L _ _ A) halg
 rw [hmap]
 exact hcustom
noncomputable def polynomialSurfaceResidueEquiv
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   (Polynomial R ⧸ relation) ≃+*
     IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation)):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 have hIJ:I ≤ relation:=Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsurface)
 exact (DoubleQuot.quotQuotEquivQuotOfLE hIJ).symm.trans
   (IsLocalization.AtPrime.equivQuotMaximalIdeal bar L)
theorem polynomialSurfaceResidueEquiv_compatible
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   let aRelation:=relationResidueAlgebra relation hcontract
   letI:Algebra (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation):=aRelation
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   (algebraMap (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation)))).comp
       (RingEquiv.refl (IsLocalRing.ResidueField R)).toRingHom=
     (polynomialSurfaceResidueEquiv surface relation hsurface).toRingHom.comp
       (algebraMap (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation)):=by
 let I:Ideal (Polynomial R):=Ideal.span {surface}
 let S:=SurfaceQuotient surface
 let bar:=polynomialRelationBar surface relation
 let L:=Localization.AtPrime bar
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:IsLocalHom (algebraMap R L):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 apply RingHom.ext
 intro z
 obtain ⟨r,rfl⟩:=IsLocalRing.residue_surjective z
 change algebraMap (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField L) (IsLocalRing.residue R r)=
   polynomialSurfaceResidueEquiv surface relation hsurface
     (algebraMap (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation) (IsLocalRing.residue R r))
 rw [IsLocalRing.ResidueField.algebraMap_residue]
 have hIJ:I ≤ relation:=
   Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsurface)
 let eDouble:(S ⧸ bar) ≃+*(Polynomial R ⧸ relation):=
   DoubleQuot.quotQuotEquivQuotOfLE hIJ
 let eLocal:(S ⧸ bar) ≃+*IsLocalRing.ResidueField L:=
   IsLocalization.AtPrime.equivQuotMaximalIdeal bar L
 change IsLocalRing.residue L (algebraMap R L r)=
   eLocal (eDouble.symm (Ideal.Quotient.mk relation (Polynomial.C r)))
 have hpre:eDouble.symm (Ideal.Quotient.mk relation (Polynomial.C r))=
     Ideal.Quotient.mk bar (Ideal.Quotient.mk I (Polynomial.C r)):=by
   change (DoubleQuot.quotQuotEquivQuotOfLE hIJ).symm
     (Ideal.Quotient.mk relation (Polynomial.C r))=
       DoubleQuot.quotQuotMk I relation (Polynomial.C r)
   exact DoubleQuot.quotQuotEquivQuotOfLE_symm_mk _ hIJ
 rw [hpre]
 rfl
theorem polynomialSurfaceResidue_finite
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]
   (hfinite:
     letI:=relationResidueAlgebra relation hcontract
     FiniteDimensional (IsLocalRing.ResidueField R)
       (Polynomial R ⧸ relation)):
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   FiniteDimensional (IsLocalRing.ResidueField R)
     (IsLocalRing.ResidueField
       (Localization.AtPrime (polynomialRelationBar surface relation))):=by
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:FiniteDimensional (IsLocalRing.ResidueField R)
     (Polynomial R ⧸ relation):=hfinite
 letI:IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 exact Module.Finite.of_equiv_equiv (RingEquiv.refl _)
   (polynomialSurfaceResidueEquiv surface relation hsurface)
     (polynomialSurfaceResidueEquiv_compatible
       surface relation hcontract hsurface)
theorem polynomialSurfaceResidue_finrank_eq_relation
   (surface:Polynomial R) (relation:Ideal (Polynomial R))
   (hcontract:relation.comap (Polynomial.C:R →+*Polynomial R)=
     IsLocalRing.maximalIdeal R)
   (hsurface:surface∈relation)
   [hbarMax:(polynomialRelationBar surface relation).IsMaximal]:
   letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
     relationResidueAlgebra relation hcontract
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar surface relation))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
   Module.finrank (IsLocalRing.ResidueField R)
       (IsLocalRing.ResidueField
         (Localization.AtPrime (polynomialRelationBar surface relation)))=
     Module.finrank (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=by
 letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ relation):=
   relationResidueAlgebra relation hcontract
 letI:IsLocalHom (algebraMap R
     (Localization.AtPrime (polynomialRelationBar surface relation))):=
   polynomialSurfaceAtPrimeNatural_isLocalHom surface relation hcontract
 exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
   (polynomialSurfaceResidueEquiv surface relation hsurface)
     (polynomialSurfaceResidueEquiv_compatible
       surface relation hcontract hsurface)).symm
end
end ProximityPrize.SubmissionLower.RCN232
end PackedLegacy_FN

/-! Packed from ProximityPrize.SubmissionLower.EB. -/
section PackedLegacy_EB
namespace ProximityPrize.SubmissionLower.RCN110
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN120 RCN102 RCN106 RCN107 RCN232 RCN197 RCN192 RCN111 RCN191
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hfinite in
theorem indexedNaturalSurfaceLocal_isLocalHom
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 letI:(polynomialRelationBar (indexedFiberSurface q hq surface)
     (indexedFiberRelation component lam mu nu order ht q hq a)).IsMaximal:=by
   change (indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal
   exact hbarMax
 exact polynomialSurfaceAtPrimeNatural_isLocalHom
   (indexedFiberSurface q hq surface)
   (indexedFiberRelation component lam mu nu order ht q hq a)
   (indexedFiberRelation_comap_C_eq_maximalIdeal
     component lam mu nu order ht hfinite q hq a)
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finite
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   have hrelFinite:=localizedRelationResidue_finite Omega L order e
     (ht a) (hfinite a) (hgen a)
   exact polynomialSurfaceResidue_finite P J hcontract hsurfaceJ hrelFinite
include hfinite hgen in
theorem indexedNaturalSurfaceResidue_finrank_eq_plane
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega)
   (a:IndexedFactorFiber component lam mu nu order ht q)
   (hsurface:surface∈relationKernel Omega
     (CoordinateField Omega (component a.1).1) order
     (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   [hbarMax:(indexedFiberRelationBar component lam mu nu order ht
     q hq surface a).IsMaximal]:
   letI:IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
     indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht hfinite
       q hq surface a
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
     indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=by
 cases a with
 | mk a hqeq =>
   subst q
   let L:=CoordinateField Omega (component a).1
   let e:=flagEvaluation Omega (component a).1 lam mu nu
   let R:=LocalCoefficient Omega L order e (ht a) (hfinite a)
   let P:=localizePlane Omega L order e (ht a) (hfinite a) surface
   let J:=localizedRelation Omega L order e (ht a) (hfinite a)
   have hcontract:=localizedRelation_comap_C_eq_maximalIdeal Omega L
     order e (ht a) (hfinite a)
   have hsurfaceJ:P∈J:=Ideal.mem_map_of_mem _ hsurface
   letI:(polynomialRelationBar P J).IsMaximal:=by
     change (indexedFiberRelationBar component lam mu nu order ht
       (indexedComponentFactor component lam mu nu order ht a) hq surface
         ⟨a,rfl⟩).IsMaximal
     exact hbarMax
   letI:IsLocalHom (algebraMap R
       (Localization.AtPrime (polynomialRelationBar P J))):=
     polynomialSurfaceAtPrimeNatural_isLocalHom P J hcontract
   let aRelation:=relationResidueAlgebra J hcontract
   letI:Algebra (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation
   letI:SMul (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=aRelation.toSMul
   let targetSemiring:Semiring (Polynomial R ⧸ J):=inferInstance
   letI:AddCommMonoid (Polynomial R ⧸ J):=targetSemiring.toAddCommMonoid
   letI:Module (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=Algebra.toModule
   calc
     Module.finrank (IsLocalRing.ResidueField R)
         (IsLocalRing.ResidueField (Localization.AtPrime
           (polynomialRelationBar P J)))=
       Module.finrank (IsLocalRing.ResidueField R) (Polynomial R ⧸ J):=
         polynomialSurfaceResidue_finrank_eq_relation P J hcontract hsurfaceJ
     _=indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
       simpa [indexedPlaneResidueWeight] using
         localizedRelationResidue_finrank_eq_unlocalized Omega L order e
           (ht a) (hfinite a) (hgen a)
end
end ProximityPrize.SubmissionLower.RCN110
end PackedLegacy_EB

/-! Packed from ProximityPrize.SubmissionLower.EA. -/
section PackedLegacy_EA
namespace ProximityPrize.SubmissionLower.RCN109
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN102 RCN106 RCN107 RCN143 RCN307 RCN014 RCN120 RCN236 RCN110 RCN111
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {Omega:Type} [Field Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   [hbarMax:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal]
   [hlocal:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   [hresfinite:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))]
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*Module.finrank
       (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))))∣
     Polynomial.resultant surface tail m n:=by
 letI:DecidableEq (RatFunc Omega):=Classical.decEq _
 letI:(Ideal.span {q}).IsPrime:=
   (PrincipalIdealRing.isMaximal_of_irreducible hq).isPrime
 let weight:IndexedFactorFiber component lam mu nu order ht q → ℕ:=fun a =>
   Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
     (IsLocalRing.ResidueField (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))
 let cert:=indexedWeightedFiberPrimaryPieces component hcomponent lam mu nu
   order ht hfinite hgen q hq surface tail hbarne multiplicity htail
     (hlocal:=hlocal) (hresfinite:=hresfinite)
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.Finite (FiberCoefficient q hq)
       (Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=fun a => by
   obtain ⟨M,hMmonic,hMmem⟩:=exists_monic_mem_indexedFiberRelation
     component lam mu nu order ht hfinite hgen q hq a
   apply RCN309.moduleFinite_quotient_of_monic_mem
     (cert.pieces a) (M^multiplicity a) (hMmonic.pow _)
   have hpow:M^multiplicity a∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a:=
     (show indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a ≤
         Ideal.span {indexedFiberSurface q hq surface} ⊔
           indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a
       from le_sup_right) (Ideal.pow_mem_pow hMmem (multiplicity a))
   simpa [cert,indexedWeightedFiberPrimaryPieces,
     primaryPiecesCertificateOfMembershipWeighted,mappedPrimaryPiece] using hpow
 letI:Module.Finite (FiberCoefficient q hq)
     (∀ a,Polynomial (FiberCoefficient q hq) ⧸ cert.pieces a):=inferInstance
 exact grouped_resultant_power_dvd_of_primary_pieces_of_surface_mod_ne_zero
   (Ideal.span {q}) q (fun a => multiplicity a*weight a)
     rfl hq hqMonic surface tail m n
     (indexedFiberSurface q hq surface) (indexedFiberTail q hq tail)
     rfl rfl hPcap hQcap hresultant hPbar cert
include hcomponent hfinite hgen in
theorem indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q) (hqMonic:q.Monic)
   (surface tail:PlaneRing Omega) (m n:ℕ)
   [hSurfacePrime:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime]
   (hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface∈relationKernel Omega (CoordinateField Omega (component a.1).1) order
       (flagEvaluation Omega (component a.1).1 lam mu nu) (ht a.1))
   (hbarne:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a≠⊥)
   (multiplicity:IndexedFactorFiber component lam mu nu order ht q → ℕ)
   (htail:∀ a,indexedFiberTail q hq tail∈
     Ideal.span {indexedFiberSurface q hq surface} ⊔
       indexedFiberRelation component lam mu nu order ht q hq a^multiplicity a)
   (hPcap:(indexedFiberSurface q hq surface).natDegree ≤ m)
   (hQcap:(indexedFiberTail q hq tail).natDegree ≤ n)
   (hresultant:Polynomial.resultant surface tail m n≠0)
   (hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq))≠0):
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     multiplicity a*indexedPlaneResidueWeight component lam mu nu order
       ht hfinite a.1)∣Polynomial.resultant surface tail m n:=by
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     (indexedFiberRelationBar component lam mu nu order ht q hq surface a).IsMaximal:=
   fun a => indexedFiberRelationBar_isMaximal component lam mu nu order ht
     hfinite hgen q hq surface hsurface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     IsLocalHom (algebraMap (FiberCoefficient q hq) (Localization.AtPrime
       (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceLocal_isLocalHom component lam mu nu order ht
     hfinite q hq surface a
 letI:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     FiniteDimensional (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a))):=
   fun a => indexedNaturalSurfaceResidue_finite component lam mu nu order ht
     hfinite hgen q hq surface a (hsurface a)
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd component hcomponent
   lam mu nu order ht hfinite hgen q hq hqMonic surface tail m n hbarne
     multiplicity htail hPcap hQcap hresultant hPbar
 have hweight:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     Module.finrank (IsLocalRing.ResidueField (FiberCoefficient q hq))
       (IsLocalRing.ResidueField (Localization.AtPrime
         (indexedFiberRelationBar component lam mu nu order ht q hq surface a)))=
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1:=
   fun a => indexedNaturalSurfaceResidue_finrank_eq_plane component lam mu nu
     order ht hfinite hgen q hq surface a (hsurface a)
 simpa only [hweight] using hpow
end
end ProximityPrize.SubmissionLower.RCN109
end PackedLegacy_EA

/-! Packed from ProximityPrize.SubmissionLower.M1. -/
section PackedLegacy_M1
namespace ProximityPrize.SubmissionLower.RCN195
open RCN011 RCN021 RCN022 RCN226 RCN191 RCN193
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable (K L:Type) [Field K] [Field L] [Algebra K L]
 (order:Fin 3 ≃ Fin 3)
 (e:MvPolynomial (Fin 3) K →ₐ[K] L)
 (ht:Transcendental K (e (MvPolynomial.X (order 0))))
theorem localized_surface_residue_ne_zero
   (hfinite:
     letI:Algebra (RatFunc K) L:=
       (elementEmbedding K L (e (MvPolynomial.X (order 0))) ht).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) L)
   (P₀:Polynomial (Polynomial (RatFunc K)))
   (hspecial:P₀.map
     (AdjoinRoot.mk (projectedFactor K L order e ht))≠0):
   (P₀.map (algebraMap (Polynomial (RatFunc K))
     (LocalCoefficient K L order e ht hfinite))).map
       (IsLocalRing.residue (LocalCoefficient K L order e ht hfinite))≠0:=by
 let q:=projectedFactor K L order e ht
 let Rp:=LocalCoefficient K L order e ht hfinite
 let E:=Rp ⧸ IsLocalRing.maximalIdeal Rp
 let eqv:=coefficientResidueEquiv K L order e ht hfinite
 let source:Polynomial (AdjoinRoot q):=P₀.map (AdjoinRoot.mk q)
 let target:Polynomial E:=
   (P₀.map (algebraMap (Polynomial (RatFunc K)) Rp)).map
     (IsLocalRing.residue Rp)
 have hmap:source.map eqv.toRingHom=target:=by
   apply Polynomial.ext
   intro n
   simp only [source,target,Polynomial.coeff_map,Function.comp_apply]
   exact coefficientResidueEquiv_mk K L order e ht hfinite (P₀.coeff n)
 intro hzero
 apply hspecial
 apply (Polynomial.map_injective eqv.toRingHom eqv.injective)
 have htargetZero:target=0:=hzero
 rw [hmap,htargetZero,Polynomial.map_zero]
end
end ProximityPrize.SubmissionLower.RCN195
end PackedLegacy_M1

/-! Packed from ProximityPrize.SubmissionLower.E2. -/
section PackedLegacy_E2
namespace ProximityPrize.SubmissionLower.RCN251
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN245 RCN246 RCN247 RCN249 RCN102 RCN103 RCN106 RCN107 RCN108 RCN109 RCN195 RCN120 RCN093 RCN095 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
 (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F)
theorem stageFamily_surfacePrime:
   (Ideal.span {indexedFiberSurface W.q W.irreducible
     (stageSurfacePlane S F.lam F.mu F.nu F.order)}).IsPrime:=by
 exact indexedFiberSurface_span_isPrime F.component F.lam F.mu F.nu F.order
   F.ht S.irreducible_G W.q W.irreducible W.witness
theorem stageFamily_surface_mem
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
   stageSurfacePlane S F.lam F.mu F.nu F.order∈
     relationKernel (GenericField K)
       (CoordinateField (GenericField K) (F.component a.1).1) F.order
       (flagEvaluation (GenericField K) (F.component a.1).1 F.lam F.mu F.nu)
       (F.ht a.1):=by
 exact indexedStageSurface_mem_relation S F.component F.lam F.mu F.nu
   F.order F.ht a.1
theorem stageFamily_bar_ne
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
   indexedFiberRelationBar F.component F.lam F.mu F.nu F.order F.ht
     W.q W.irreducible (stageSurfacePlane S F.lam F.mu F.nu F.order) a≠⊥:=by
 have hproperLocal:indexedFiberTail W.q W.irreducible
     (stageTailPlane S F.lam F.mu F.nu F.order)∉
     Ideal.span {indexedFiberSurface W.q W.irreducible
       (stageSurfacePlane S F.lam F.mu F.nu F.order)}:=
   indexedFiberTail_not_mem_surface F.component F.lam F.mu F.nu F.order F.ht
     S.irreducible_G hfirstProper W.q W.irreducible W.witness
 exact indexedFiberRelationBar_ne_bot F.component F.lam F.mu F.nu F.order
   F.ht W.q W.irreducible
   (stageSurfacePlane S F.lam F.mu F.nu F.order)
   (stageTailPlane S F.lam F.mu F.nu F.order)
   (fun b↦indexedStageTail_mem_relation S F.component F.lam F.mu F.nu
     F.order F.ht b.1) hproperLocal a
theorem stageFamily_tail_mem
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht W.q):
   indexedFiberTail W.q W.irreducible
     (stageTailPlane S F.lam F.mu F.nu F.order)∈
     Ideal.span {indexedFiberSurface W.q W.irreducible
       (stageSurfacePlane S F.lam F.mu F.nu F.order)} ⊔
     indexedFiberRelation F.component F.lam F.mu F.nu F.order F.ht
       W.q W.irreducible a^
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (F.component a.1):=by
 exact indexedFiberTail_mem_primary S hfirstProper F.component F.lam F.mu
   F.nu F.order F.ht F.finite F.generates W.q W.irreducible a
end
end ProximityPrize.SubmissionLower.RCN251
end PackedLegacy_E2

/-! Packed from ProximityPrize.SubmissionLower.N3. -/
section PackedLegacy_N3
namespace ProximityPrize.SubmissionLower.RCN255
open RCN135 RCN136 RCN244 RCN249 RCN245 RCN106 RCN103 RCN093 RCN095 RCN125 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
theorem planeSurface_map_adjoinRoot_ne_zero
   (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
   (surface:PlaneRing Omega) (hirr:Irreducible surface)
   (hpositive:0 < surface.natDegree):
   surface.map (AdjoinRoot.mk q)≠0:=by
 letI:Fact (Irreducible q):=⟨hq⟩
 have hcoeff:Polynomial.eval₂RingHom
     (algebraMap (RatFunc Omega) (AdjoinRoot q))
       (AdjoinRoot.root q)=AdjoinRoot.mk q:=by
   apply Polynomial.ringHom_ext
   · intro c
     simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
       AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
   · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,AdjoinRoot.mk_X]
 have hs:=RCN360.bimap_specialization_ne_zero
   (algebraMap (RatFunc Omega) (AdjoinRoot q)) surface
   (hirr.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root q)
 rw [RCN360.bimap_specialization,hcoeff] at hs
 exact hs
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
def StageFamilySurfaceSpecializationNonzero
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))):Prop:=
 (stageSurfacePlane S F.lam F.mu F.nu F.order).map (AdjoinRoot.mk q)≠0
theorem stageFamily_surface_specialization_ne
   (F:StageIndexedFlagFamily S A)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q):
   StageFamilySurfaceSpecializationNonzero S F q:=by
 change (planeMap (GenericField K) F.order
   (flagAlgHom F.lam F.mu F.nu S.G)).map (AdjoinRoot.mk q)≠0
 exact planeSurface_map_adjoinRoot_ne_zero q hq
   (planeMap (GenericField K) F.order (flagAlgHom F.lam F.mu F.nu S.G))
   (transformedSurface_irreducible F.lam F.mu F.nu F.order S.irreducible_G
     (F.component a.1) (F.ht a.1)) F.positive
end
end ProximityPrize.SubmissionLower.RCN255
end PackedLegacy_N3

/-! Packed from ProximityPrize.SubmissionLower.C4. -/
section PackedLegacy_C4
namespace ProximityPrize.SubmissionLower.RCN112
open RCN095 RCN125 RCN093 RCN123 RCN121 RCN103 RCN012 RCN011 RCN264
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega]
local instance:DecidableEq (RatFunc Omega):=Classical.decEq _
variable {G T H:MvPolynomial (Fin 3) Omega}
def flagPlaneResultant (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (G T:MvPolynomial (Fin 3) Omega):Polynomial (RatFunc Omega):=
 let P:=planeMap Omega order (flagAlgHom lam mu nu G)
 let Q:=planeMap Omega order (flagAlgHom lam mu nu T)
 Polynomial.resultant P Q P.natDegree Q.natDegree
theorem flagPlaneResultant_ne
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (hG:Irreducible G) (hproper:¬ G∣T)
   (C:RegularComponent Omega G T H)
   (ht:Transcendental Omega
     (flagEvaluation Omega C.1 lam mu nu (MvPolynomial.X (order 0))))
   (hpositive:0 < (planeMap Omega order (flagAlgHom lam mu nu G)).natDegree):
   flagPlaneResultant lam mu nu order G T≠0:=by
 exact RCN362.irreducible_resultant_ne_zero_of_not_dvd
   (planeMap Omega order (flagAlgHom lam mu nu G))
   (planeMap Omega order (flagAlgHom lam mu nu T))
   (transformedSurface_irreducible lam mu nu order hG C ht) hpositive
   (transformedSurface_not_dvd_tail lam mu nu order hG hproper C ht)
theorem flagPlaneResultant_z_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu zOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitZFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega zOrder (flagAlgHom lam mu nu G))
   (planeMap Omega zOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega zOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   surfaceFlag.all tailFlag.all (surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.yz+tailFlag.all) (flagMixed surfaceFlag tailFlag unitZFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.zOuter tCaps.zOuter
   gCaps.zTotal tCaps.zTotal (z_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_u_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu uOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitYZFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega uOrder (flagAlgHom lam mu nu G))
   (planeMap Omega uOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega uOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   surfaceFlag.all tailFlag.all
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitYZFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.uOuter tCaps.uOuter
   gCaps.uTotal tCaps.uTotal (u_flag_trapezoid_budget surfaceFlag tailFlag)
theorem flagPlaneResultant_v_degree_le
   (surfaceFlag tailFlag:FlagDegree) (lam mu nu:Omega)
   (hGsupport:G.support ⊆ flagSupport surfaceFlag)
   (hTsupport:T.support ⊆ flagSupport tailFlag) (hTne:T≠0):
   (flagPlaneResultant lam mu nu vOrder G T).natDegree ≤
     flagMixed surfaceFlag tailFlag unitAllFlag:=by
 let gCaps:=flagTrapezoidCaps_flagAlgHom surfaceFlag G lam mu nu hGsupport
 let tCaps:=flagTrapezoidCaps_flagAlgHom tailFlag T lam mu nu hTsupport
 change (Polynomial.resultant
   (planeMap Omega vOrder (flagAlgHom lam mu nu G))
   (planeMap Omega vOrder (flagAlgHom lam mu nu T))).natDegree ≤ _
 exact planeMap_trapezoid_resultant_natDegree_le Omega vOrder
   (flagAlgHom lam mu nu G) (flagAlgHom lam mu nu T)
   (surfaceFlag.yz+surfaceFlag.all) (tailFlag.yz+tailFlag.all)
   (surfaceFlag.zOnly+surfaceFlag.yz+surfaceFlag.all)
   (tailFlag.zOnly+tailFlag.yz+tailFlag.all)
   (flagMixed surfaceFlag tailFlag unitAllFlag)
   (flag_ne_zero lam mu nu hTne) gCaps.vOuter tCaps.vOuter
   gCaps.vTotal tCaps.vTotal (v_flag_trapezoid_budget surfaceFlag tailFlag)
end
end ProximityPrize.SubmissionLower.RCN112
end PackedLegacy_C4

/-! Packed from ProximityPrize.SubmissionLower.N2. -/
section PackedLegacy_N2
namespace ProximityPrize.SubmissionLower.RCN254
open RCN135 RCN136 RCN086 RCN244 RCN245 RCN249 RCN112 RCN103 RCN113 RCN093 RCN095 RCN011
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_resultant_ne
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   stageFamilyResultant S A F≠0:=by
 change flagPlaneResultant F.lam F.mu F.nu F.order S.G
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))≠0
 exact flagPlaneResultant_ne F.lam F.mu F.nu F.order S.irreducible_G hfirstProper
   (F.component W.witness.1) (F.ht W.witness.1) F.positive
end
end ProximityPrize.SubmissionLower.RCN254
end PackedLegacy_N2

/-! Packed from ProximityPrize.SubmissionLower.FZ. -/
section PackedLegacy_FZ
namespace ProximityPrize.SubmissionLower.RCN250
open scoped Classical BigOperators
open RCN135 RCN086 RCN244 RCN245 RCN249 RCN251 RCN254 RCN102 RCN106 RCN107 RCN109 RCN120 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
def StageFamilySurfaceModNonzero
   (S:Stage K I Gamma x p flag errorCap stageSupport) (F:StageIndexedFlagFamily S A)
   (W:StageIndexedFactor S A F):Prop:=
 (indexedFiberSurface W.q W.irreducible
   (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
     (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0
@[simp] theorem stageFamilySurfaceModNonzero_eq
   (S:Stage K I Gamma x p flag errorCap stageSupport) (F:StageIndexedFlagFamily S A)
   (W:StageIndexedFactor S A F):
   StageFamilySurfaceModNonzero S F W ↔
     (indexedFiberSurface W.q W.irreducible
       (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
         (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0:=Iff.rfl
theorem properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F)
   (hPbar:StageFamilySurfaceModNonzero S F W):
   W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
     stageFamilyResultant S A F:=by
 let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
 let tail:=stageTailPlane S F.lam F.mu F.nu F.order
 letI:(Ideal.span {indexedFiberSurface W.q W.irreducible surface}).IsPrime:=
   stageFamily_surfacePrime S F W
 have hpower:=indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   F.component F.injective F.lam F.mu F.nu F.order F.ht F.finite F.generates
     W.q W.irreducible W.monic surface tail surface.natDegree tail.natDegree
     (fun a => stageFamily_surface_mem S F W a)
     (fun a => stageFamily_bar_ne S F W hfirstProper a)
     (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
       (F.component a.1))
     (fun a => stageFamily_tail_mem S F W hfirstProper a)
     Polynomial.natDegree_map_le Polynomial.natDegree_map_le
     (stageFamily_resultant_ne S hfirstProper F W) hPbar
 simpa only [stageFamilyGroupedExponent_eq,stageFamilyResultant] using hpower
end
end ProximityPrize.SubmissionLower.RCN250
end PackedLegacy_FZ

/-! Packed from ProximityPrize.SubmissionLower.N0. -/
section PackedLegacy_N0
namespace ProximityPrize.SubmissionLower.RCN252
open RCN135 RCN136 RCN074 RCN244 RCN249 RCN245 RCN106 RCN107 RCN108 RCN103 RCN102 RCN195 RCN255 RCN250 RCN093 RCN095 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_surface_mod_ne
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   StageFamilySurfaceModNonzero S F W:=by
 rcases W with ⟨q,hq,_hqMonic,⟨a,hqeq⟩⟩
 let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
 have hspecial:=stageFamily_surface_specialization_ne S F q hq
   (⟨a,hqeq⟩:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q)
 change surface.map (AdjoinRoot.mk q)≠0 at hspecial
 change (indexedFiberSurface q hq surface).map
   (IsLocalRing.residue (FiberCoefficient q hq))≠0
 subst q
 exact localized_surface_residue_ne_zero (GenericField K)
   (CoordinateField (GenericField K) (F.component a).1) F.order
   (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu) (F.ht a)
   (F.finite a) surface hspecial
end
end ProximityPrize.SubmissionLower.RCN252
end PackedLegacy_N0

/-! Packed from ProximityPrize.SubmissionLower.N1. -/
section PackedLegacy_N1
namespace ProximityPrize.SubmissionLower.RCN253
open RCN135 RCN086 RCN244 RCN249 RCN250 RCN252 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem properStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
     stageFamilyResultant S A F:=
 properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod S hfirstProper F W
   (stageFamily_surface_mod_ne S F W)
end
end ProximityPrize.SubmissionLower.RCN253
end PackedLegacy_N1

/-! Packed from ProximityPrize.SubmissionLower.Q0. -/
section PackedLegacy_Q0
namespace ProximityPrize.SubmissionLower.RCN333
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN249 RCN251 RCN252 RCN255 RCN250 RCN247 RCN245 RCN106 RCN107 RCN108 RCN102 RCN103 RCN109 RCN112 RCN113 RCN264 RCN120 RCN243 RCN111 RCN093 RCN095 RCN125 RCN066 RCN336 RCN226 RCN002 RCN011 RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 80000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem finiteDimensional_coordinateField_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hfinite:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega P)) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   FiniteDimensional (RatFunc Omega) (CoordinateField Omega Q):=by
 subst Q
 exact hfinite
theorem flagGenerators_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0))))
   (hgen:letI:=flagBaseAlgebra Omega P lam mu nu order htP
     IntermediateField.adjoin (RatFunc Omega)
       ({flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 2)),
         flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 1))} :
         Set (CoordinateField Omega P)) = ⊤) :
   letI:=flagBaseAlgebra Omega Q lam mu nu order htQ
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 2)),
       flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 1))} :
       Set (CoordinateField Omega Q)) = ⊤:=by
 subst Q
 exact hgen
theorem indexedComponentFactor_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   projectedFactor Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   projectedFactor Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem relationKernel_congr
   {Omega:Type} [Field Omega]
   {P Q:Ideal (MvPolynomial (Fin 3) Omega)} [P.IsPrime] [Q.IsPrime]
   (hPQ:P = Q) (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (htP:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   (htQ:Transcendental Omega
     (flagEvaluation Omega Q lam mu nu (MvPolynomial.X (order 0)))) :
   relationKernel Omega (CoordinateField Omega P) order
     (flagEvaluation Omega P lam mu nu) htP =
   relationKernel Omega (CoordinateField Omega Q) order
     (flagEvaluation Omega Q lam mu nu) htQ:=by
 subst Q
 rfl
theorem flagPlaneMap_mem_relation
   {Omega:Type} [Field Omega]
   (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
   (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental Omega
     (flagEvaluation Omega P lam mu nu (MvPolynomial.X (order 0))))
   {A:MvPolynomial (Fin 3) Omega} (hA:A ∈ P) :
   flagPlaneMap Omega lam mu nu order A ∈
     relationKernel Omega (CoordinateField Omega P) order
       (flagEvaluation Omega P lam mu nu) ht:=by
 change planeEvaluation Omega (CoordinateField Omega P) order
   (flagEvaluation Omega P lam mu nu) ht
     (planeMap Omega order (flagAlgHom lam mu nu A)) = 0
 rw [← RingHom.comp_apply,planeEvaluation_comp_planeMap]
 change flagEvaluation Omega P lam mu nu (flagAlgHom lam mu nu A) = 0
 rw [flagEvaluation_flag]
 change A ∈ RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rw [coordinateEvaluation_ker]
 exact hA
theorem ideal_mem_right_of_sub_mem
   {R:Type} [CommRing R] (P:Ideal R) {A B:R}
   (hA:A ∈ P) (hAB:A - B ∈ P):B ∈ P:=by
 have h:=P.sub_mem hA hAB
 simpa only [sub_sub_cancel] using h
@[simp] theorem flagPlaneMap_apply
   {Omega:Type} [Field Omega] (lam mu nu:Omega)
   (order:Fin 3 ≃ Fin 3) (A:MvPolynomial (Fin 3) Omega) :
   flagPlaneMap Omega lam mu nu order A =
     planeMap Omega order (flagAlgHom lam mu nu A):=rfl
theorem reducedStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1) - Tred)
   {A:Type} [Fintype A]
   (component:A → RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F))
   (hcomponent:Function.Injective component)
   (lam mu nu:GenericField K) (order:Fin 3 ≃ Fin 3)
   (ht:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (component a).1 lam mu nu
       (MvPolynomial.X (order 0))))
   (hfinite:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (component a).1))
   (hgen:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (component a).1
       lam mu nu order (ht a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (component a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (component a).1)) = ⊤)
   (positive:0 < (stageSurfacePlane S lam mu nu order).natDegree)
   (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
   (hqMonic:q.Monic)
   (a0:IndexedFactorFiber component lam mu nu order ht q) :
   q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
     transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1) *
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a.1) ∣
     flagPlaneResultant lam mu nu order S.G Tred:=by
 let e:=regularComponentEquiv
   (H:=regularitySurface (polynomialEmbedding K) S.F) hd
 let oldComponent:A → StageComponent S:=fun a => e.symm (component a)
 have oldComponent_val (a:A):(oldComponent a).1 = (component a).1 :=
   regularComponentEquiv_symm_val hd (component a)
 have holdInjective:Function.Injective oldComponent :=
   e.symm.injective.comp hcomponent
 have htold:∀ a,Transcendental (GenericField K)
     (flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
       (MvPolynomial.X (order 0))):=by
   intro a
   rw [oldComponent_val a]
   exact ht a
 have hfiniteold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     FiniteDimensional (RatFunc (GenericField K))
       (CoordinateField (GenericField K) (oldComponent a).1):=by
   intro a
   exact finiteDimensional_coordinateField_congr
     (oldComponent_val a).symm lam mu nu order (ht a) (htold a) (hfinite a)
 have hgenold:∀ a,
     letI:=flagBaseAlgebra (GenericField K) (oldComponent a).1
       lam mu nu order (htold a)
     IntermediateField.adjoin (RatFunc (GenericField K))
       ({flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 2)),
         flagEvaluation (GenericField K) (oldComponent a).1 lam mu nu
           (MvPolynomial.X (order 1))} :
         Set (CoordinateField (GenericField K) (oldComponent a).1)) = ⊤:=by
   intro a
   exact flagGenerators_congr (oldComponent_val a).symm lam mu nu order
     (ht a) (htold a) (hgen a)
 let surface:=stageSurfacePlane S lam mu nu order
 let oldTail:=stageTailPlane S lam mu nu order
 let redTail:=flagPlaneMap (GenericField K) lam mu nu order Tred
 letI:(Ideal.span {indexedFiberSurface q hq surface}).IsPrime:=by
   exact indexedFiberSurface_span_isPrime component lam mu nu order ht
     S.irreducible_G q hq a0
 have hsurface:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     surface ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   change flagPlaneMap (GenericField K) lam mu nu order S.G ∈ _
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_G_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperRed:¬ S.G ∣ Tred:=by
   intro hr
   apply hfirstProper
   have hsum:=hd.add hr
   simpa only [sub_add_cancel] using hsum
 have hredTailRoot:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     redTail ∈ relationKernel (GenericField K)
       (CoordinateField (GenericField K) (component a.1).1) order
       (flagEvaluation (GenericField K) (component a.1).1 lam mu nu) (ht a.1):=by
   intro a
   exact flagPlaneMap_mem_relation (component a.1).1 lam mu nu order (ht a.1)
     (regularComponent_T_mem (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) (component a.1))
 have hproperLocal:indexedFiberTail q hq redTail ∉
     Ideal.span {indexedFiberSurface q hq surface}:=by
   exact indexedFiberTail_not_mem_surface component lam mu nu order ht
     S.irreducible_G hproperRed q hq a0
 have hbar:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberRelationBar component lam mu nu order ht q hq surface a ≠ ⊥:=by
   intro a
   exact indexedFiberRelationBar_ne_bot component lam mu nu order ht q hq
     surface redTail hredTailRoot hproperLocal a
 have hplaneDvd:surface ∣ oldTail-redTail:=by
   simpa only [surface,oldTail,redTail,stageSurfacePlane,stageTailPlane,
     map_sub] using map_dvd (flagPlaneMap (GenericField K) lam mu nu order) hd
 have htail:∀ a:IndexedFactorFiber component lam mu nu order ht q,
     indexedFiberTail q hq redTail ∈
       Ideal.span {indexedFiberSurface q hq surface} ⊔
         indexedFiberRelation component lam mu nu order ht q hq a ^
           transportedMultiplicity hd
             (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
             (component a.1):=by
   intro a
   let Q:=Ideal.span {indexedFiberSurface q hq surface} ⊔
     indexedFiberRelation component lam mu nu order ht q hq a ^
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1)
   have hfactorOld:q =
       indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a.1:=a.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a.1).symm
           lam mu nu order (ht a.1) (htold a.1)
   let aold:IndexedFactorFiber oldComponent lam mu nu order htold q :=
     ⟨a.1,hfactorOld⟩
   have hold:=indexedFiberTail_mem_primary S hfirstProper oldComponent
     lam mu nu order htold hfiniteold hgenold q hq aold
   have aold_val:aold.1 = a.1:=rfl
   have hcomponentVal:(oldComponent aold.1).1 = (component a.1).1:=by
     rw [aold_val,oldComponent_val]
   have hrel:indexedFiberRelation oldComponent lam mu nu order htold q hq aold =
       indexedFiberRelation component lam mu nu order ht q hq a:=by
     unfold indexedFiberRelation
     exact congrArg (Ideal.map (fiberLocalizePlane q hq))
       (relationKernel_congr hcomponentVal lam mu nu order
         (htold aold.1) (ht a.1))
   have hmult:localMultiplicity S
       (canonicalLocalDVRFamily S hfirstProper) (oldComponent aold.1) =
       transportedMultiplicity hd
         (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
         (component a.1):=by
     change localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component aold.1)) =
       localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
         (e.symm (component a.1))
     rw [aold_val]
   rw [hrel,hmult] at hold
   have holdQ:indexedFiberTail q hq oldTail ∈ Q:=by
     simpa only [oldTail,surface,Q] using hold
   have hfiberDvd:indexedFiberSurface q hq surface ∣
       indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail:=by
     simpa only [indexedFiberSurface,indexedFiberTail,map_sub] using
       map_dvd (fiberLocalizePlane q hq) hplaneDvd
   have hdiff:indexedFiberTail q hq oldTail-indexedFiberTail q hq redTail ∈ Q :=
     (show Ideal.span {indexedFiberSurface q hq surface} ≤ Q from le_sup_left)
       (Ideal.mem_span_singleton.mpr hfiberDvd)
   exact ideal_mem_right_of_sub_mem Q
     (A:=indexedFiberTail q hq oldTail)
     (B:=indexedFiberTail q hq redTail) holdQ hdiff
 have hresultant0:=flagPlaneResultant_ne lam mu nu order
   S.irreducible_G hproperRed (component a0.1) (ht a0.1) positive
 have hresultant:Polynomial.resultant surface redTail surface.natDegree
     redTail.natDegree ≠ 0:=by
   simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
     flagPlaneMap_apply] using hresultant0
 have hPbar:(indexedFiberSurface q hq surface).map
     (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0:=by
   have hfactorA0old:q =
       indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
     calc
       q = indexedComponentFactor component lam mu nu order ht a0.1:=a0.2
       _ = indexedComponentFactor oldComponent lam mu nu order htold a0.1:=by
         exact indexedComponentFactor_congr (oldComponent_val a0.1).symm
           lam mu nu order (ht a0.1) (htold a0.1)
   let F:StageIndexedFlagFamily S A:={
     component:=oldComponent
     injective:=holdInjective
     lam:=lam
     mu:=mu
     nu:=nu
     order:=order
     ht:=htold
     finite:=hfiniteold
     generates:=hgenold
     positive:=positive }
   let a0old:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q :=
     ⟨a0.1,hfactorA0old⟩
   let W:StageIndexedFactor S A F :=
     { q:=q, irreducible:=hq, monic:=hqMonic, witness:=a0old }
   have hPbar0:=stageFamily_surface_mod_ne S F W
   change (indexedFiberSurface q hq
     (stageSurfacePlane S lam mu nu order)).map
       (IsLocalRing.residue (FiberCoefficient q hq)) ≠ 0 at hPbar0
   simpa only [surface] using hPbar0
 have hpow:=indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
   component hcomponent lam mu nu order ht hfinite hgen q hq hqMonic
   surface redTail surface.natDegree redTail.natDegree hsurface hbar
   (fun a => transportedMultiplicity hd
     (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))
     (component a.1)) htail Polynomial.natDegree_map_le
       Polynomial.natDegree_map_le hresultant hPbar
 simpa only [flagPlaneResultant,surface,redTail,stageSurfacePlane,
   flagPlaneMap_apply] using hpow
end
end ProximityPrize.SubmissionLower.RCN333
end PackedLegacy_Q0

/-! Packed from ProximityPrize.SubmissionLower.A1. -/
section PackedLegacy_A1
namespace ProximityPrize.SubmissionLower.RCN031
open RCN002 RCN264 RCN341 RCN037 RCN038 RCN093 RCN125 RCN116 RCN120 RCN021 RCN022
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
abbrev ActiveNestedZIndex:={C:RegularComponent Omega G T H//
 Transcendental Omega (coordinate Omega C.1 2)}
def activeNestedZComponent:ActiveNestedZIndex (G:=G) (T:=T) (H:=H) →
   RegularComponent Omega G T H:=Subtype.val
theorem activeNestedZComponent_injective:Function.Injective
   (activeNestedZComponent (G:=G) (T:=T) (H:=H)):=
 Subtype.val_injective
def activeNestedZTranscendental
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0))):=by
 simpa [zOrder,Equiv.swap_apply_def] using a.2
def activeNestedUTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0))):=by
 simpa [uOrder] using D.uTranscendental C
def activeNestedVTranscendental (C:RegularComponent Omega G T H):
   Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0))):=by
 simpa [vOrder,Equiv.swap_apply_def] using D.allAffineTranscendental C
include hZ in
theorem activeNestedZGate
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H))
   (hx:Transcendental Omega
     (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (zOrder 0)))):
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam) zOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1)):=by
 have hx':Transcendental Omega (coordinate Omega a.1.1 2):=by
   simpa [zOrder,Equiv.swap_apply_def] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega a.1.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega a.1.1))
 rw [hemb]
 exact hZ a.1 hx'
theorem activeNestedUGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (uOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) uOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hx':Transcendental Omega (affineU Omega C.1 D.lam):=by
   simpa [uOrder] using hx
 have hemb:=elementEmbedding_congr hx hx' (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact D.uGate C hx'
theorem activeNestedVGate (C:RegularComponent Omega G T H)
   (hx:Transcendental Omega
     (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
       (MvPolynomial.X (vOrder 0)))):
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam) vOrder hx
    Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1)):=by
 have hemb:=elementEmbedding_congr hx (D.allAffineTranscendental C)
   (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     FiniteDimensional (RatFunc Omega) (CoordinateField Omega C.1))∧
   (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1) _ hx).toRingHom.toAlgebra;
     Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega C.1))
 rw [hemb]
 exact ⟨D.allFinite C,D.allSeparable C⟩
def activeNestedZFinite (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):=
 (activeNestedZGate base hactive hZ hSderiv D a
   (activeNestedZTranscendental base hactive hSderiv D a)).1
def activeNestedUFinite (C:RegularComponent Omega G T H):=
 (activeNestedUGate base hactive hSderiv D C
   (activeNestedUTranscendental base hactive hSderiv D C)).1
def activeNestedVFinite (C:RegularComponent Omega G T H):=
 (activeNestedVGate base hactive hSderiv D C
   (activeNestedVTranscendental base hactive hSderiv D C)).1
theorem activeNestedZGenerates
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   letI:=flagBaseAlgebra Omega a.1.1 D.lam D.mu (D.mu*D.lam)
     zOrder (activeNestedZTranscendental base hactive hSderiv D a)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (zOrder 1))}:
       Set (CoordinateField Omega a.1.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedZTranscendental base hactive hSderiv D a) a.2
   (by simp [zOrder,flagEvaluation_X_two])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega a.1.1):=
     (elementEmbedding Omega (CoordinateField Omega a.1.1)
       (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 0)))
       (activeNestedZTranscendental base hactive hSderiv D a)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 2)),
       flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (zOrder 1))}:Set (CoordinateField Omega a.1.1))=⊤)
 rw [hemb]
 simpa [zOrder,Equiv.swap_apply_def] using flag_generators_z Omega a.1.1 D.lam D.mu
   (D.mu*D.lam) a.2
theorem activeNestedUGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     uOrder (activeNestedUTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (uOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedUTranscendental base hactive hSderiv D C)
   (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 0)))
       (activeNestedUTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (uOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [uOrder] using flag_generators_u Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.uTranscendental C)
theorem activeNestedVGenerates (C:RegularComponent Omega G T H):
   letI:=flagBaseAlgebra Omega C.1 D.lam D.mu (D.mu*D.lam)
     vOrder (activeNestedVTranscendental base hactive hSderiv D C)
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (vOrder 1))}:
       Set (CoordinateField Omega C.1))=⊤:=by
 have hemb:=elementEmbedding_congr
   (activeNestedVTranscendental base hactive hSderiv D C)
   (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 0)))
       (activeNestedVTranscendental base hactive hSderiv D C)).toRingHom.toAlgebra;
   IntermediateField.adjoin (RatFunc Omega)
     ({flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 2)),
       flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
         (MvPolynomial.X (vOrder 1))}:Set (CoordinateField Omega C.1))=⊤)
 rw [hemb]
 simpa [vOrder,Equiv.swap_apply_def] using flag_generators_v Omega C.1 D.lam D.mu
   (D.mu*D.lam) (D.allAffineTranscendental C)
end
end ProximityPrize.SubmissionLower.RCN031
end PackedLegacy_A1

/-! Packed from ProximityPrize.SubmissionLower.A0. -/
section PackedLegacy_A0
namespace ProximityPrize.SubmissionLower.RCN029
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN125 RCN031 RCN106 RCN111 RCN112
noncomputable section
set_option autoImplicit false
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (multiplicity:RegularComponent Omega G T H → ℕ)
def ActiveNestedZFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (a₀:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q),
   q^(∑ a:IndexedFactorFiber
     (activeNestedZComponent (G:=G) (T:=T) (H:=H))
     D.lam D.mu (D.mu*D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D) q,
     multiplicity a.1.1*indexedPlaneResidueWeight
       (activeNestedZComponent (G:=G) (T:=T) (H:=H))
       D.lam D.mu (D.mu*D.lam) zOrder
       (activeNestedZTranscendental base hactive hSderiv D)
       (activeNestedZFinite base hactive hZ hSderiv D) a.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T
def ActiveNestedUFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) uOrder
       (activeNestedUTranscendental base hactive hSderiv D)
       (activeNestedUFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T
def ActiveNestedVFixedPowers:Prop:=
 ∀ q (hq:Irreducible q) (hm:q.Monic)
   (C₀:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q),
   q^(∑ C:IndexedFactorFiber (fun C:RegularComponent Omega G T H↦C)
     D.lam D.mu (D.mu*D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D) q,
     multiplicity C.1*indexedPlaneResidueWeight
       (fun C:RegularComponent Omega G T H↦C)
       D.lam D.mu (D.mu*D.lam) vOrder
       (activeNestedVTranscendental base hactive hSderiv D)
       (activeNestedVFinite base hactive hSderiv D) C.1)∣
     flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T
structure ActiveNestedFixedPowers:Prop where
 z:ActiveNestedZFixedPowers base hactive hZ hSderiv D multiplicity
 u:ActiveNestedUFixedPowers base hactive hSderiv D multiplicity
 v:ActiveNestedVFixedPowers base hactive hSderiv D multiplicity
end
end ProximityPrize.SubmissionLower.RCN029
end PackedLegacy_A0

/-! Packed from ProximityPrize.SubmissionLower.P8. -/
section PackedLegacy_P8
namespace ProximityPrize.SubmissionLower.RCN331
open scoped Classical BigOperators
open RCN135 RCN136 RCN086 RCN244 RCN074 RCN243 RCN264 RCN095 RCN066 RCN336 RCN333 RCN029 RCN031 RCN037 RCN038 RCN341 RCN117 RCN125 RCN002
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
theorem reducedStage_activeFixedPowers
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1))
   (Tred:MvPolynomial (Fin 3) (GenericField K))
   (hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w + 1) - Tred)
   (base:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     SeparableLiteralCoordinate C.1)
   (hactive:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 0) ≠ 0 ∨
       KaehlerDifferential.D (GenericField K)
         (CoordinateField (GenericField K) C.1)
         (coordinate (GenericField K) C.1 2) ≠ 0)
   (hZ:∀ C:RegularComponent (GenericField K) S.G Tred
     (regularitySurface (polynomialEmbedding K) S.F),
     LiteralProjectionGate C 2)
   (hSderiv:MvPolynomial.pderiv (1:Fin 3) S.G ≠ 0)
   (D:AdaptiveNestedProjectionDataActive base hactive hSderiv) :
   ActiveNestedFixedPowers base hactive hZ hSderiv D
     (transportedMultiplicity hd
       (localMultiplicity S (canonicalLocalDVRFamily S hfirstProper))):=by
 refine { z:=?_, u:=?_, v:=?_ }
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (activeNestedZComponent (G:=S.G) (T:=Tred)
       (H:=regularitySurface (polynomialEmbedding K) S.F))
     activeNestedZComponent_injective D.lam D.mu (D.mu * D.lam) zOrder
     (activeNestedZTranscendental base hactive hSderiv D)
     (activeNestedZFinite base hactive hZ hSderiv D)
     (activeNestedZGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).2
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) uOrder
     (activeNestedUTranscendental base hactive hSderiv D)
     (activeNestedUFinite base hactive hSderiv D)
     (activeNestedUGenerates base hactive hSderiv D)
     (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hSderiv).1
     q hq hqMonic a0
 · intro q hq hqMonic a0
   exact reducedStage_indexedFixedFactor_groupedPowerDvd S hfirstProper Tred hd
     (fun C:RegularComponent (GenericField K) S.G Tred
       (regularitySurface (polynomialEmbedding K) S.F) => C)
     Function.injective_id D.lam D.mu (D.mu * D.lam) vOrder
     (activeNestedVTranscendental base hactive hSderiv D)
     (activeNestedVFinite base hactive hSderiv D)
     (activeNestedVGenerates base hactive hSderiv D)
     (flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional)
     q hq hqMonic a0
end
end ProximityPrize.SubmissionLower.RCN331
end PackedLegacy_P8

/-! Packed from ProximityPrize.SubmissionLower.DJ. -/
section PackedLegacy_DJ
namespace ProximityPrize.SubmissionLower.RCN030
open RCN002 RCN264 RCN341 RCN042 RCN344 RCN037 RCN038 RCN040 RCN046 RCN237 RCN095 RCN093 RCN125 RCN116 RCN022 RCN031
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
noncomputable def activeNestedUnitFamily:
   AdaptiveUnitProjectionFamily base surfaceFlag tailFlag:=
 adaptiveUnitProjectionFamily_of_active_nested surfaceFlag tailFlag base hactive
   hZ hSderiv D hG hproper hGsupport hTsupport
theorem activeNestedUnitFamily_zCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=rfl
theorem activeNestedUnitFamily_uCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate (affineU Omega C.1 D.lam) (D.uGate C)):=rfl
theorem activeNestedUnitFamily_allCost (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (Sum.inr {
         embedding:=elementEmbedding Omega (CoordinateField Omega C.1)
           (affineV Omega C.1 D.mu (D.mu*D.lam))
             (D.allAffineTranscendental C)
         finite:=D.allFinite C
         separable:=D.allSeparable C}):=rfl
theorem activeNestedUnitFamily_zCost_eq_flagCost
   (a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.zCost a.1=
     coordinateDegree Omega (CoordinateField Omega a.1.1)
       (coordinateOfGate
         (flagEvaluation Omega a.1.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (zOrder 0)))
         (activeNestedZGate base hactive hZ hSderiv D a)):=by
 rw [activeNestedUnitFamily_zCost]
 rw [coordinateOfGate_degree_of_transcendental _ _ a.2]
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedZTranscendental base hactive hSderiv D a)]
 rw [elementEmbedding_congr
   (activeNestedZTranscendental base hactive hSderiv D a) a.2
   (by simp [zOrder,flagEvaluation_X_two])]
theorem activeNestedUnitFamily_uCost_eq_flagCost
   (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.yzCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate
         (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (uOrder 0)))
         (activeNestedUGate base hactive hSderiv D C)):=by
 rw [activeNestedUnitFamily_uCost]
 rw [coordinateOfGate_degree_of_transcendental _ _ (D.uTranscendental C)]
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedUTranscendental base hactive hSderiv D C)]
 rw [elementEmbedding_congr
   (activeNestedUTranscendental base hactive hSderiv D C)
   (D.uTranscendental C) (by simp [uOrder,flagEvaluation_X_zero])]
theorem activeNestedUnitFamily_allCost_eq_flagCost
   (C:RegularComponent Omega G T H):
   (activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport).toPrimeFlagBudgetFamily.allCost C=
     coordinateDegree Omega (CoordinateField Omega C.1)
       (coordinateOfGate
         (flagEvaluation Omega C.1 D.lam D.mu (D.mu*D.lam)
           (MvPolynomial.X (vOrder 0)))
         (activeNestedVGate base hactive hSderiv D C)):=by
 rw [activeNestedUnitFamily_allCost]
 change (letI:Algebra (RatFunc Omega) (CoordinateField Omega C.1):=
     (elementEmbedding Omega (CoordinateField Omega C.1)
       (affineV Omega C.1 D.mu (D.mu*D.lam))
         (D.allAffineTranscendental C)).toRingHom.toAlgebra;
   Module.finrank (RatFunc Omega) (CoordinateField Omega C.1))=_
 rw [coordinateOfGate_degree_of_transcendental _ _
   (activeNestedVTranscendental base hactive hSderiv D C)]
 rw [elementEmbedding_congr
   (activeNestedVTranscendental base hactive hSderiv D C)
   (D.allAffineTranscendental C) (by simp [vOrder,flagEvaluation_X_one])]
end
end ProximityPrize.SubmissionLower.RCN030
end PackedLegacy_DJ

/-! Packed from ProximityPrize.SubmissionLower.K2. -/
section PackedLegacy_K2
namespace ProximityPrize.SubmissionLower.RCN105
open RCN002 RCN011 RCN264 RCN093 RCN120 RCN042 RCN344 RCN106 RCN111 RCN226 RCN113 RCN021 RCN014
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type}
 (component:A → RegularComponent Omega G T H)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
theorem indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (a:A):
   coordinateDegree Omega (CoordinateField Omega (component a).1)
     (coordinateOfGate
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0)))
       (hgate a))=
     (indexedComponentFactor component lam mu nu order ht a).natDegree*
       indexedPlaneResidueWeight component lam mu nu order ht hfinite a:=by
 rw [coordinateOfGate_degree_of_transcendental _ (hgate a) (ht a)]
 let F:=RatFunc Omega
 let L:=CoordinateField Omega (component a).1
 let e:=flagEvaluation Omega (component a).1 lam mu nu
 let q:=projectedFactor Omega L order e (ht a)
 let J:=relationKernel Omega L order e (ht a)
 letI:Algebra F L:=flagBaseAlgebra Omega (component a).1
   lam mu nu order (ht a)
 letI:FiniteDimensional F L:=hfinite a
 letI:J.IsMaximal:=relationKernel_isMaximal Omega L order e (ht a)
   (hfinite a) (hgen a)
 let aResidue:=residueAlgebra q J
   (relationKernel_comap_C Omega L order e (ht a))
 letI:Algebra (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue
 letI:SMul (AdjoinRoot q) (PlaneRing Omega ⧸ J):=aResidue.toSMul
 let targetSemiring:Semiring (PlaneRing Omega ⧸ J):=inferInstance
 letI:AddCommMonoid (PlaneRing Omega ⧸ J):=targetSemiring.toAddCommMonoid
 letI:Module (AdjoinRoot q) (PlaneRing Omega ⧸ J):=Algebra.toModule
 have hq:Irreducible q:=projectedFactor_irreducible Omega L order e
   (ht a) (hfinite a)
 let phi:PlaneRing Omega →ₐ[F] L:={
   toRingHom:=planeEvaluation Omega L order e (ht a)
   commutes':=fun c => by
     change planeEvaluation Omega L order e (ht a)
       (Polynomial.C (Polynomial.C c))=algebraMap F L c
     rw [planeEvaluation_C_C]
     rfl}
 have hsurj:Function.Surjective phi:=by
   change Function.Surjective
     (RCN361.planeEval F L
       (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))))
   exact planeEvaluation_surjective_of_finite_generatingPair
     (e (MvPolynomial.X (order 2))) (e (MvPolynomial.X (order 1))) (hgen a)
 let eqv:(PlaneRing Omega ⧸ J) ≃ₐ[F] L:=by
   change (PlaneRing Omega ⧸ RingHom.ker phi) ≃ₐ[F] L
   exact Ideal.quotientKerAlgEquivOfSurjective hsurj
 have hquot:Module.finrank F (PlaneRing Omega ⧸ J)=
     Module.finrank F L:=eqv.toLinearEquiv.finrank_eq
 change Module.finrank F L=q.natDegree*
   indexedPlaneResidueWeight component lam mu nu order ht hfinite a
 rw [show indexedPlaneResidueWeight component lam mu nu order ht hfinite a=
     Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J) by rfl]
 calc
   Module.finrank F L=Module.finrank F (PlaneRing Omega ⧸ J):=hquot.symm
   _=q.natDegree*Module.finrank (AdjoinRoot q) (PlaneRing Omega ⧸ J):=
     quotient_finrank_eq_natDegree_mul_residue_finrank q hq J
       (relationKernel_comap_C Omega L order e (ht a))
end
end ProximityPrize.SubmissionLower.RCN105
end PackedLegacy_K2

/-! Packed from ProximityPrize.SubmissionLower.AN. -/
section PackedLegacy_AN
namespace ProximityPrize.SubmissionLower.RCN343
open scoped Classical BigOperators
open RCN337
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {Base:Type} [Field Base] [DecidableEq Base]
structure WeightedGroupedResultantChannel
   {I:Type*} [Fintype I]
   (multiplicity cost:I → ℕ) (budget:ℕ) where
 resultant:Polynomial Base
 factor:I → Polynomial Base
 residueWeight:I → ℕ
 resultant_ne:resultant≠0
 factor_irreducible:∀ i,Irreducible (factor i)
 factor_monic:∀ i,(factor i).Monic
 groupedPowerDvd:∀ f∈Finset.univ.image factor,
   f^(∑ i with factor i=f,multiplicity i*residueWeight i)∣resultant
 cost_le_residue_mul_degree:∀ i,
   cost i ≤ residueWeight i*(factor i).natDegree
 resultant_degree_le:resultant.natDegree ≤ budget
theorem WeightedGroupedResultantChannel.sum_mul_cost_le
   {I:Type*} [Fintype I]
   {multiplicity cost:I → ℕ} {budget:ℕ}
   (C:WeightedGroupedResultantChannel
     (Base:=Base) multiplicity cost budget):
   (∑ i,multiplicity i*cost i) ≤ budget:=by
 let weightedMultiplicity:I → ℕ:=fun i↦
   multiplicity i*C.residueWeight i
 have hfactor:=sum_grouped_power_factor_degrees_le
   C.resultant C.factor weightedMultiplicity C.resultant_ne
     C.factor_irreducible C.factor_monic C.groupedPowerDvd
 calc
   (∑ i,multiplicity i*cost i) ≤
       ∑ i,multiplicity i*
         (C.residueWeight i*(C.factor i).natDegree):=
     Finset.sum_le_sum (fun i _↦
       Nat.mul_le_mul_left (multiplicity i)
         (C.cost_le_residue_mul_degree i))
   _=∑ i,weightedMultiplicity i*(C.factor i).natDegree:=by
     apply Finset.sum_congr rfl
     intro i _
     simp only [weightedMultiplicity,Nat.mul_assoc]
   _ ≤ C.resultant.natDegree:=hfactor
   _ ≤ budget:=C.resultant_degree_le
end
end ProximityPrize.SubmissionLower.RCN343
end PackedLegacy_AN

/-! Packed from ProximityPrize.SubmissionLower.K1. -/
section PackedLegacy_K1
namespace ProximityPrize.SubmissionLower.RCN104
open scoped Classical BigOperators
open RCN011 RCN021 RCN002 RCN264 RCN093 RCN106 RCN111 RCN105 RCN120 RCN226 RCN042 RCN344 RCN343
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {A:Type} [Fintype A]
 (component:A → RegularComponent Omega G T H)
 (hcomponent:Function.Injective component)
 (lam mu nu:Omega) (order:Fin 3 ≃ Fin 3)
variable (ht:∀ a:A,Transcendental Omega
 (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))))
variable (hfinite:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))
variable (hgen:∀ a:A,
 letI:=flagBaseAlgebra Omega (component a).1 lam mu nu order (ht a)
 IntermediateField.adjoin (RatFunc Omega)
   ({flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 2)),
     flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 1))}:
     Set (CoordinateField Omega (component a).1))=⊤)
include hgen in
noncomputable def indexedWeightedFlagPlaneChannel_of_fixedFactors
   (hgate:∀ a:A,∀ hx:Transcendental Omega
       (flagEvaluation Omega (component a).1 lam mu nu (MvPolynomial.X (order 0))),
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       FiniteDimensional (RatFunc Omega) (CoordinateField Omega (component a).1))∧
     (letI:Algebra (RatFunc Omega) (CoordinateField Omega (component a).1):=
         flagBaseAlgebra Omega (component a).1 lam mu nu order hx;
       Algebra.IsSeparable (RatFunc Omega) (CoordinateField Omega (component a).1)))
   (multiplicity:A → ℕ)
   (resultant:Polynomial (RatFunc Omega)) (budget:ℕ)
   (hresultant:resultant≠0)
   (hdegree:resultant.natDegree ≤ budget)
   (hfixed:∀ (q:Polynomial (RatFunc Omega))
     (hq:Irreducible q) (hqMonic:q.Monic)
     (a₀:IndexedFactorFiber component lam mu nu order ht q),
     q^(∑ a:IndexedFactorFiber component lam mu nu order ht q,
       multiplicity a.1*indexedPlaneResidueWeight component
         lam mu nu order ht hfinite a.1)∣resultant):
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     (fun a↦coordinateDegree Omega (CoordinateField Omega (component a).1)
       (coordinateOfGate
         (flagEvaluation Omega (component a).1 lam mu nu
           (MvPolynomial.X (order 0))) (hgate a))) budget:=by
 let factor:=indexedComponentFactor component lam mu nu order ht
 let weight:=indexedPlaneResidueWeight component lam mu nu order ht hfinite
 refine {
   resultant:=resultant
   factor:=factor
   residueWeight:=weight
   resultant_ne:=hresultant
   factor_irreducible:=?_
   factor_monic:=?_
   groupedPowerDvd:=?_
   cost_le_residue_mul_degree:=?_
   resultant_degree_le:=hdegree}
 · intro a
   exact projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro a
   exact projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
 · intro q hqmem
   obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hqmem
   subst q
   have hqirr:Irreducible (factor a):=projectedFactor_irreducible Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   have hqmonic:(factor a).Monic:=projectedFactor_monic Omega
     (CoordinateField Omega (component a).1) order
       (flagEvaluation Omega (component a).1 lam mu nu) (ht a) (hfinite a)
   let a₀:IndexedFactorFiber component lam mu nu order ht (factor a):=⟨a,rfl⟩
   have hpow:=hfixed (factor a) hqirr hqmonic a₀
   have hsum:
       (∑ b with factor b=factor a,multiplicity b*weight b)=
         ∑ b:IndexedFactorFiber component lam mu nu order ht (factor a),
           multiplicity b.1*weight b.1:=by
     simpa only [Finset.subtype_univ,eq_comm] using
       (Finset.sum_subtype_eq_sum_filter
         (s:=(Finset.univ:Finset A))
         (fun b↦multiplicity b*weight b)
         (p:=fun b↦factor a=factor b)).symm
   rw [hsum]
   exact hpow
 · intro a
   have hcost:=indexed_coordinateDegree_eq_factorDegree_mul_planeWeight
     component lam mu nu order ht hfinite hgen hgate a
   simpa only [factor,weight,Nat.mul_comm] using hcost.le
end
end ProximityPrize.SubmissionLower.RCN104
end PackedLegacy_K1

/-! Packed from ProximityPrize.SubmissionLower.Q9. -/
section PackedLegacy_Q9
namespace ProximityPrize.SubmissionLower.RCN342
open scoped Classical BigOperators
open RCN343
noncomputable section
set_option autoImplicit false
variable {Base:Type} [Field Base] [DecidableEq Base]
noncomputable def recost
   {I:Type*} [Fintype I] {multiplicity oldCost newCost:I → ℕ}
   {budget:ℕ}
   (C:WeightedGroupedResultantChannel (Base:=Base)
     multiplicity oldCost budget)
   (hcost:∀ i,newCost i ≤ oldCost i):
   WeightedGroupedResultantChannel (Base:=Base)
     multiplicity newCost budget where
 resultant:=C.resultant
 factor:=C.factor
 residueWeight:=C.residueWeight
 resultant_ne:=C.resultant_ne
 factor_irreducible:=C.factor_irreducible
 factor_monic:=C.factor_monic
 groupedPowerDvd:=C.groupedPowerDvd
 cost_le_residue_mul_degree i:=(hcost i).trans (C.cost_le_residue_mul_degree i)
 resultant_degree_le:=C.resultant_degree_le
noncomputable def emptyChannel
   {I:Type*} [Fintype I] [IsEmpty I]
   (multiplicity cost:I → ℕ) (budget:ℕ):
   WeightedGroupedResultantChannel (Base:=Base) multiplicity cost budget where
 resultant:=1
 factor i:=isEmptyElim i
 residueWeight i:=isEmptyElim i
 resultant_ne:=one_ne_zero
 factor_irreducible i:=isEmptyElim i
 factor_monic i:=isEmptyElim i
 groupedPowerDvd f hf:=by simp at hf
 cost_le_residue_mul_degree i:=isEmptyElim i
 resultant_degree_le:=by simp
end
end ProximityPrize.SubmissionLower.RCN342
end PackedLegacy_Q9

/-! Packed from ProximityPrize.SubmissionLower.DI. -/
section PackedLegacy_DI
namespace ProximityPrize.SubmissionLower.RCN028
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN037 RCN038 RCN095 RCN125 RCN117 RCN031 RCN030 RCN029 RCN112 RCN104 RCN343 RCN342
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
 (multiplicity:RegularComponent Omega G T H → ℕ)
 (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedZChannel
   [Nonempty (ActiveNestedZIndex (G:=G) (T:=T) (H:=H))]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:ActiveNestedZIndex (G:=G) (T:=T) (H:=H)↦multiplicity a.1)
     (fun a↦U.toPrimeFlagBudgetFamily.zCost a.1)
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let a₀:ActiveNestedZIndex (G:=G) (T:=T) (H:=H):=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) zOrder
   hG hproper a₀.1 (activeNestedZTranscendental base hactive hSderiv D a₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).2
 have hdeg:=flagPlaneResultant_z_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (activeNestedZComponent (G:=G) (T:=T) (H:=H))
   D.lam D.mu (D.mu*D.lam) zOrder
   (activeNestedZTranscendental base hactive hSderiv D)
   (activeNestedZFinite base hactive hZ hSderiv D)
   (activeNestedZGenerates base hactive hSderiv D)
   (activeNestedZGate base hactive hZ hSderiv D)
   (fun a↦multiplicity a.1)
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) zOrder G T)
   (flagMixed surfaceFlag tailFlag unitZFlag) hres hdeg powers.z
 exact recost raw fun a↦
   (activeNestedUnitFamily_zCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport a).le
noncomputable def activeNestedUChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.yzCost
     (flagMixed surfaceFlag tailFlag unitYZFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) uOrder
   hG hproper C₀ (activeNestedUTranscendental base hactive hSderiv D C₀)
   (flag_u_z_outer_positive_of_pderiv D.lam D.mu G hSderiv).1
 have hdeg:=flagPlaneResultant_u_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) uOrder
   (activeNestedUTranscendental base hactive hSderiv D)
   (activeNestedUFinite base hactive hSderiv D)
   (activeNestedUGenerates base hactive hSderiv D)
   (activeNestedUGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) uOrder G T)
   (flagMixed surfaceFlag tailFlag unitYZFlag) hres hdeg powers.u
 exact recost raw fun C↦
   (activeNestedUnitFamily_uCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
noncomputable def activeNestedVChannel
   [Nonempty (RegularComponent Omega G T H)]:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   WeightedGroupedResultantChannel (Base:=RatFunc Omega) multiplicity
     U.toPrimeFlagBudgetFamily.allCost
     (flagMixed surfaceFlag tailFlag unitAllFlag):=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper hGsupport hTsupport
 let C₀:RegularComponent Omega G T H:=Classical.choice inferInstance
 have hTne:T≠0:=fun hz↦hproper (hz ▸ dvd_zero G)
 have hres:=flagPlaneResultant_ne D.lam D.mu (D.mu*D.lam) vOrder
   hG hproper C₀ (activeNestedVTranscendental base hactive hSderiv D C₀)
   (flag_v_outer_positive_of_directional D.lam D.mu G D.directional)
 have hdeg:=flagPlaneResultant_v_degree_le surfaceFlag tailFlag D.lam D.mu
   (D.mu*D.lam) hGsupport hTsupport hTne
 let raw:=indexedWeightedFlagPlaneChannel_of_fixedFactors
   (fun C:RegularComponent Omega G T H↦C) D.lam D.mu (D.mu*D.lam) vOrder
   (activeNestedVTranscendental base hactive hSderiv D)
   (activeNestedVFinite base hactive hSderiv D)
   (activeNestedVGenerates base hactive hSderiv D)
   (activeNestedVGate base hactive hSderiv D) multiplicity
   (flagPlaneResultant D.lam D.mu (D.mu*D.lam) vOrder G T)
   (flagMixed surfaceFlag tailFlag unitAllFlag) hres hdeg powers.v
 exact recost raw fun C↦
   (activeNestedUnitFamily_allCost_eq_flagCost base hactive hZ hSderiv D
     hG hproper hGsupport hTsupport C).le
end
end ProximityPrize.SubmissionLower.RCN028
end PackedLegacy_DI

/-! Packed from ProximityPrize.SubmissionLower.DK. -/
section PackedLegacy_DK
namespace ProximityPrize.SubmissionLower.RCN032
open scoped Classical BigOperators
open RCN042 RCN344 RCN022
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
end PackedLegacy_DK

/-! Packed from ProximityPrize.SubmissionLower.DL. -/
section PackedLegacy_DL
namespace ProximityPrize.SubmissionLower.RCN033
open scoped Classical BigOperators
open RCN264 RCN095 RCN237 RCN343 RCN338
noncomputable section
set_option autoImplicit false
variable {Base Omega:Type} [Field Base] [Field Omega]
local instance:DecidableEq Base:=Classical.decEq Base
variable {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag firstTailFlag:FlagDegree}
theorem regularComponentWeightedInertiaCertificate_of_active_channels
   (B:PrimeFlagBudgetFamily
     (G:=G) (T:=T) (H:=H) surfaceFlag firstTailFlag)
   (multiplicity:RegularComponent Omega G T H → ℕ)
   {zIndex uIndex:Type*} [Fintype zIndex] [Fintype uIndex]
   (zComponent:zIndex → RegularComponent Omega G T H)
   (uComponent:uIndex → RegularComponent Omega G T H)
   (zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a))
   (uRewrite:(∑ C,multiplicity C*B.yzCost C)=
     ∑ a:uIndex,multiplicity (uComponent a)*B.yzCost (uComponent a))
   (zChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag firstTailFlag unitZFlag))
   (uChannel:WeightedGroupedResultantChannel (Base:=Base)
     (fun a↦multiplicity (uComponent a))
     (fun a↦B.yzCost (uComponent a))
     (flagMixed surfaceFlag firstTailFlag unitYZFlag))
   (allChannel:WeightedGroupedResultantChannel (Base:=Base) multiplicity
     B.allCost (flagMixed surfaceFlag firstTailFlag unitAllFlag)):
   RegularComponentWeightedInertiaResultantCertificate B multiplicity where
 z:=by
   rw [zRewrite]
   exact zChannel.sum_mul_cost_le
 yz:=by
   rw [uRewrite]
   exact uChannel.sum_mul_cost_le
 all:=allChannel.sum_mul_cost_le
end
end ProximityPrize.SubmissionLower.RCN033
end PackedLegacy_DL

/-! Packed from ProximityPrize.SubmissionLower.DH. -/
section PackedLegacy_DH
namespace ProximityPrize.SubmissionLower.RCN027
open scoped Classical BigOperators
open RCN264 RCN002 RCN341 RCN042 RCN344 RCN037 RCN038 RCN095 RCN031 RCN030 RCN029 RCN028 RCN032 RCN033 RCN343 RCN342 RCN338
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {Omega:Type} [Field Omega] [IsAlgClosed Omega]
 {G T H:MvPolynomial (Fin 3) Omega}
 {surfaceFlag tailFlag:FlagDegree}
variable (base:∀ C:RegularComponent Omega G T H,
 SeparableLiteralCoordinate C.1)
variable (hactive:∀ C:RegularComponent Omega G T H,
 KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 0)≠0∨
   KaehlerDifferential.D Omega (CoordinateField Omega C.1)
     (coordinate Omega C.1 2)≠0)
variable (hZ:∀ C:RegularComponent Omega G T H,LiteralProjectionGate C 2)
 (hSderiv:MvPolynomial.pderiv (1:Fin 3) G≠0)
 (D:AdaptiveNestedProjectionDataActive base hactive hSderiv)
 (hG:Irreducible G) (hproper:¬ G∣T)
 (hGsupport:G.support ⊆ flagSupport surfaceFlag)
 (hTsupport:T.support ⊆ flagSupport tailFlag)
 (multiplicity:RegularComponent Omega G T H → ℕ)
 (powers:ActiveNestedFixedPowers base hactive hZ hSderiv D multiplicity)
noncomputable def activeNestedWeightedCertificate:
   let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
     hGsupport hTsupport
   RegularComponentWeightedInertiaResultantCertificate
     U.toPrimeFlagBudgetFamily multiplicity:=by
 let U:=activeNestedUnitFamily base hactive hZ hSderiv D hG hproper
   hGsupport hTsupport
 let B:=U.toPrimeFlagBudgetFamily
 let zIndex:=ActiveNestedZIndex (G:=G) (T:=T) (H:=H)
 let zComponent:=activeNestedZComponent (G:=G) (T:=T) (H:=H)
 let zChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     (fun a:zIndex↦multiplicity (zComponent a))
     (fun a↦B.zCost (zComponent a))
     (flagMixed surfaceFlag tailFlag unitZFlag):=by
   by_cases hz:Nonempty zIndex
   · letI:Nonempty zIndex:=hz
     exact activeNestedZChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty zIndex:=⟨fun a↦hz ⟨a⟩⟩
     exact emptyChannel _ _ _
 let uChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.yzCost (flagMixed surfaceFlag tailFlag unitYZFlag):=by
   by_cases hu:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hu
     exact activeNestedUChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hu ⟨C⟩⟩
     exact emptyChannel _ _ _
 let allChannel:WeightedGroupedResultantChannel (Base:=RatFunc Omega)
     multiplicity B.allCost (flagMixed surfaceFlag tailFlag unitAllFlag):=by
   by_cases hv:Nonempty (RegularComponent Omega G T H)
   · letI:Nonempty (RegularComponent Omega G T H):=hv
     exact activeNestedVChannel base hactive hZ hSderiv D hG hproper
       hGsupport hTsupport multiplicity powers
   · letI:IsEmpty (RegularComponent Omega G T H):=⟨fun C↦hv ⟨C⟩⟩
     exact emptyChannel _ _ _
 have zRewrite:(∑ C,multiplicity C*B.zCost C)=
     ∑ a:zIndex,multiplicity (zComponent a)*B.zCost (zComponent a):=by
   calc
     _=∑ C,multiplicity C*coordinateDegree Omega
         (CoordinateField Omega C.1)
         (coordinateOfGate (coordinate Omega C.1 2) (hZ C)):=by
       apply Finset.sum_congr rfl
       intro C _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
     _=∑ a:zIndex,multiplicity a.1*coordinateDegree Omega
         (CoordinateField Omega a.1.1)
         (coordinateOfGate (coordinate Omega a.1.1 2) (hZ a.1)):=
       sum_mul_coordinateOfGate_eq_active
         (fun C:RegularComponent Omega G T H↦CoordinateField Omega C.1)
         (fun C↦coordinate Omega C.1 2) hZ multiplicity
     _=_:=by
       apply Finset.sum_congr rfl
       intro a _
       rw [activeNestedUnitFamily_zCost base hactive hZ hSderiv D hG
         hproper hGsupport hTsupport]
       rfl
 exact regularComponentWeightedInertiaCertificate_of_active_channels B
   multiplicity zComponent (fun C:RegularComponent Omega G T H↦C)
   zRewrite rfl zChannel uChannel allChannel
end
end ProximityPrize.SubmissionLower.RCN027
end PackedLegacy_DH

/-! Packed from ProximityPrize.SubmissionLower.Q1. -/
section PackedLegacy_Q1
namespace ProximityPrize.SubmissionLower.RCN334
open scoped Classical BigOperators
open RCN135 RCN136 RCN319 RCN174 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN090 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN037 RCN038 RCN042 RCN341 RCN312 RCN339 RCN330 RCN002 RCN344
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
 {tightSupport:ResidualSupportParameters}
def loosenStageGeneral
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport) :
   Stage K I Gamma x p flag stageErrorCap tightSupport:=S
theorem loosenStageGeneral_one_le_localMultiplicity
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ∀ C, 1 ≤ localMultiplicity (loosenStageGeneral S)
     (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C:=by
 exact one_le_localMultiplicity (loosenStageGeneral S) hfirstProper
def loosenStage
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hs:tightSupport.s ≤ fixedSupport.s)
   (hys:tightSupport.ys ≤ fixedSupport.ys)
   (htotal:tightSupport.total ≤ fixedSupport.total) :
   Stage K I Gamma x p flag stageErrorCap fixedSupport :=
 { S with
   surface_s_weight:=S.surface_s_weight.trans hs
   surface_ys_weight:=S.surface_ys_weight.trans hys
   surface_total_weight:=S.surface_total_weight.trans htotal }
theorem loosenStage_one_le_localMultiplicity
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hs:tightSupport.s ≤ fixedSupport.s)
   (hys:tightSupport.ys ≤ fixedSupport.ys)
   (htotal:tightSupport.total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ∀ C, 1 ≤ localMultiplicity (loosenStage S hs hys htotal)
     (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper) C:=by
 exact one_le_localMultiplicity (loosenStage S hs hys htotal) hfirstProper
theorem laterTail_in_reduced_delay_secondFlag
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (C:FirstTailComponent S) (delay:ℕ) (hdelay:1 ≤ delay) :
   PolynomialInFlagMod C.1
     (delay • reducedResidualAgreementFlag tightSupport (w + 2))
     (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)):=by
 let d:=w + 1 + delay
 let Tred:=reducedGlobalTailCut (polynomialEmbedding K) tightSupport S.F d
 let Hsupport:ResidualSupportData tightSupport S.F :=
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩
 have hred:PolynomialInFlag (reducedResidualAgreementFlag tightSupport d) Tred :=
   reducedGlobalTailCut_in_flag (polynomialEmbedding K) tightSupport Hsupport d
 have hflag:PolynomialInFlag
     (delay • reducedResidualAgreementFlag tightSupport (w + 2)) Tred:=by
   have hscale:d ≤ delay * (w + 2):=by
     dsimp only [d]
     norm_num [w]
     omega
   have hallFlag:(reducedResidualAgreementFlag tightSupport d).all ≤
       (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     simp only [reducedResidualAgreementFlag, reducedAgreementDirection, nsmul_all]
     calc
       (2 * tightSupport.s - 2) * d ≤
           (2 * tightSupport.s - 2) * (delay * (w + 2)) :=
         Nat.mul_le_mul_left _ hscale
       _ = delay * ((2 * tightSupport.s - 2) * (w + 2)):=by ring
   have hysFlag :
       (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_ys]
     simp only [nsmul_yz, nsmul_all]
     rw [← Nat.mul_add]
     rw [reducedResidualAgreementFlag_ys]
     calc
       1 + d * (2 * tightSupport.ys - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.ys - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.ys - 2)):=by ring
   have htotalFlag :
       (reducedResidualAgreementFlag tightSupport d).zOnly +
           (reducedResidualAgreementFlag tightSupport d).yz +
           (reducedResidualAgreementFlag tightSupport d).all ≤
         (delay • reducedResidualAgreementFlag tightSupport (w + 2)).zOnly +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).yz +
           (delay • reducedResidualAgreementFlag tightSupport (w + 2)).all:=by
     rw [reducedResidualAgreementFlag_total]
     simp only [nsmul_zOnly, nsmul_yz, nsmul_all]
     rw [← Nat.mul_add, ← Nat.mul_add]
     rw [reducedResidualAgreementFlag_total]
     calc
       1 + d * (2 * tightSupport.total - 2) ≤
           delay + (delay * (w + 2)) * (2 * tightSupport.total - 2) :=
         Nat.add_le_add hdelay (Nat.mul_le_mul_right _ hscale)
       _ = delay * (1 + (w + 2) * (2 * tightSupport.total - 2)):=by ring
   intro exponent hexponent
   have h:=hred exponent hexponent
   exact ⟨h.1.trans hallFlag, h.2.1.trans hysFlag, h.2.2.trans htotalFlag⟩
 refine ⟨Tred, hflag, ?_⟩
 have hd:S.G ∣ globalTailCut (polynomialEmbedding K) S.F d - Tred :=
   S.G_dvd_surface.trans
     (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) tightSupport S.F d)
 exact C.1.mem_of_dvd hd
   (regularComponent_G_mem (GenericField K) S.G
     (globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F) C)
theorem loosenStage_dichotomy_with_tangent
   {tailFlag1:FlagDegree}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hs:tightSupport.s ≤ fixedSupport.s)
   (hys:tightSupport.ys ≤ fixedSupport.ys)
   (htotal:tightSupport.total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent:∀ C:FirstTailComponent S,
     (∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) →
     (componentSeeds (GenericField K) S.G
       (globalTailCut (polynomialEmbedding K) S.F (w + 1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C) :
   ∀ C:FirstTailComponent S,
     (∃ delay, 1 ≤ delay ∧
       delay ≤ localMultiplicity (loosenStage S hs hys htotal)
         (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper) C ∧
       globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1) ∨
     ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1) ∧
       (componentSeeds (GenericField K) S.G
         (globalTailCut (polynomialEmbedding K) S.F (w + 1))
         (regularitySurface (polynomialEmbedding K) S.F) Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
           (stageErrorCap + 1) * B.yzCost C):=by
 intro C
 have dichotomy:=local_order_tail_dichotomy (loosenStage S hs hys htotal)
   (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall, htangent C hall⟩
structure ReducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) where
 base:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   SeparableLiteralCoordinate C.1
 hactive:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F),
   KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 0) ≠ 0 ∨
     KaehlerDifferential.D (GenericField K) (CoordinateField (GenericField K) C.1)
       (coordinate (GenericField K) C.1 2) ≠ 0
 hZ:∀ C:RegularComponent (GenericField K) S.G
     (reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1))
     (regularitySurface (polynomialEmbedding K) S.F), LiteralProjectionGate C 2
 data:AdaptiveNestedProjectionDataActive base hactive
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
theorem exists_reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   Nonempty (ReducedActiveGeometry S):=by
 obtain ⟨base, hactive, hZ, ⟨D⟩⟩ :=
   exists_reduced_firstTail_activeNestedData_of_caps S hfirstProper hflagChar hmixed
 exact ⟨⟨base, hactive, hZ, D⟩⟩
noncomputable def reducedActiveGeometry
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   ReducedActiveGeometry S :=
 Classical.choice (exists_reducedActiveGeometry S hfirstProper hflagChar hmixed)
theorem loosenStageGeneral_dichotomy_with_tangent
   {tailFlag1:FlagDegree}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w tightSupport)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (B:PrimeFlagBudgetFamily
     (G:=S.G) (T:=globalTailCut (polynomialEmbedding K) S.F (w + 1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag tailFlag1)
   (htangent:∀ C:FirstTailComponent S,
     (∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) →
     (componentSeeds (GenericField K) S.G
       (globalTailCut (polynomialEmbedding K) S.F (w + 1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C) :
   ∀ C:FirstTailComponent S,
     (∃ delay, 1 ≤ delay ∧
       delay ≤ localMultiplicity (loosenStageGeneral S)
         (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper) C ∧
       globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1) ∨
     ((∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1) ∧
       (componentSeeds (GenericField K) S.G
         (globalTailCut (polynomialEmbedding K) S.F (w + 1))
         (regularitySurface (polynomialEmbedding K) S.F) Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
           (stageErrorCap + 1) * B.yzCost C):=by
 intro C
 have dichotomy:=local_order_tail_dichotomy (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
   C hfirstProper
 rcases dichotomy.2 with hproper | hall
 · exact Or.inl hproper
 · exact Or.inr ⟨hall, htangent C hall⟩
end
end ProximityPrize.SubmissionLower.RCN334
end PackedLegacy_Q1

/-! Packed from ProximityPrize.SubmissionLower.P9. -/
section PackedLegacy_P9
namespace ProximityPrize.SubmissionLower.RCN332
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN089 RCN066 RCN334 RCN331 RCN336 RCN027 RCN030 RCN029 RCN338 RCN042 RCN341 RCN002 RCN344 RCN340
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
def reducedFirstCut
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)):MvPolynomial (Fin 3) (GenericField K) :=
 reducedGlobalTailCut (polynomialEmbedding K) (support a b s) S.F (w + 1)
theorem ordinary_sub_reducedFirstCut_dvd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1) -
     reducedFirstCut S :=
 S.G_dvd_surface.trans
   (globalTailCut_sub_reduced_dvd (polynomialEmbedding K) (support a b s)
     S.F (w + 1))
theorem reducedFirstCut_proper
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   ¬ S.G ∣ reducedFirstCut S:=by
 intro hr
 apply hfirstProper
 have h:=(ordinary_sub_reducedFirstCut_dvd S).add hr
 simpa only [reducedFirstCut, sub_add_cancel] using h
theorem reducedFirstCut_in_flag
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s)) :
   PolynomialInFlag (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S):=by
 exact reducedGlobalTailCut_in_flag (polynomialEmbedding K) (support a b s)
   ⟨S.surface_s_weight, S.surface_ys_weight, S.surface_total_weight⟩ (w + 1)
noncomputable def reducedUnitFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 activeNestedUnitFamily A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
noncomputable def reducedMultiplicity
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStage S hs hys htotal)
   (canonicalLocalDVRFamily (loosenStage S hs hys htotal) hfirstProper)
theorem reducedFixedPowers
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicity S hs hys htotal hfirstProper)):=by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStage S hs hys htotal)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultants
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicity S hs hys htotal hfirstProper)):=by
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicity S hs hys htotal hfirstProper))
   (reducedFixedPowers S hs hys htotal hfirstProper hflagChar hmixed)
noncomputable def reducedBudgetFamily
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :=
 PrimeFlagBudgetFamily.ofCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
theorem transportedWeightedResultants
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicity S hs hys htotal hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicity S hs hys htotal hfirstProper)
   (reducedWeightedResultants S hs hys htotal hfirstProper hflagChar hmixed)
noncomputable def reducedBaseOrd
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S):SeparableLiteralCoordinate C.1:=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 exact (reducedActiveGeometry S hfirstProper hflagChar hmixed).base C'
theorem reducedBudgetFamily_yzPositive
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S) :
   1 ≤ (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C:=by
 let hd:=ordinary_sub_reducedFirstCut_dvd S
 let C':=regularComponentEquiv hd C
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 let U:=reducedUnitFamily S hfirstProper hflagChar hmixed
 change 1 ≤ U.toPrimeFlagBudgetFamily.yzCost C'
 change 1 ≤ coordinateDegree (GenericField K)
   (CoordinateField (GenericField K) C'.1) (U.yzProjection C')
 apply one_le_coordinateDegree_of_transcendental_value
 have hproj:U.yzProjection C' = coordinateOfGate
     (RCN093.affineU
       (GenericField K) C'.1 A.data.lam) (A.data.uGate C'):=rfl
 rw [hproj, coordinateOfGate_value]
 exact A.data.uTranscendental C'
theorem reducedBudgetFamily_yzPole
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (C:FirstTailComponent S) :
   LiteralSupportPoleBound
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     (flagSupport unitYZFlag)
     ((reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C):=by
 let C':RegularComponent (GenericField K) S.G (reducedFirstCut S)
     (regularitySurface (polynomialEmbedding K) S.F) :=
   ⟨C.1, by
     rw [← regularComponents_eq_of_dvd_sub (ordinary_sub_reducedFirstCut_dvd S)]
     exact C.2⟩
 have heq:regularComponentEquiv (ordinary_sub_reducedFirstCut_dvd S) C = C':=by
   apply Subtype.ext
   rfl
 rw [show (reducedBudgetFamily S hfirstProper hflagChar hmixed).yzCost C =
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C' by
   simp only [reducedBudgetFamily, PrimeFlagBudgetFamily.ofCongruentCut, heq]]
 change LiteralSupportPoleBound
   ((reducedActiveGeometry S hfirstProper hflagChar hmixed).base C')
   (flagSupport unitYZFlag)
   ((reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily.yzCost C')
 exact (reducedUnitFamily S hfirstProper hflagChar hmixed).toAdaptiveUnitPoleBudget.yzPole C'
noncomputable def reducedMultiplicityGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1)) :
   FirstTailComponent S → ℕ :=
 localMultiplicity (loosenStageGeneral S)
   (canonicalLocalDVRFamily (loosenStageGeneral S) hfirstProper)
theorem reducedFixedPowersGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
   ActiveNestedFixedPowers A.base A.hactive A.hZ
     (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 dsimp only
 exact reducedStage_activeFixedPowers (loosenStageGeneral S)
   hfirstProper (reducedFirstCut S) (ordinary_sub_reducedFirstCut_dvd S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).base
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hactive
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   (reducedActiveGeometry S hfirstProper hflagChar hmixed).data
theorem reducedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
     (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
       (reducedMultiplicityGeneral S hfirstProper)):=by
 let A:=reducedActiveGeometry S hfirstProper hflagChar hmixed
 exact activeNestedWeightedCertificate A.base A.hactive A.hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
   S.irreducible_G (reducedFirstCut_proper S hfirstProper)
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (reducedResidualAgreementFlag (support a b s) (w + 1))
     (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))
   (transportedMultiplicity (ordinary_sub_reducedFirstCut_dvd S)
     (reducedMultiplicityGeneral S hfirstProper))
   (reducedFixedPowersGeneral S hfirstProper hflagChar hmixed)
theorem transportedWeightedResultantsGeneral
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p) :
   RegularComponentWeightedInertiaResultantCertificate
     (reducedBudgetFamily S hfirstProper hflagChar hmixed)
     (reducedMultiplicityGeneral S hfirstProper):=by
 exact weightedCertificate_of_congruentCut (ordinary_sub_reducedFirstCut_dvd S)
   (reducedUnitFamily S hfirstProper hflagChar hmixed).toPrimeFlagBudgetFamily
   (reducedMultiplicityGeneral S hfirstProper)
   (reducedWeightedResultantsGeneral S hfirstProper hflagChar hmixed)
end
end ProximityPrize.SubmissionLower.RCN332
end PackedLegacy_P9

/-! Packed from ProximityPrize.SubmissionLower.Q2. -/
section PackedLegacy_Q2
namespace ProximityPrize.SubmissionLower.RCN335
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {stageErrorCap:ℕ}
theorem exists_delayedTailMultiplicityProvider_of_reducedGeneral
   {a b s:ℕ}
   (agreementCap:ℕ)
   (S:ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card = agreementCap + stageErrorCap)
   (hagreement:∀ gamma ∈ Gamma, agreementCap ≤ (S.agreementFiber gamma).card)
   (hwa:w < agreementCap)
   (hshort:w + 1 ≤ bound) (hchar:bound < p)
   (hbox:S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate:stageErrorCap + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2:=reducedResidualAgreementFlag (support a b s) (w + 2)) S):=by
 classical
 let supp:=support a b s
 let S0:=loosenStageGeneral S
 let T:=globalTailCut (polynomialEmbedding K) S.F (w + 1)
 let H:=regularitySurface (polynomialEmbedding K) S.F
 let secondFlag:=reducedResidualAgreementFlag supp (w + 2)
 let B:=reducedBudgetFamily S hfirstProper hflagChar hmixed
 let multiplicity:=reducedMultiplicityGeneral S hfirstProper
 have hone:∀ C, 1 ≤ multiplicity C:=by
   exact loosenStageGeneral_one_le_localMultiplicity S hfirstProper
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) :
     (componentSeeds (GenericField K) S.G T H Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     agreementCap bound seedCap slopeCap hnodes hagreement
     hwa (by norm_num [w])
     hshort hchar hbox B
     (reducedBudgetFamily_yzPositive S hfirstProper hflagChar hmixed C)
     hall (reducedBudgetFamily_yzPole S hfirstProper hflagChar hmixed C)
 have branchBound (C:FirstTailComponent S) :
     ((∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
         globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1 ∧
         (componentSeeds (GenericField K) S.G T H Gamma
           (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
             multiplicity C * B.weightedCost secondFlag C) ∨
       (∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1)):=by
   have dichotomy:=local_order_tail_dichotomy S0
     (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
   rcases dichotomy.2 with hproper | htangent
   · left
     obtain ⟨delay, hdelay, hdelayMu, htail⟩:=hproper
     have hzero:∀ gamma ∈ componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C,
         MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)
           (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0:=by
       intro gamma hgamma
       have hGamma:=componentSeeds_subset (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
       exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected
         gamma w (w + 1 + delay) (S.degree_le gamma hGamma)
         (S.solution gamma hGamma) (by omega)
     have hcount:=component_secondTail_card_le_mod B C Gamma
       (selectedPoint (polynomialEmbedding K) S.selected)
       (selectedPoint_injective (polynomialEmbedding K) S.selected)
       (laterTail_in_reduced_delay_secondFlag S C delay hdelay) htail hzero
     have hscale:B.weightedCost (delay • secondFlag) C =
         delay * B.weightedCost secondFlag C:=by
       simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
         nsmul_all]
       ring
     rw [hscale] at hcount
     exact ⟨delay, hdelay, hdelayMu, htail,
       hcount.trans (Nat.mul_le_mul_right (B.weightedCost secondFlag C) hdelayMu)⟩
   · exact Or.inr htangent
 have providerDichotomy :=
   loosenStageGeneral_dichotomy_with_tangent S hfirstProper B tangentCount
 refine ⟨{
   budgetFamily:=B
   multiplicity:=multiplicity
   cost:=fun C => multiplicity C * B.weightedCost secondFlag C
   one_le_multiplicity:=hone
   tangentYZGate:=htangentGate
   cost_le:=fun _ => le_rfl
   divisor_le :=
     (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixed).divisor_le
       B multiplicity
   componentBound:=?_
   dichotomy:=providerDichotomy }⟩
 intro C
 rcases branchBound C with hproper | htangent
 · obtain ⟨_delay, _hdelay, _hdelayMu, _htail, hcount⟩:=hproper
   exact hcount
 · calc
     (componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C:=tangentCount C htangent
     _ ≤ B.weightedCost secondFlag C :=
       yzCost_mul_le_weightedCost B secondFlag C (stageErrorCap + 1) htangentGate
     _ = 1 * B.weightedCost secondFlag C:=by simp
     _ ≤ multiplicity C * B.weightedCost secondFlag C :=
       Nat.mul_le_mul_right (B.weightedCost secondFlag C) (hone C)
theorem exists_delayedTailMultiplicityProvider_of_reduced
   {a b s:ℕ}
   (S:ResidualStage (polynomialEmbedding K) Gamma x p errors flag w
     (support a b s))
   (hs:(support a b s).s ≤ fixedSupport.s)
   (hys:(support a b s).ys ≤ fixedSupport.ys)
   (htotal:(support a b s).total ≤ fixedSupport.total)
   (hfirstProper:¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar:flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed:(1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card = agreements + errors)
   (hagreement:∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card)
   (hshort:w + 1 ≤ bound) (hchar:bound < p)
   (hbox:S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate:errors + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2:=reducedResidualAgreementFlag (support a b s) (w + 2)) S):=by
 exact exists_delayedTailMultiplicityProvider_of_reducedGeneral agreements S
   hfirstProper hflagChar hmixed bound seedCap slopeCap hnodes hagreement
   (by norm_num [agreements, errors, n, w]) hshort hchar hbox htangentGate
end
end ProximityPrize.SubmissionLower.RCN335
end PackedLegacy_Q2

/-! Packed from ProximityPrize.SubmissionLower.J4. -/
section PackedLegacy_J4
namespace ProximityPrize.SubmissionLower.RCN087
open scoped Classical BigOperators
open RCN136 RCN231 RCN319 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 25000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e:ℕ} [CharP Ω p]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
local instance:DecidableEq I:=Classical.decEq I
def IdentityCurveCountProvider
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support) (identityDegree:ℕ):Prop:=
 ∀ i∈S.nodes,
   let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
   (hproper:¬S.G∣T) →
   let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
   ∃ cost:RegularComponent Ω S.G T (regularitySurface φ S.F)→ℕ,
     (∀ C,(componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
       (selectedPoint φ S.selected) C).card≤(e+1)*cost C)∧
     (∑ C,cost C) ≤ identityDegree
private theorem proper_node_fiber_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (identityDegree:ℕ) (hprovider:IdentityCurveCountProvider S identityDegree)
   (i:I) (hi:i∈S.nodes)
   (hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)):
   (Γ.filter (fun γ=>S.Agrees γ i)).card≤(e+1)*identityDegree:=by
 let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨cost,hcomponent,hsum⟩:=hprovider i hi hproper
 have hsub:Gi⊆Γ:=Finset.filter_subset _ _
 have hGpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) S.G=0:=by
   intro γ hγ;exact S.on_component γ (hsub hγ)
 have hTpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) T=0:=by
   intro γ hγ
   exact (selected_agreement_zero_iff φ S.F S.selected p w S.characteristic_bound γ
     (S.degree_le γ (hsub hγ)) (S.solution γ (hsub hγ))
     (S.regular γ (hsub hγ)) (x i) (S.u0 i) (S.u1 i)).mpr
     (Finset.mem_filter.mp hγ).2
 have hHp:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ)
     (regularitySurface φ S.F)≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ S.selected γ)
     (surfaceMap φ (MvPolynomial.pderiv 2 S.F))≠0
   rw [selectedPoint_evaluation]
   exact S.regular γ (hsub hγ)
 calc
   Gi.card≤∑ C:RegularComponent Ω S.G T (regularitySurface φ S.F),
       (componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
         (selectedPoint φ S.selected) C).card:=
     card_le_sum_componentSeeds Ω _ _ _ Gi _ hGpoint hTpoint hHp
   _≤∑ C,(e+1)*cost C:=Finset.sum_le_sum fun C _=>hcomponent C
   _=(e+1)*(∑ C,cost C):=by rw [Finset.mul_sum]
   _≤(e+1)*identityDegree:=Nat.mul_le_mul_left _ hsum
theorem identity_surface_seed_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (a identityDegree:ℕ)
   (hprovider:IdentityCurveCountProvider S identityDegree)
   (hagreement:∀ γ∈Γ,a≤(S.agreementFiber γ).card)
   (hwa:w < a) (han:a ≤ S.nodes.card) (hdegreePos:1 ≤ identityDegree):
   Γ.card*(a-w)≤(S.nodes.card-w)*(e+1)*identityDegree:=by
 classical
 letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
 let relation:K→I→Prop:=fun γ i=>S.Agrees γ i
 let identities:=S.identities
 by_cases hI:identities.card ≤ w
 · have hfiber:∀ i∈S.nodes\identities,
       (Γ.filter (fun γ=>relation γ i)).card≤(e+1)*identityDegree:=by
     intro i hi
     obtain ⟨hiNode,hiNot⟩:=Finset.mem_sdiff.mp hi
     have hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i):=by
       intro hd
       exact hiNot (Finset.mem_filter.mpr ⟨hiNode,Ideal.mem_span_singleton.mpr hd⟩)
     exact proper_node_fiber_bound S identityDegree hprovider i hiNode hproper
   simpa only [mul_assoc] using RCN173.sharp_incidence_bound relation Γ S.nodes
     identities a w ((e+1)*identityDegree)
     (identityNodes_subset φ S.componentIdeal S.F S.nodes x S.u0 S.u1 w)
     hI hwa han hagreement hfiber
 · have hi:w < identities.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈identities→
       (S.selected t.1).eval (x i)=S.u0 i+t.1*S.u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ S.componentIdeal S.F S.nodes x S.u0 S.u1
       p w S.characteristic_bound (S.selected t.1) t.1 (S.degree_le t.1 t.2)
       (S.solution t.1 t.2) (S.regular t.1 t.2) (S.selected_point_ideal t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=exists_common_pencil_of_many_identities
     φ S.componentIdeal S.F S.surface_mem_componentIdeal S.regularity_not_mem_componentIdeal
     S.nodes x S.u0 S.u1 w S.x_injective hi
     (fun t:{γ:K//γ∈Γ}=>t.1) (fun t=>S.selected t.1)
     (fun t=>S.degree_le t.1 t.2) hvalues
   have hsmall:Γ.card ≤ e+1:=by
     have hf:Γ.filter (fun γ=>S.selected γ=P0+Polynomial.C γ*P1)=Γ:=
       Finset.filter_eq_self.mpr (fun γ hγ=>hpencil ⟨γ,hγ⟩)
     simpa only [hf] using S.no_large_pencil P0 P1 h0 h1
   calc
     Γ.card*(a-w)≤(e+1)*(a-w):=Nat.mul_le_mul_right _ hsmall
     _≤(e+1)*(S.nodes.card-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _≤(S.nodes.card-w)*(e+1)*identityDegree:=by
       have h:=Nat.mul_le_mul_left ((S.nodes.card-w)*(e+1)) hdegreePos
       simpa [mul_assoc,mul_comm,mul_left_comm] using h
end
end ProximityPrize.SubmissionLower.RCN087
end PackedLegacy_J4

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLegacyBarrier23 : True := by trivial
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.DU. -/
section PackedLegacy_DU
namespace ProximityPrize.SubmissionLower.RCN049
open scoped Classical BigOperators
open Polynomial KaehlerDifferential RCN002 RCN005 RCN003 RCN001 RCN136 RCN238 RCN264 RCN243 RCN095 RCN159 RCN275 RCN287 RCN341 RCN277 RCN037 RCN038 RCN039 RCN040 RCN041 RCN265 RCN274 RCN198
noncomputable section
set_option maxHeartbeats 3500000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
 {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
 {p e w a b s:ℕ} [CharP Ω p] {flag:FlagDegree}
theorem exists_agreement_projection_of_caps
   (S:ResidualStage φ Γ x p e flag w (support a b s))
   (x0 u0 u1:K)
   (hproper:¬S.G∣agreementPolynomial φ S.F w x0 u0 u1)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   ∃ base:∀ C:RegularComponent Ω S.G
       (agreementPolynomial φ S.F w x0 u0 u1) (regularitySurface φ S.F),
       SeparableLiteralCoordinate C.1,
     Nonempty (AdaptiveUnitProjectionFamilyYZ base flag
       (sharpResidualAgreementFlag (support a b s) w)):=by
 classical
 let T:=agreementPolynomial φ S.F w x0 u0 u1
 let H:=regularitySurface φ S.F
 have hsy:s+2 < b+s+3:=by omega
 have hTflag:PolynomialInFlag (sharpResidualAgreementFlag (support a b s) w) T:=
   surfaceMap_agreement_in_sharp_flag hsy (phi:=φ)
     ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
     w (fun j:ℕ => (j.factorial:K)⁻¹) x0 u0 u1
 obtain ⟨hGY,hGS,hGZ⟩:=
   RCN314.degree_bounds_of_polynomialInFlag S.flag_support
 obtain ⟨hTY,hTS,_⟩:=
   RCN314.degree_bounds_of_polynomialInFlag hTflag
 have hTY':T.degreeOf 0 ≤ 1+w*(2*(b+s+3)-2):=by
   apply hTY.trans_eq
   exact sharpResidualAgreementFlag_ys (support a b s) hsy w
 have hTS':T.degreeOf 1 ≤ (2*(s+2)-1)*w:=by
   apply hTS.trans_eq
   simp only [sharpResidualAgreementFlag,sharpAgreementDirection,
     RCN198.support]
 have hGdegree:∀ j:Fin 3,S.G.degreeOf j<p:=by
   intro j
   fin_cases j
   · exact hGY.trans_lt hflagChar.1
   · exact hGS.trans_lt hflagChar.2.1
   · exact hGZ.trans_lt hflagChar.2.2
 have hmixZ:coordinateMixedDegree Ω S.G T 2<p:=by
   rw [coordinateMixedDegree_two]
   exact (Nat.add_le_add (Nat.mul_le_mul hTY' hGS)
     (Nat.mul_le_mul hGY hTS')).trans_lt hmixed
 let choiceData:∀ C:RegularComponent Ω S.G T H,
     ∃ B:SeparableLiteralCoordinate C.1,B.index=0∨B.index=2:=
   fun C => regularComponent_exists_separableLiteralCoordinate6630
     φ S.F S.G T p S.G_dvd_surface S.irreducible_G hproper
     S.y_dependent hGdegree hmixZ C
 let base:∀ C:RegularComponent Ω S.G T H,
     SeparableLiteralCoordinate C.1:=fun C => (choiceData C).choose
 have hbaseIndex:∀ C:RegularComponent Ω S.G T H,
     (base C).index=0∨(base C).index=2:=by
   intro C
   exact (choiceData C).choose_spec
 have hactive:∀ C:RegularComponent Ω S.G T H,
     D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 0)≠0∨
       D Ω (CoordinateField Ω C.1) (coordinate Ω C.1 2)≠0:=by
   intro C
   have hb:=base_differential_ne_zero (base C)
   rcases hbaseIndex C with hidx | hidx
   · left;simpa only [hidx] using hb
   · right;simpa only [hidx] using hb
 let hZ:∀ C:RegularComponent Ω S.G T H,LiteralProjectionGate C 2:=by
   intro C htr
   exact finite_separable_at_of_original_coordinate_gate Ω C.1 2 htr
     p S.G T S.irreducible_G
     (regularComponent_G_mem Ω S.G T H C)
     (regularComponent_T_mem Ω S.G T H C)
     hproper hGdegree hmixZ
 obtain ⟨P⟩:=exists_adaptiveUnitProjectionFamilyYZ_of_active_nested
   flag (sharpResidualAgreementFlag (support a b s) w) base hactive hZ
   (RCN315.residualStage_pderiv_one_ne_zero_of_support S)
   S.irreducible_G hproper
   ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
   ((support_subset_flagSupport_iff
     (sharpResidualAgreementFlag (support a b s) w) T).2 hTflag)
 exact ⟨base,⟨P⟩⟩
end
end ProximityPrize.SubmissionLower.RCN049
end PackedLegacy_DU

/-! Packed from ProximityPrize.SubmissionLower.EQ. -/
section PackedLegacy_EQ
namespace ProximityPrize.SubmissionLower.RCN146
open scoped Classical BigOperators
open RCN135 RCN136 RCN231 RCN319 RCN313 RCN174 RCN238 RCN065 RCN243 RCN264 RCN159 RCN095 RCN275 RCN198 RCN203 RCN287 RCN049 RCN144 RCN063 RCN145 RCN087 RCN046 RCN265 RCN295 RCN344 RCN002
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 45000
set_option synthInstance.maxHeartbeats 300000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Ω (K:Type) [Field K]:=GenericField K
def identityCurveDegree (flag:FlagDegree) (a b s w:ℕ):ℕ:=
 flagMixed flag (paddedCut a b s (w+1)) unitZFlag+
   flagMixed flag (paddedCut a b s (w+1)) unitYZFlag
theorem mixed_padded_le_succ (flag:FlagDegree) (a b s d:ℕ) (r:FlagDegree):
   flagMixed flag (paddedCut a b s d) r ≤
     flagMixed flag (paddedCut a b s (d+1)) r:=by
 have he:paddedCut a b s (d+1)=paddedCut a b s d+
     RCN206.directionFlag a b s:=by
   change FlagDegree.mk _ _ _=FlagDegree.mk _ _ _
   congr 1 <;> simp only [paddedCut,
     RCN206.centreFlag,
     RCN206.directionFlag,
     add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all] <;> ring
 rw [he,mixed_add_second]
 exact Nat.le_add_right _ _
variable {Γ:Finset K} {x:I → K} {p e a b s:ℕ} [CharP (Ω K) p]
 {flag:FlagDegree} {w:ℕ}
theorem actual_identityCurveCountProvider
   (S:ResidualStage (polynomialEmbedding K) Γ x p e flag w (support a b s))
   (agreements:ℕ) (hnodes:S.nodes.card=agreements+e)
   (hagreement:∀ γ∈Γ,agreements≤(S.agreementFiber γ).card)
   (hwa:w<agreements)
   (hTail:S.G∣surfaceMap (polynomialEmbedding K) (numerator K S.F (w+1)))
   (bound seedCap slopeCap:ℕ) (hw:1≤w)
   (hshort:w+1≤bound) (hchar:bound<p)
   (hbox:S.F∈globalCoefficientBox K bound w seedCap slopeCap)
   (hflagChar:flag.yz+flag.all<p∧flag.all<p∧
     flag.zOnly+flag.yz+flag.all<p)
   (hmixed:(1+w*(2*(b+s+3)-2))*flag.all+
     (flag.yz+flag.all)*((2*(s+2)-1)*w)<p):
   IdentityCurveCountProvider S (identityCurveDegree flag a b s w):=by
 classical
 unfold IdentityCurveCountProvider
 intro i hi
 dsimp only
 intro hproper
 let T:=agreementPolynomial (polynomialEmbedding K) S.F w
   (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ => S.Agrees γ i)
 obtain ⟨base,⟨U⟩⟩:=exists_agreement_projection_of_caps S
   (x i) (S.u0 i) (S.u1 i) hproper hflagChar hmixed
 let cost:RegularComponent (Ω K) S.G T (regularitySurface (polynomialEmbedding K) S.F)→ℕ:=
   fun C => U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C
 refine ⟨cost,?_,?_⟩
 · intro C
   let Gc:=componentSeeds (Ω K) S.G T
     (regularitySurface (polynomialEmbedding K) S.F) Gi
     (selectedPoint (polynomialEmbedding K) S.selected) C
   have hGcGi:Gc⊆Gi:=componentSeeds_subset (Ω K) S.G T _ Gi _ C
   have hGiΓ:Gi⊆Γ:=Finset.filter_subset _ _
   have hGcΓ:Gc⊆Γ:=hGcGi.trans hGiΓ
   have hyzC:∀ W:Finset (RCN346.Place (Ω K)
       (CoordinateField (Ω K) C.1)),
       (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
         (flagSupport unitYZFlag))≤
         (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ):=by
     intro W
     change (∑ v∈W,exponentSetPoleWeight v.val (coordinate (Ω K) C.1)
       (flagSupport unitYZFlag))≤
       (coordinateDegree (Ω K) (CoordinateField (Ω K) C.1)
         (U.family.yzProjection C):ℤ)
     calc
       _=∑ v∈W,RCN346.poleOrder (Ω K)
           (CoordinateField (Ω K) C.1) v
           (coordinateValue (Ω K) (CoordinateField (Ω K) C.1)
             (U.family.yzProjection C)):=by
         apply Finset.sum_congr rfl
         intro v _
         exact U.family.yzPole_eq C v
       _ ≤ _:=finite_sum_coordinate_pole_le_degree (Ω K)
         (CoordinateField (Ω K) C.1) (U.family.yzProjection C) W
   have hprofileYZ:=coefficientPoleProfile_of_regular_agreement_curve
     S hTail (x i) (S.u0 i) (S.u1 i) hproper C
     bound seedCap slopeCap (U.family.toPrimeFlagBudgetFamily.yzCost C)
     hw hshort hchar hbox hyzC
   have hprofile:CoefficientPoleProfile (polynomialEmbedding K) C.1 S.F
       (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
       (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C) w (cost C):=by
     intro W
     exact (hprofileYZ W).trans (by
       change (U.family.toPrimeFlagBudgetFamily.yzCost C:ℤ) ≤
         ((U.family.toPrimeFlagBudgetFamily.zCost C+
           U.family.toPrimeFlagBudgetFamily.yzCost C:ℕ):ℤ)
       norm_cast
       omega)
   have hcost:1≤cost C:=
     U.one_le_zCost_add_yzCost (polynomialEmbedding K) S.F rfl S.G_dvd_surface C
   apply prime_curve_card_le_of_coefficientPoleProfile
     (polynomialEmbedding K) C.1 S.F
     (stage_surface_mem S (x i) (S.u0 i) (S.u1 i) C)
     (stage_regularity_not_mem S (x i) (S.u0 i) (S.u1 i) C)
     (base C) p w agreements e (cost C) S.characteristic_bound hwa hcost hprofile
     S.selected Gc S.nodes x S.u0 S.u1 S.x_injective hnodes
   · intro γ hγ
     exact S.degree_le γ (hGcΓ hγ)
   · intro γ hγ
     exact S.solution γ (hGcΓ hγ)
   · intro γ hγ
     exact S.regular γ (hGcΓ hγ)
   · intro γ hγ
     exact componentSeeds_on_prime (Ω K) S.G T
       (regularitySurface (polynomialEmbedding K) S.F) Gi
       (selectedPoint (polynomialEmbedding K) S.selected) C γ hγ
   · intro γ hγ
     have hΓ:=hGcΓ hγ
     simpa only [ResidualStage.agreementFiber,ResidualStage.Agrees] using
       hagreement γ hΓ
   · exact noLargeSelectedPencil_mono S.selected Γ Gc w e hGcΓ S.no_large_pencil
 · have hz:=U.family.sum_zDegree_le
   have hyz:=U.family.sum_yzDegree_le
   change (∑ C,U.family.toPrimeFlagBudgetFamily.zCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitZFlag at hz
   change (∑ C,U.family.toPrimeFlagBudgetFamily.yzCost C)≤
     flagMixed flag (sharpResidualAgreementFlag (support a b s) w) unitYZFlag at hyz
   have hz':=hz.trans (mixed_sharp_le_padded a b s w flag unitZFlag)
   have hyz':=hyz.trans (mixed_sharp_le_padded a b s w flag unitYZFlag)
   have hz'':=hz'.trans (mixed_padded_le_succ flag a b s w unitZFlag)
   have hyz'':=hyz'.trans (mixed_padded_le_succ flag a b s w unitYZFlag)
   change (∑ C,(U.family.toPrimeFlagBudgetFamily.zCost C+
     U.family.toPrimeFlagBudgetFamily.yzCost C)) ≤ identityCurveDegree flag a b s w
   rw [Finset.sum_add_distrib]
   exact Nat.add_le_add hz'' hyz''
end
end ProximityPrize.SubmissionLower.RCN146
end PackedLegacy_EQ

/-! Packed from ProximityPrize.SubmissionLower.O0. -/
section PackedLegacy_O0
namespace ProximityPrize.SubmissionLower.RCN268
open scoped Classical
open RCN223 RCN286 RCN174 RCN319 RCN135 RCN238 RCN243 RCN081 RCN222 RCN221 RCN266 RCN140 RCN159 RCN095 RCN275 RCN214
noncomputable section
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
def regularGeometricResidualStageOfSupport
   (support:ResidualSupportParameters)
   {pchar errorCap degree:ℕ} [CharP K pchar]
   (Q:MvPolynomial (Fin 4) K)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ degree)
   (hnoPencil:NoLargeSelectedPencil selected Gamma degree errorCap)
   (R:RCN266.RegularIndex Q)
   (hRirred:Irreducible R.1)
   (hRpos:0 < R.1.degreeOf (2:Fin 4))
   (hRsmall:R.1.degreeOf (2:Fin 4) < pchar)
   (hRsupport:ResidualSupportData support R.1)
   (hdegreeChar:degree < pchar)
   (g:GeometricFactor K R.1):
   letI:CharP (GenericField K) pchar:=genericField_charP K pchar
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
     x pchar errorCap (geometricFlag K g) degree support:=by
 have hsub:=regularSeeds_subset Q selected Gamma R
 exact geometricResidualStageOfSupport K support R.1 hRirred hRpos
   hRsmall hRsupport selected
   (regularSeeds Q selected Gamma R) nodes x u0 u1 hinj
   (fun gamma hgamma↦hdegree gamma (hsub hgamma))
   (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.1)
   (fun gamma hgamma↦(Finset.mem_filter.mp hgamma).2.2)
   (noLargeSelectedPencil_mono selected Gamma _ degree errorCap hsub hnoPencil)
   hdegreeChar g
def regularGeometricResidualStage
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors)
   (R:RCN266.RegularIndex Q)
   (g:GeometricFactor K R.1):
   letI:CharP (GenericField K) prime:=genericField_charP K prime
   ResidualStage (polynomialEmbedding K)
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g)
     x prime errors (geometricFlag K g) w:=by
 have hRdata:=
   directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
 have hRsmall:R.1.degreeOf (2:Fin 4) < prime:=
   (degreeOf_R_le_of_mem_box R.1 weightedCap w seedTotalCap slopeCap
     hRdata.2.2).trans_lt (by norm_num [slopeCap,prime])
 have hsupport:=residual_surface_weights_of_box K R.1 hRdata.2.2
 exact regularGeometricResidualStageOfSupport
   ResidualSupportParameters.acceptedSupport Q selected Gamma nodes x u0 u1
   hinj hdegree hnoPencil R hRdata.1 hRdata.2.1 hRsmall
   ⟨hsupport.1,hsupport.2.1,hsupport.2.2⟩
   (by norm_num [w,prime]) g
theorem regular_factor_seed_bound_of_geometric_counts
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (R:RCN266.RegularIndex Q)
   (hcount:∀ g:GeometricFactor K R.1,
     (geometricSeeds K R.1 selected (regularSeeds Q selected Gamma R) g).card*
         gap^2 ≤ factorRegularLedger (geometricFlag K g)):
   (regularSeeds Q selected Gamma R).card*gap^2 ≤
     factorRegularLedger (regularFlag Q R):=by
 obtain ⟨hRirred,_,_⟩:=
   directFactor_data Q R.1 hQ weightedCap w seedTotalCap slopeCap hbox R.2
 have hsolutions:∀ gamma∈regularSeeds Q selected Gamma R,
     specialization K (selected gamma) gamma R.1=0:=by
   intro gamma hgamma
   exact (Finset.mem_filter.mp hgamma).2.1
 simpa only [geometricFlag,regularFlag] using
   original_regular_seed_bound_of_geometric_factor_counts K R.1 hRirred
     selected (regularSeeds Q selected Gamma R) hsolutions hcount
end
end ProximityPrize.SubmissionLower.RCN268
end PackedLegacy_O0

/-! Packed from ProximityPrize.SubmissionLower.FQ. -/
section PackedLegacy_FQ
namespace ProximityPrize.SubmissionLower.RCN239
open scoped Classical BigOperators
open RCN174 RCN319 RCN286 RCN167 RCN169 RCN290 RCN238 RCN266 RCN095 RCN140 RCN291 RCN318 RCN292 RCN276
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 40000
structure FixedParameterAlignment (p:Profile)
   (t:RCN318.TightParameters):Prop where
 n:t.n=p.n
 w:t.w=p.w
 agreements:t.a=p.agreements
 weightedCap:t.D=p.weightedCap
 seedTotalCap:t.L=p.seedTotalCap
 slopeCap:t.s=p.slopeCap
namespace FixedParameterAlignment
theorem errors {p:Profile}
   {t:RCN318.TightParameters}
   (A:FixedParameterAlignment p t):t.errors=p.errors:=by
 simp only [RCN318.TightParameters.errors,
   Profile.errors,A.n,A.agreements]
theorem gap {p:Profile}
   {t:RCN318.TightParameters}
   (A:FixedParameterAlignment p t):t.gap=p.gap:=by
 simp only [RCN318.TightParameters.gap,
   Profile.gap,A.w,A.agreements]
end FixedParameterAlignment
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem card_le_regular_sum_add_singular
   (p:Profile) {prime:ℕ}
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (hs:1 ≤ p.slopeCap) (hsSmall:p.slopeCap < prime)
   (hw:1 ≤ p.w)
   (hDw:p.w < (2*p.slopeCap-1)*p.weightedCap)
   (hj:1 ≤ (2*p.slopeCap-1)*p.seedTotalCap)
   (hjSmall:(2*p.slopeCap-1)*p.seedTotalCap < prime)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0):
   Gamma.card ≤
     (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ
   p.weightedCap p.w p.seedTotalCap p.slopeCap prime
   hs hsSmall hw hDw hj hjSmall hbox Gamma selected hsolution
 let regularUnion:=Finset.univ.biUnion (regularSeeds Q selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   by_cases hexc:gamma∈
       exceptionalSeeds (singularAuxiliary Q) Gamma selected
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     right
     exact hexc
   · obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩:=
       hdecomp.2.1 gamma hgamma hexc
     · apply Finset.mem_union.mpr
       left
       apply Finset.mem_biUnion.mpr
       exact ⟨⟨F,hF⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,hreg⟩⟩
     · apply Finset.mem_union.mpr
       right
       apply Finset.mem_union.mpr
       left
       apply Finset.mem_biUnion.mpr
       exact ⟨⟨q,hq⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
theorem global_count_le_regular_div_add_tight_countCap
   (p:Profile)
   (t:RCN318.TightParameters)
   (A:FixedParameterAlignment p t)
   {prime regularNumerator:ℕ}
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (hs:1 ≤ p.slopeCap) (hsSmall:p.slopeCap < prime)
   (hw:1 ≤ p.w) (hchar:p.w < prime)
   (hDw:p.w < (2*p.slopeCap-1)*p.weightedCap)
   (hj:1 ≤ (2*p.slopeCap-1)*p.seedTotalCap)
   (hjSmall:(2*p.slopeCap-1)*p.seedTotalCap < prime)
   (hjYSmall:t.implicitYCap < prime)
   (hmixedSmall:2*t.implicitYCap*t.algebraicCap < prime)
   (hwa:p.w < p.agreements) (han:p.agreements ≤ p.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=p.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ p.w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     p.agreements ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma p.w p.errors)
   (regularFlagFor:RegularIndex Q → FlagDegree)
   (regularLedger:FlagDegree → ℕ)
   (hregularAggregate:
     ∀ count:RegularIndex Q → ℕ,
       (∀ F,count F*p.gap^2 ≤ regularLedger (regularFlagFor F)) →
       (∑ F,count F)*p.gap^2 ≤ regularNumerator)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*p.gap^2 ≤
       regularLedger (regularFlagFor F)):
   Gamma.card ≤ regularNumerator/p.gap^2+t.countCap:=by
 have hcover:=card_le_regular_sum_add_singular p Q hQ hbox
   hs hsSmall hw hDw hj hjSmall selected Gamma hsolution
 have hreg:=hregularAggregate
   (fun F:RegularIndex Q↦(regularSeeds Q selected Gamma F).card)
   hregular
 have hboxT:Q∈globalCoefficientBox K t.D t.w t.L t.s:=by
   simpa only [A.weightedCap,A.w,A.seedTotalCap,A.slopeCap] using hbox
 have hsing:=
   RCN292.TightParameters.singularSeeds_tight_gap_bound
     t Q hQ hboxT
   (by simpa only [A.slopeCap] using hs)
   (by simpa only [A.slopeCap] using hsSmall)
   (by simpa only [A.w] using hw)
   (by simpa only [A.w] using hchar)
   (by
     simpa only [RCN318.TightParameters.kappa,
       A.w,A.weightedCap,A.slopeCap]
       using hDw)
   (by simpa only
     [RCN318.TightParameters.algebraicCap,
       RCN318.TightParameters.kappa,
       A.seedTotalCap,A.slopeCap] using hj)
   hjYSmall
   (by simpa only
     [RCN318.TightParameters.algebraicCap,
       RCN318.TightParameters.kappa,
       A.seedTotalCap,A.slopeCap] using hjSmall)
   hmixedSmall
   (by simpa only [A.w,A.agreements] using hwa)
   (by simpa only [A.agreements,A.n] using han)
   selected Gamma nodes x u0 u1 hinj
   (by simpa only [A.n] using hnodes)
   (by simpa only [A.w] using hdegree)
   (by simpa only [A.agreements] using hagreement)
   (by simpa only [A.w,A.errors] using hnoPencil)
 have hpgap:0 < p.gap:=by
   simpa only [Profile.gap] using Nat.sub_pos_of_lt hwa
 have htgap:0 < t.gap:=by simpa only [A.gap] using hpgap
 have hregCount:
     (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card) ≤
       regularNumerator/p.gap^2:=
   (Nat.le_div_iff_mul_le (pow_pos hpgap 2)).2 hreg
 have hsingCount:(singularSeeds Q selected Gamma).card ≤ t.countCap:=
   t.count_le_countCap _ htgap hsing
 exact hcover.trans (Nat.add_le_add hregCount hsingCount)
end
end ProximityPrize.SubmissionLower.RCN239
end PackedLegacy_FQ

/-! Packed from ProximityPrize.SubmissionLower.AB. -/
section PackedLegacy_AB
namespace ProximityPrize.SubmissionLower.RCN259
noncomputable section
section Quotients
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def leftGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_left a b)
def rightGCDQuotient (a b:A):A:=Classical.choose (gcd_dvd_right a b)
theorem left_eq_gcd_mul_leftGCDQuotient (a b:A):
   a=gcd a b*leftGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_left a b)
theorem right_eq_gcd_mul_rightGCDQuotient (a b:A):
   b=gcd a b*rightGCDQuotient a b:=
 Classical.choose_spec (gcd_dvd_right a b)
theorem gcdQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (leftGCDQuotient a b) (rightGCDQuotient a b):=by
 intro d hdleft hdright
 have hg:gcd a b≠0:=gcd_ne_zero_of_left ha
 have hda:gcd a b*d∣a:=by
   calc
     gcd a b*d∣gcd a b*leftGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdleft
     _=a:=(left_eq_gcd_mul_leftGCDQuotient a b).symm
 have hdb:gcd a b*d∣b:=by
   calc
     gcd a b*d∣gcd a b*rightGCDQuotient a b:=
       mul_dvd_mul_left (gcd a b) hdright
     _=b:=(right_eq_gcd_mul_rightGCDQuotient a b).symm
 have hdg:gcd a b*d∣gcd a b:=dvd_gcd hda hdb
 apply isUnit_iff_dvd_one.mpr
 apply (mul_dvd_mul_iff_left hg).mp
 simpa only [mul_one] using hdg
end Quotients
section RecursiveDefinitions
variable {A:Type*} [CommMonoidWithZero A] [GCDMonoid A]
def gcd12 (a b:A):A:=gcd a b
def gcd123 (a b c:A):A:=gcd (gcd12 a b) c
def quotientA (a b:A):A:=leftGCDQuotient a b
def quotientB (a b:A):A:=rightGCDQuotient a b
def middleQuotient (a b c:A):A:=leftGCDQuotient (gcd12 a b) c
def quotientC (a b c:A):A:=rightGCDQuotient (gcd12 a b) c
theorem a_eq_gcd12_mul_quotientA (a b:A):
   a=gcd12 a b*quotientA a b:=
 left_eq_gcd_mul_leftGCDQuotient a b
theorem b_eq_gcd12_mul_quotientB (a b:A):
   b=gcd12 a b*quotientB a b:=
 right_eq_gcd_mul_rightGCDQuotient a b
theorem gcd12_eq_gcd123_mul_middleQuotient (a b c:A):
   gcd12 a b=gcd123 a b c*middleQuotient a b c:=
 left_eq_gcd_mul_leftGCDQuotient (gcd12 a b) c
theorem c_eq_gcd123_mul_quotientC (a b c:A):
   c=gcd123 a b c*quotientC a b c:=
 right_eq_gcd_mul_rightGCDQuotient (gcd12 a b) c
theorem firstQuotients_isRelPrime {a b:A} (ha:a≠0):
   IsRelPrime (quotientA a b) (quotientB a b):=
 gcdQuotients_isRelPrime ha
theorem secondQuotients_isRelPrime {a b c:A} (ha:a≠0):
   IsRelPrime (middleQuotient a b c) (quotientC a b c):=
 gcdQuotients_isRelPrime (gcd_ne_zero_of_left ha)
end RecursiveDefinitions
section Normalization
variable {A:Type*} [CommMonoidWithZero A] [NormalizedGCDMonoid A]
theorem gcd12_normalized (a b:A):normalize (gcd12 a b)=gcd12 a b:=
 normalize_gcd a b
theorem gcd123_normalized (a b c:A):
   normalize (gcd123 a b c)=gcd123 a b c:=
 normalize_gcd (gcd12 a b) c
end Normalization
section ThreeBranchCover
variable {A B:Type*} [CommRing A] [GCDMonoid A]
 [CommRing B] [IsDomain B]
theorem recursive_three_branch_cover
   (phi:A →+*B) (a b c:A)
   (ha:phi a=0) (hb:phi b=0) (hc:phi c=0):
   (phi (gcd12 a b)≠0∧
       phi (quotientA a b)=0∧phi (quotientB a b)=0)∨
     (phi (gcd12 a b)=0∧phi (gcd123 a b c)≠0∧
       phi (middleQuotient a b c)=0∧phi (quotientC a b c)=0)∨
     (phi (gcd123 a b c)=0∧phi (gcd12 a b)=0):=by
 rcases eq_or_ne (phi (gcd12 a b)) 0 with h12 | h12
 · rcases eq_or_ne (phi (gcd123 a b c)) 0 with h123 | h123
   · exact Or.inr (Or.inr ⟨h123,h12⟩)
   · have hm:phi (middleQuotient a b c)=0:=by
       rw [gcd12_eq_gcd123_mul_middleQuotient,map_mul] at h12
       exact (mul_eq_zero.mp h12).resolve_left h123
     have hqC:phi (quotientC a b c)=0:=by
       rw [c_eq_gcd123_mul_quotientC a b c,map_mul] at hc
       exact (mul_eq_zero.mp hc).resolve_left h123
     exact Or.inr (Or.inl ⟨h12,h123,hm,hqC⟩)
 · have hqA:phi (quotientA a b)=0:=by
     rw [a_eq_gcd12_mul_quotientA a b,map_mul] at ha
     exact (mul_eq_zero.mp ha).resolve_left h12
   have hqB:phi (quotientB a b)=0:=by
     rw [b_eq_gcd12_mul_quotientB a b,map_mul] at hb
     exact (mul_eq_zero.mp hb).resolve_left h12
   exact Or.inl ⟨h12,hqA,hqB⟩
end ThreeBranchCover
end
end ProximityPrize.SubmissionLower.RCN259
end PackedLegacy_AB

/-! Packed from ProximityPrize.SubmissionLower.L3. -/
section PackedLegacy_L3
namespace ProximityPrize.SubmissionLower.RCN182
open ProximityPrize.Benchmark RCN174 RCN256 RCN319
noncomputable section
variable (K:Type*) [Field K]
theorem block_equations_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:Fin m),
     contactJet K (m-r.val)
       ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
         Poly K)=0:=by
 intro i r
 have hzero:constraintMap K D w L s m nodes u0 u1 theta=0:=
   LinearMap.mem_ker.mp htheta
 have happ:=congrArg
   (fun target:GlobalTarget K I m L s => ((target i r):Poly K)) hzero
 change contactJet K (m-r.val)
   ((extractBlock K D w L s (nodes i) (u0 i) (u1 i) r.val theta):
     Poly K)=0 at happ
 exact happ
theorem translated_contact_of_mem_ker
   {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1)):
   ∀ (i:I) (r:ℕ),
     slopeDifference K^(m-r)∣
       (homogenizedTranslation K (nodes i) (u0 i) (u1 i)
         (reconstruct K D w L s theta)).coeff r:=by
 intro i r
 rw [translation_reconstruct_coeff]
 exact all_blocks_divisible_of_equations K D w L s m
   (nodes i) (u0 i) (u1 i) theta
   (block_equations_of_mem_ker K D w L s m nodes u0 u1 theta htheta i) r
theorem specialization_eq_zero_of_mem_ker
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hD:0 < D) (hP:P.natDegree ≤ w)
   (hcapacity:D ≤ m*support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_contact_and_degree K
   (reconstruct K D w L s theta) P gamma nodes u0 u1 support m
 · intro i hi r
   exact translated_contact_of_mem_ker K D w L s m nodes u0 u1 theta
     htheta i r
 · exact hvalues
 · have hdegree:=specialization_natDegree_lt K D w L s
     (reconstruct K D w L s theta) P gamma hD
     (reconstruct_mem_globalCoefficientBox K D w L s theta) hP
   exact hdegree.trans_le hcapacity
theorem specialization_eq_zero_of_agreements
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a)
   (P:Polynomial K) (gamma:K) (support:Finset I)
   (hP:P.natDegree ≤ w) (hcard:a ≤ support.card)
   (hvalues:∀ i∈support,
     P.eval (nodes i)=u0 i+gamma*u1 i):
   specialization K P gamma (reconstruct K D w L s theta)=0:=by
 apply specialization_eq_zero_of_mem_ker K D w L s m nodes u0 u1 theta
   htheta P gamma support hD hP
 · rw [hDa]
   exact Nat.mul_le_mul_left m hcard
 · exact hvalues
theorem nonzero_kernel_member_universal
   [DecidableEq K] {I:Type*} [Fintype I] [DecidableEq I]
   (D w L s m a:ℕ) (nodes:I ↪ K) (u0 u1:I → K)
   (theta:CoefficientIndex D w L s → K)
   (htheta0:theta≠0)
   (htheta:theta∈LinearMap.ker
     (constraintMap K D w L s m nodes u0 u1))
   (hD:0 < D) (hDa:D=m*a):
   reconstruct K D w L s theta≠0∧
     reconstruct K D w L s theta∈globalCoefficientBox K D w L s∧
     ∀ (gamma:K) (P:Polynomial K) (support:Finset I),
       P.natDegree ≤ w → a ≤ support.card →
       (∀ i∈support,
         P.eval (nodes i)=u0 i+gamma*u1 i) →
       specialization K P gamma (reconstruct K D w L s theta)=0:=by
 refine ⟨reconstruct_ne_zero K D w L s theta htheta0,
   reconstruct_mem_globalCoefficientBox K D w L s theta,?_⟩
 intro gamma P support hP hcard hvalues
 exact specialization_eq_zero_of_agreements K D w L s m a nodes u0 u1
   theta htheta hD hDa P gamma support hP hcard hvalues
end
end ProximityPrize.SubmissionLower.RCN182
end PackedLegacy_L3

/-! Packed from ProximityPrize.SubmissionLower.GF. -/
section PackedLegacy_GF
namespace ProximityPrize.SubmissionLower.RCN300
open ProximityPrize.Benchmark RCN174 RCN256 RCN319 RCN182 RCN301
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
theorem exists_stacked_universal_vanishing_interpolants
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ QA QB QC:MvPolynomial (Fin 4) IRSProfile.Field,
     QA≠0∧
     QA∈globalCoefficientBox IRSProfile.Field
       (25*agreements) w 5263 7∧
     QB≠0∧
     QB∈globalCoefficientBox IRSProfile.Field
       (47*agreements) w 598 14∧
     QC≠0∧
     QC∈globalCoefficientBox IRSProfile.Field
       (27*agreements) w 579299 6∧
     ∀ (gamma:IRSProfile.Field) (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,
         P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
       specialization IRSProfile.Field P gamma QA=0∧
       specialization IRSProfile.Field P gamma QB=0∧
       specialization IRSProfile.Field P gamma QC=0:=by
 have hgateA:Fintype.card IRSProfile.Index*localRankBound 25 5263 7 <
     coefficientCount (25*agreements) w 5263 7:=by
   rw [show Fintype.card IRSProfile.Index=n by norm_num [IRSProfile.Index,n]]
   change profileA.totalRank < profileA.coefficients
   exact interpolation_gates.1
 have hgateB:Fintype.card IRSProfile.Index*localRankBound 47 598 14 <
     coefficientCount (47*agreements) w 598 14:=by
   rw [show Fintype.card IRSProfile.Index=n by norm_num [IRSProfile.Index,n]]
   change profileB.totalRank < profileB.coefficients
   exact interpolation_gates.2.1
 have hgateC:Fintype.card IRSProfile.Index*localRankBound 27 579299 6 <
     coefficientCount (27*agreements) w 579299 6:=by
   rw [show Fintype.card IRSProfile.Index=n by norm_num [IRSProfile.Index,n]]
   change profileC.totalRank < profileC.coefficients
   exact interpolation_gates.2.2
 obtain ⟨thetaA,hthetaA,hkernelA⟩:=exists_nonzero_kernel_array
   IRSProfile.Field (25*agreements) w 5263 7 25 IRSProfile.domain u0 u1 hgateA
 obtain ⟨thetaB,hthetaB,hkernelB⟩:=exists_nonzero_kernel_array
   IRSProfile.Field (47*agreements) w 598 14 47 IRSProfile.domain u0 u1 hgateB
 obtain ⟨thetaC,hthetaC,hkernelC⟩:=exists_nonzero_kernel_array
   IRSProfile.Field (27*agreements) w 579299 6 27 IRSProfile.domain u0 u1 hgateC
 have hDA:0 < 25*agreements:=by norm_num [agreements]
 have hDB:0 < 47*agreements:=by norm_num [agreements]
 have hDC:0 < 27*agreements:=by norm_num [agreements]
 have hA:=nonzero_kernel_member_universal IRSProfile.Field
   (25*agreements) w 5263 7 25 agreements IRSProfile.domain u0 u1 thetaA
   hthetaA (LinearMap.mem_ker.mpr hkernelA) hDA rfl
 have hB:=nonzero_kernel_member_universal IRSProfile.Field
   (47*agreements) w 598 14 47 agreements IRSProfile.domain u0 u1 thetaB
   hthetaB (LinearMap.mem_ker.mpr hkernelB) hDB rfl
 have hC:=nonzero_kernel_member_universal IRSProfile.Field
   (27*agreements) w 579299 6 27 agreements IRSProfile.domain u0 u1 thetaC
   hthetaC (LinearMap.mem_ker.mpr hkernelC) hDC rfl
 refine ⟨reconstruct IRSProfile.Field (25*agreements) w 5263 7 thetaA,
   reconstruct IRSProfile.Field (47*agreements) w 598 14 thetaB,
   reconstruct IRSProfile.Field (27*agreements) w 579299 6 thetaC,
   hA.1,hA.2.1,hB.1,hB.2.1,hC.1,hC.2.1,?_⟩
 intro gamma P support hP hcard hvalues
 exact ⟨hA.2.2 gamma P support hP hcard hvalues,
   hB.2.2 gamma P support hP hcard hvalues,
   hC.2.2 gamma P support hP hcard hvalues⟩
end
end ProximityPrize.SubmissionLower.RCN300
end PackedLegacy_GF

/-! Packed from ProximityPrize.SubmissionLower.GD. -/
section PackedLegacy_GD
namespace ProximityPrize.SubmissionLower.RCN299
open ProximityPrize.Benchmark RCN174 RCN319 RCN259 RCN301 RCN300
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def RecursiveSpecializationBranch
   (P:Polynomial IRSProfile.Field) (gamma:IRSProfile.Field)
   (QA QB QC:GlobalPoly):Prop:=
 let phi:=(specialization IRSProfile.Field P gamma).toRingHom
 (phi (gcd12 QA QB)≠0∧
     phi (quotientA QA QB)=0∧phi (quotientB QA QB)=0)∨
   (phi (gcd12 QA QB)=0∧phi (gcd123 QA QB QC)≠0∧
     phi (middleQuotient QA QB QC)=0∧
     phi (quotientC QA QB QC)=0)∨
   (phi (gcd123 QA QB QC)=0∧phi (gcd12 QA QB)=0)
theorem recursive_branch_of_three_vanishings
   (P:Polynomial IRSProfile.Field) (gamma:IRSProfile.Field)
   (QA QB QC:GlobalPoly)
   (hA:specialization IRSProfile.Field P gamma QA=0)
   (hB:specialization IRSProfile.Field P gamma QB=0)
   (hC:specialization IRSProfile.Field P gamma QC=0):
   RecursiveSpecializationBranch P gamma QA QB QC:=by
 exact recursive_three_branch_cover
   (specialization IRSProfile.Field P gamma).toRingHom QA QB QC hA hB hC
theorem exists_stacked_interpolants_with_recursive_cover
   (u0 u1:IRSProfile.Index → IRSProfile.Field):
   ∃ QA QB QC:GlobalPoly,
     QA≠0∧
     QA∈globalCoefficientBox IRSProfile.Field
       (25*agreements) w 5263 7∧
     QB≠0∧
     QB∈globalCoefficientBox IRSProfile.Field
       (47*agreements) w 598 14∧
     QC≠0∧
     QC∈globalCoefficientBox IRSProfile.Field
       (27*agreements) w 579299 6∧
     ∀ (gamma:IRSProfile.Field) (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,
         P.eval (IRSProfile.domain i)=u0 i+gamma*u1 i) →
       RecursiveSpecializationBranch P gamma QA QB QC:=by
 obtain ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,huniversal⟩:=
   exists_stacked_universal_vanishing_interpolants u0 u1
 refine ⟨QA,QB,QC,hQA,hboxA,hQB,hboxB,hQC,hboxC,?_⟩
 intro gamma P support hP hcard hvalues
 obtain ⟨hA,hB,hC⟩:=huniversal gamma P support hP hcard hvalues
 exact recursive_branch_of_three_vanishings P gamma QA QB QC hA hB hC
end
end ProximityPrize.SubmissionLower.RCN299
end PackedLegacy_GD

/-! Packed from ProximityPrize.SubmissionLower.CC. -/
section PackedLegacy_CC
namespace ProximityPrize.SubmissionLower.RCN304
open ProximityPrize.Benchmark RCN319 RCN259 RCN299
noncomputable section
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq (Polynomial IRSProfile.Field):=Classical.decEq _
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
def gcd12Vanishes
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (QA QB:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
 specialization IRSProfile.Field (selected gamma) gamma (gcd12 QA QB)=0
def gcd123Vanishes
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (QA QB QC:GlobalPoly) (gamma:IRSProfile.Field):Prop:=
 specialization IRSProfile.Field (selected gamma) gamma (gcd123 QA QB QC)=0
def firstResidualSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB:GlobalPoly):
   Finset IRSProfile.Field:=by
 classical
 exact Gamma.filter (fun gamma↦¬ gcd12Vanishes selected QA QB gamma)
def secondResidualSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   Finset IRSProfile.Field:=by
 classical
 exact (Gamma.filter (gcd12Vanishes selected QA QB)).filter
   (fun gamma↦¬ gcd123Vanishes selected QA QB QC gamma)
def fixedSeeds
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   Finset IRSProfile.Field:=by
 classical
 exact (Gamma.filter (gcd12Vanishes selected QA QB)).filter
   (gcd123Vanishes selected QA QB QC)
theorem partition_card
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   (firstResidualSeeds selected Gamma QA QB).card+
     (secondResidualSeeds selected Gamma QA QB QC).card+
     (fixedSeeds selected Gamma QA QB QC).card=Gamma.card:=by
 classical
 have houter:=Finset.card_filter_add_card_filter_not
   (s:=Gamma) (gcd12Vanishes selected QA QB)
 have hinner:=Finset.card_filter_add_card_filter_not
   (s:=Gamma.filter (gcd12Vanishes selected QA QB))
   (gcd123Vanishes selected QA QB QC)
 simp only [firstResidualSeeds,secondResidualSeeds,fixedSeeds]
 change
   (Gamma.filter (fun gamma↦¬ gcd12Vanishes selected QA QB gamma)).card+
     ((Gamma.filter (gcd12Vanishes selected QA QB)).filter
       (fun gamma↦¬ gcd123Vanishes selected QA QB QC gamma)).card+
     ((Gamma.filter (gcd12Vanishes selected QA QB)).filter
       (gcd123Vanishes selected QA QB QC)).card=Gamma.card
 omega
theorem firstResidualSeeds_quotient_vanish
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC):
   ∀ gamma∈firstResidualSeeds selected Gamma QA QB,
     specialization IRSProfile.Field (selected gamma) gamma
         (quotientA QA QB)=0∧
       specialization IRSProfile.Field (selected gamma) gamma
         (quotientB QA QB)=0:=by
 classical
 intro gamma hgamma
 rw [firstResidualSeeds] at hgamma
 have hm:=Finset.mem_filter.mp hgamma
 have hbranch:=hcover gamma hm.1
 rcases hbranch with hfirst | hsecond | hfixed
 · exact hfirst.2
 · exact False.elim (hm.2 hsecond.1)
 · exact False.elim (hm.2 hfixed.2)
theorem secondResidualSeeds_quotient_vanish
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC):
   ∀ gamma∈secondResidualSeeds selected Gamma QA QB QC,
     specialization IRSProfile.Field (selected gamma) gamma
         (middleQuotient QA QB QC)=0∧
       specialization IRSProfile.Field (selected gamma) gamma
         (quotientC QA QB QC)=0:=by
 classical
 intro gamma hgamma
 rw [secondResidualSeeds] at hgamma
 have hmOuter:=Finset.mem_filter.mp hgamma
 have hmInner:=Finset.mem_filter.mp hmOuter.1
 have hbranch:=hcover gamma hmInner.1
 rcases hbranch with hfirst | hsecond | hfixed
 · exact False.elim (hfirst.1 hmInner.2)
 · exact hsecond.2.2
 · exact False.elim (hmOuter.2 hfixed.1)
theorem fixedSeeds_vanish
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field) (QA QB QC:GlobalPoly):
   ∀ gamma∈fixedSeeds selected Gamma QA QB QC,
     specialization IRSProfile.Field (selected gamma) gamma
       (gcd123 QA QB QC)=0:=by
 classical
 intro gamma hgamma
 rw [fixedSeeds] at hgamma
 exact (Finset.mem_filter.mp hgamma).2
end
end ProximityPrize.SubmissionLower.RCN304
end PackedLegacy_CC

/-! Packed from ProximityPrize.SubmissionLower.GC. -/
section PackedLegacy_GC
namespace ProximityPrize.SubmissionLower.RCN298
open ProximityPrize.Benchmark RCN174 RCN081 RCN259 RCN301
noncomputable section
abbrev GlobalPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid GlobalPoly:=
 UniqueFactorizationMonoid.toGCDMonoid GlobalPoly
theorem gcd12_ne_zero {A B:GlobalPoly} (hA:A≠0):
   gcd12 A B≠0:=
 gcd_ne_zero_of_left hA
theorem gcd123_ne_zero {A B C:GlobalPoly} (hA:A≠0):
   gcd123 A B C≠0:=
 gcd_ne_zero_of_left (gcd12_ne_zero hA)
theorem quotientA_dvd_left (A B:GlobalPoly):quotientA A B∣A:=by
 refine ⟨gcd12 A B,?_⟩
 simpa only [mul_comm] using a_eq_gcd12_mul_quotientA A B
theorem quotientB_dvd_right (A B:GlobalPoly):quotientB A B∣B:=by
 refine ⟨gcd12 A B,?_⟩
 simpa only [mul_comm] using b_eq_gcd12_mul_quotientB A B
theorem middleQuotient_dvd_gcd12 (A B C:GlobalPoly):
   middleQuotient A B C∣gcd12 A B:=by
 refine ⟨gcd123 A B C,?_⟩
 simpa only [mul_comm] using gcd12_eq_gcd123_mul_middleQuotient A B C
theorem quotientC_dvd_right (A B C:GlobalPoly):quotientC A B C∣C:=by
 refine ⟨gcd123 A B C,?_⟩
 simpa only [mul_comm] using c_eq_gcd123_mul_quotientC A B C
theorem gcd12_mem_meet_box
   (A B:GlobalPoly) (hA:A≠0) (hB:B≠0)
   (hboxA:A∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 5263 7)
   (hboxB:B∈globalCoefficientBox IRSProfile.Field
     (47*agreements) w 598 14):
   gcd12 A B∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 598 7:=by
 have hfromA:=mem_globalCoefficientBox_of_dvd (gcd12 A B) A
   (25*agreements) w 5263 7 hA (gcd_dvd_left A B) hboxA
 have hfromB:=mem_globalCoefficientBox_of_dvd (gcd12 A B) B
   (47*agreements) w 598 14 hB (gcd_dvd_right A B) hboxB
 intro d hd
 exact ⟨(hfromB hd).1,(hfromA hd).2.1,(hfromA hd).2.2⟩
theorem gcd123_mem_meet_box
   (A B C:GlobalPoly) (hA:A≠0) (hC:C≠0)
   (hbox12:gcd12 A B∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 598 7)
   (hboxC:C∈globalCoefficientBox IRSProfile.Field
     (27*agreements) w 579299 6):
   gcd123 A B C∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 598 6:=by
 have h12:=gcd12_ne_zero (B:=B) hA
 have hfrom12:=mem_globalCoefficientBox_of_dvd (gcd123 A B C) (gcd12 A B)
   (25*agreements) w 598 7 h12 (gcd_dvd_left (gcd12 A B) C) hbox12
 have hfromC:=mem_globalCoefficientBox_of_dvd (gcd123 A B C) C
   (27*agreements) w 579299 6 hC (gcd_dvd_right (gcd12 A B) C) hboxC
 intro d hd
 exact ⟨(hfrom12 hd).1,(hfromC hd).2.1,(hfrom12 hd).2.2⟩
theorem quotientA_mem_parent_box
   (A B:GlobalPoly) (hA:A≠0)
   (hboxA:A∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 5263 7):
   quotientA A B∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 5263 7:=
 mem_globalCoefficientBox_of_dvd (quotientA A B) A
   (25*agreements) w 5263 7 hA (quotientA_dvd_left A B) hboxA
theorem quotientB_mem_parent_box
   (A B:GlobalPoly) (hB:B≠0)
   (hboxB:B∈globalCoefficientBox IRSProfile.Field
     (47*agreements) w 598 14):
   quotientB A B∈globalCoefficientBox IRSProfile.Field
     (47*agreements) w 598 14:=
 mem_globalCoefficientBox_of_dvd (quotientB A B) B
   (47*agreements) w 598 14 hB (quotientB_dvd_right A B) hboxB
theorem middleQuotient_mem_parent_box
   (A B C:GlobalPoly) (hA:A≠0)
   (hbox12:gcd12 A B∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 598 7):
   middleQuotient A B C∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 598 7:=
 mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
   (25*agreements) w 598 7 (gcd12_ne_zero (B:=B) hA)
   (middleQuotient_dvd_gcd12 A B C) hbox12
theorem quotientC_mem_parent_box
   (A B C:GlobalPoly) (hC:C≠0)
   (hboxC:C∈globalCoefficientBox IRSProfile.Field
     (27*agreements) w 579299 6):
   quotientC A B C∈globalCoefficientBox IRSProfile.Field
     (27*agreements) w 579299 6:=
 mem_globalCoefficientBox_of_dvd (quotientC A B C) C
   (27*agreements) w 579299 6 hC (quotientC_dvd_right A B C) hboxC
end
end ProximityPrize.SubmissionLower.RCN298
end PackedLegacy_GC

/-! Packed from ProximityPrize.SubmissionLower.GH. -/
section PackedLegacy_GH
namespace ProximityPrize.SubmissionLower.RCN303
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN174 RCN319 RCN081 RCN238 RCN243 RCN259 RCN301 RCN299 RCN304 RCN298 RCN260 RCN318 RCN294 RCN291 RCN292 RCN052
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 35000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
abbrev StackedPoly:=MvPolynomial (Fin 4) IRSProfile.Field
local instance:GCDMonoid StackedPoly:=
 UniqueFactorizationMonoid.toGCDMonoid StackedPoly
local instance:CharP IRSProfile.Field prime:=by
 simpa [prime,RCN223.prime] using
   RCN128.challenge_field_characteristic6600
def firstResidualQ2Stage:UnequalParameters:=
 ⟨262144,131071,182807,65,14,598,34,7,5263⟩
def firstResidualQ2Ceiling:ℕ:=66773536747163
def secondResidualGcd12Ceiling:ℕ:=370003897865012
theorem optimized_residual_cell_values:
   firstResidualQ2Stage.agreement=⟨17039231,3538917,1379653347⟩∧
     firstResidualQ2Stage.mixedCost=⟨77868,362427,931⟩∧
     firstResidualQ2Stage.regularCountCap=9865174615710∧
     firstResidualQ2Stage.regularCountCap+firstResidualQ2.countCap+1=
       firstResidualQ2Ceiling∧
     residualStageTwo.regularCountCap+secondResidualGcd12.countCap+1=
       secondResidualGcd12Ceiling:=by
 norm_num [firstResidualQ2Stage,firstResidualQ2Ceiling,
   secondResidualGcd12Ceiling,firstResidualQ2,secondResidualGcd12,
   UnequalParameters.agreement,UnequalParameters.leftAgreement,
   UnequalParameters.rightAgreement,UnequalParameters.mixedCost,
   UnequalParameters.regularCountCap,UnequalParameters.regularNumerator,
   UnequalParameters.errors,UnequalParameters.gap,
   TightParameters.countCap,TightParameters.tightNumerator,
   TightParameters.coreNumerator,TightParameters.aggregateCost,
   TightParameters.agreement,TightParameters.implicitYCap,
   TightParameters.algebraicCap,TightParameters.kappa,
   TightParameters.errors,TightParameters.gap,residualStageTwo,dot]
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem asymmetric_stage_count_lt_of_regular_factors
   (P:UnequalParameters)
   (S:RCN318.TightParameters)
   (Q T:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (p:ℕ) [CharP K p]
   (hs:1 ≤ S.s) (hsmall:S.s < p) (hw:1 ≤ S.w)
   (hchar:S.w < p) (hDw:S.w < S.kappa*S.D)
   (hj:1 ≤ S.algebraicCap)
   (hjYSmall:S.implicitYCap < p)
   (hjZSmall:S.algebraicCap < p)
   (hmixedSmall:2*S.implicitYCap*S.algebraicCap < p)
   (hwa:S.w < S.a) (han:S.a ≤ S.n)
   (hbox:Q∈globalCoefficientBox K S.D S.w S.L S.s)
   (hgap:0 < P.gap) (_hgapEq:S.gap=P.gap)
   (hY:(S.D-1)/S.w ≤ P.leftY)
   (hR:S.s ≤ P.leftR) (hZ:S.L ≤ P.leftZ)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=S.n)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ S.w)
   (hQsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hTsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma T=0)
   (hagreement:∀ gamma∈Gamma,
     S.a ≤ (nodes.filter (fun i =>
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma S.w S.errors)
   (hregular:∀ F:RCN052.RegularIndex Q,
     (regularPairSeeds Q T selected Gamma F).card*P.gap ≤
       (P.n-P.w)*dot P.agreement (regularVector P F.1)+
         (P.errors+1)*P.gap*(regularVector P F.1).z):
   Gamma.card < P.regularCountCap+S.countCap+1:=by
 classical
 have hcover:=card_le_regular_sum_add_singular Q T hQ
   S.D S.w S.L S.s p hs hsmall hw hDw hj hjZSmall hbox
   selected Gamma hQsolution hTsolution
 have hregularScaled:=sum_regular_counts_bound P Q T selected Gamma
   (regularVector_budgets P Q hQ S.D S.w S.L S.s (by omega) hbox hY hR hZ)
   hregular
 have hregularCap:
     (∑ F:RCN052.RegularIndex Q,
       (regularPairSeeds Q T selected Gamma F).card) ≤ P.regularCountCap:=
   P.regular_count_le _ hgap hregularScaled
 have hsingularOld:=
   RCN292.TightParameters.singularSeeds_count_le_countCap
     S Q hQ hbox hs hsmall hw hchar hDw hj hjYSmall hjZSmall hmixedSmall
     hwa han selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
     hnoPencil
 have hsingular:
     (RCN052.singularSeeds Q selected Gamma).card ≤
       S.countCap:=by
   change (RCN291.singularSeeds Q selected Gamma).card ≤
     S.countCap
   exact hsingularOld
 omega
theorem quotientB_ne_zero
   (QA QB:StackedPoly) (hQB:QB≠0):quotientB QA QB≠0:=by
 intro hz
 apply hQB
 rw [b_eq_gcd12_mul_quotientB QA QB,hz,mul_zero]
theorem middleQuotient_ne_zero
   (QA QB QC:StackedPoly) (hQA:QA≠0):
   middleQuotient QA QB QC≠0:=by
 intro hz
 apply gcd12_ne_zero (B:=QB) hQA
 rw [gcd12_eq_gcd123_mul_middleQuotient QA QB QC,hz,mul_zero]
theorem firstResidualCell_count_lt
   (QA QB QC:StackedPoly) (hQA:QA≠0) (hQB:QB≠0)
   (hboxA:QA∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 5263 7)
   (hboxB:QB∈globalCoefficientBox IRSProfile.Field
     (47*agreements) w 598 14)
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field)
   (u0 u1:IRSProfile.Index → IRSProfile.Field)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i)=
         u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
   (firstResidualSeeds selected Gamma QA QB).card <
     firstResidualQ2Ceiling:=by
 let Delta:=firstResidualSeeds selected Gamma QA QB
 let Q:=quotientB QA QB
 let T:=quotientA QA QB
 have hsub:Delta ⊆ Gamma:=by
   intro gamma hgamma
   exact (Finset.mem_filter.mp hgamma).1
 have hsolutions:=firstResidualSeeds_quotient_vanish selected Gamma
   QA QB QC hcover
 have hQsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma Q=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).2
 have hTsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma T=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).1
 have hQ:Q≠0:=quotientB_ne_zero QA QB hQB
 have hQbox:=quotientB_mem_parent_box QA QB hQB hboxB
 have hTbox:=quotientA_mem_parent_box QA QB hQA hboxA
 have hTcaps:=degree_bounds_of_mem_box T (25*agreements) w 5263 7
   (by norm_num [w]) hTbox
 have hrel:IsRelPrime Q T:=
   (firstQuotients_isRelPrime hQA).symm
 have hdegreeDelta:∀ gamma∈Delta,
     (selected gamma).natDegree ≤ firstResidualQ2.w:=by
   intro gamma hgamma
   simpa [firstResidualQ2,w] using hdegree gamma (hsub hgamma)
 have hagreementDelta:∀ gamma∈Delta,
     firstResidualQ2.a ≤
       ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
         (selected gamma).eval (IRSProfile.domain i)=
           u0 i+gamma*u1 i)).card:=by
   intro gamma hgamma
   simpa [firstResidualQ2,agreements] using hagreement gamma (hsub hgamma)
 have hnoPencilDelta:NoLargeSelectedPencil selected Delta
     firstResidualQ2.w firstResidualQ2.errors:=by
   simpa [firstResidualQ2,TightParameters.errors,errors,n,agreements,w] using
     noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
 have hstage:=asymmetric_stage_count_lt_of_regular_factors
   firstResidualQ2Stage firstResidualQ2 Q T hQ prime
   (by norm_num [firstResidualQ2])
   (by norm_num [firstResidualQ2,prime])
   (by norm_num [firstResidualQ2])
   (by norm_num [firstResidualQ2,prime])
   (by norm_num [firstResidualQ2,TightParameters.kappa])
   (by norm_num [firstResidualQ2,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [firstResidualQ2,prime,TightParameters.implicitYCap,
     TightParameters.kappa])
   (by norm_num [firstResidualQ2,prime,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [firstResidualQ2,prime,TightParameters.implicitYCap,
     TightParameters.algebraicCap,TightParameters.kappa])
   (by norm_num [firstResidualQ2])
   (by norm_num [firstResidualQ2])
   hQbox
   (by norm_num [firstResidualQ2Stage,UnequalParameters.gap])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2,
     UnequalParameters.gap,TightParameters.gap])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2])
   (by norm_num [firstResidualQ2Stage,firstResidualQ2])
   selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
   u0 u1 IRSProfile.domain.injective.injOn
   (by norm_num [IRSProfile.Index,firstResidualQ2])
   hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
   (all_regularPairSeeds_bound firstResidualQ2Stage Q T hQ hrel
     firstResidualQ2.D firstResidualQ2.w firstResidualQ2.L firstResidualQ2.s
     prime hQbox
     (by norm_num [firstResidualQ2])
     (by norm_num [firstResidualQ2Stage,firstResidualQ2])
     (by norm_num [firstResidualQ2Stage,firstResidualQ2])
     (by norm_num [firstResidualQ2Stage,firstResidualQ2])
     (by simpa [firstResidualQ2Stage,agreements,w] using hTcaps.1)
     (by simpa [firstResidualQ2Stage] using hTcaps.2.1)
     (by simpa [firstResidualQ2Stage] using hTcaps.2.2)
     (by norm_num [firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage,UnequalParameters.mixedCost,prime])
     (by norm_num [firstResidualQ2Stage,UnequalParameters.mixedCost,prime])
     (by norm_num [firstResidualQ2Stage,UnequalParameters.mixedCost,prime])
     selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
     u0 u1 IRSProfile.domain.injective.injOn
     (by norm_num [IRSProfile.Index,firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage,prime])
     (by norm_num [firstResidualQ2Stage])
     (by norm_num [firstResidualQ2Stage])
     (by simpa [firstResidualQ2Stage,firstResidualQ2] using hdegreeDelta)
     (by simpa [firstResidualQ2Stage,firstResidualQ2] using hagreementDelta)
     (by simpa [firstResidualQ2Stage,firstResidualQ2,
       UnequalParameters.errors,TightParameters.errors] using hnoPencilDelta))
 simpa [Delta,firstResidualQ2Ceiling,optimized_residual_cell_values.2.2.2.1]
   using hstage
theorem secondResidualCell_count_lt
   (QA QB QC:StackedPoly) (hQA:QA≠0) (hQB:QB≠0) (hQC:QC≠0)
   (hboxA:QA∈globalCoefficientBox IRSProfile.Field
     (25*agreements) w 5263 7)
   (hboxB:QB∈globalCoefficientBox IRSProfile.Field
     (47*agreements) w 598 14)
   (hboxC:QC∈globalCoefficientBox IRSProfile.Field
     (27*agreements) w 579299 6)
   (selected:IRSProfile.Field → Polynomial IRSProfile.Field)
   (Gamma:Finset IRSProfile.Field)
   (u0 u1:IRSProfile.Index → IRSProfile.Field)
   (hcover:∀ gamma∈Gamma,
     RecursiveSpecializationBranch (selected gamma) gamma QA QB QC)
   (hdegree:∀ gamma∈Gamma,(selected gamma).natDegree ≤ w)
   (hagreement:∀ gamma∈Gamma,
     agreements ≤ ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
       (selected gamma).eval (IRSProfile.domain i)=
         u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma w errors):
   (secondResidualSeeds selected Gamma QA QB QC).card <
     secondResidualGcd12Ceiling:=by
 let Delta:=secondResidualSeeds selected Gamma QA QB QC
 let Q:=middleQuotient QA QB QC
 let T:=quotientC QA QB QC
 have hsub:Delta ⊆ Gamma:=by
   intro gamma hgamma
   exact (Finset.mem_filter.mp (Finset.mem_filter.mp hgamma).1).1
 have hsolutions:=secondResidualSeeds_quotient_vanish selected Gamma
   QA QB QC hcover
 have hQsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma Q=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).1
 have hTsolution:∀ gamma∈Delta,
     specialization IRSProfile.Field (selected gamma) gamma T=0:=
   fun gamma hgamma => (hsolutions gamma hgamma).2
 have hbox12:=gcd12_mem_meet_box QA QB hQA hQB hboxA hboxB
 have hQ:Q≠0:=middleQuotient_ne_zero QA QB QC hQA
 have hQbox:=middleQuotient_mem_parent_box QA QB QC hQA hbox12
 have hTbox:=quotientC_mem_parent_box QA QB QC hQC hboxC
 have hTcaps:=degree_bounds_of_mem_box T (27*agreements) w 579299 6
   (by norm_num [w]) hTbox
 have hrel:IsRelPrime Q T:=secondQuotients_isRelPrime hQA
 have hdegreeDelta:∀ gamma∈Delta,
     (selected gamma).natDegree ≤ secondResidualGcd12.w:=by
   intro gamma hgamma
   simpa [secondResidualGcd12,w] using hdegree gamma (hsub hgamma)
 have hagreementDelta:∀ gamma∈Delta,
     secondResidualGcd12.a ≤
       ((Finset.univ:Finset IRSProfile.Index).filter (fun i =>
         (selected gamma).eval (IRSProfile.domain i)=
           u0 i+gamma*u1 i)).card:=by
   intro gamma hgamma
   simpa [secondResidualGcd12,agreements] using hagreement gamma (hsub hgamma)
 have hnoPencilDelta:NoLargeSelectedPencil selected Delta
     secondResidualGcd12.w secondResidualGcd12.errors:=by
   simpa [secondResidualGcd12,TightParameters.errors,errors,n,agreements,w] using
     noLargeSelectedPencil_mono selected Gamma Delta w errors hsub hnoPencil
 have hstage:=asymmetric_stage_count_lt_of_regular_factors
   residualStageTwo secondResidualGcd12 Q T hQ prime
   (by norm_num [secondResidualGcd12])
   (by norm_num [secondResidualGcd12,prime])
   (by norm_num [secondResidualGcd12])
   (by norm_num [secondResidualGcd12,prime])
   (by norm_num [secondResidualGcd12,TightParameters.kappa])
   (by norm_num [secondResidualGcd12,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [secondResidualGcd12,prime,TightParameters.implicitYCap,
     TightParameters.kappa])
   (by norm_num [secondResidualGcd12,prime,TightParameters.algebraicCap,
     TightParameters.kappa])
   (by norm_num [secondResidualGcd12,prime,TightParameters.implicitYCap,
     TightParameters.algebraicCap,TightParameters.kappa])
   (by norm_num [secondResidualGcd12])
   (by norm_num [secondResidualGcd12])
   hQbox
   (by norm_num [residualStageTwo,UnequalParameters.gap])
   (by norm_num [residualStageTwo,secondResidualGcd12,
     UnequalParameters.gap,TightParameters.gap])
   (by norm_num [residualStageTwo,secondResidualGcd12])
   (by norm_num [residualStageTwo,secondResidualGcd12])
   (by norm_num [residualStageTwo,secondResidualGcd12])
   selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
   u0 u1 IRSProfile.domain.injective.injOn
   (by norm_num [IRSProfile.Index,secondResidualGcd12])
   hdegreeDelta hQsolution hTsolution hagreementDelta hnoPencilDelta
   (all_regularPairSeeds_bound residualStageTwo Q T hQ hrel
     secondResidualGcd12.D secondResidualGcd12.w secondResidualGcd12.L
     secondResidualGcd12.s prime hQbox
     (by norm_num [secondResidualGcd12])
     (by norm_num [residualStageTwo,secondResidualGcd12])
     (by norm_num [residualStageTwo,secondResidualGcd12])
     (by norm_num [residualStageTwo,secondResidualGcd12])
     (by simpa [residualStageTwo,agreements,w] using hTcaps.1)
     (by simpa [residualStageTwo] using hTcaps.2.1)
     (by simpa [residualStageTwo] using hTcaps.2.2)
     (by norm_num [residualStageTwo])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo,UnequalParameters.mixedCost,prime])
     (by norm_num [residualStageTwo,UnequalParameters.mixedCost,prime])
     (by norm_num [residualStageTwo,UnequalParameters.mixedCost,prime])
     selected Delta (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain
     u0 u1 IRSProfile.domain.injective.injOn
     (by norm_num [IRSProfile.Index,residualStageTwo])
     (by norm_num [residualStageTwo])
     (by norm_num [residualStageTwo,prime])
     (by norm_num [residualStageTwo])
     (by norm_num [residualStageTwo])
     (by simpa [residualStageTwo,secondResidualGcd12] using hdegreeDelta)
     (by simpa [residualStageTwo,secondResidualGcd12] using hagreementDelta)
     (by simpa [residualStageTwo,secondResidualGcd12,
       UnequalParameters.errors,TightParameters.errors] using hnoPencilDelta))
 simpa [Delta,secondResidualGcd12Ceiling,
   optimized_residual_cell_values.2.2.2.2] using hstage
end
end ProximityPrize.SubmissionLower.RCN303
end PackedLegacy_GH

/-! Packed from ProximityPrize.SubmissionLower.P2. -/
section PackedLegacy_P2
namespace ProximityPrize.SubmissionLower.RCN285
open scoped BigOperators Pointwise
open RCN119
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def seedlessExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 1 ≤ L∧d 1 ≤ s∧d 2=0}
def seedlessBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (seedlessExponents M L s)
theorem seedlessBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈seedlessBox K M L s)
   (hg:g∈seedlessBox K M' L' s'):
   f*g∈seedlessBox K (M+M') (L+L') (s+s'):=by
 have hset:seedlessExponents M L s+seedlessExponents M' L' s' ⊆
     seedlessExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   rcases he with ⟨he0,he01,he1,he2⟩
   simp only [seedlessExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   exact ⟨by omega,by omega,by omega,by omega⟩
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_seedlessBox:
   slopeDifference K∈seedlessBox K 1 1 1:=by
 apply (seedlessBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
theorem slopeDifference_pow_mem_seedlessBox (h:ℕ):
   slopeDifference K^h∈seedlessBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [seedlessExponents]
 | succ h ih =>
     simpa only [pow_succ] using
       seedlessBox_mul K ih (slopeDifference_mem_seedlessBox K)
theorem slopeDifference_mul_mem_seedlessBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈seedlessBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈seedlessBox K M L s:=by
 have hh:=seedlessBox_mul K (slopeDifference_pow_mem_seedlessBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,
   Nat.add_sub_of_le hs] using hh
private def exponentPair (i j:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j
@[simp] private theorem exponentPair_zero (i j:ℕ):
   exponentPair i j 0=i:=by simp [exponentPair]
@[simp] private theorem exponentPair_one (i j:ℕ):
   exponentPair i j 1=j:=by simp [exponentPair]
@[simp] private theorem exponentPair_two (i j:ℕ):
   exponentPair i j 2=0:=by simp [exponentPair]
private theorem exponentPair_eta (d:Fin 3 →₀ ℕ) (hd:d 2=0):
   exponentPair (d 0) (d 1)=d:=by
 ext i
 fin_cases i <;> simp [hd]
abbrev SeedlessBoxIndex (M L s:ℕ):=
 (i:Fin (M+1)) × Fin (min (s+1) (L+1-i.val))
private theorem fin_heq_of_val_eq
   {a b:ℕ} {u:Fin a} {v:Fin b}
   (hab:a=b) (huv:u.val=v.val):HEq u v:=by
 subst b
 exact heq_of_eq (Fin.ext huv)
def seedlessExponentsEquivIndex (M L s:ℕ):
   seedlessExponents M L s ≃ SeedlessBoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,Nat.lt_succ_of_le d.property.1⟩,
     ⟨d.val 1,by
       rcases d.property with ⟨_,h01,h1,_⟩
       rw [lt_min_iff]
       constructor
       · omega
       · change d.val 1 < L+1-d.val 0
         omega⟩⟩
 invFun q:=
   ⟨exponentPair q.1.val q.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.isLt
     rw [lt_min_iff] at hj
     simp only [seedlessExponents,Set.mem_setOf_eq,exponentPair_zero,
       exponentPair_one,exponentPair_two]
     exact ⟨by omega,by omega,by omega,by simp⟩⟩
 left_inv d:=Subtype.ext (exponentPair_eta d.val d.property.2.2.2)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact exponentPair_zero i j
   · apply fin_heq_of_val_eq
     · simp only [exponentPair_zero]
     · exact exponentPair_one i j
instance seedlessExponentsFintype (M L s:ℕ):
   Fintype (seedlessExponents M L s):=
 Fintype.ofEquiv (SeedlessBoxIndex M L s)
   (seedlessExponentsEquivIndex M L s).symm
instance seedlessBoxFinite (M L s:ℕ):
   Module.Finite K (seedlessBox K M L s):=
 Module.Finite.of_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))
def seedlessInputCount (M L s:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1),min (s+1) (L+1-i)
theorem seedlessBox_finrank (M L s:ℕ):
   Module.finrank K (seedlessBox K M L s)=seedlessInputCount M L s:=by
 change Module.finrank K
     (MvPolynomial.restrictSupport K (seedlessExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))]
 rw [Fintype.card_congr (seedlessExponentsEquivIndex M L s)]
 simp [SeedlessBoxIndex,seedlessInputCount,Fintype.card_sigma,
   Finset.sum_range]
def seedlessBlockJet (M L s h:ℕ):
   seedlessBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (seedlessBox K M L s).subtype
def multiplyIntoSeedlessBox {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     seedlessBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_seedlessBox K hM hL hs q.property⟩
 map_add' q r:=by apply Subtype.ext;simp [mul_add]
 map_smul' c q:=by apply Subtype.ext;simp [mul_smul_comm]
theorem multiplyIntoSeedlessBox_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoSeedlessBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=
     slopeDifference K^h*r.val:=congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def seedlessKernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (seedlessBlockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (seedlessBlockJet K M L s h))
   (multiplyIntoSeedlessBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem seedlessKernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (seedlessKernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoSeedlessBox_injective K hM hL hs
 exact congrArg Subtype.val heq
def seedlessKernelLowerBound (M L s h:ℕ):ℕ:=
 if h ≤ M∧h ≤ L∧h ≤ s then
   seedlessInputCount (M-h) (L-h) (s-h)
 else 0
def seedlessContactRankBound (M L s h:ℕ):ℕ:=
 seedlessInputCount M L s-seedlessKernelLowerBound M L s h
theorem seedlessBlockJet_rank_le_contactRankBound
   (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (seedlessBlockJet K M L s h)) ≤
     seedlessContactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hker:=LinearMap.finrank_le_finrank_of_injective
       (seedlessKernelEmbedding_injective K hM hL hs)
     have hsum:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hker
     rw [seedlessBox_finrank K] at hsum
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_pos ⟨hM,hL,hs⟩]
     omega
   · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
       intro hh
       exact hs hh.2.2
     have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hinput
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_neg hbad,Nat.sub_zero]
     omega
 · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
     intro hh
     exact hM hh.1
   have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
   rw [seedlessBox_finrank K] at hinput
   unfold seedlessContactRankBound seedlessKernelLowerBound
   rw [if_neg hbad,Nat.sub_zero]
   omega
end
end ProximityPrize.SubmissionLower.RCN285
end PackedLegacy_P2

/-! Packed from ProximityPrize.SubmissionLower.E9. -/
section PackedLegacy_E9
namespace ProximityPrize.SubmissionLower.RCN279
open scoped BigOperators
open ProximityPrize.Benchmark RCN285 RCN119
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
variable (K:Type*) [Field K]
abbrev LocalPoly:=MvPolynomial (Fin 3) K
abbrev Poly4:=MvPolynomial (Fin 4) K
abbrev CoefficientIndex (D w L s:ℕ):=
 (i:Fin (L+1)) × (j:Fin (s+1)) ×
   (Fin (min 1 (L+1-i.val-j.val)) ×
     Fin (D-w*i.val-(w-1)*j.val))
def columnExponent {D w L s:ℕ}
   (c:CoefficientIndex D w L s):Fin 4 →₀ ℕ:=
 Finsupp.single 0 c.2.2.2.val+Finsupp.single 1 c.1.val+
   Finsupp.single 2 c.2.1.val
@[simp] theorem columnExponent_x {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 0=c.2.2.2.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_y {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 1=c.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_r {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 2=c.2.1.val:=by
 simp [columnExponent]
@[simp] theorem columnExponent_z {D w L s:ℕ}
   (c:CoefficientIndex D w L s):columnExponent c 3=0:=by
 simp [columnExponent]
theorem columnExponent_injective (D w L s:ℕ):
   Function.Injective
     (columnExponent (D:=D) (w:=w) (L:=L) (s:=s)):=by
 intro c d h
 have hx:=congrArg (fun e:Fin 4 →₀ ℕ => e 0) h
 have hy:=congrArg (fun e:Fin 4 →₀ ℕ => e 1) h
 have hr:=congrArg (fun e:Fin 4 →₀ ℕ => e 2) h
 rcases c with ⟨⟨ci,hci⟩,⟨⟨cj,hcj⟩,⟨⟨cz,hcz⟩,⟨ce,hce⟩⟩⟩⟩
 rcases d with ⟨⟨di,hdi⟩,⟨⟨dj,hdj⟩,⟨⟨dz,hdz⟩,⟨de,hde⟩⟩⟩⟩
 simp only [columnExponent_x] at hx
 simp only [columnExponent_y] at hy
 simp only [columnExponent_r] at hr
 subst di
 subst dj
 subst de
 have hcz0:cz=0:=by omega
 have hdz0:dz=0:=by omega
 subst cz
 subst dz
 rfl
def globalExponents (D w L s:ℕ):Set (Fin 4 →₀ ℕ):=
 {d | d 1+d 2 ≤ L∧d 2 ≤ s∧d 3=0∧
   d 0+w*d 1+(w-1)*d 2 < D}
def globalCoefficientBox (D w L s:ℕ):Submodule K (Poly4 K):=
 MvPolynomial.restrictSupport K (globalExponents D w L s)
theorem columnMonomial_mem (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a∈
     globalCoefficientBox K D w L s:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 have hi:=c.1.isLt
 have hj:=c.2.1.isLt
 have ht:=c.2.2.1.isLt
 have he:=c.2.2.2.isLt
 have htri:c.1.val+c.2.1.val ≤ L:=by
   have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
     omega
   have hpos:0 < L+1-c.1.val-c.2.1.val:=
     hminpos.trans_le (min_le_right _ _)
   omega
 unfold globalExponents
 simp only [Set.mem_setOf_eq,columnExponent_x,columnExponent_y,
   columnExponent_r,columnExponent_z]
 exact ⟨htri,by omega,by simp,by omega⟩
def reconstruct (D w L s:ℕ) (theta:CoefficientIndex D w L s → K):
   Poly4 K:=
 ∑ c:CoefficientIndex D w L s,
   MvPolynomial.monomial (columnExponent c) (theta c)
theorem reconstruct_coeff (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (c:CoefficientIndex D w L s):
   MvPolynomial.coeff (columnExponent c) (reconstruct K D w L s theta)=
     theta c:=by
 classical
 simp [reconstruct,MvPolynomial.coeff_sum,
   (columnExponent_injective D w L s).eq_iff]
@[simp] theorem reconstruct_zero (D w L s:ℕ):
   reconstruct K D w L s (0:CoefficientIndex D w L s → K)=0:=by
 simp [reconstruct]
theorem reconstruct_injective (D w L s:ℕ):
   Function.Injective (reconstruct K D w L s):=by
 intro theta eta h
 funext c
 have hh:=congrArg (MvPolynomial.coeff (columnExponent c)) h
 simpa only [reconstruct_coeff] using hh
theorem reconstruct_ne_zero (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K) (htheta:theta≠0):
   reconstruct K D w L s theta≠0:=by
 intro hz
 apply htheta
 apply reconstruct_injective K D w L s
 simpa only [reconstruct_zero] using hz
theorem reconstruct_mem_box (D w L s:ℕ)
   (theta:CoefficientIndex D w L s → K):
   reconstruct K D w L s theta∈globalCoefficientBox K D w L s:=by
 classical
 unfold reconstruct
 apply Submodule.sum_mem
 intro c hc
 exact columnMonomial_mem K D w L s c (theta c)
def coefficientCount (D w L s:ℕ):ℕ:=
 ∑ i∈Finset.range (L+1),
   ∑ j∈Finset.range (s+1),
     min 1 (L+1-i-j)*(D-w*i-(w-1)*j)
theorem coefficient_index_card (D w L s:ℕ):
   Fintype.card (CoefficientIndex D w L s)=coefficientCount D w L s:=by
 simp [CoefficientIndex,coefficientCount,Fintype.card_sigma,
   Finset.sum_range]
def localMonomial (f j:ℕ):LocalPoly K:=
 MvPolynomial.monomial (Finsupp.single 0 f+Finsupp.single 1 j) 1
theorem localMonomial_mem (f j:ℕ):
   localMonomial K f j∈seedlessBox K f (f+j) j:=by
 apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
 left
 simp [localMonomial,seedlessExponents]
def blockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):LocalPoly K:=
 ∑ f:Fin (c.1.val+1),
   if f.val ≤ r then
     ((((c.2.2.2.val.choose (r-f.val):ℕ):K)*
       x^(c.2.2.2.val-(r-f.val))*
       ((c.1.val.choose f.val:ℕ):K)*u^(c.1.val-f.val))) •
         localMonomial K f.val c.2.1.val
   else 0
theorem blockEntry_mem (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   blockEntry K D w L s x u c r∈
     seedlessBox K (min r L) L s:=by
 classical
 unfold blockEntry
 apply Submodule.sum_mem
 intro f hf
 split_ifs with hfr
 · apply (seedlessBox K (min r L) L s).smul_mem
   apply MvPolynomial.restrictSupport_mono (R:=K) ?_
     (localMonomial_mem K f.val c.2.1.val)
   intro d hd
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   have hi:=c.1.isLt
   have hj:=c.2.1.isLt
   have ht:=c.2.2.1.isLt
   have hfi:=f.isLt
   have htri:c.1.val+c.2.1.val ≤ L:=by
     have hminpos:0 < min 1 (L+1-c.1.val-c.2.1.val):=by
       omega
     have hpos:0 < L+1-c.1.val-c.2.1.val:=
       hminpos.trans_le (min_le_right _ _)
     omega
   exact ⟨hd0.trans (by omega),by omega,hd1.trans (by omega),hd2⟩
 · exact (seedlessBox K (min r L) L s).zero_mem
def boundedBlockEntry (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (r:ℕ):
   seedlessBox K (min r L) L s:=
 ⟨blockEntry K D w L s x u c r,blockEntry_mem K D w L s x u c r⟩
def extractBlock (D w L s:ℕ) (x u:K) (r:ℕ):
   (CoefficientIndex D w L s → K) →ₗ[K]
     seedlessBox K (min r L) L s where
 toFun theta:=∑ c:CoefficientIndex D w L s,
   theta c • boundedBlockEntry K D w L s x u c r
 map_add' theta eta:=by
   simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
 map_smul' a theta:=by
   simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,
     RingHom.id_apply]
def localRankBound (m L s:ℕ):ℕ:=
 ∑ r∈Finset.range m,
   seedlessContactRankBound (min r L) L s (m-r)
abbrev LocalTarget (m L s:ℕ):=
 (r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))
theorem localTarget_finrank_le (m L s:ℕ):
   Module.finrank K (LocalTarget K m L s) ≤ localRankBound m L s:=by
 change Module.finrank K ((r:Fin m) → LinearMap.range
   (seedlessBlockJet K (min r.val L) L s (m-r.val))) ≤ _
 rw [Module.finrank_pi_fintype]
 unfold localRankBound
 rw [Finset.sum_range]
 apply Finset.sum_le_sum
 intro r hr
 exact seedlessBlockJet_rank_le_contactRankBound K (min r.val L) L s
   (m-r.val) (min_le_right r.val L)
abbrev GlobalTarget (I:Type*) (m L s:ℕ):=I → LocalTarget K m L s
def constraintMap {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K):
   (CoefficientIndex D w L s → K) →ₗ[K] GlobalTarget K I m L s:=
 LinearMap.pi fun i => LinearMap.pi fun r =>
   (seedlessBlockJet K (min r.val L) L s (m-r.val)).rangeRestrict.comp
     (extractBlock K D w L s (nodes i) (received i) r.val)
theorem exists_nonzero_kernel_array {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (hgate:Fintype.card I*localRankBound m L s <
     coefficientCount D w L s):
   ∃ theta:CoefficientIndex D w L s → K,theta≠0∧
     constraintMap K D w L s m nodes received theta=0:=by
 classical
 by_contra hnone
 have hinj:Function.Injective
     (constraintMap K D w L s m nodes received):=by
   intro theta eta heq
   by_contra hne
   apply hnone
   refine ⟨theta-eta,sub_ne_zero.mpr hne,?_⟩
   rw [map_sub,heq,sub_self]
 have hdim:=LinearMap.finrank_le_finrank_of_injective hinj
 rw [Module.finrank_fintype_fun_eq_card,coefficient_index_card] at hdim
 have htarget:Module.finrank K (GlobalTarget K I m L s) ≤
     Fintype.card I*localRankBound m L s:=by
   change Module.finrank K (I → LocalTarget K m L s) ≤ _
   rw [Module.finrank_pi_fintype]
   calc
     (∑ _i:I,Module.finrank K (LocalTarget K m L s)) ≤
         ∑ _i:I,localRankBound m L s:=by
       apply Finset.sum_le_sum
       intro i hi
       exact localTarget_finrank_le K m L s
     _=Fintype.card I*localRankBound m L s:=by simp
 exact (Nat.not_le_of_gt hgate) (hdim.trans htarget)
theorem all_blocks_divisible_of_kernel {I:Type*} [Fintype I]
   (D w L s m:ℕ) (nodes received:I → K)
   (theta:CoefficientIndex D w L s → K)
   (hzero:constraintMap K D w L s m nodes received theta=0):
   ∀ i:I,∀ r:ℕ,slopeDifference K^(m-r)∣
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K):=by
 intro i r
 by_cases hr:r < m
 · have hh:=congrArg
     (fun t:GlobalTarget K I m L s => ((t i ⟨r,hr⟩):LocalPoly K)) hzero
   change contactJet K (m-r)
     ((extractBlock K D w L s (nodes i) (received i) r theta):LocalPoly K)=0 at hh
   exact (contactJet_eq_zero_iff K (m-r) _).mp hh
 · have hm:m-r=0:=by omega
   simp only [hm,pow_zero,one_dvd]
def homogenizedTranslation (x u:K):
   Poly4 K →ₐ[K] Polynomial (LocalPoly K):=
 RCN122.homogenizedTranslation K x u 0
theorem columnMonomial_eq (D w L s:ℕ)
   (c:CoefficientIndex D w L s) (a:K):
   MvPolynomial.monomial (columnExponent c) a=
     MvPolynomial.C a*MvPolynomial.X 0^c.2.2.2.val*
       MvPolynomial.X 1^c.1.val*MvPolynomial.X 2^c.2.1.val:=by
 rw [columnExponent,MvPolynomial.monomial_add_single,
   MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem localMonomial_eq (f j:ℕ):
   localMonomial K f j=MvPolynomial.X 0^f*MvPolynomial.X 1^j:=by
 rw [localMonomial,MvPolynomial.monomial_add_single,
   ←MvPolynomial.X_pow_eq_monomial]
theorem translation_column_coeff (D w L s:ℕ) (x u:K)
   (c:CoefficientIndex D w L s) (a:K) (r:ℕ):
   (homogenizedTranslation K x u
     (MvPolynomial.monomial (columnExponent c) a)).coeff r=
       a • blockEntry K D w L s x u c r:=by
 have hfactor:
     homogenizedTranslation K x u
         (MvPolynomial.monomial (columnExponent c) a)=
       Polynomial.C (MvPolynomial.C a)*
         (((Polynomial.X+Polynomial.C (MvPolynomial.C x))^c.2.2.2.val*
           (Polynomial.X*Polynomial.C (MvPolynomial.X 0)+
             Polynomial.C (MvPolynomial.C u))^c.1.val*
           Polynomial.C (MvPolynomial.X 1^c.2.1.val))):=by
   rw [columnMonomial_eq K D w L s]
   simp [homogenizedTranslation,
     RCN122.homogenizedTranslation,
     RCN122.translationVariables,
     RCN100.seedAffine,
     Polynomial.algebraMap_apply,MvPolynomial.algebraMap_eq]
   ring
 rw [hfactor,Polynomial.coeff_C_mul,
   RCN122.coeff_shifted_affine_product]
 unfold blockEntry
 rw [Finset.mul_sum,Finset.smul_sum]
 apply Finset.sum_congr rfl
 intro f hf
 split_ifs with hfr
 · simp only [localMonomial_eq,MvPolynomial.smul_eq_C_mul,map_mul,
     map_pow,map_natCast]
   ring
 · simp
theorem translation_reconstruct_coeff (D w L s:ℕ) (x u:K)
   (theta:CoefficientIndex D w L s → K) (r:ℕ):
   (homogenizedTranslation K x u (reconstruct K D w L s theta)).coeff r=
     ((extractBlock K D w L s x u r theta):LocalPoly K):=by
 rw [reconstruct,map_sum,Polynomial.finsetSum_coeff]
 simp only [translation_column_coeff]
 change (∑ c:CoefficientIndex D w L s,
     theta c • blockEntry K D w L s x u c r)=
   (((∑ c:CoefficientIndex D w L s,
     theta c • boundedBlockEntry K D w L s x u c r):
       seedlessBox K (min r L) L s):LocalPoly K)
 simp [boundedBlockEntry]
def n:ℕ:=262144
def errors:ℕ:=79866
def agreements:ℕ:=n-errors
def w:ℕ:=131071
def multiplicity:ℕ:=37
def yTotalCap:ℕ:=51
def slopeCap:ℕ:=9
def weightedCap:ℕ:=multiplicity*agreements
theorem parameter_values:
   agreements=182278∧weightedCap=6744286:=by
 norm_num [agreements,weightedCap,multiplicity,n,errors]
theorem coefficient_count_exact:
   coefficientCount weightedCap w yTotalCap slopeCap=1481264965:=by
 decide
theorem local_rank_exact:
   localRankBound multiplicity yTotalCap slopeCap=5650:=by
 decide
theorem nullity_exact:
   coefficientCount weightedCap w yTotalCap slopeCap-
     n*localRankBound multiplicity yTotalCap slopeCap=151365:=by
 rw [coefficient_count_exact,local_rank_exact]
 norm_num [n]
theorem interpolation_gate:
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap:=by
 rw [coefficient_count_exact,local_rank_exact]
 norm_num [n]
theorem exists_frozen_seedless_interpolant
   (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     ∀ (i:IRSProfile.Index) (r:ℕ),
       slopeDifference IRSProfile.Field^(multiplicity-r)∣
         (RCN319.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r:=by
 obtain ⟨theta,htheta,hzero⟩:=exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index=n by
       norm_num [IRSProfile.Index,n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta,?_⟩
 intro i r
 have hdiv:=all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received
   theta hzero i r
 rw [←translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
theorem seedlessBox_le_legacy:
   globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ≤
     RCN174.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap:=by
 apply MvPolynomial.restrictSupport_mono
 intro d hd
 rcases hd with ⟨hYR,hR,hZ,hweighted⟩
 exact ⟨by omega,hR,hweighted⟩
theorem exists_frozen_seedless_vanishing_interpolant
   (received:IRSProfile.Index → IRSProfile.Field):
   ∃ Q:MvPolynomial (Fin 4) IRSProfile.Field,
     Q≠0∧
     Q∈globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     Q∈RCN174.globalCoefficientBox IRSProfile.Field
       weightedCap w yTotalCap slopeCap∧
     ∀ (P:Polynomial IRSProfile.Field)
       (support:Finset IRSProfile.Index),
       P.natDegree ≤ w → agreements ≤ support.card →
       (∀ i∈support,P.eval (IRSProfile.domain i)=received i) →
       RCN319.specialization IRSProfile.Field P 0 Q=0:=by
 classical
 obtain ⟨Q,hQ,hbox,hcontact⟩:=
   exists_frozen_seedless_interpolant received
 have hlegacy:=seedlessBox_le_legacy hbox
 refine ⟨Q,hQ,hbox,hlegacy,?_⟩
 intro P support hdegree hcard hvalues
 apply RCN319.specialization_eq_zero_of_contact_and_degree
   IRSProfile.Field Q P 0 IRSProfile.domain received (fun _ => 0)
     support multiplicity
 · intro i hi r
   exact hcontact i r
 · intro i hi
   simpa only [mul_zero,add_zero] using hvalues i hi
 · have hdeg:=RCN319.specialization_natDegree_lt
     IRSProfile.Field weightedCap w yTotalCap slopeCap Q P 0
     (by norm_num [weightedCap,multiplicity,agreements,n,errors])
     hlegacy hdegree
   have hbound:weightedCap ≤ multiplicity*support.card:=by
     rw [weightedCap]
     exact Nat.mul_le_mul_left multiplicity hcard
   exact hdeg.trans_le hbound
end
end ProximityPrize.SubmissionLower.RCN279
end PackedLegacy_E9

/-! Packed from ProximityPrize.SubmissionLower.O9. -/
section PackedLegacy_O9
namespace ProximityPrize.SubmissionLower.RCN282
open scoped Classical BigOperators
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN229 RCN065 RCN238 RCN173 RCN264 RCN243 RCN319 RCN163
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {K Omega:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
def seedlessPoint (S:Polynomial K):Fin 3 → Omega:=
 fun i => polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X) i.succ
theorem seedlessPoint_value (S:Polynomial K):
   seedlessPoint phi S=![phi S,phi S.derivative,0]:=by
 funext i
 fin_cases i <;>
   simp [seedlessPoint,polynomialPoint,polynomial_eval₂_comp_C_X]
theorem seedlessPoint_injective (hphi:Function.Injective phi):
   Function.Injective (seedlessPoint phi):=by
 intro S T h
 apply hphi
 have h0:=congrFun h (0:Fin 3)
 simpa only [seedlessPoint_value,Matrix.cons_val_zero] using h0
theorem seedlessPoint_surface_evaluation (S:Polynomial K)
   (Q:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (seedlessPoint phi S) (surfaceMap phi Q)=
     MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
       (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X)) Q:=by
 rw [eval_surfaceMap]
 have hv:Fin.cases (phi Polynomial.X) (seedlessPoint phi S)=
     polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
theorem seedless_agreement_zero_iff
   (F:MvPolynomial (Fin 4) K) (S:Polynomial K)
   (p w:ℕ) [CharP Omega p] (hchar:w < p)
   (hdegree:S.natDegree ≤ w)
   (hsolution:specialization K S 0 F=0)
   (hregular:MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (x u:K):
   MvPolynomial.aeval (seedlessPoint phi S)
     (agreementPolynomial phi F w x u 0)=0 ↔ S.eval x=u:=by
 have hpoint:seedlessPoint phi S=selectedPoint phi (fun _:K => S) 0:=rfl
 rw [hpoint]
 simpa only [zero_mul,add_zero] using
   (selected_agreement_zero_iff phi F (fun _:K => S) p w hchar 0
     hdegree hsolution hregular x u 0)
variable (P:Ideal (MvPolynomial (Fin 3) Omega)) [P.IsPrime]
theorem seedless_agreement_fiber_card_le
   (hphi:Function.Injective phi)
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K) (Gamma:Finset (Polynomial K))
   (p w:ℕ) [CharP Omega p] (hchar:w < p)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ S∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
   (x u:K) (hproper:agreementPolynomial phi F w x u 0∉P)
   (cap:Fin 3 → ℕ)
   (hcap:∀ j,(agreementPolynomial phi F w x u 0).degreeOf j ≤ cap j):
   (Gamma.filter (fun S => S.eval x=u)).card ≤ componentCost P cap:=by
 classical
 let fiber:=Gamma.filter (fun S => S.eval x=u)
 let points:=fiber.image (seedlessPoint phi)
 have hpointsP:∀ v∈points,
     P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom:=by
   intro v hv
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hv
   exact hpoint S (Finset.mem_filter.mp hS).1
 have hpointsF:∀ v∈points,
     MvPolynomial.aeval v (agreementPolynomial phi F w x u 0)=0:=by
   intro v hv
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hv
   obtain ⟨hGamma,hagree⟩:=Finset.mem_filter.mp hS
   exact (seedless_agreement_zero_iff phi F S p w hchar
     (hdegree S hGamma) (hsolution S hGamma) (hregular S hGamma) x u).mpr hagree
 have hcount:=RCN007.finite_zero_points_le_box Omega P hproj
   hnonpoint (agreementPolynomial phi F w x u 0) hproper cap hcap
   points hpointsP hpointsF
 have hcard:points.card=fiber.card:=
   Finset.card_image_of_injective _ (seedlessPoint_injective phi hphi)
 rw [hcard] at hcount
 unfold componentCost
 exact_mod_cast hcount
theorem coordinate_two_eq_zero (hZ:MvPolynomial.X (2:Fin 3)∈P):
   coordinate Omega P 2=0:=by
 change coordinateEvaluation Omega P (MvPolynomial.X (2:Fin 3))=0
 change MvPolynomial.X (2:Fin 3)∈
   RingHom.ker (coordinateEvaluation Omega P).toRingHom
 rwa [coordinateEvaluation_ker]
theorem identityNodes_card_le_of_seedless_cut
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (hZ:MvPolynomial.X (2:Fin 3)∈P)
   {Iota:Type} (nodes:Finset Iota) (x u:Iota → K)
   (w:ℕ) (hw:1 ≤ w) (hinj:Set.InjOn x nodes)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom):
   (identityNodes phi P F nodes x u (fun _ => 0) w).card ≤ w:=by
 classical
 by_contra hnot
 have hmany:w < (identityNodes phi P F nodes x u (fun _ => 0) w).card:=
   Nat.lt_of_not_ge hnot
 have htrans:=seed_transcendental_of_many_identities phi P F hF hH
   nodes x u (fun _ => 0) w hw hinj hmany hnonpoint
 have hz0:=coordinate_two_eq_zero P hZ
 rw [hz0] at htrans
 exact htrans isAlgebraic_zero
variable {Iota:Type}
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem seedless_prime_incidence
   (hphi:Function.Injective phi)
   (hproj:ProjectionsFiniteSeparable Omega P)
   (hnonpoint:∀ v:Fin 3 → Omega,
     P≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
   (F:MvPolynomial (Fin 4) K)
   (hF:surfaceMap phi F∈P)
   (hH:surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F)∉P)
   (hZ:MvPolynomial.X (2:Fin 3)∈P)
   (Gamma:Finset (Polynomial K))
   (nodes:Finset Iota) (x u:Iota → K) (hinj:Set.InjOn x nodes)
   (p w a:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hpoint:∀ S∈Gamma,P ≤ RingHom.ker
     (MvPolynomial.aeval (seedlessPoint phi S)).toRingHom)
   (hagreement:∀ S∈Gamma,
     a ≤ (nodes.filter (fun i => S.eval (x i)=u i)).card)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j):
   Gamma.card*(a-w) ≤ (nodes.card-w)*componentCost P cap:=by
 classical
 let I:=identityNodes phi P F nodes x u (fun _ => 0) w
 let relation:Polynomial K → Iota → Prop:=fun S i => S.eval (x i)=u i
 have hI:I.card ≤ w:=identityNodes_card_le_of_seedless_cut phi P F hF hH
   hZ nodes x u w hw hinj hnonpoint
 have hfiber:∀ i∈nodes \ I,
     (Gamma.filter (fun S => relation S i)).card ≤ componentCost P cap:=by
   intro i hi
   obtain ⟨hinodes,hnotI⟩:=Finset.mem_sdiff.mp hi
   have hproper:agreementPolynomial phi F w (x i) (u i) 0∉P:=by
     intro hmem
     apply hnotI
     exact Finset.mem_filter.mpr ⟨hinodes,hmem⟩
   exact seedless_agreement_fiber_card_le phi P hphi hproj hnonpoint F Gamma
     p w hchar hdegree hsolution hregular hpoint (x i) (u i) hproper cap
     (hcap i hinodes)
 exact sharp_incidence_bound relation Gamma nodes I a w (componentCost P cap)
   (identityNodes_subset phi P F nodes x u (fun _ => 0) w) hI hwa han
   hagreement hfiber
end
end ProximityPrize.SubmissionLower.RCN282
end PackedLegacy_O9

/-! Packed from ProximityPrize.SubmissionLower.P0. -/
section PackedLegacy_P0
namespace ProximityPrize.SubmissionLower.RCN283
open scoped Classical BigOperators
open RCN002 RCN007 RCN004 RCN001 RCN013 RCN136 RCN231 RCN319 RCN238 RCN264 RCN243 RCN282
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
 (phi:Polynomial K →+*Omega)
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
def seedlessCut:MvPolynomial (Fin 3) Omega:=MvPolynomial.X 2
theorem seedless_proper_cut_bound
   (hphi:Function.Injective phi)
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Omega)
   (hG:Irreducible G) (hdiv:G∣surfaceMap phi F)
   (hproper:¬ G∣seedlessCut)
   (Gamma:Finset (Polynomial K))
   (nodes:Finset Iota) (x u:Iota → K) (hinj:Set.InjOn x nodes)
   (p w a:ℕ) [CharP Omega p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hcutDegree:∀ j k:Fin 3,j≠k →
     (seedlessCut (Omega:=Omega)).degreeOf j*G.degreeOf k+
       G.degreeOf j*(seedlessCut (Omega:=Omega)).degreeOf k < p)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolution:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,MvPolynomial.eval₂Hom (phi.comp Polynomial.C)
     (polynomialPoint (phi.comp Polynomial.C) S 0 (phi Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) G=0)
   (hagreement:∀ S∈Gamma,
     a ≤ (nodes.filter (fun i => S.eval (x i)=u i)).card)
   (cap:Fin 3 → ℕ)
   (hcap:∀ i∈nodes,∀ j,
     (agreementPolynomial phi F w (x i) (u i) 0).degreeOf j ≤ cap j):
   Gamma.card*(a-w) ≤
     (nodes.card-w)*
       (∑ i,cap i*coordinateMixedDegree Omega G seedlessCut i):=by
 classical
 let T:MvPolynomial (Fin 3) Omega:=seedlessCut
 let H:=regularitySurface phi F
 have hTpoint:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) T=0:=by
   intro S hS
   simp [T,seedlessCut,seedlessPoint_value]
 have hHp:∀ S∈Gamma,
     MvPolynomial.eval (seedlessPoint phi S) H≠0:=by
   intro S hS
   change MvPolynomial.eval (seedlessPoint phi S)
     (surfaceMap phi (MvPolynomial.pderiv (2:Fin 4) F))≠0
   rw [seedlessPoint_surface_evaluation]
   exact hregular S hS
 let degree:RegularComponent Omega G T H → Fin 3 → ℕ:=
   fun C i => actualCoordinateDegree Omega C.1 i
 have hcomponent:∀ C:RegularComponent Omega G T H,
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C).card*
         (a-w) ≤
       (nodes.card-w)*(∑ i,cap i*degree C i):=by
   intro C
   have hsub:=componentSeeds_subset Omega G T H Gamma (seedlessPoint phi) C
   have hgmem:=regularComponent_G_mem Omega G T H C
   have htmem:=regularComponent_T_mem Omega G T H C
   have hFmem:surfaceMap phi F∈C.1:=
     ((Ideal.span_singleton_le_iff_mem (I:=C.1)).mpr hgmem)
       (Ideal.mem_span_singleton.mpr hdiv)
   have hproj:ProjectionsFiniteSeparable Omega C.1:=
     all_transcendental_coordinates_finite_separable Omega C.1 p G T
       hG hgmem htmem hproper hGdegree hcutDegree
   exact seedless_prime_incidence phi C.1 hphi hproj
     (regularComponent_ne_point Omega G T H C) F hFmem
     (regularComponent_H_not_mem Omega G T H C) htmem
     (componentSeeds Omega G T H Gamma (seedlessPoint phi) C)
     nodes x u hinj p w a hw hchar hwa han
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolution S (hsub hS))
     (fun S hS => hregular S (hsub hS))
     (fun S hS => componentSeeds_on_prime Omega G T H Gamma
       (seedlessPoint phi) C S hS)
     (fun S hS => hagreement S (hsub hS)) cap hcap
 have hbudget:∀ i,
     (∑ C:RegularComponent Omega G T H,
       actualCoordinateDegree Omega C.1 i) ≤
         coordinateMixedDegree Omega G T i:=
   regularComponents_degree_budget phi F G T p hG hproper hGdegree hcutDegree
 have hagg:=aggregate_component_incidence Omega G T H Gamma
   (seedlessPoint phi) hGpoint hTpoint hHp (a-w) (nodes.card-w) 0
   cap (coordinateMixedDegree Omega G T) degree
   (fun C => by simpa only [Nat.zero_mul,Nat.add_zero] using hcomponent C)
   hbudget
 simpa only [T,Nat.zero_mul,Nat.add_zero] using hagg
end
end ProximityPrize.SubmissionLower.RCN283
end PackedLegacy_P0

/-! Packed from ProximityPrize.SubmissionLower.O8. -/
section PackedLegacy_O8
namespace ProximityPrize.SubmissionLower.RCN281
open scoped Classical BigOperators
open ProximityPrize.Benchmark RCN319 RCN174 RCN231 RCN081 RCN167 RCN313 RCN136 RCN135 RCN138 RCN137 RCN267 RCN238 RCN243 RCN222 RCN290 RCN293 RCN286 RCN279 RCN282 RCN283 RCN001
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
def prime:ℕ:=2130706433
def gap:ℕ:=agreements-w
def capY:ℕ:=1+2*w*yTotalCap
def capR:ℕ:=w*(2*slopeCap-1)
def agreementCap:Fin 3 → ℕ:=![capY,capR,1]
def regularListNumerator:ℕ:=
 (n-w)*(capY*slopeCap+capR*yTotalCap)
def singularListCap:ℕ:=(2*slopeCap-1)*yTotalCap
def listNumerator:ℕ:=regularListNumerator+singularListCap*gap
def listBudget:ℕ:=600000000
theorem numeric_values:
   gap=51207∧capY=13369243∧capR=2228207∧
     regularListNumerator=30666067671312∧
     singularListCap=867∧listNumerator=30666112067781:=by
 norm_num [gap,capY,capR,regularListNumerator,singularListCap,
   listNumerator,agreements,n,errors,w,yTotalCap,slopeCap]
theorem list_numerator_fits:listNumerator < listBudget*gap:=by
 norm_num [listNumerator,regularListNumerator,singularListCap,listBudget,
   gap,capY,capR,agreements,n,errors,w,yTotalCap,slopeCap]
theorem list_strict_ceiling_exact:
   listNumerator/gap+1=598865626∧
     listNumerator < 598865626*gap∧
     598865626 < listBudget:=by
 norm_num [listNumerator,regularListNumerator,singularListCap,listBudget,
   gap,capY,capR,agreements,n,errors,w,yTotalCap,slopeCap]
variable (K:Type) [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq (GenericField K):=Classical.decEq (GenericField K)
theorem seedless_degree_caps
   (Q:MvPolynomial (Fin 4) K)
   (hbox:Q∈RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap):
   Q.degreeOf 1 ≤ yTotalCap∧Q.degreeOf 2 ≤ slopeCap∧
     Q.degreeOf 3=0:=by
 refine ⟨MvPolynomial.degreeOf_le_iff.mpr ?_,
   MvPolynomial.degreeOf_le_iff.mpr ?_,?_⟩
 · intro d hd
   exact (Nat.le_add_right (d 1) (d 2)).trans (hbox hd).1
 · intro d hd
   exact (hbox hd).2.1
 · apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.2.1.le
theorem agreement_cap
   (phi:Polynomial K →+*GenericField K)
   (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3=0) (x u:K):
   ∀ j,(agreementPolynomial phi F w x u 0).degreeOf j ≤ agreementCap j:=by
 have hb:=agreementNumerator_degree_bounds F yTotalCap slopeCap 0
   (by norm_num [slopeCap]) hY hR hZ.le w
     (fun j => (j.factorial:K)⁻¹) x u 0
 intro j
 fin_cases j
 · exact (surfaceMap_degreeOf_le phi _ 0).trans
     (hb.1.trans (by simp [agreementCap,capY]))
 · exact (surfaceMap_degreeOf_le phi _ 1).trans
     (hb.2.1.trans (by simp [agreementCap,capR]))
 · exact (surfaceMap_degreeOf_le phi _ 2).trans
     (hb.2.2.trans (by simp [agreementCap]))
abbrev GeometricFactor (F:MvPolynomial (Fin 4) K):=
 RCN222.GeometricFactor K F
def geometricPolynomials (F:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)) (g:GeometricFactor K F):
   Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S =>
   MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S) g.1=0)
theorem geometricPolynomials_subset
   (F:MvPolynomial (Fin 4) K) (Gamma:Finset (Polynomial K))
   (g:GeometricFactor K F):geometricPolynomials K F Gamma g ⊆ Gamma:=by
 classical
 exact Finset.filter_subset _ _
theorem card_le_sum_geometricPolynomials
   (F:MvPolynomial (Fin 4) K) (hF:F≠0)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,specialization K S 0 F=0):
   Gamma.card ≤ ∑ g:GeometricFactor K F,
     (geometricPolynomials K F Gamma g).card:=by
 classical
 have hcover:Gamma ⊆ Finset.univ.biUnion (geometricPolynomials K F Gamma):=by
   intro S hS
   have hz:MvPolynomial.eval (seedlessPoint (polynomialEmbedding K) S)
       (surfaceMap (polynomialEmbedding K) F)=0:=by
     rw [seedlessPoint_surface_evaluation,
       eval_polynomialPoint_eq_specialization,hsolutions S hS]
     simp
   obtain ⟨g,hg,hzg⟩:=exists_surfaceFactor_zero (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F hF
     (seedlessPoint (polynomialEmbedding K) S) hz
   exact Finset.mem_biUnion.mpr ⟨⟨g,hg⟩,Finset.mem_univ _,
     Finset.mem_filter.mpr ⟨hS,hzg⟩⟩
 exact (Finset.card_le_card hcover).trans Finset.card_biUnion_le
theorem geometric_seedless_cut_proper
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hR:0 < g.degreeOf 1):
   ¬ g∣(seedlessCut:MvPolynomial (Fin 3) (GenericField K)):=by
 intro hdvd
 have hle:=coordinate_degree_le_of_dvd 1 g seedlessCut hdvd
   (by simp [seedlessCut])
 have hx:(seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
   simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2)]
 rw [hx] at hle
 omega
theorem original_regular_seedless_bound
   [CharP K prime]
   (F:MvPolynomial (Fin 4) K) (hF:Irreducible F)
   (hRpos:0 < F.degreeOf 2)
   (hbox:F∈RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hY:F.degreeOf 1 ≤ yTotalCap)
   (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3=0)
   (Gamma:Finset (Polynomial K))
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolutions:∀ S∈Gamma,specialization K S 0 F=0)
   (hregular:∀ S∈Gamma,
     specialization K S 0 (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hagreement:∀ S∈Gamma,agreements ≤
     (nodes.filter (fun i => S.eval (x i)=received i)).card):
   Gamma.card*gap ≤
     (n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
 classical
 letI:CharP (GenericField K) prime:=genericField_charP K prime
 have hsmall:F.degreeOf 2 < prime:=hR.trans_lt (by
   norm_num [slopeCap,prime])
 have hcount (g:GeometricFactor K F):
     (geometricPolynomials K F Gamma g).card*gap ≤
       (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=by
   obtain ⟨hgirred,hgdiv⟩:=
     surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
   have hgate:=geometric_factor_regular_gate K (GenericField K) F hF
     prime hRpos hsmall g.1 hgirred
     (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
   have hproper:=geometric_seedless_cut_proper K g.1 hgate.1
   have hgY:=(geometricFactor_degree_le K F hF.ne_zero g 0).trans hY
   have hgR:=(geometricFactor_degree_le K F hF.ne_zero g 1).trans hR
   have hgZ:g.1.degreeOf 2=0:=Nat.eq_zero_of_le_zero
     ((geometricFactor_degree_le K F hF.ne_zero g 2).trans_eq hZ)
   have hGdegree:∀ j:Fin 3,g.1.degreeOf j < prime:=by
     intro j
     fin_cases j
     · exact hgY.trans_lt (by norm_num [yTotalCap,prime])
     · exact hgR.trans_lt (by norm_num [slopeCap,prime])
     · simp [hgZ,prime]
   have hcutDegree:∀ j k:Fin 3,j≠k →
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf j*
           g.1.degreeOf k+
         g.1.degreeOf j*
           (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf k < prime:=by
     intro j k hjk
     have h0:=hGdegree 0
     have h1:=hGdegree 1
     have h2:=hGdegree 2
     fin_cases j <;> fin_cases k <;>
       simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne] at hjk ⊢ <;>
       omega
   have hsub:=geometricPolynomials_subset K F Gamma g
   have hraw:=seedless_proper_cut_bound (polynomialEmbedding K)
     (polynomialEmbedding_injective K) F g.1 hgirred hgdiv hproper
     (geometricPolynomials K F Gamma g) nodes x received hinj prime w agreements
     (by norm_num [w])
     (by norm_num [w,prime])
     (by norm_num [agreements,w,n,errors])
     (by rw [hnodes];norm_num [agreements,n,errors])
     hGdegree hcutDegree
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => hsolutions S (hsub hS))
     (fun S hS => selectedPoint_regular_of_specialization K F
       (fun _:K => S) 0 (hregular S (hsub hS)))
     (fun S hS => (Finset.mem_filter.mp hS).2)
     (fun S hS => hagreement S (hsub hS)) agreementCap
     (fun i hi => agreement_cap K (polynomialEmbedding K) F hY hR hZ
       (x i) (received i))
   have hx0:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 0=0:=by
     simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(0:Fin 3)≠2)]
   have hx1:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 1=0:=by
     simp [seedlessCut,MvPolynomial.degreeOf_X_of_ne (by decide:(1:Fin 3)≠2)]
   have hx2:
       (seedlessCut:MvPolynomial (Fin 3) (GenericField K)).degreeOf 2=1:=by
     simp [seedlessCut]
   have hm0:coordinateMixedDegree (GenericField K) g.1 seedlessCut 0=
       g.1.degreeOf 1:=by
     rw [RCN001.coordinateMixedDegree_zero,hx1,hx2]
     omega
   have hm1:coordinateMixedDegree (GenericField K) g.1 seedlessCut 1=
       g.1.degreeOf 0:=by
     rw [RCN001.coordinateMixedDegree_one,hx0,hx2]
     omega
   have hm2:coordinateMixedDegree (GenericField K) g.1 seedlessCut 2=0:=by
     rw [RCN001.coordinateMixedDegree_two,hx0,hx1]
     omega
   have hcost:
       (∑ i:Fin 3,agreementCap i*
         coordinateMixedDegree (GenericField K) g.1 seedlessCut i)=
       capY*g.1.degreeOf 1+capR*g.1.degreeOf 0:=by
     simp [Fin.sum_univ_succ,agreementCap,hm0,hm1,hm2]
   rw [hnodes,hcost] at hraw
   change (geometricPolynomials K F Gamma g).card*(agreements-w) ≤
     (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0)
   exact hraw
 calc
   Gamma.card*gap ≤
       (∑ g:GeometricFactor K F,
         (geometricPolynomials K F Gamma g).card)*gap:=
     Nat.mul_le_mul_right _
       (card_le_sum_geometricPolynomials K F hF.ne_zero Gamma hsolutions)
   _=∑ g:GeometricFactor K F,
       (geometricPolynomials K F Gamma g).card*gap:=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g:GeometricFactor K F,
       (n-w)*(capY*g.1.degreeOf 1+capR*g.1.degreeOf 0):=
     Finset.sum_le_sum (fun g _ => hcount g)
   _=(n-w)*(capY*(∑ g:GeometricFactor K F,g.1.degreeOf 1)+
       capR*(∑ g:GeometricFactor K F,g.1.degreeOf 0)):=by
     rw [←Finset.mul_sum,Finset.sum_add_distrib,
       ←Finset.mul_sum, ←Finset.mul_sum]
   _ ≤ (n-w)*(capY*F.degreeOf 2+capR*F.degreeOf 1):=by
     apply Nat.mul_le_mul_left
     exact Nat.add_le_add
       (Nat.mul_le_mul_left capY (geometricFactor_sum_degree_le K F hF.ne_zero 1))
       (Nat.mul_le_mul_left capR (geometricFactor_sum_degree_le K F hF.ne_zero 0))
def yProjection (T:Type*) [Field T]:
   MvPolynomial (Fin 3) T →+*Polynomial T:=
 MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X,0,0]
def yEmbedding (T:Type*) [Field T]:
   Polynomial T →+*MvPolynomial (Fin 3) T:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
theorem y_only_vars {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
   (i:Fin 3) (hi:i∈S.vars):i=0:=by
 fin_cases i
 · rfl
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hZ)
theorem yProjection_reconstruct {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
   yEmbedding T (yProjection T S)=S:=by
 change ((yEmbedding T).comp (yProjection T)) S=(RingHom.id _) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [yEmbedding,yProjection]
 · intro i hi _
   rw [y_only_vars S hR hZ i hi]
   simp [yEmbedding,yProjection]
 · rfl
theorem yProjection_nonzero {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T) (hS:S≠0)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0):
   yProjection T S≠0:=by
 intro hz
 apply hS
 rw [←yProjection_reconstruct S hR hZ,hz,map_zero]
theorem yProjection_natDegree_le {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T):
   (yProjection T S).natDegree ≤ S.degreeOf 0:=by
 classical
 have hsum:yProjection T S=
     ∑ d∈S.support,yProjection T (MvPolynomial.monomial d (S.coeff d)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 rw [hsum]
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro d hd
 have hmono:(yProjection T (MvPolynomial.monomial d (S.coeff d))).natDegree ≤
     d 0:=by
   have heq:MvPolynomial.monomial d (S.coeff d)=
       MvPolynomial.C (S.coeff d)*MvPolynomial.X 0^d 0*
         MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
     exact RCN080.monomial_fin3 d (S.coeff d)
   rw [heq]
   by_cases h1:d 1=0 <;> by_cases h2:d 2=0 <;>
     simp [yProjection,h1,h2]
   have hc:(Polynomial.C (S.coeff d)).natDegree ≤ 0:=by simp
   have hx:((Polynomial.X:Polynomial T)^d 0).natDegree ≤ d 0:=by simp
   simpa only [Nat.zero_add] using Polynomial.natDegree_mul_le_of_le hc hx
 exact hmono.trans (MvPolynomial.monomial_le_degreeOf 0 hd)
theorem yProjection_eval {T:Type*} [Field T]
   (S:MvPolynomial (Fin 3) T)
   (hR:S.degreeOf 1=0) (hZ:S.degreeOf 2=0)
   (v:Fin 3 → T):
   (yProjection T S).eval (v 0)=MvPolynomial.eval v S:=by
 change ((Polynomial.evalRingHom (v 0)).comp (yProjection T)) S=
   (MvPolynomial.eval v) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [yProjection]
 · intro i hi _
   rw [y_only_vars S hR hZ i hi]
   simp [yProjection]
 · rfl
def yWeights:Fin 4 → ℕ:=![0,1,0,0]
def zWeights:Fin 4 → ℕ:=![0,0,0,1]
theorem degreeY_le_yWeight (Q:MvPolynomial (Fin 4) K):
   Q.degreeOf 1 ≤ MvPolynomial.weightedTotalDegree yWeights Q:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=MvPolynomial.le_weightedTotalDegree yWeights hd
 rw [weight_fin4] at h
 simpa [yWeights] using h
theorem degreeZ_le_zWeight (Q:MvPolynomial (Fin 4) K):
   Q.degreeOf 3 ≤ MvPolynomial.weightedTotalDegree zWeights Q:=by
 apply MvPolynomial.degreeOf_le_iff.mpr
 intro d hd
 have h:=MvPolynomial.le_weightedTotalDegree zWeights hd
 rw [weight_fin4] at h
 simpa [zWeights] using h
theorem singular_seedless_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,
     specialization K S 0 (singularAuxiliary Q)=0):
   Gamma.card ≤ singularListCap:=by
 classical
 let phi:=polynomialEmbedding K
 let J:=singularAuxiliary Q
 have hcaps:=seedless_degree_caps K Q hbox
 have hJne:J≠0:=singularAuxiliary_nonzero Q hQ prime
   (hcaps.2.1.trans_lt (by norm_num [slopeCap,prime]))
 have hJR:J.degreeOf 2=0:=singularAuxiliary_R_degree Q hQ prime
   (hcaps.2.1.trans_lt (by norm_num [slopeCap,prime]))
 have hQY:MvPolynomial.weightedTotalDegree yWeights Q ≤ yTotalCap:=by
   apply (weightedTotalDegree_le_iff yWeights Q yTotalCap).mpr
   intro d hd
   have hh:=(hbox hd).1
   rw [weight_fin4]
   simpa [yWeights] using (Nat.le_add_right (d 1) (d 2)).trans hh
 have hQZ:MvPolynomial.weightedTotalDegree zWeights Q ≤ 0:=by
   apply (weightedTotalDegree_le_iff zWeights Q 0).mpr
   intro d hd
   have hh:=(hbox hd).2.2.1
   rw [weight_fin4]
   simpa [zWeights,hh]
 have hJYw:=singularAuxiliary_weight_le yWeights Q hQ slopeCap
   (by norm_num [slopeCap]) hcaps.2.1
 have hJZw:=singularAuxiliary_weight_le zWeights Q hQ slopeCap
   (by norm_num [slopeCap]) hcaps.2.1
 have hJY:J.degreeOf 1 ≤ singularListCap:=
   (degreeY_le_yWeight K J).trans (hJYw.trans (by
     unfold singularListCap
     exact Nat.mul_le_mul_left _ hQY))
 have hJZ:J.degreeOf 3=0:=Nat.eq_zero_of_le_zero
   ((degreeZ_le_zWeight K J).trans (hJZw.trans (by
     simpa only [Nat.mul_zero] using Nat.mul_le_mul_left (2*slopeCap-1) hQZ)))
 let A:MvPolynomial (Fin 3) (GenericField K):=surfaceMap phi J
 have hAne:A≠0:=surfaceMap_ne_zero phi (polynomialEmbedding_injective K) J hJne
 have hAR:A.degreeOf 1=0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 1).trans_eq hJR)
 have hAZ:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero
   ((surfaceMap_degreeOf_le phi J 2).trans_eq hJZ)
 let q:Polynomial (GenericField K):=yProjection (GenericField K) A
 have hq:q≠0:=yProjection_nonzero A hAne hAR hAZ
 have hroots:∀ z∈Gamma.image phi,z∈q.roots:=by
   intro z hz
   obtain ⟨S,hS,rfl⟩:=Finset.mem_image.mp hz
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (phi S)=0
   have hv:seedlessPoint phi S 0=phi S:=by
     simp [seedlessPoint_value]
   change (yProjection (GenericField K) A).eval (phi S)=0
   rw [←hv,yProjection_eval A hAR hAZ (seedlessPoint phi S)]
   rw [seedlessPoint_surface_evaluation,eval_polynomialPoint_eq_specialization,
     hsolutions S hS]
   simp
 have hcard:(Gamma.image phi).card=Gamma.card:=
   Finset.card_image_of_injective _ (polynomialEmbedding_injective K)
 rw [←hcard]
 calc
   (Gamma.image phi).card ≤ q.roots.toFinset.card:=by
     apply Finset.card_le_card
     intro z hz
     exact Multiset.mem_toFinset.mpr (hroots z hz)
   _ ≤ q.roots.card:=Multiset.toFinset_card_le _
   _ ≤ q.natDegree:=Polynomial.card_roots' q
   _ ≤ A.degreeOf 0:=yProjection_natDegree_le A
   _ ≤ J.degreeOf 1:=surfaceMap_degreeOf_le phi J 0
   _ ≤ singularListCap:=hJY
def singularPolynomials (Q:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)):Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S => specialization K S 0 (singularAuxiliary Q)=0)
def regularPolynomials (Q:MvPolynomial (Fin 4) K)
   (Gamma:Finset (Polynomial K)) (F:↥(positiveRFactors Q)):
   Finset (Polynomial K):=by
 classical
 exact Gamma.filter (fun S => RegularSolution F.1 S 0)
theorem seedless_solution_cover
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (Gamma:Finset (Polynomial K))
   (hsolutions:∀ S∈Gamma,specialization K S 0 Q=0):
   Gamma.card ≤ (singularPolynomials K Q Gamma).card+
     ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=by
 classical
 let regularUnion:=Finset.univ.biUnion (regularPolynomials K Q Gamma)
 have hcover:Gamma ⊆ singularPolynomials K Q Gamma ∪ regularUnion:=by
   intro S hS
   obtain hsing | ⟨F,hF,hreg⟩:=solution_regular_or_auxiliary
     Q hQ S 0 (hsolutions S hS)
   · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hsing⟩)
   · apply Finset.mem_union_right
     apply Finset.mem_biUnion.mpr
     exact ⟨⟨F,hF⟩,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hS,hreg⟩⟩
 calc
   Gamma.card ≤ (singularPolynomials K Q Gamma ∪ regularUnion).card:=
     Finset.card_le_card hcover
   _ ≤ (singularPolynomials K Q Gamma).card+regularUnion.card:=
     Finset.card_union_le _ _
   _ ≤ (singularPolynomials K Q Gamma).card+
       ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card:=
     Nat.add_le_add_left Finset.card_biUnion_le _
theorem seedless_list_card_le
   [CharP K prime]
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (hbox:Q∈RCN279.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (hlegacy:Q∈RCN174.globalCoefficientBox K
     weightedCap w yTotalCap slopeCap)
   (Gamma:Finset (Polynomial K))
   {Iota:Type} [Fintype Iota] [DecidableEq Iota]
   (nodes:Finset Iota) (x received:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=n)
   (hdegree:∀ S∈Gamma,S.natDegree ≤ w)
   (hsolutions:∀ S∈Gamma,specialization K S 0 Q=0)
   (hagreement:∀ S∈Gamma,agreements ≤
     (nodes.filter (fun i => S.eval (x i)=received i)).card):
   Gamma.card ≤ listBudget:=by
 classical
 have hcaps:=seedless_degree_caps K Q hbox
 have hsing:(singularPolynomials K Q Gamma).card ≤ singularListCap:=
   singular_seedless_card_le K Q hQ hbox (singularPolynomials K Q Gamma)
     (fun S hS => (Finset.mem_filter.mp hS).2)
 have hreg (F:↥(positiveRFactors Q)):
     (regularPolynomials K Q Gamma F).card*gap ≤
       (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=by
   have hdata:=directFactor_data Q F.1 hQ weightedCap w yTotalCap slopeCap
     hlegacy F.2
   have hdivF:=(positiveRFactors_spec Q F.1 F.2).2.1
   have hFZ:F.1.degreeOf 3=0:=Nat.eq_zero_of_le_zero
     ((degreeOf_le_of_dvd 3 F.1 Q hdivF hQ).trans_eq hcaps.2.2)
   have hsub:regularPolynomials K Q Gamma F ⊆ Gamma:=Finset.filter_subset _ _
   exact original_regular_seedless_bound K F.1 hdata.1 hdata.2.1 hdata.2.2
     ((degreeOf_le_of_dvd 1 F.1 Q hdivF hQ).trans hcaps.1)
     ((degreeOf_le_of_dvd 2 F.1 Q hdivF hQ).trans hcaps.2.1)
     hFZ (regularPolynomials K Q Gamma F)
     (fun S hS => hdegree S (hsub hS))
     (fun S hS => (Finset.mem_filter.mp hS).2.1)
     (fun S hS => (Finset.mem_filter.mp hS).2.2)
     nodes x received hinj hnodes (fun S hS => hagreement S (hsub hS))
 have hsumY:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 1
 have hsumR:=sum_coordinate_degrees_le_of_prod_dvd
   (positiveRFactors Q) id Q hQ (positiveRFactors_product_dvd Q hQ) 2
 have hsumY':(∑ F:↥(positiveRFactors Q),F.1.degreeOf 1) ≤ Q.degreeOf 1:=by
   simpa only [Finset.sum_coe_sort,id_eq] using hsumY
 have hsumR':(∑ F:↥(positiveRFactors Q),F.1.degreeOf 2) ≤ Q.degreeOf 2:=by
   simpa only [Finset.sum_coe_sort,id_eq] using hsumR
 have hregularScaled:
     (∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap ≤
       regularListNumerator:=by
   calc
     _=∑ F:↥(positiveRFactors Q),
         (regularPolynomials K Q Gamma F).card*gap:=by rw [Finset.sum_mul]
     _ ≤ ∑ F:↥(positiveRFactors Q),
         (n-w)*(capY*F.1.degreeOf 2+capR*F.1.degreeOf 1):=
       Finset.sum_le_sum (fun F _ => hreg F)
     _=(n-w)*(capY*(∑ F:↥(positiveRFactors Q),F.1.degreeOf 2)+
         capR*(∑ F:↥(positiveRFactors Q),F.1.degreeOf 1)):=by
       rw [←Finset.mul_sum,Finset.sum_add_distrib,
         ←Finset.mul_sum, ←Finset.mul_sum]
     _ ≤ (n-w)*(capY*slopeCap+capR*yTotalCap):=by
       apply Nat.mul_le_mul_left
       exact Nat.add_le_add (Nat.mul_le_mul_left capY (hsumR'.trans hcaps.2.1))
         (Nat.mul_le_mul_left capR (hsumY'.trans hcaps.1))
     _=regularListNumerator:=rfl
 have hcover:=seedless_solution_cover K Q hQ Gamma hsolutions
 have hscaled:=Nat.mul_le_mul_right gap hcover
 have htotal:Gamma.card*gap ≤ listNumerator:=by
   calc
     Gamma.card*gap ≤
         ((singularPolynomials K Q Gamma).card+
           ∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap:=
       hscaled
     _=(singularPolynomials K Q Gamma).card*gap+
         (∑ F:↥(positiveRFactors Q),(regularPolynomials K Q Gamma F).card)*gap:=by
       ring
     _ ≤ singularListCap*gap+regularListNumerator:=
       Nat.add_le_add (Nat.mul_le_mul_right gap hsing) hregularScaled
     _=listNumerator:=by simp only [listNumerator];ring
 by_contra hnot
 have hlarge:listBudget < Gamma.card:=Nat.lt_of_not_ge hnot
 have hgap:0 < gap:=by norm_num [gap,agreements,n,errors,w]
 have hmul:=Nat.mul_lt_mul_of_pos_right hlarge hgap
 have hcontra:listBudget*gap < listNumerator:=hmul.trans_le htotal
 exact (Nat.not_lt_of_ge hcontra.le) list_numerator_fits
end
end ProximityPrize.SubmissionLower.RCN281
end PackedLegacy_O8

/-! Packed from ProximityPrize.SubmissionLower.H7. -/
section PackedLegacy_H7
namespace ProximityPrize.SubmissionLower.RCN020
noncomputable section Proofs
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
def ZeroCoordinateBound (C:LinearCode ι F) (w:ℕ):Prop:=
 ∀ c:ι → F,c∈C → c≠0 →
   (Finset.univ.filter (fun i => c i=0)).card ≤ w
theorem eq_of_agreement_on_large_support
   (C:LinearCode ι F) (w:ℕ) (hzero:ZeroCoordinateBound C w)
   (c d:ι → F) (hc:c∈C) (hd:d∈C)
   (A:Finset ι) (hA:w < A.card)
   (hagree:∀ i∈A,c i=d i):c=d:=by
 classical
 by_contra hne
 have hbound:=hzero (c-d) (C.sub_mem hc hd) (sub_ne_zero.mpr hne)
 have hsub:A ⊆ Finset.univ.filter (fun i => (c-d) i=0):=by
   intro i hi
   refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
   change c i-d i=0
   exact sub_eq_zero.mpr (hagree i hi)
 have hcard:=Finset.card_le_card hsub
 omega
theorem seed_indexed_list_card_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (u:ι → F) (S:Finset F) (selected:F → ι → F)
   (A:F → Finset ι)
   (hinj:Set.InjOn selected S)
   (hcode:∀ seed∈S,selected seed∈C)
   (hcard:∀ seed∈S,Fintype.card ι-e ≤ (A seed).card)
   (hagree:∀ seed∈S,∀ i∈A seed,selected seed i=u i):
   S.card ≤ B:=by
 classical
 by_contra hnot
 have hlarge:B < S.card:=Nat.lt_of_not_ge hnot
 let U:Fin 2 → ι → F:=![u,0]
 have hprojected:∀ seed∈S,
     LinearCode.projectedWord (fun i => U 0 i+seed*U 1 i) (A seed)∈
       LinearCode.projectedCodeSubmod C (A seed):=by
   intro seed hseed
   rw [LinearCode.mem_projectedCodeSubmod_iff]
   refine ⟨selected seed,hcode seed hseed,?_⟩
   funext i
   change u i.1+seed*0=selected seed i.1
   simpa only [mul_zero,add_zero] using (hagree seed hseed i.1 i.2).symm
 obtain ⟨p,hp,T,hTS,hTcard,heq⟩:=
   halign U S A hlarge hcard hprojected
 obtain ⟨seed,hseed,hcommon⟩:=
   ProximityPrize.SubmissionLower.exists_common_affine_set U p T A e hTcard
     (fun z hz => hcard z (hTS hz)) heq
 have hdir:p 1=0:=by
   apply eq_of_agreement_on_large_support C w hzero (p 1) 0 (hp 1) C.zero_mem
     (A seed) (hgap.trans_le (hcard seed (hTS hseed)))
   intro i hi
   have hv:=(hcommon i hi).2
   change 0=p 1 i at hv
   exact hv.symm
 have hselected:∀ z∈T,selected z=p 0:=by
   intro z hz
   apply eq_of_agreement_on_large_support C w hzero (selected z) (p 0)
     (hcode z (hTS hz)) (hp 0) (A z) (hgap.trans_le (hcard z (hTS hz)))
   intro i hi
   have hv:=heq z hz i hi
   change u i+z*0=p 0 i+z*p 1 i at hv
   have hdi:p 1 i=0:=congrFun hdir i
   have huv:u i=p 0 i:=by
     simpa only [hdi,mul_zero,add_zero] using hv
   exact (hagree z (hTS hz) i hi).trans huv
 have hsmall:T.card ≤ 1:=by
   apply Finset.card_le_one.mpr
   intro z hz t ht
   exact hinj (hTS hz) (hTS ht) ((hselected z hz).trans (hselected t ht).symm)
 omega
theorem finite_list_card_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (u:ι → F) (L:Finset (ι → F))
   (hcode:∀ c∈L,c∈C)
   (hclose:∀ c∈L,
     Fintype.card ι-e ≤ (Finset.univ.filter (fun i => c i=u i)).card):
   L.card ≤ B:=by
 classical
 letI:DecidableEq (ι → F):=Classical.decEq (ι → F)
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩:=
   Finset.exists_subset_card_eq (show B+1 ≤ L.card by omega)
 have hsize:Fintype.card ↥D ≤ Fintype.card F:=by
   rw [Fintype.card_coe,hDcard]
   omega
 let toSeed:↥D → F:=fun d =>
   (Fintype.equivFin F).symm
     ⟨(Fintype.equivFin ↥D d).val,
       lt_of_lt_of_le (Fintype.equivFin ↥D d).isLt hsize⟩
 have htoSeed:Function.Injective toSeed:=by
   intro c d heq
   apply (Fintype.equivFin ↥D).injective
   apply Fin.ext
   have hfin:=(Fintype.equivFin F).symm.injective heq
   exact congrArg (fun z:Fin (Fintype.card F) => z.val) hfin
 let S:Finset F:=Finset.univ.image toSeed
 have hScard:S.card=D.card:=by
   change (Finset.univ.image toSeed).card=D.card
   rw [Finset.card_image_of_injective _ htoSeed,Finset.card_univ,
     Fintype.card_coe]
 have hex (seed:F) (hseed:seed∈S):∃ d:↥D,toSeed d=seed:=by
   obtain ⟨d,_,hd⟩:=Finset.mem_image.mp hseed
   exact ⟨d,hd⟩
 let chosen:(seed:F) → seed∈S → ↥D:=
   fun seed hseed => Classical.choose (hex seed hseed)
 have hchosen (seed:F) (hseed:seed∈S):
     toSeed (chosen seed hseed)=seed:=Classical.choose_spec (hex seed hseed)
 let selected:F → ι → F:=fun seed =>
   if hseed:seed∈S then (chosen seed hseed).val else 0
 have hselected (seed:F) (hseed:seed∈S):
     selected seed=(chosen seed hseed).val:=by
   dsimp only [selected]
   exact dif_pos hseed
 have hmem (seed:F) (hseed:seed∈S):selected seed∈L:=by
   have hh:=hDL (chosen seed hseed).property
   simpa only [selected,dif_pos hseed] using hh
 have hinj:Set.InjOn selected S:=by
   intro seed hseed other hother heq
   have hd:chosen seed hseed=chosen other hother:=by
     apply Subtype.ext
     exact (hselected seed hseed).symm.trans (heq.trans (hselected other hother))
   exact (hchosen seed hseed).symm.trans
     ((congrArg toSeed hd).trans (hchosen other hother))
 let A:F → Finset ι:=fun seed =>
   Finset.univ.filter (fun i => selected seed i=u i)
 have hbounded:S.card ≤ B:=seed_indexed_list_card_le C e w B hzero hgap
   halign u S selected A hinj
   (fun seed hseed => hcode _ (hmem seed hseed))
   (fun seed hseed => hclose _ (hmem seed hseed))
   (fun seed _ i hi => (Finset.mem_filter.mp hi).2)
 rw [hScard,hDcard] at hbounded
 omega
def scalarList (C:LinearCode ι F) (u:ι → F) (e:ℕ):
   Finset (ι → F):=by
 classical
 exact Finset.univ.filter (fun c => c∈C∧
   Fintype.card ι-e ≤ (Finset.univ.filter (fun i => c i=u i)).card)
theorem scalarList_card_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F) (u:ι → F):
   (scalarList C u e).card ≤ B:=by
 classical
 apply finite_list_card_le C e w B hzero hgap halign hfield u (scalarList C u e)
 · intro c hc
   exact (Finset.mem_filter.mp hc).2.1
 · intro c hc
   exact (Finset.mem_filter.mp hc).2.2
end Proofs
end ProximityPrize.SubmissionLower.RCN020
end PackedLegacy_H7

/-! Packed from ProximityPrize.SubmissionLower.H6. -/
section PackedLegacy_H6
namespace ProximityPrize.SubmissionLower.RCN019
open scoped BigOperators
noncomputable section Proofs
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
 {r:ℕ}
def rowPolynomial (v:Fin r → F):Polynomial F:=
 ∑ j:Fin r,Polynomial.monomial j.val (v j)
theorem rowPolynomial_coeff (v:Fin r → F) (j:Fin r):
   (rowPolynomial v).coeff j.val=v j:=by
 classical
 rw [rowPolynomial,Polynomial.finsetSum_coeff]
 calc
   (∑ k:Fin r,(Polynomial.monomial k.val (v k)).coeff j.val)=
       (Polynomial.monomial j.val (v j)).coeff j.val:=by
     apply Finset.sum_eq_single j
     · intro k _ hkj
       have hval:k.val≠j.val:=fun hh => hkj (Fin.ext hh)
       simp [Polynomial.coeff_monomial,hval,Ne.symm hval]
     · intro hnot
       exact (hnot (Finset.mem_univ j)).elim
   _=v j:=by simp [Polynomial.coeff_monomial]
theorem rowPolynomial_injective:
   Function.Injective (rowPolynomial:(Fin r → F) → Polynomial F):=by
 intro v u heq
 funext j
 have hc:=congrArg (fun P:Polynomial F => P.coeff j.val) heq
 simpa only [rowPolynomial_coeff] using hc
theorem rowPolynomial_natDegree_le (v:Fin r → F):
   (rowPolynomial v).natDegree ≤ r-1:=by
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro j _
 have hterm:=Polynomial.natDegree_monomial_le (v j) (m:=j.val)
 have hj:=j.isLt
 exact hterm.trans (by omega)
def momentProjection (t:F) (v:ι → Fin r → F):ι → F:=
 fun i => (rowPolynomial (v i)).eval t
theorem momentProjection_apply (t:F) (v:ι → Fin r → F) (i:ι):
   momentProjection t v i=∑ j:Fin r,t^j.val*v i j:=by
 change (Polynomial.evalRingHom t)
     (∑ j:Fin r,Polynomial.monomial j.val (v i j))=_
 rw [map_sum]
 apply Finset.sum_congr rfl
 intro j _
 change (Polynomial.monomial j.val (v i j)).eval t=t^j.val*v i j
 rw [Polynomial.eval_monomial,mul_comm]
theorem exists_nonzero_coordinate_difference
   (v u:ι → Fin r → F) (hne:v≠u):
   ∃ P:Polynomial F,P≠0∧P.natDegree ≤ r-1∧
     ∀ t:F,momentProjection t v=momentProjection t u → P.eval t=0:=by
 classical
 obtain ⟨i,hi⟩:∃ i:ι,v i≠u i:=by
   by_contra hno
   push_neg at hno
   exact hne (funext hno)
 refine ⟨rowPolynomial (v i)-rowPolynomial (u i),?_,?_,?_⟩
 · apply sub_ne_zero.mpr
   intro hh
   exact hi (rowPolynomial_injective hh)
 · exact (Polynomial.natDegree_sub_le _ _).trans
     (max_le (rowPolynomial_natDegree_le _) (rowPolynomial_natDegree_le _))
 · intro t ht
   rw [Polynomial.eval_sub]
   exact sub_eq_zero.mpr (congrFun ht i)
def pairCollisionSeeds (pair:Finset (ι → Fin r → F)):Finset F:=by
 classical
 exact Finset.univ.filter (fun t => ∃ v∈pair,∃ u∈pair,
   v≠u∧momentProjection t v=momentProjection t u)
theorem mem_pairCollisionSeeds_iff
   (pair:Finset (ι → Fin r → F)) (t:F):
   t∈pairCollisionSeeds pair ↔ ∃ v∈pair,∃ u∈pair,
     v≠u∧momentProjection t v=momentProjection t u:=by
 classical
 simp only [pairCollisionSeeds,Finset.mem_filter,Finset.mem_univ,true_and]
theorem pairCollisionSeeds_card_le
   (pair:Finset (ι → Fin r → F)) (hpair:pair.card=2):
   (pairCollisionSeeds pair).card ≤ r-1:=by
 classical
 letI:DecidableEq (ι → Fin r → F):=Classical.decEq (ι → Fin r → F)
 obtain ⟨v,u,hne,rfl⟩:=Finset.card_eq_two.mp hpair
 obtain ⟨P,hP,hdegree,heval⟩:=exists_nonzero_coordinate_difference v u hne
 have hcard:(pairCollisionSeeds ({v,u}:Finset (ι → Fin r → F))).card ≤
     P.natDegree:=by
   apply Polynomial.card_le_degree_of_subset_roots
   intro t ht
   apply (Polynomial.mem_roots hP).mpr
   apply heval t
   have ht':t∈pairCollisionSeeds ({v,u}:Finset (ι → Fin r → F)):=ht
   obtain ⟨a,ha,b,hb,hab,habproj⟩:=
     (mem_pairCollisionSeeds_iff ({v,u}:Finset (ι → Fin r → F)) t).mp ht'
   simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
   rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
   · exact (hab rfl).elim
   · exact habproj
   · exact habproj.symm
   · exact (hab rfl).elim
 exact hcard.trans hdegree
def allCollisionSeeds (L:Finset (ι → Fin r → F)):Finset F:=by
 classical
 exact (L.powersetCard 2).biUnion pairCollisionSeeds
theorem allCollisionSeeds_card_le (L:Finset (ι → Fin r → F)):
   (allCollisionSeeds L).card ≤ (r-1)*L.card.choose 2:=by
 classical
 calc
   (allCollisionSeeds L).card ≤
       ∑ pair∈L.powersetCard 2,(pairCollisionSeeds pair).card:=
     Finset.card_biUnion_le
   _ ≤ ∑ _pair∈L.powersetCard 2,(r-1):=by
     apply Finset.sum_le_sum
     intro pair hpair
     exact pairCollisionSeeds_card_le pair (Finset.mem_powersetCard.mp hpair).2
   _=(L.powersetCard 2).card*(r-1):=by simp
   _=(r-1)*L.card.choose 2:=by
     rw [Finset.card_powersetCard,Nat.mul_comm]
theorem exists_separating_moment_parameter
   (L:Finset (ι → Fin r → F))
   (hfield:(r-1)*L.card.choose 2 < Fintype.card F):
   ∃ t:F,Set.InjOn (momentProjection (ι:=ι) (r:=r) t)
     (L:Set (ι → Fin r → F)):=by
 classical
 letI:DecidableEq (ι → Fin r → F):=Classical.decEq (ι → Fin r → F)
 have hsmall:(allCollisionSeeds L).card < Fintype.card F:=
   (allCollisionSeeds_card_le L).trans_lt hfield
 obtain ⟨t,ht⟩:∃ t:F,t∉allCollisionSeeds L:=by
   by_contra hno
   have hsub:Finset.univ ⊆ allCollisionSeeds L:=by
     intro t _
     by_contra ht
     exact hno ⟨t,ht⟩
   have hc:=Finset.card_le_card hsub
   rw [Finset.card_univ] at hc
   omega
 refine ⟨t,?_⟩
 intro v hv u hu hproj
 change v∈L at hv
 change u∈L at hu
 by_contra hne
 apply ht
 apply Finset.mem_biUnion.mpr
 refine ⟨{v,u},?_,?_⟩
 · apply Finset.mem_powersetCard.mpr
   constructor
   · intro c hc
     simp only [Finset.mem_insert,Finset.mem_singleton] at hc
     rcases hc with rfl | rfl
     · exact hv
     · exact hu
   · simp [hne]
 · apply (mem_pairCollisionSeeds_iff ({v,u}:Finset (ι → Fin r → F)) t).mpr
   exact ⟨v,by simp,u,by simp,hne,hproj⟩
theorem momentProjection_mem_code
   (C:LinearCode ι F) (t:F) (v:ι → Fin r → F)
   (hrows:∀ j:Fin r,(fun i => v i j)∈C):
   momentProjection t v∈C:=by
 classical
 have heq:momentProjection t v=
     ∑ j:Fin r,t^j.val • (fun i => v i j):=by
   funext i
   rw [momentProjection_apply]
   simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
 rw [heq]
 exact C.sum_mem (fun j _ => C.smul_mem (t^j.val) (hrows j))
theorem momentProjection_preserves_agreements
   (t:F) (v u:ι → Fin r → F):
   (Finset.univ.filter (fun i => v i=u i)) ⊆
     Finset.univ.filter (fun i => momentProjection t v i=momentProjection t u i):=by
 classical
 intro i hi
 refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
 have hv:=(Finset.mem_filter.mp hi).2
 change (rowPolynomial (v i)).eval t=(rowPolynomial (u i)).eval t
 rw [hv]
theorem interleaved_finite_list_card_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:RCN020.ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (hseparation:(r-1)*(B+1).choose 2 < Fintype.card F)
   (u:ι → Fin r → F) (L:Finset (ι → Fin r → F))
   (hrows:∀ v∈L,∀ j:Fin r,(fun i => v i j)∈C)
   (hclose:∀ v∈L,
     Fintype.card ι-e ≤ (Finset.univ.filter (fun i => v i=u i)).card):
   L.card ≤ B:=by
 classical
 letI:DecidableEq (ι → Fin r → F):=Classical.decEq (ι → Fin r → F)
 letI:DecidableEq (ι → F):=Classical.decEq (ι → F)
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩:=
   Finset.exists_subset_card_eq (show B+1 ≤ L.card by omega)
 have hsepD:(r-1)*D.card.choose 2 < Fintype.card F:=by
   rw [hDcard]
   exact hseparation
 obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
 let projected:Finset (ι → F):=D.image (momentProjection (ι:=ι) (r:=r) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀ c∈projected,c∈C:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact momentProjection_mem_code C t v (hrows v (hDL hv))
 have hnear:∀ c∈projected,
     Fintype.card ι-e ≤
       (Finset.univ.filter (fun i => c i=momentProjection t u i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose v (hDL hv)).trans
     (Finset.card_le_card (momentProjection_preserves_agreements t v u))
 have hbound:=RCN020.finite_list_card_le C e w B
   hzero hgap halign hfield (momentProjection t u) projected hcode hnear
 rw [hprojcard,hDcard] at hbound
 omega
end Proofs
end ProximityPrize.SubmissionLower.RCN019
end PackedLegacy_H6

/-! Packed from ProximityPrize.SubmissionLower.H5. -/
section PackedLegacy_H5
namespace ProximityPrize.SubmissionLower.RCN018
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section DraftProofs
section RadiusCell
variable {ι A:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [DecidableEq A]
theorem agreement_card_ge_of_closeCodewordsRel
   (C:Set (ι → A)) (y c:ι → A) (δ:ℝ) (e:ℕ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ))
   (hc:c∈Code.closeCodewordsRel C y δ):
   Fintype.card ι-e ≤
     (Finset.univ.filter (fun i => c i=y i)).card:=by
 classical
 have hball:=(Code.mem_closeCodewordsRel_iff.mp hc).2
 simp only [Code.relHammingDist_coe] at hball
 have hn:(0:ℝ) < (Fintype.card ι:ℝ):=by
   exact_mod_cast Fintype.card_pos
 have hdistR:(hammingDist y c:ℝ) < ((e+1:ℕ):ℝ):=
   ((div_le_iff₀ hn).mp hball).trans_lt hcell
 have hdist:hammingDist y c ≤ e:=by
   have hlt:hammingDist y c < e+1:=by exact_mod_cast hdistR
   omega
 have hagree:Code.agree c y+hammingDist y c=Fintype.card ι:=by
   rw [hammingDist_comm]
   exact Code.agree_add_hammingDist (u:=c) (v:=y)
 change Fintype.card ι-e ≤ Code.agree c y
 omega
end RadiusCell
theorem radius_cell_of_floor_le (δ:ℝ) (n e:ℕ)
   (hfloor:⌊δ*(n:ℝ)⌋₊ ≤ e):
   δ*(n:ℝ) < ((e+1:ℕ):ℝ):=by
 have hf:(⌊δ*(n:ℝ)⌋₊:ℝ) ≤ (e:ℝ):=by exact_mod_cast hfloor
 calc
   δ*(n:ℝ) < (⌊δ*(n:ℝ)⌋₊:ℝ)+1:=Nat.lt_floor_add_one _
   _ ≤ (e:ℝ)+1:=by linarith
   _=((e+1:ℕ):ℝ):=by simp only [Nat.cast_add,Nat.cast_one]
theorem rational_radius_cell (num den n e:ℕ) (hden:0 < den)
   (hcross:num*n < (e+1)*den):
   ((num:ℝ)/(den:ℝ))*(n:ℝ) < ((e+1:ℕ):ℝ):=by
 have hdenR:(0:ℝ) < (den:ℝ):=by exact_mod_cast hden
 calc
   ((num:ℝ)/(den:ℝ))*(n:ℝ)=
       ((num*n:ℕ):ℝ)/(den:ℝ):=by push_cast;ring
   _ < ((e+1:ℕ):ℝ):=(div_lt_iff₀ hdenR).mpr (by exact_mod_cast hcross)
section GenericCode
variable {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
 [Field F] [Fintype F] [DecidableEq F]
theorem interleaved_lambda_le
   (C:LinearCode ι F) (r e w B:ℕ)
   (hzero:RCN020.ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (hseparation:(r-1)*(B+1).choose 2 < Fintype.card F)
   (δ:ℝ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     ((C^⋈ (Fin r):ModuleCode ι F (Fin r → F)):Set (ι → Fin r → F))
     δ ≤ (B:ℕ∞):=by
 classical
 apply Code.Lambda_le_of_forall_finset_card_le
 intro y T hT
 apply RCN019.interleaved_finite_list_card_le
   C e w B hzero hgap halign hfield hseparation y T
 · intro c hc j
   have hcode:=(Code.mem_closeCodewordsRel_iff.mp (hT c hc)).1
   exact (Code.mem_moduleInterleavedCode_iff F F (Fin r) ι C c).mp hcode j
 · intro c hc
   exact agreement_card_ge_of_closeCodewordsRel _ y c δ e hcell (hT c hc)
def sixteenIndexEquiv:Fin 2 × Fin 8 ≃ Fin 16:=finProdFinEquiv
def flattenSymbol (v:Fin 2 → Fin 8 → F) (j:Fin 16):F:=
 v (sixteenIndexEquiv.symm j).1 (sixteenIndexEquiv.symm j).2
def unflattenSymbol (v:Fin 16 → F) (a:Fin 2) (b:Fin 8):F:=
 v (sixteenIndexEquiv (a,b))
theorem unflatten_flattenSymbol (v:Fin 2 → Fin 8 → F):
   unflattenSymbol (flattenSymbol v)=v:=by
 funext a b
 simp only [unflattenSymbol,flattenSymbol,Equiv.symm_apply_apply]
theorem flatten_unflattenSymbol (v:Fin 16 → F):
   flattenSymbol (unflattenSymbol v)=v:=by
 funext j
 change v (sixteenIndexEquiv (sixteenIndexEquiv.symm j))=v j
 rw [Equiv.apply_symm_apply]
def squaredEightSymbolEquiv:(Fin 2 → Fin 8 → F) ≃ (Fin 16 → F) where
 toFun:=flattenSymbol
 invFun:=unflattenSymbol
 left_inv:=unflatten_flattenSymbol
 right_inv:=flatten_unflattenSymbol
def flattenWord (v:ι → Fin 2 → Fin 8 → F):ι → Fin 16 → F:=
 fun i => squaredEightSymbolEquiv (v i)
theorem flattenWord_injective:
   Function.Injective (flattenWord:(ι → Fin 2 → Fin 8 → F) → ι → Fin 16 → F):=by
 intro v u h
 funext i
 exact squaredEightSymbolEquiv.injective (congrFun h i)
theorem flattenWord_agreement_iff
   (v u:ι → Fin 2 → Fin 8 → F) (i:ι):
   flattenWord v i=flattenWord u i ↔ v i=u i:=by
 constructor
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i) at hh
   exact (squaredEightSymbolEquiv (F:=F)).injective hh
 · intro hh
   change (squaredEightSymbolEquiv (F:=F)) (v i)=
     (squaredEightSymbolEquiv (F:=F)) (u i)
   exact congrArg (squaredEightSymbolEquiv (F:=F)) hh
theorem flattenWord_agreement_card (v u:ι → Fin 2 → Fin 8 → F):
   (Finset.univ.filter (fun i => flattenWord v i=flattenWord u i)).card=
     (Finset.univ.filter (fun i => v i=u i)).card:=by
 classical
 congr 1
 ext i
 simp only [Finset.mem_filter,flattenWord_agreement_iff]
theorem squared_eight_rows
   (C:LinearCode ι F) (v:ι → Fin 2 → Fin 8 → F)
   (hv:v∈((C^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode ι F (Fin 2 → Fin 8 → F))):
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈C:=by
 intro a b
 have houter:=
   (Code.mem_moduleInterleavedCode_iff F (Fin 8 → F) (Fin 2) ι
     (C^⋈ (Fin 8)) v).mp hv a
 exact (Code.mem_moduleInterleavedCode_iff F F (Fin 8) ι C _).mp houter b
theorem squared_eight_lambda_le
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:RCN020.ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (hseparation:15*(B+1).choose 2 < Fintype.card F)
   (δ:ℝ)
   (hcell:δ*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     (((C^⋈ (Fin 8))^⋈ (Fin 2):ModuleCode ι F (Fin 2 → Fin 8 → F)):
       Set (ι → Fin 2 → Fin 8 → F)) δ ≤ (B:ℕ∞):=by
 classical
 letI:DecidableEq (ι → Fin 2 → Fin 8 → F):=Classical.decEq _
 letI:DecidableEq (ι → Fin 16 → F):=Classical.decEq _
 apply Code.Lambda_le_of_forall_finset_card_le
 intro y T hT
 let projected:Finset (ι → Fin 16 → F):=T.image flattenWord
 have hinj:Set.InjOn flattenWord (T:Set (ι → Fin 2 → Fin 8 → F)):=
   fun _ _ _ _ hh => flattenWord_injective hh
 have hcard:projected.card=T.card:=Finset.card_image_of_injOn hinj
 have hrows:∀ v∈projected,∀ j:Fin 16,(fun i => v i j)∈C:=by
   intro v hv j
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   have hcode:=(Code.mem_closeCodewordsRel_iff.mp (hT c hc)).1
   change (fun i => c i (sixteenIndexEquiv.symm j).1
     (sixteenIndexEquiv.symm j).2)∈C
   exact squared_eight_rows C c hcode _ _
 have hclose:∀ v∈projected,
     Fintype.card ι-e ≤
       (Finset.univ.filter (fun i => v i=flattenWord y i)).card:=by
   intro v hv
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   rw [flattenWord_agreement_card]
   exact agreement_card_ge_of_closeCodewordsRel _ y c δ e hcell (hT c hc)
 have hbound:=RCN019.interleaved_finite_list_card_le
   (r:=16) C e w B hzero hgap halign hfield hseparation
   (flattenWord y) projected hrows hclose
 rwa [hcard] at hbound
theorem squared_eight_lambda_le_of_floor
   (C:LinearCode ι F) (e w B:ℕ)
   (hzero:RCN020.ZeroCoordinateBound C w)
   (hgap:w < Fintype.card ι-e)
   (halign:AffineLineAlignmentBound C e B)
   (hfield:B < Fintype.card F)
   (hseparation:15*(B+1).choose 2 < Fintype.card F)
   (δ:ℝ) (hfloor:⌊δ*(Fintype.card ι:ℝ)⌋₊ ≤ e):
   Code.Lambda
     (((C^⋈ (Fin 8))^⋈ (Fin 2):ModuleCode ι F (Fin 2 → Fin 8 → F)):
       Set (ι → Fin 2 → Fin 8 → F)) δ ≤ (B:ℕ∞):=
 squared_eight_lambda_le C e w B hzero hgap halign hfield hseparation δ
   (radius_cell_of_floor_le δ (Fintype.card ι) e hfloor)
end GenericCode
theorem irs_zeroCoordinateBound:
   RCN020.ZeroCoordinateBound IRSProfile.baseCode 131071:=by
 classical
 intro c hc hne
 have hdist:=Code.minDist_le_dist
   (C:=(IRSProfile.baseCode:Set (IRSProfile.Index → IRSProfile.Field)))
   hc IRSProfile.baseCode.zero_mem hne
 rw [IRSProfile.baseMinDistance] at hdist
 have hagree:=Code.agree_add_hammingDist
   (u:=c) (v:=(0:IRSProfile.Index → IRSProfile.Field))
 have hn:Fintype.card IRSProfile.Index=262144:=by
   norm_num [IRSProfile.Index]
 rw [hn] at hagree
 have hz:(Finset.univ.filter (fun i => c i=0)).card ≤ 131071:=by
   change Code.agree c (0:IRSProfile.Index → IRSProfile.Field) ≤ 131071
   omega
 exact hz
theorem irs_code_mem_iff_rows
   (v:IRSProfile.Index → Fin IRSProfile.interleaving → IRSProfile.Field):
   v∈IRSProfile.code ↔
     ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode:=by
 change (∀ b:Fin IRSProfile.interleaving,
   (fun i => v i b)∈ReedSolomon.code IRSProfile.domain
     (IRSProfile.totalDimension/IRSProfile.interleaving)) ↔ _
 rw [IRSProfile.totalDimension_div_interleaving]
 rfl
theorem irs_squared_carrier_eq:
   (((IRSProfile.code^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field
       (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)))=
   ((((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
     ModuleCode IRSProfile.Index IRSProfile.Field (Fin 2 → Fin 8 → IRSProfile.Field)):
     Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))):=by
 ext v
 change (∀ a:Fin 2,(fun i => v i a)∈IRSProfile.code) ↔
   ∀ a:Fin 2,∀ b:Fin 8,(fun i => v i a b)∈IRSProfile.baseCode
 constructor
 · intro hv a b
   exact (irs_code_mem_iff_rows _).mp (hv a) b
 · intro hv a
   exact (irs_code_mem_iff_rows _).mpr (hv a)
theorem irs_squared_lambda_le
   (e B:ℕ) (δ:ℝ≥0)
   (hgap:131071 < Fintype.card IRSProfile.Index-e)
   (halign:AffineLineAlignmentBound IRSProfile.baseCode e B)
   (hfield:B < Fintype.card IRSProfile.Field)
   (hseparation:15*(B+1).choose 2 < Fintype.card IRSProfile.Field)
   (hcell:(δ:ℝ)*(Fintype.card IRSProfile.Index:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (δ:ℝ) ≤ (B:ℕ∞):=by
 classical
 rw [irs_squared_carrier_eq]
 exact squared_eight_lambda_le IRSProfile.baseCode e 131071 B
   irs_zeroCoordinateBound hgap halign hfield hseparation (δ:ℝ) hcell
theorem irs_squared_claimedRadius_lambda_le
   (num den e B:ℕ) (hden:0 < den)
   (hcross:num*Fintype.card IRSProfile.Index < (e+1)*den)
   (hgap:131071 < Fintype.card IRSProfile.Index-e)
   (halign:AffineLineAlignmentBound IRSProfile.baseCode e B)
   (hfield:B < Fintype.card IRSProfile.Field)
   (hseparation:15*(B+1).choose 2 < Fintype.card IRSProfile.Field):
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (claimedRadius num den:ℝ) ≤ (B:ℕ∞):=by
 apply irs_squared_lambda_le e B (claimedRadius num den) hgap halign hfield hseparation
 simpa only [claimedRadius,NNReal.coe_div,NNReal.coe_natCast] using
   rational_radius_cell num den (Fintype.card IRSProfile.Index) e hden hcross
theorem irs_squared_lambda_toNat_le
   (e B:ℕ) (δ:ℝ≥0)
   (hgap:131071 < Fintype.card IRSProfile.Index-e)
   (halign:AffineLineAlignmentBound IRSProfile.baseCode e B)
   (hfield:B < Fintype.card IRSProfile.Field)
   (hseparation:15*(B+1).choose 2 < Fintype.card IRSProfile.Field)
   (hcell:(δ:ℝ)*(Fintype.card IRSProfile.Index:ℝ) < ((e+1:ℕ):ℝ)):
   (Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (δ:ℝ)).toNat ≤ B:=
 ENat.toNat_le_of_le_coe
   (irs_squared_lambda_le e B δ hgap halign hfield hseparation hcell)
end DraftProofs
end ProximityPrize.SubmissionLower.RCN018
end PackedLegacy_H5

/-! Packed from ProximityPrize.SubmissionLower.F0. -/
section PackedLegacy_F0
namespace ProximityPrize.SubmissionLower.RCN280
open scoped Classical NNReal
open ProximityPrize.Benchmark RCN279 RCN281 RCN019 RCN018 RCN319
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
local instance:DecidableEq IRSProfile.Field:=Classical.decEq _
local instance:DecidableEq IRSProfile.Index:=Classical.decEq _
local instance:CharP IRSProfile.Field prime:=by
 change CharP KoalaBear.Ext6 2130706433
 exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433
theorem irs_scalar_finite_list_card_le
   (received:IRSProfile.Index → IRSProfile.Field)
   (L:Finset (IRSProfile.Index → IRSProfile.Field))
   (hcode:∀ c∈L,c∈IRSProfile.baseCode)
   (hclose:∀ c∈L,agreements ≤
     (Finset.univ.filter (fun i => c i=received i)).card):
   L.card ≤ listBudget:=by
 classical
 let D:=↥L
 let codeword:D → IRSProfile.baseCode:=fun c => ⟨c.1,hcode c.1 c.2⟩
 let selected:D → Polynomial IRSProfile.Field:=fun c => ReedSolomon.toPolynomial (codeword c)
 let Gamma:Finset (Polynomial IRSProfile.Field):=Finset.univ.image selected
 have hselected:Function.Injective selected:=by
   intro c d h
   apply Subtype.ext
   funext i
   have hh:=congrArg (fun P:Polynomial IRSProfile.Field =>
     P.eval (IRSProfile.domain i)) h
   simpa only [selected,ReedSolomon.toPolynomial_eval_at_domain] using hh
 have hcard:Gamma.card=L.card:=by
   rw [show Gamma=Finset.univ.image selected by rfl,
     Finset.card_image_of_injective _ hselected,Finset.card_univ,
     Fintype.card_coe]
 obtain ⟨Q,hQ,hbox,hlegacy,hvanish⟩:=
   exists_frozen_seedless_vanishing_interpolant received
 have hdegree:∀ P∈Gamma,P.natDegree ≤ w:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   have hp:=ReedSolomon.toPolynomial_mem_lt_deg (codeword c)
   have hdeg:(selected c).degree < ((w+1:ℕ):WithBot ℕ):=by
     have hh:=Polynomial.mem_degreeLT.mp hp
     change (selected c).degree <
       ((IRSProfile.baseDimension:ℕ):WithBot ℕ) at hh
     rw [show IRSProfile.baseDimension=w+1 by
       norm_num [IRSProfile.baseDimension,w]] at hh
     exact hh
   by_cases hz:selected c=0
   · simp [hz]
   · rw [←Polynomial.natDegree_lt_iff_degree_lt hz] at hdeg
     omega
 have hsolution:∀ P∈Gamma,specialization IRSProfile.Field P 0 Q=0:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   let A:=Finset.univ.filter (fun i => c.1 i=received i)
   apply hvanish (selected c) A (hdegree (selected c)
     (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩))
     (hclose c.1 c.2)
   intro i hi
   have hcval:=ReedSolomon.toPolynomial_eval_at_domain (c:=codeword c) (i:=i)
   exact hcval.trans (Finset.mem_filter.mp hi).2
 have hagreement:∀ P∈Gamma,agreements ≤
     (Finset.univ.filter (fun i => P.eval (IRSProfile.domain i)=received i)).card:=by
   intro P hP
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hP
   have heq:Finset.univ.filter
       (fun i => (selected c).eval (IRSProfile.domain i)=received i)=
       Finset.univ.filter (fun i => c.1 i=received i):=by
     apply Finset.filter_congr
     intro i hi
     rw [ReedSolomon.toPolynomial_eval_at_domain]
   rw [heq]
   exact hclose c.1 c.2
 have hbound:=seedless_list_card_le IRSProfile.Field Q hQ hbox hlegacy Gamma
   (Finset.univ:Finset IRSProfile.Index) IRSProfile.domain received
   IRSProfile.domain.injective.injOn
   (by norm_num [IRSProfile.Index,n]) hdegree hsolution hagreement
 rwa [hcard] at hbound
theorem irs_interleaved_finite_list_card_le
   {r:ℕ}
   (received:IRSProfile.Index → Fin r → IRSProfile.Field)
   (L:Finset (IRSProfile.Index → Fin r → IRSProfile.Field))
   (hrows:∀ v∈L,∀ j:Fin r,
     (fun i => v i j)∈IRSProfile.baseCode)
   (hclose:∀ v∈L,agreements ≤
     (Finset.univ.filter (fun i => v i=received i)).card)
   (hseparation:(r-1)*(listBudget+1).choose 2 <
     Fintype.card IRSProfile.Field):
   L.card ≤ listBudget:=by
 classical
 letI:DecidableEq (IRSProfile.Index → Fin r → IRSProfile.Field):=Classical.decEq _
 letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩:=
   Finset.exists_subset_card_eq (show listBudget+1 ≤ L.card by omega)
 have hsepD:(r-1)*D.card.choose 2 < Fintype.card IRSProfile.Field:=by
   rw [hDcard]
   exact hseparation
 obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
 let projected:Finset (IRSProfile.Index → IRSProfile.Field):=
   D.image (momentProjection (ι:=IRSProfile.Index) (r:=r) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀ c∈projected,c∈IRSProfile.baseCode:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
 have hnear:∀ c∈projected,agreements ≤
     (Finset.univ.filter (fun i => c i=momentProjection t received i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose v (hDL hv)).trans
     (Finset.card_le_card (momentProjection_preserves_agreements t v received))
 have hbound:=irs_scalar_finite_list_card_le (momentProjection t received)
   projected hcode hnear
 rw [hprojcard,hDcard] at hbound
 omega
theorem sixteen_row_separation:
   15*(listBudget+1).choose 2 < Fintype.card IRSProfile.Field:=by
 rw [show Fintype.card IRSProfile.Field=(2130706433:ℕ)^6 by
   norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize],
   Nat.choose_eq_descFactorial_div_factorial]
 norm_num [listBudget,Nat.descFactorial_succ,Nat.factorial_succ]
theorem squared_eight_lambda_le_of_interleaved_list
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   (C:LinearCode ι F) (e B:ℕ)
   (hfinite:∀ (received:ι → Fin 16 → F)
       (L:Finset (ι → Fin 16 → F)),
     (∀ v∈L,∀ j:Fin 16,(fun i => v i j)∈C) →
     (∀ v∈L,Fintype.card ι-e ≤
       (Finset.univ.filter (fun i => v i=received i)).card) →
     L.card ≤ B)
   (delta:ℝ)
   (hcell:delta*(Fintype.card ι:ℝ) < ((e+1:ℕ):ℝ)):
   Code.Lambda
     (((C^⋈ (Fin 8))^⋈ (Fin 2):ModuleCode ι F (Fin 2 → Fin 8 → F)):
       Set (ι → Fin 2 → Fin 8 → F)) delta ≤ (B:ℕ∞):=by
 classical
 letI:DecidableEq (ι → Fin 2 → Fin 8 → F):=Classical.decEq _
 letI:DecidableEq (ι → Fin 16 → F):=Classical.decEq _
 apply Code.Lambda_le_of_forall_finset_card_le
 intro received L hL
 let projected:Finset (ι → Fin 16 → F):=L.image flattenWord
 have hinj:Set.InjOn flattenWord (L:Set (ι → Fin 2 → Fin 8 → F)):=
   fun _ _ _ _ hh => flattenWord_injective hh
 have hcard:projected.card=L.card:=Finset.card_image_of_injOn hinj
 have hrows:∀ v∈projected,∀ j:Fin 16,(fun i => v i j)∈C:=by
   intro v hv j
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   have hcode:=(Code.mem_closeCodewordsRel_iff.mp (hL c hc)).1
   change (fun i => c i (sixteenIndexEquiv.symm j).1
     (sixteenIndexEquiv.symm j).2)∈C
   exact squared_eight_rows C c hcode _ _
 have hclose:∀ v∈projected,Fintype.card ι-e ≤
     (Finset.univ.filter (fun i => v i=flattenWord received i)).card:=by
   intro v hv
   obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hv
   rw [flattenWord_agreement_card]
   exact agreement_card_ge_of_closeCodewordsRel _ received c delta e hcell (hL c hc)
 have hbound:=hfinite (flattenWord received) projected hrows hclose
 rwa [hcard] at hbound
theorem squared_eight_lambda_seedless
   (delta:ℝ)
   (hcell:(delta:ℝ)*(Fintype.card IRSProfile.Index:ℝ) <
     ((errors+1:ℕ):ℝ)):
   Code.Lambda
     (((IRSProfile.baseCode^⋈ (Fin 8))^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin 8 → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin 8 → IRSProfile.Field))
     delta ≤ (listBudget:ℕ∞):=by
 apply squared_eight_lambda_le_of_interleaved_list
   IRSProfile.baseCode errors listBudget ?_ delta hcell
 intro received L hrows hclose
 have hclose':∀ v∈L,agreements ≤
     (Finset.univ.filter (fun i => v i=received i)).card:=by
   intro v hv
   simpa [agreements,n,errors,IRSProfile.Index] using hclose v hv
 classical
 letI:DecidableEq (IRSProfile.Index → Fin 16 → IRSProfile.Field):=Classical.decEq _
 letI:DecidableEq (IRSProfile.Index → IRSProfile.Field):=Classical.decEq _
 by_contra hnot
 obtain ⟨D,hDL,hDcard⟩:=
   Finset.exists_subset_card_eq (show listBudget+1 ≤ L.card by omega)
 have hsepD:15*D.card.choose 2 < Fintype.card IRSProfile.Field:=by
   rw [hDcard]
   exact sixteen_row_separation
 obtain ⟨t,ht⟩:=exists_separating_moment_parameter D hsepD
 let projected:Finset (IRSProfile.Index → IRSProfile.Field):=
   D.image (momentProjection (ι:=IRSProfile.Index) (r:=16) t)
 have hprojcard:projected.card=D.card:=Finset.card_image_of_injOn ht
 have hcode:∀ c∈projected,c∈IRSProfile.baseCode:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact momentProjection_mem_code IRSProfile.baseCode t v (hrows v (hDL hv))
 have hnear:∀ c∈projected,agreements ≤
     (Finset.univ.filter (fun i => c i=momentProjection t received i)).card:=by
   intro c hc
   obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hc
   exact (hclose' v (hDL hv)).trans
     (Finset.card_le_card (momentProjection_preserves_agreements t v received))
 have hbound:=irs_scalar_finite_list_card_le
   (momentProjection t received) projected hcode hnear
 rw [hprojcard,hDcard] at hbound
 omega
theorem irs_squared_lambda_seedless
   (delta:ℝ≥0)
   (hcell:(delta:ℝ)*(Fintype.card IRSProfile.Index:ℝ) <
     ((errors+1:ℕ):ℝ)):
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
     (delta:ℝ) ≤ (listBudget:ℕ∞):=by
 rw [irs_squared_carrier_eq]
 exact squared_eight_lambda_seedless (delta:ℝ) hcell
end
end ProximityPrize.SubmissionLower.RCN280
end PackedLegacy_F0

/-! Packed from ProximityPrize.SubmissionLower.O7. -/
section PackedLegacy_O7
namespace ProximityPrize.SubmissionLower.RCN278
open ProximityPrize.Benchmark
open scoped NNReal
noncomputable section
def radius6630:ℝ≥0:=claimedRadius 319467 1048576
def errors6630:ℕ:=79866
def score6630:ℕ:=6710
theorem radius_numerator_exact:319467=4*errors6630+3:=by
 norm_num [errors6630]
theorem radius6630_floor:
   ⌊(radius6630:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=
     errors6630:=by
 norm_num [radius6630,claimedRadius,errors6630,IRSProfile.Index]
theorem radius6630_cell_cross:
   319467*Fintype.card IRSProfile.Index <
     (errors6630+1)*1048576:=by
 norm_num [IRSProfile.Index,errors6630]
theorem radius6630_gap:
   131071 < Fintype.card IRSProfile.Index-errors6630:=by
 norm_num [IRSProfile.Index,errors6630]
theorem radius6630_admissible:
   radius6630∈Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
 constructor <;>
   norm_num [radius6630,claimedRadius,IRSProfile.minRelativeDistance]
theorem two_rpow_one_tenth_le:
   (2:ℝ≥0)^((1:ℝ)/10) ≤ (134:ℝ≥0)/125:=by
 have hroot:
     ((2:ℝ≥0)^(1:ℕ))^((10:ℝ)⁻¹) ≤
       (134:ℝ≥0)/125:=by
   rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 10)]
   norm_num [NNReal.rpow_natCast,div_pow,le_div_iff₀]
 calc
   (2:ℝ≥0)^((1:ℝ)/10)=
       ((2:ℝ≥0)^(1:ℕ))^((10:ℝ)⁻¹):=by
     rw [←NNReal.rpow_natCast_mul]
     norm_num [div_eq_mul_inv]
   _ ≤ (134:ℝ≥0)/125:=hroot
theorem radius6630_power_rational_bound:
   (1-radius6630)^IRSProfile.repetitions ≤
     ((1:ℝ≥0)/2^(67:ℕ))*(125/134):=by
 rw [←NNReal.coe_le_coe]
 norm_num [radius6630,claimedRadius,IRSProfile.repetitions,div_le_iff₀]
theorem radius6630_score:
   (1-radius6630)^IRSProfile.repetitions ≤ claimedError score6630:=by
 have hscale:
     (125:ℝ≥0)/134 ≤ (2:ℝ≥0)^(-((1:ℝ)/10)):=by
   calc
     (125:ℝ≥0)/134=1/((134:ℝ≥0)/125):=by norm_num
     _ ≤ 1/((2:ℝ≥0)^((1:ℝ)/10)):=
       one_div_le_one_div_of_le (by positivity) two_rpow_one_tenth_le
     _=(2:ℝ≥0)^(-((1:ℝ)/10)):=by
       rw [one_div,NNReal.rpow_neg]
 calc
   (1-radius6630)^IRSProfile.repetitions ≤
       ((1:ℝ≥0)/2^(67:ℕ))*(125/134):=
     radius6630_power_rational_bound
   _ ≤ ((1:ℝ≥0)/2^(67:ℕ))*
       (2:ℝ≥0)^(-((1:ℝ)/10)):=
     mul_le_mul_of_nonneg_left hscale (by positivity)
   _=claimedError score6630:=by
     unfold claimedError score6630
     rw [show-((((6710:ℕ):ℝ)/100))=
         -((67:ℕ):ℝ)+ -((1:ℝ)/10) by norm_num,
       NNReal.rpow_add (by norm_num:(2:ℝ≥0)≠0)]
     simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end ProximityPrize.SubmissionLower.RCN278
end PackedLegacy_O7

/-! Packed from ProximityPrize.SubmissionLower.P1. -/
section PackedLegacy_P1
namespace ProximityPrize.SubmissionLower.RCN284
open ProximityPrize.Benchmark CoreDefinitions ProximityGap ToyProblem
open scoped NNReal
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
def radius:ℝ≥0:=RCN278.radius6630
def errors:ℕ:=RCN278.errors6630
def mcaBudget:ℕ:=274980727511395087
theorem field_cardinality:
   Fintype.card IRSProfile.Field=(2130706433:ℕ)^6:=by
 norm_num [IRSProfile.Field,KoalaBear.Ext6,KoalaBear.fieldSize]
theorem irs_code_eq_base_interleaved:
   IRSProfile.code=
     (IRSProfile.baseCode^⋈ (Fin IRSProfile.interleaving):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin IRSProfile.interleaving → IRSProfile.Field)):=by
 ext v
 change v∈IRSProfile.code ↔
   ∀ b:Fin IRSProfile.interleaving,(fun i => v i b)∈IRSProfile.baseCode
 exact RCN018.irs_code_mem_iff_rows v
theorem nat_div_le_inv_pow {m q t:ℕ} (hm:0 < m)
   (hq:m*2^t ≤ q):
   (m:ENNReal)/(q:ENNReal) ≤ 1/2^t:=by
 have hm0:(m:ENNReal)≠0:=by exact_mod_cast hm.ne'
 have hmtop:(m:ENNReal)≠⊤:=ENNReal.natCast_ne_top m
 have hqE:((m*2^t:ℕ):ENNReal) ≤ (q:ENNReal):=by
   exact_mod_cast hq
 have hcast:((m*2^t:ℕ):ENNReal)=(m:ENNReal)*2^t:=by
   push_cast
   ring
 calc
   (m:ENNReal)/(q:ENNReal) ≤
       (m:ENNReal)/((m*2^t:ℕ):ENNReal):=
     ENNReal.div_le_div_left hqE _
   _=(m:ENNReal)/((m:ENNReal)*2^t):=by rw [hcast]
   _=(m:ENNReal)*1/((m:ENNReal)*2^t):=by rw [mul_one]
   _=1/2^t:=ENNReal.mul_div_mul_left 1 (2^t) hm0 hmtop
theorem affineLineAlignmentBound_mono_budget
   {ι F:Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
   [Field F] [Fintype F] [DecidableEq F]
   {C:LinearCode ι F} {e a b:ℕ}
   (hab:a ≤ b) (h:AffineLineAlignmentBound C e a):
   AffineLineAlignmentBound C e b:=by
 intro U S A hS hcard hprojected
 exact h U S A (hab.trans_lt hS) hcard hprojected
theorem field_capacity_split:
   2^(128:ℕ)*
       (mcaBudget+RCN281.listBudget) ≤
     Fintype.card IRSProfile.Field:=by
 rw [field_cardinality]
 norm_num [mcaBudget,RCN281.listBudget]
theorem base_mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ) ≤
     ENNReal.ofReal ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=by
 apply mcaError_affineLine_le_of_givenSetsBound
 apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
   (radius:ℝ) errors mcaBudget
 · intro A hA
   have hcomp:=
     (mul_one_sub_le_card_iff_sub_card_le_floor A
       (show (0:ℝ) ≤ (radius:ℝ) by positivity)).mp hA
   rw [show ⌊(radius:ℝ)*(Fintype.card IRSProfile.Index:ℝ)⌋₊=errors by
     simpa only [radius,errors] using
       RCN278.radius6630_floor] at hcomp
   have hn:Fintype.card IRSProfile.Index=262144:=by
     norm_num [IRSProfile.Index]
   rw [hn]
   norm_num [errors,RCN278.errors6630] at hcomp ⊢
   omega
 · exact halign
theorem mca_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
       (radius:ℝ) ≤
     (mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
 calc
   _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
       (radius:ℝ):=by
     rw [irs_code_eq_base_interleaved]
     exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
       IRSProfile.interleaving radius
       (by norm_num [IRSProfile.interleaving])
       (by norm_num [radius,RCN278.radius6630,
         claimedRadius])
       (by norm_num [radius,RCN278.radius6630,
         claimedRadius])
   _ ≤ ENNReal.ofReal
       ((mcaBudget:ℝ)/Fintype.card IRSProfile.Field):=
     base_mca_le_of_alignment halign
   _=(mcaBudget:ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
       ENNReal.ofReal_natCast]
theorem lambda_le:
   Code.Lambda
     ((IRSProfile.code^⋈ (Fin 2):
       ModuleCode IRSProfile.Index IRSProfile.Field
         (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
       Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
         IRSProfile.Field))
     (radius:ℝ) ≤
       (RCN281.listBudget:ℕ∞):=by
 apply RCN280.irs_squared_lambda_seedless
 norm_num [radius,RCN278.radius6630,claimedRadius,
   RCN279.errors,IRSProfile.Index]
theorem certifiedGammaError_le_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   certifiedGammaError IRSProfile.code radius ≤
     (1:ℝ≥0)/2^(128:ℕ):=by
 rw [←ENNReal.coe_le_coe,coe_certifiedGammaError]
 push_cast
 have hLambdaNat:=ENat.toNat_le_of_le_coe lambda_le
 have hList:
     ((Code.Lambda
       ((IRSProfile.code^⋈ (Fin 2):
         ModuleCode IRSProfile.Index IRSProfile.Field
           (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)):
         Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
           IRSProfile.Field))
       (radius:ℝ)).toNat:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal) ≤
       (RCN281.listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
   ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
 calc
   _ ≤ (mcaBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal)+
       (RCN281.listBudget:ENNReal)/
         (Fintype.card IRSProfile.Field:ENNReal):=
     add_le_add (mca_le_of_alignment halign) hList
   _=((mcaBudget+RCN281.listBudget:ℕ):ENNReal)/
       (Fintype.card IRSProfile.Field:ENNReal):=by
     rw [←ENNReal.add_div,Nat.cast_add]
   _ ≤ (1:ENNReal)/2^(128:ℕ):=by
     apply nat_div_le_inv_pow
     · norm_num [mcaBudget,RCN281.listBudget]
     · simpa only [Nat.mul_comm] using field_capacity_split
theorem protocolClaim6710_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   ProtocolClaim 6710 319467 1048576 where
 admissible:=RCN278.radius6630_admissible
 reduction:=by
   change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
   exact (certifiedGammaError_le_of_alignment halign).trans
     (by norm_num [reductionTarget,ProximityGap.prizeThreshold,div_le_iff₀])
 score:=RCN278.radius6630_score
theorem protocolClaim6696_of_alignment
   (halign:AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget):
   ProtocolClaim 6710 319467 1048576:=
 protocolClaim6710_of_alignment halign
end
end ProximityPrize.SubmissionLower.RCN284
end PackedLegacy_P1
