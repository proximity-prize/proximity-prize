import ProximityPrize.SubmissionLower.PartF005

section Compact_PackedLegacy
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
end FiniteAgreement
section IteratedSets
variable {Node:Type*} [DecidableEq Node]
end IteratedSets
section Arithmetic
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
abbrev ResidualReachable:=Relation.ReflTransGen
 (ResidualAdvance (phi:=phi) (Gamma:=Gamma) (x:=x)
   (p:=p) (e:=e) (flag:=flag) (support:=support))
end
end Terminalization
end ProximityPrize.SubmissionLower.RCN158
end PackedLegacy_EY

/-! Packed from ProximityPrize.SubmissionLower.D6. -/
section PackedLegacy_D6
namespace ProximityPrize.SubmissionLower.RCN216
open RCN173 RCN213
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
end
end ProximityPrize.SubmissionLower.RCN305
end PackedLegacy_GJ
end Compact_PackedLegacy
