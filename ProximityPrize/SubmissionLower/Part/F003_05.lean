import ProximityPrize.SubmissionLower.Part.F003_04
section Compact_PackedLegacyCore1
section PackedLegacy_I9
namespace ProximityPrize.SubmissionLower.RCN079
open RCN136 RCN082 RCN290 RCN293 RCN081 RCN319
noncomputable section
variable {K:Type*} [Field K]

theorem originalImplicitFactors_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈originalImplicitFactors J,A.degreeOf (1:Fin 4)) ≤ J.degreeOf 1∧
     (∑ A∈originalImplicitFactors J,A.degreeOf (3:Fin 4)) ≤ J.degreeOf 3:=by
 have hh:=RCN081.sum_degreeOf_le_of_prod_dvd
   (originalImplicitFactors J) id J hJ (originalImplicitFactors_product_dvd J hJ)
 exact ⟨hh 1,hh 3⟩
section SurfaceCoverage
variable {T:Type*} [Field T]
def swapSurfacePoint (v:Fin 3 → T):Fin 3 → T:=![v 1,v 0,v 2]
@[simp] theorem swapSurfacePoint_twice (v:Fin 3 → T):
   swapSurfacePoint (swapSurfacePoint v)=v:=by
 funext i
 fin_cases i <;> simp [swapSurfacePoint]
theorem eval_surface_swap (φ:Polynomial K →+*T) (v:Fin 3 → T)
   (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval v (surfaceMap φ (swapYR K F))=
     MvPolynomial.eval (swapSurfacePoint v) (surfaceMap φ F):=by
 have hfix0:Equiv.swap (1:Fin 4) 2 (0:Fin 4)=0:=by decide
 have hfix3:Equiv.swap (1:Fin 4) 2 (3:Fin 4)=3:=by decide
 have hs1:surfaceMap φ (MvPolynomial.X (1:Fin 4))=MvPolynomial.X (0:Fin 3):=
   surfaceMap_X_succ φ 0
 have hs2:surfaceMap φ (MvPolynomial.X (2:Fin 4))=MvPolynomial.X (1:Fin 3):=
   surfaceMap_X_succ φ 1
 have hs3:surfaceMap φ (MvPolynomial.X (3:Fin 4))=MvPolynomial.X (2:Fin 3):=
   surfaceMap_X_succ φ 2
 have hh:((MvPolynomial.eval v).comp (surfaceMap φ)).comp (swapYR K).toRingHom=
     (MvPolynomial.eval (swapSurfacePoint v)).comp (surfaceMap φ):=by
   apply MvPolynomial.ringHom_ext
   · intro a
     simp [RingHom.comp_apply,swapYR,MvPolynomial.renameEquiv_apply]
   · intro i
     fin_cases i <;>
       simp [RingHom.comp_apply,swapYR,MvPolynomial.renameEquiv_apply,
         hfix0,hfix3,hs1,hs2,hs3,swapSurfacePoint]
 exact RingHom.congr_fun hh F
theorem surface_zero_exceptional_or_implicit_regular
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (v:Fin 3 → T) (hzero:MvPolynomial.eval v (surfaceMap φ J)=0):
   MvPolynomial.eval v (surfaceMap φ (exceptionalAuxiliary J))=0∨
     ∃ A∈originalImplicitFactors J,Irreducible A∧A∣J∧
       A.degreeOf 2=0∧0 < A.degreeOf 1∧
       MvPolynomial.eval v (surfaceMap φ A)=0∧
       MvPolynomial.eval v (surfaceMap φ (MvPolynomial.pderiv (1:Fin 4) A))≠0:=by
 classical
 have hswap:MvPolynomial.eval (swapSurfacePoint v) (surfaceMap φ (swapYR K J))=0:=by
   rw [eval_surface_swap,swapSurfacePoint_twice]
   exact hzero
 obtain haux | ⟨F,hF,hi,hpos,hz,hreg⟩:=surface_zero_singular_or_regular
   φ hφ (swapYR K J) (swapYR_ne_zero J hJ) (swapSurfacePoint v) hswap
 · left
   rw [exceptionalAuxiliary,eval_surface_swap]
   exact haux
 · right
   have hmem:swapYR K F∈originalImplicitFactors J:=Finset.mem_image.mpr ⟨F,hF,rfl⟩
   have hs:=originalImplicitFactors_spec J (swapYR K F) hmem
   have hAR:(swapYR K F).degreeOf 2=0:=by
     have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) (swapYR K F) J hs.2 hJ
     omega
   refine ⟨swapYR K F,hmem,hs.1,hs.2,hAR,?_,?_,?_⟩
   · rw [swapYR_degree_Y]
     exact hpos
   · rw [eval_surface_swap]
     exact hz
   · rw [swapYR_pderiv_Y,eval_surface_swap]
     exact hreg
end SurfaceCoverage
theorem solution_exceptional_or_implicit_regular
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ J=0):
   specialization K P γ (exceptionalAuxiliary J)=0∨
     ∃ A∈originalImplicitFactors J,Irreducible A∧A∣J∧
       A.degreeOf 2=0∧0 < A.degreeOf 1∧specialization K P γ A=0∧
       specialization K P γ (MvPolynomial.pderiv (1:Fin 4) A)≠0:=by
 let φ:=RCN135.polynomialEmbedding K
 let v:Fin 3 → RCN135.GenericField K:=
   fun i => RCN135.initialPoint K P γ i.succ
 have heval (F:MvPolynomial (Fin 4) K):
     MvPolynomial.eval v (surfaceMap φ F)=0 ↔ specialization K P γ F=0:=by
   simpa only [RCN138.canonical_geometricSurfaceMap] using
     (RCN138.actual_generic_initial_zero_iff K P γ F)
 obtain haux | ⟨A,hA,hi,hd,hAR,hAY,hz,hreg⟩:=
   surface_zero_exceptional_or_implicit_regular φ
     (RCN135.polynomialEmbedding_injective K) J hJ hR v ((heval J).mpr hsolution)
 · exact Or.inl ((heval _).mp haux)
 · exact Or.inr ⟨A,hA,hi,hd,hAR,hAY,(heval _).mp hz,(heval _).not.mp hreg⟩
end
end ProximityPrize.SubmissionLower.RCN079
end PackedLegacy_I9

/-! Packed from ProximityPrize.SubmissionLower.J0. -/
section PackedLegacy_J0
namespace ProximityPrize.SubmissionLower.RCN080
open RCN136 RCN079 RCN319
noncomputable section
section SeedProjection
variable {T:Type*} [Field T]
def seedProjection (T:Type*) [Field T]:MvPolynomial (Fin 3) T →+*Polynomial T:=
 MvPolynomial.eval₂Hom Polynomial.C ![0,0,Polynomial.X]
def seedEmbedding (T:Type*) [Field T]:Polynomial T →+*MvPolynomial (Fin 3) T:=
 Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2:Fin 3))
theorem seed_only_vars (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0)
   (i:Fin 3) (hi:i∈S.vars):i=2:=by
 fin_cases i
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hY)
 · exact False.elim ((MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hi) hR)
 · rfl
theorem seedProjection_reconstruct (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0):
   seedEmbedding T (seedProjection T S)=S:=by
 change ((seedEmbedding T).comp (seedProjection T)) S=(RingHom.id _) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [seedEmbedding,seedProjection]
 · intro i hi _
   rw [seed_only_vars S hY hR i hi]
   simp [seedEmbedding,seedProjection]
 · rfl
theorem seedProjection_nonzero (S:MvPolynomial (Fin 3) T) (hS:S≠0)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0):seedProjection T S≠0:=by
 intro hz
 apply hS
 rw [←seedProjection_reconstruct S hY hR,hz,map_zero]
theorem monomial_fin3 (d:Fin 3 →₀ ℕ) (a:T):
   MvPolynomial.monomial d a=MvPolynomial.C a*MvPolynomial.X 0^d 0*
     MvPolynomial.X 1^d 1*MvPolynomial.X 2^d 2:=by
 have hd:d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1)+Finsupp.single 2 (d 2):=by
   ext i
   fin_cases i <;> simp
 conv_lhs => rw [hd]
 rw [MvPolynomial.monomial_add_single,MvPolynomial.monomial_add_single,
   ←MvPolynomial.C_mul_X_pow_eq_monomial]
theorem seedProjection_monomial (d:Fin 3 →₀ ℕ) (a:T):
   seedProjection T (MvPolynomial.monomial d a)=
     Polynomial.C a*0^d 0*0^d 1*Polynomial.X^d 2:=by
 rw [monomial_fin3]
 simp [seedProjection]
theorem seedProjection_monomial_natDegree_le (d:Fin 3 →₀ ℕ) (a:T):
   (seedProjection T (MvPolynomial.monomial d a)).natDegree ≤ d 2:=by
 rw [seedProjection_monomial]
 have hc:(Polynomial.C a).natDegree ≤ 0:=by simp
 have h0:((0:Polynomial T)^d 0).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 0)
     (show (0:Polynomial T).natDegree ≤ 0 by simp)
 have h1:((0:Polynomial T)^d 1).natDegree ≤ 0:=by
   simpa only [Nat.mul_zero] using Polynomial.natDegree_pow_le_of_le (d 1)
     (show (0:Polynomial T).natDegree ≤ 0 by simp)
 have hx:((Polynomial.X:Polynomial T)^d 2).natDegree ≤ d 2:=by simp
 have hh:=Polynomial.natDegree_mul_le_of_le
   (Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hc h0) h1) hx
 simpa using hh
theorem seedProjection_natDegree_le (S:MvPolynomial (Fin 3) T):
   (seedProjection T S).natDegree ≤ S.degreeOf 2:=by
 classical
 have hsum:seedProjection T S=
     ∑ d∈S.support,seedProjection T (MvPolynomial.monomial d (S.coeff d)):=by
   rw [←map_sum,MvPolynomial.support_sum_monomial_coeff]
 rw [hsum]
 exact Polynomial.natDegree_sum_le_of_forall_le S.support _ (fun d hd =>
   (seedProjection_monomial_natDegree_le d (S.coeff d)).trans (MvPolynomial.monomial_le_degreeOf 2 hd))
theorem seedProjection_eval (S:MvPolynomial (Fin 3) T)
   (hY:S.degreeOf 0=0) (hR:S.degreeOf 1=0) (v:Fin 3 → T):
   (seedProjection T S).eval (v 2)=MvPolynomial.eval v S:=by
 change ((Polynomial.evalRingHom (v 2)).comp (seedProjection T)) S=(MvPolynomial.eval v) S
 apply MvPolynomial.hom_congr_vars
 · ext a
   simp [seedProjection]
 · intro i hi _
   rw [seed_only_vars S hY hR i hi]
   simp [seedProjection]
 · rfl
end SeedProjection
section GenericSurface
variable {K T:Type*} [Field K] [Field T]
def auxiliarySeedPolynomial (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K):Polynomial T:=
 seedProjection T (surfaceMap φ H)
theorem surface_seed_only (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0):
   (surfaceMap φ H).degreeOf 0=0∧(surfaceMap φ H).degreeOf 1=0:=
 ⟨Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 0).trans_eq hY),
   Nat.eq_zero_of_le_zero ((surfaceMap_degreeOf_le φ H 1).trans_eq hR)⟩
theorem auxiliarySeedPolynomial_nonzero
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0):auxiliarySeedPolynomial φ H≠0:=by
 have hs:=surface_seed_only φ H hY hR
 exact seedProjection_nonzero (surfaceMap φ H) (surfaceMap_ne_zero φ hφ H hH) hs.1 hs.2
theorem auxiliarySeedPolynomial_natDegree_le
   (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K):
   (auxiliarySeedPolynomial φ H).natDegree ≤ H.degreeOf 3:=
 (seedProjection_natDegree_le (surfaceMap φ H)).trans (surfaceMap_degreeOf_le φ H 2)
theorem auxiliarySeedPolynomial_eval
   (φ:Polynomial K →+*T) (H:MvPolynomial (Fin 4) K)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (v:Fin 3 → T):
   (auxiliarySeedPolynomial φ H).eval (v 2)=MvPolynomial.eval v (surfaceMap φ H):=by
 have hs:=surface_seed_only φ H hY hR
 exact seedProjection_eval (surfaceMap φ H) hs.1 hs.2 v
theorem card_surface_seeds_le
   (φ:Polynomial K →+*T) (hφ:Function.Injective φ)
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ v:Fin 3 → T,
     v 2=φ (Polynomial.C γ)∧MvPolynomial.eval v (surfaceMap φ H)=0):
   seeds.card ≤ H.degreeOf 3:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq T:=Classical.decEq T
 let q:Polynomial T:=auxiliarySeedPolynomial φ H
 let c:K →+*T:=φ.comp Polynomial.C
 have hq:q≠0:=auxiliarySeedPolynomial_nonzero φ hφ H hH hY hR
 have hroots:∀ z∈seeds.image c,z∈q.roots:=by
   intro z hz
   obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp hz
   obtain ⟨v,hv,hzero⟩:=hsolutions γ hγ
   apply (Polynomial.mem_roots hq).mpr
   change q.eval (φ (Polynomial.C γ))=0
   rw [←hv]
   exact (auxiliarySeedPolynomial_eval φ H hY hR v).trans hzero
 calc
   seeds.card=(seeds.image c).card:=(Finset.card_image_of_injOn c.injective.injOn).symm
   _ ≤ q.natDegree:=Polynomial.card_le_degree_of_subset_roots hroots
   _ ≤ H.degreeOf 3:=auxiliarySeedPolynomial_natDegree_le φ H
end GenericSurface
section ActualSolutions
variable {K:Type*} [Field K]
theorem card_actual_solution_seeds_le
   (H:MvPolynomial (Fin 4) K) (hH:H≠0)
   (hY:H.degreeOf 1=0) (hR:H.degreeOf 2=0) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ P:Polynomial K,specialization K P γ H=0):
   seeds.card ≤ H.degreeOf 3:=by
 apply card_surface_seeds_le (RCN135.polynomialEmbedding K)
   (RCN135.polynomialEmbedding_injective K) H hH hY hR seeds
 intro γ hγ
 obtain ⟨P,hP⟩:=hsolutions γ hγ
 refine ⟨fun i => RCN135.initialPoint K P γ i.succ,?_,?_⟩
 · rfl
 · have hh:=(RCN138.actual_generic_initial_zero_iff K P γ H).mpr hP
   simpa only [RCN138.canonical_geometricSurfaceMap] using hh
theorem exceptional_solution_seed_card_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j) (seeds:Finset K)
   (hsolutions:∀ γ∈seeds,∃ P:Polynomial K,
     specialization K P γ (exceptionalAuxiliary J)=0):seeds.card ≤ 2*j^2:=by
 have hd:=exceptionalAuxiliary_data J hJ hR j p hj hsmall hY hZ
 exact (card_actual_solution_seeds_le (exceptionalAuxiliary J) hd.1 hd.2.1 hd.2.2.1
   seeds hsolutions).trans hd.2.2.2.2
end ActualSolutions
end
end ProximityPrize.SubmissionLower.RCN080
end PackedLegacy_J0

namespace ProximityPrize.SubmissionLower
end ProximityPrize.SubmissionLower

/-! Packed from ProximityPrize.SubmissionLower.BU. -/
section PackedLegacy_BU
namespace ProximityPrize.SubmissionLower.RCN169
open RCN079 RCN167 RCN081 RCN267 RCN174
noncomputable section
variable {K:Type*} [Field K]
def implicitBaseFactors (J:MvPolynomial (Fin 4) K):
   Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (originalImplicitFactors J).filter
   (fun A => MvPolynomial.pderiv (1:Fin 4) A≠0)
theorem implicitBaseFactors_subset (J:MvPolynomial (Fin 4) K):
   implicitBaseFactors J ⊆ originalImplicitFactors J:=by
 classical
 exact Finset.filter_subset _ _
theorem implicitBaseFactors_spec (J A:MvPolynomial (Fin 4) K)
   (hJ:J≠0) (hR:J.degreeOf 2=0) (hA:A∈implicitBaseFactors J):
   Irreducible A∧A∣J∧A.degreeOf 2=0∧
     MvPolynomial.pderiv (1:Fin 4) A≠0:=by
 classical
 obtain ⟨hm,hy⟩:=Finset.mem_filter.mp hA
 have hs:=originalImplicitFactors_spec J A hm
 have hr:=RCN081.degreeOf_le_of_dvd (2:Fin 4) A J hs.2 hJ
 exact ⟨hs.1,hs.2,by omega,hy⟩
theorem implicitBaseFactors_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)) ≤ J.degreeOf 1∧
     (∑ A∈implicitBaseFactors J,A.degreeOf (3:Fin 4)) ≤ J.degreeOf 3:=by
 classical
 have hb:=originalImplicitFactors_degree_budgets J hJ
 exact ⟨(Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.1,
   (Finset.sum_le_sum_of_subset (implicitBaseFactors_subset J)).trans hb.2⟩
def implicitPairSet (J:MvPolynomial (Fin 4) K):
   Finset ((A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):=
 (implicitBaseFactors J).sigma (fun A => positiveRFactors (implicitLift A))
theorem mem_implicitPairSet (J A G:MvPolynomial (Fin 4) K):
   (⟨A,G⟩:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)∈
       implicitPairSet J ↔
     A∈implicitBaseFactors J∧G∈positiveRFactors (implicitLift A):=by
 classical
 exact Finset.mem_sigma
theorem implicitPair_spec (J A G:MvPolynomial (Fin 4) K)
   (hJ:J≠0) (hR:J.degreeOf 2=0)
   (hpair:(⟨A,G⟩:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)∈
     implicitPairSet J):
   Irreducible A∧A∣J∧A.degreeOf 2=0∧
     MvPolynomial.pderiv (1:Fin 4) A≠0∧
     Irreducible G∧G∣implicitLift A∧G.degreeOf 2=1∧¬ G∣A:=by
 obtain ⟨hA,hG⟩:=(mem_implicitPairSet J A G).mp hpair
 obtain ⟨hiA,hdA,hrA,hyA⟩:=implicitBaseFactors_spec J A hJ hR hA
 obtain ⟨hiG,hdG,hrG⟩:=positiveRFactors_spec (implicitLift A) G hG
 have hF:=implicitLift_nonzero A hrA hyA
 have hgcap:=(RCN081.degreeOf_le_of_dvd (2:Fin 4)
   G (implicitLift A) hdG hF).trans (implicitLift_R_degree_le A hrA)
 refine ⟨hiA,hdA,hrA,hyA,hiG,hdG,by omega,?_⟩
 intro hd
 have hh:=RCN081.degreeOf_le_of_dvd (2:Fin 4) G A hd hiA.ne_zero
 omega
theorem sum_products_le_product_sums {ι:Type*} (I:Finset ι) (f g:ι → ℕ):
   (∑ i∈I,f i*g i) ≤ (∑ i∈I,f i)*(∑ i∈I,g i):=by
 calc
   _ ≤ ∑ i∈I,f i*(∑ j∈I,g j):=by
     apply Finset.sum_le_sum
     intro i hi
     exact Nat.mul_le_mul_left (f i) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi)
   _=_:=(Finset.sum_mul I f (∑ j∈I,g j)).symm
theorem implicitBaseFactors_product_degree_budget
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)) ≤
     J.degreeOf 1*J.degreeOf 3:=by
 have hb:=implicitBaseFactors_degree_budgets J hJ
 exact (sum_products_le_product_sums (implicitBaseFactors J)
   (fun A => A.degreeOf 1) (fun A => A.degreeOf 3)).trans (Nat.mul_le_mul hb.1 hb.2)
def pairYCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 2*q.1.degreeOf 3
def pairRCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 1*q.1.degreeOf 3+q.2.degreeOf 3*q.1.degreeOf 1
def pairZCost (q:(A:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K):ℕ:=
 q.2.degreeOf 2*q.1.degreeOf 1
theorem implicitPair_degree_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0):
   (∑ q∈implicitPairSet J,pairYCost q) ≤ J.degreeOf 3∧
     (∑ q∈implicitPairSet J,pairRCost q) ≤ 2*J.degreeOf 1*J.degreeOf 3∧
     (∑ q∈implicitPairSet J,pairZCost q) ≤ J.degreeOf 1:=by
 classical
 have hlocal (A:MvPolynomial (Fin 4) K) (hA:A∈implicitBaseFactors J):
     (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (2:Fin 4)) ≤ 1∧
       (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (1:Fin 4)) ≤ A.degreeOf 1∧
       (∑ G∈positiveRFactors (implicitLift A),G.degreeOf (3:Fin 4)) ≤ A.degreeOf 3:=by
   obtain ⟨_,_,hr,hy⟩:=implicitBaseFactors_spec J A hJ hR hA
   exact lift_positive_factor_budgets A hr hy
 have hb:=implicitBaseFactors_degree_budgets J hJ
 have hy:(∑ q∈implicitPairSet J,pairYCost q) ≤
     ∑ A∈implicitBaseFactors J,A.degreeOf (3:Fin 4):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),G.degreeOf 2*A.degreeOf 3) ≤ _
   rw [←Finset.sum_mul]
   simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 3) (hlocal A hA).1
 have hz:(∑ q∈implicitPairSet J,pairZCost q) ≤
     ∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),G.degreeOf 2*A.degreeOf 1) ≤ _
   rw [←Finset.sum_mul]
   simpa only [one_mul] using Nat.mul_le_mul_right (A.degreeOf 1) (hlocal A hA).1
 have hr:(∑ q∈implicitPairSet J,pairRCost q) ≤
     ∑ A∈implicitBaseFactors J,2*(A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=by
   rw [implicitPairSet,Finset.sum_sigma]
   apply Finset.sum_le_sum
   intro A hA
   change (∑ G∈positiveRFactors (implicitLift A),
     (G.degreeOf 1*A.degreeOf 3+G.degreeOf 3*A.degreeOf 1)) ≤ _
   rw [Finset.sum_add_distrib, ←Finset.sum_mul, ←Finset.sum_mul]
   calc
     _ ≤ A.degreeOf 1*A.degreeOf 3+A.degreeOf 3*A.degreeOf 1:=
       Nat.add_le_add (Nat.mul_le_mul_right _ (hlocal A hA).2.1)
         (Nat.mul_le_mul_right _ (hlocal A hA).2.2)
     _=_:=by ring
 refine ⟨hy.trans hb.2,?_,hz.trans hb.1⟩
 calc
   _ ≤ ∑ A∈implicitBaseFactors J,2*(A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=hr
   _=2*(∑ A∈implicitBaseFactors J,A.degreeOf (1:Fin 4)*A.degreeOf (3:Fin 4)):=
     (Finset.mul_sum _ _ _).symm
   _ ≤ 2*(J.degreeOf 1*J.degreeOf 3):=
     Nat.mul_le_mul_left 2 (implicitBaseFactors_product_degree_budget J hJ)
   _=_:=by ring
theorem implicitPair_input_budgets
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (D w j:ℕ) (hw:0 < w) (hbox:J∈globalCoefficientBox K D w j 0):
   (∑ q∈implicitPairSet J,pairYCost q) ≤ j∧
     (∑ q∈implicitPairSet J,pairRCost q) ≤ 2*((D-1)/w)*j∧
     (∑ q∈implicitPairSet J,pairZCost q) ≤ (D-1)/w:=by
 have hR:J.degreeOf 2=0:=by
   apply Nat.eq_zero_of_le_zero
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   exact (hbox hd).2.1
 have hcaps:=degree_bounds_of_mem_box J D w j 0 hw hbox
 have hy:J.degreeOf 1 ≤ (D-1)/w:=hcaps.1
 have hz:J.degreeOf 3 ≤ j:=hcaps.2.2
 have hb:=implicitPair_degree_budgets J hJ hR
 exact ⟨hb.1.trans hz,
   hb.2.1.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hy) hz),hb.2.2.trans hy⟩
end
end ProximityPrize.SubmissionLower.RCN169
end PackedLegacy_BU

/-! Packed from ProximityPrize.SubmissionLower.V. -/
section PackedLegacy_V
namespace ProximityPrize.SubmissionLower.RCN286
open RCN169 RCN167 RCN079 RCN080 RCN290 RCN293 RCN135 RCN136 RCN138 RCN082 RCN081 RCN174 RCN319
noncomputable section
variable {K:Type*} [Field K]
def RegularSolution (F:MvPolynomial (Fin 4) K) (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ F=0∧
   specialization K P γ (MvPolynomial.pderiv (2:Fin 4) F)≠0
def LiftedSolutionPair
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (P:Polynomial K) (γ:K):Prop:=
 specialization K P γ q.1=0∧
   specialization K P γ (MvPolynomial.pderiv (1:Fin 4) q.1)≠0∧
   RegularSolution q.2 P γ
theorem solution_regular_or_auxiliary
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) (P:Polynomial K) (γ:K)
   (hsolution:specialization K P γ Q=0):
   specialization K P γ (singularAuxiliary Q)=0∨
     ∃ F∈positiveRFactors Q,RegularSolution F P γ:=by
 classical
 let φ:=polynomialEmbedding K
 let v:Fin 3 → GenericField K:=fun i => initialPoint K P γ i.succ
 have heval (F:MvPolynomial (Fin 4) K):
     MvPolynomial.eval v (surfaceMap φ F)=0 ↔ specialization K P γ F=0:=by
   simpa only [canonical_geometricSurfaceMap] using (actual_generic_initial_zero_iff K P γ F)
 obtain haux | ⟨F,hF,_hi,hpos,hz,hregular⟩:=
   surface_zero_singular_or_regular φ (polynomialEmbedding_injective K)
     Q hQ v ((heval Q).mpr hsolution)
 · exact Or.inl ((heval _).mp haux)
 · exact Or.inr ⟨F,Finset.mem_filter.mpr ⟨hF,hpos⟩,
     (heval F).mp hz,(heval _).not.mp hregular⟩
theorem directFactor_data
   (Q F:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hbox:Q∈globalCoefficientBox K D w L s)
   (hF:F∈positiveRFactors Q):
   Irreducible F∧0 < F.degreeOf 2∧F∈globalCoefficientBox K D w L s:=by
 obtain ⟨hi,hd,hr⟩:=positiveRFactors_spec Q F hF
 exact ⟨hi,hr,mem_globalCoefficientBox_of_dvd F Q D w L s hQ hd hbox⟩
theorem directFactor_input_budgets
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s:ℕ) (hw:0 < w) (hbox:Q∈globalCoefficientBox K D w L s):
   (∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
     (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
     (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L:=
 separated_factor_caps_of_prod_dvd (positiveRFactors Q) id Q D w L s hw hQ hbox
   (positiveRFactors_product_dvd Q hQ)
theorem implicitPair_data
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (D w j:ℕ) (hw:1 ≤ w) (hDw:w < D)
   (hbox:J∈globalCoefficientBox K D w j 0)
   (q:(_:MvPolynomial (Fin 4) K) × MvPolynomial (Fin 4) K)
   (hq:q∈implicitPairSet J):
   Irreducible q.1∧Irreducible q.2∧q.2.degreeOf 2=1∧
     q.1∈globalCoefficientBox K D w j 0∧
     q.2∈globalCoefficientBox K D w j 1∧¬ q.2∣q.1:=by
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain ⟨hiA,hdA,hrA,hyA,hiG,hdG,hrG,hproper⟩:=
   implicitPair_spec J q.1 q.2 hJ hR hq
 have hAbox:=mem_globalCoefficientBox_of_dvd q.1 J D w j 0 hJ hdA hbox
 have hGbox:=mem_globalCoefficientBox_of_dvd q.2 (implicitLift q.1) D w j 1
   (implicitLift_nonzero q.1 hrA hyA) hdG
   (implicitLift_mem_box q.1 D w j hw hDw hAbox)
 exact ⟨hiA,hiG,hrG,hAbox,hGbox,hproper⟩
theorem solution_implicit_pair_or_exceptional
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (P:Polynomial K) (γ:K) (D w j:ℕ)
   (hw:1 ≤ w) (hDw:w < D) (hbox:J∈globalCoefficientBox K D w j 0)
   (hsolution:specialization K P γ J=0):
   specialization K P γ (exceptionalAuxiliary J)=0∨
     ∃ q∈implicitPairSet J,LiftedSolutionPair q P γ:=by
 classical
 have hR:J.degreeOf 2=0:=Nat.eq_zero_of_le_zero (degreeOf_R_le_of_mem_box J D w j 0 hbox)
 obtain haux | ⟨A,hA,hi,hd,_hAR,_hAY,hsolA,hregA⟩:=
   solution_exceptional_or_implicit_regular J hJ hR P γ hsolution
 · exact Or.inl haux
 · have hy:MvPolynomial.pderiv (1:Fin 4) A≠0:=by
     intro hz
     exact hregA (by rw [hz,map_zero])
   have hAmem:A∈implicitBaseFactors J:=Finset.mem_filter.mpr ⟨hA,hy⟩
   have hAbox:=mem_globalCoefficientBox_of_dvd A J D w j 0 hJ hd hbox
   obtain ⟨G,hG,_hiG,_hrG,_hGbox,hsolG,hregG,_hproper⟩:=
     exists_regular_lift_factor_of_solution A hi.ne_zero P γ D w j hw hDw hAbox hsolA hregA
   exact Or.inr ⟨⟨A,G⟩,(mem_implicitPairSet J A G).mpr ⟨hAmem,hG⟩,
     hsolA,hregA,hsolG,hregG⟩
def exceptionalSeeds (J:MvPolynomial (Fin 4) K) (seeds:Finset K)
   (selected:K → Polynomial K):Finset K:=by
 classical
 exact seeds.filter (fun γ => specialization K (selected γ) γ (exceptionalAuxiliary J)=0)
theorem exceptionalSeeds_card_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j)
   (seeds:Finset K) (selected:K → Polynomial K):
   (exceptionalSeeds J seeds selected).card ≤ 2*j^2:=by
 classical
 apply exceptional_solution_seed_card_le J hJ hR j p hj hsmall hY hZ
 intro γ hγ
 exact ⟨selected γ,(Finset.mem_filter.mp hγ).2⟩
theorem solution_three_way
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (P:Polynomial K) (γ:K) (hsolution:specialization K P γ Q=0):
   (∃ F∈positiveRFactors Q,RegularSolution F P γ)∨
     (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q P γ)∨
     specialization K P γ (exceptionalAuxiliary (singularAuxiliary Q))=0:=by
 obtain haux | hregular:=solution_regular_or_auxiliary Q hQ P γ hsolution
 · have hJ:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
   obtain hexceptional | himplicit:=solution_implicit_pair_or_exceptional
     (singularAuxiliary Q) hJ.1 P γ ((2*s-1)*D) w ((2*s-1)*L)
     hw hDw hJ.2 haux
   · exact Or.inr (Or.inr hexceptional)
   · exact Or.inr (Or.inl himplicit)
 · exact Or.inl hregular
theorem selected_seed_decomposition
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
   (D w L s p:ℕ) [CharP K p] (hs:1 ≤ s) (hsmall:s < p)
   (hw:1 ≤ w) (hDw:w < (2*s-1)*D)
   (hj:1 ≤ (2*s-1)*L) (hjSmall:(2*s-1)*L < p)
   (hbox:Q∈globalCoefficientBox K D w L s)
   (seeds:Finset K) (selected:K → Polynomial K)
   (hsolutions:∀ γ∈seeds,specialization K (selected γ) γ Q=0):
   (exceptionalSeeds (singularAuxiliary Q) seeds selected).card ≤
       2*((2*s-1)*L)^2∧
     (∀ γ∈seeds,γ∉exceptionalSeeds (singularAuxiliary Q) seeds selected →
       (∃ F∈positiveRFactors Q,RegularSolution F (selected γ) γ)∨
         (∃ q∈implicitPairSet (singularAuxiliary Q),LiftedSolutionPair q (selected γ) γ))∧
     ((∑ F∈positiveRFactors Q,F.degreeOf (1:Fin 4)) ≤ (D-1)/w∧
       (∑ F∈positiveRFactors Q,F.degreeOf (2:Fin 4)) ≤ s∧
       (∑ F∈positiveRFactors Q,F.degreeOf (3:Fin 4)) ≤ L)∧
     ((∑ q∈implicitPairSet (singularAuxiliary Q),pairYCost q) ≤ (2*s-1)*L∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairRCost q) ≤
         2*(((2*s-1)*D-1)/w)*((2*s-1)*L)∧
       (∑ q∈implicitPairSet (singularAuxiliary Q),pairZCost q) ≤
         ((2*s-1)*D-1)/w):=by
 classical
 have hwpos:0 < w:=by omega
 obtain ⟨hJ,hJbox⟩:=singularAuxiliary_nonzero_mem_box Q D w L s p hQ hs hsmall hbox
 have hJR:(singularAuxiliary Q).degreeOf 2=0:=Nat.eq_zero_of_le_zero
   (degreeOf_R_le_of_mem_box _ _ _ _ _ hJbox)
 have hJY:(singularAuxiliary Q).degreeOf 1 ≤ (2*s-1)*L:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   intro d hd
   have hh:=(hJbox hd).1
   omega
 have hJZ:=degreeOf_Z_le_of_mem_box _ _ _ _ _ hJbox
 refine ⟨exceptionalSeeds_card_le (singularAuxiliary Q) hJ hJR ((2*s-1)*L)
     p hj hjSmall hJY hJZ seeds selected,?_,
   directFactor_input_budgets Q hQ D w L s hwpos hbox,
   implicitPair_input_budgets (singularAuxiliary Q) hJ ((2*s-1)*D) w
     ((2*s-1)*L) hwpos hJbox⟩
 intro γ hγ hnot
 obtain hregular | himplicit | hexceptional:=solution_three_way
   Q hQ D w L s p hs hsmall hw hDw hbox (selected γ) γ (hsolutions γ hγ)
 · exact Or.inl hregular
 · exact Or.inr himplicit
 · exact False.elim (hnot (Finset.mem_filter.mpr ⟨hγ,hexceptional⟩))
end
end ProximityPrize.SubmissionLower.RCN286
end PackedLegacy_V

/-! Packed from ProximityPrize.SubmissionLower.FS. -/
section PackedLegacy_FS
namespace ProximityPrize.SubmissionLower.RCN242
open RCN051
def surfaceVector:DegreeVector:=⟨yCap,slopeCap,seedTotalCap⟩
end ProximityPrize.SubmissionLower.RCN242
end PackedLegacy_FS

/-! Packed from ProximityPrize.SubmissionLower.BT. -/
section PackedLegacy_BT
namespace ProximityPrize.SubmissionLower.RCN168
open RCN051
def implicitWeightedCap:ℕ:=(2*slopeCap-1)*weightedCap
def implicitYCap:ℕ:=(implicitWeightedCap-1)/w
def liftedSurface:DegreeVector:=⟨implicitYCap,1,algebraicCap⟩
def implicitCut:DegreeVector:=⟨implicitYCap,0,algebraicCap⟩
def liftedLastTail:DegreeVector:=
 ⟨1+2*implicitWeightedCap*implicitYCap,
   implicitWeightedCap,2*implicitWeightedCap*algebraicCap⟩
def liftedAgreement:DegreeVector:=
 ⟨1+2*w*implicitYCap,w,2*w*algebraicCap+1⟩
def liftedSingularNumerator:ℕ:=
 gap*(algebraicCap+2*algebraicCap^2+
   mixed liftedSurface implicitCut liftedLastTail+
   (errors+1)*mixed liftedSurface implicitCut unitZ)+
 (n-w)*mixed liftedSurface implicitCut liftedAgreement
def liftedTotalNumerator:ℕ:=regularNumerator+gap*liftedSingularNumerator
theorem lifted_parameter_values:
   implicitWeightedCap=29924640∧implicitYCap=228∧
   liftedLastTail=⟨13645635841,29924640,94801259520⟩∧
   liftedAgreement=⟨59768377,131071,415232929⟩:=by
 norm_num [implicitWeightedCap,implicitYCap,liftedLastTail,liftedAgreement,
   algebraicCap,weightedCap,RCN051.multiplicity,agreements,
   w,slopeCap,seedTotalCap]
theorem lifted_projection_values:
   mixed liftedSurface implicitCut unitY=1584∧
   mixed liftedSurface implicitCut unitR=722304∧
   mixed liftedSurface implicitCut unitZ=228:=by
 norm_num [mixed,liftedSurface,implicitCut,implicitYCap,implicitWeightedCap,
   unitY,unitR,unitZ,algebraicCap,weightedCap,
   RCN051.multiplicity,agreements,w,slopeCap,seedTotalCap]
theorem lifted_projection_characteristic_gates:
   implicitWeightedCap < prime∧
   mixed liftedSurface implicitCut unitY < prime∧
   mixed liftedSurface implicitCut unitR < prime∧
   mixed liftedSurface implicitCut unitZ < prime:=by
 rcases lifted_projection_values with ⟨hY,hR,hZ⟩
 rw [hY,hR,hZ,lifted_parameter_values.1]
 norm_num [prime]
end ProximityPrize.SubmissionLower.RCN168
end PackedLegacy_BT

/-! Packed from ProximityPrize.SubmissionLower.P4. -/
section PackedLegacy_P4
namespace ProximityPrize.SubmissionLower.RCN289
open RCN174 RCN081 RCN313
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K]
abbrev Poly4 (K:Type*) [Field K]:=MvPolynomial (Fin 4) K
end
end ProximityPrize.SubmissionLower.RCN289
end PackedLegacy_P4

/-! Packed from ProximityPrize.SubmissionLower.Y4. -/
section PackedLegacy_Y4
namespace ProximityPrize.SubmissionLower.RCN068
open scoped Classical
open RCN051 RCN313 RCN136 RCN174 RCN231 RCN238 RCN289
noncomputable section
def capAt (v:DegreeVector):Fin 3 → ℕ:=![v.y,v.r,v.z]
def numeratorCaps (ell s L b:ℕ):DegreeVector:=
 ⟨1+2*b*ell,b*(2*s-1),2*b*L⟩
def agreementCaps (ell s L w:ℕ):DegreeVector:=
 ⟨1+2*w*ell,w*(2*s-1),2*w*L+1⟩
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def HasCaps (Q:MvPolynomial (Fin 3) Ω) (v:DegreeVector):Prop:=
 ∀ i,Q.degreeOf i ≤ capAt v i
variable (φ:Polynomial K →+*Ω)
def firstTailSurface (F:MvPolynomial (Fin 4) K) (w:ℕ):MvPolynomial (Fin 3) Ω:=
 surfaceMap φ (numerator K F (w+1))
theorem surface_agreement_caps
   (F:MvPolynomial (Fin 4) K) (ell s L:ℕ) (hs:1 ≤ s)
   (hY:F.degreeOf 1 ≤ ell) (hR:F.degreeOf 2 ≤ s) (hZ:F.degreeOf 3 ≤ L)
   (w:ℕ) (c:ℕ → K) (x u₀ u₁:K):
   HasCaps (surfaceMap φ (agreementNumerator F w c x u₀ u₁))
     (agreementCaps ell s L w):=by
 obtain ⟨hy,hr,hz⟩:=agreementNumerator_degree_bounds F ell s L hs hY hR hZ w c x u₀ u₁
 intro i
 fin_cases i
 · exact (surfaceMap_degreeOf_le φ _ 0).trans hy
 · exact (surfaceMap_degreeOf_le φ _ 1).trans hr
 · exact (surfaceMap_degreeOf_le φ _ 2).trans hz
theorem selected_firstTail_zero
   (F:MvPolynomial (Fin 4) K) (selected:K → Polynomial K)
   (γ:K) (w:ℕ) (hdegree:(selected γ).natDegree ≤ w)
   (hsolution:RCN319.specialization K (selected γ) γ F=0):
   MvPolynomial.aeval (selectedPoint φ selected γ) (firstTailSurface φ F w)=0:=by
 change MvPolynomial.eval (selectedPoint φ selected γ)
   (surfaceMap φ (numerator K F (w+1)))=0
 rw [eval_surfaceMap]
 have hv:Fin.cases (φ Polynomial.X) (selectedPoint φ selected γ)=
     polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X):=by
   funext i
   fin_cases i <;> rfl
 rw [hv]
 exact polynomialPoint_numerator_zero (φ.comp Polynomial.C) F (selected γ) γ
   (φ Polynomial.X) hsolution (w+1) (Nat.lt_succ_of_le hdegree)
theorem fixed_implicit_agreement_caps (F:MvPolynomial (Fin 4) K)
   (hY:F.degreeOf 1 ≤ RCN168.implicitYCap)
   (hR:F.degreeOf 2 ≤ 1) (hZ:F.degreeOf 3 ≤ algebraicCap)
   (x u₀ u₁:K):
   HasCaps (agreementPolynomial φ F w x u₀ u₁)
     RCN168.liftedAgreement:=by
 have h:=surface_agreement_caps φ F RCN168.implicitYCap 1
   algebraicCap (by decide) hY hR hZ w (fun j↦(j.factorial:K)⁻¹) x u₀ u₁
 simpa [agreementPolynomial,agreementCaps,RCN168.liftedAgreement] using h
section MixedGates
variable (G T:MvPolynomial (Fin 3) Ω) (g t:DegreeVector)
theorem actual_pair_degree_le (hG:HasCaps G g) (hT:HasCaps T t) (j k:Fin 3):
   T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k ≤
     capAt t j*capAt g k+capAt g j*capAt t k:=
 Nat.add_le_add (Nat.mul_le_mul (hT j) (hG k)) (Nat.mul_le_mul (hG j) (hT k))
theorem pair_caps_below_of_mixed (p:ℕ)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   ∀ j k:Fin 3,j≠k →
     capAt t j*capAt g k+capAt g j*capAt t k < p:=by
 intro j k hne
 fin_cases j <;> fin_cases k
 all_goals try exact (hne rfl).elim
 all_goals first
   | simpa [capAt,mixed,unitY,Nat.mul_comm,Nat.add_comm] using hY
   | simpa [capAt,mixed,unitR,Nat.mul_comm,Nat.add_comm] using hR
   | simpa [capAt,mixed,unitZ,Nat.mul_comm,Nat.add_comm] using hZ
theorem actual_characteristic_gates (p:ℕ)
   (hG:HasCaps G g) (hT:HasCaps T t)
   (hg:∀ j,capAt g j < p)
   (hY:mixed g t unitY < p) (hR:mixed g t unitR < p) (hZ:mixed g t unitZ < p):
   (∀ j,G.degreeOf j < p)∧
     ∀ j k:Fin 3,j≠k →
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < p:=by
 refine ⟨fun j↦(hG j).trans_lt (hg j),?_⟩
 intro j k hjk
 exact (actual_pair_degree_le G T g t hG hT j k).trans_lt
   (pair_caps_below_of_mixed g t p hY hR hZ j k hjk)
end MixedGates
theorem fixed_implicit_surface_caps_below_characteristic:
   ∀ j,capAt RCN168.liftedSurface j < prime:=by
 intro j
 fin_cases j <;>
   norm_num [capAt,RCN168.liftedSurface,
     RCN168.implicitYCap,RCN168.implicitWeightedCap,
     algebraicCap,weightedCap,RCN051.multiplicity,agreements,
     w,slopeCap,seedTotalCap,prime]
theorem fixed_implicit_characteristic_gates (G T:MvPolynomial (Fin 3) Ω)
   (hG:HasCaps G RCN168.liftedSurface)
   (hT:HasCaps T RCN168.implicitCut):
   (∀ j,G.degreeOf j < prime)∧
     ∀ j k:Fin 3,j≠k →
       T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < prime:=by
 rcases RCN168.lifted_projection_characteristic_gates with
   ⟨_,hY,hR,hZ⟩
 exact actual_characteristic_gates G T _ _ prime hG hT
   fixed_implicit_surface_caps_below_characteristic hY hR hZ
end
end ProximityPrize.SubmissionLower.RCN068
end PackedLegacy_Y4

/-! Packed from ProximityPrize.SubmissionLower.B2. -/
section PackedLegacy_B2
namespace ProximityPrize.SubmissionLower.RCN070
open RCN051 RCN168
open scoped BigOperators
def addVector (a b:DegreeVector):DegreeVector:=
 ⟨a.y+b.y,a.r+b.r,a.z+b.z⟩
def scaleVector (c:ℕ) (v:DegreeVector):DegreeVector:=
 ⟨c*v.y,c*v.r,c*v.z⟩
def sumVector {I:Type} [Fintype I] (v:I → DegreeVector):DegreeVector:=
 ⟨∑ i,(v i).y,∑ i,(v i).r,∑ i,(v i).z⟩
def vectorLE (a b:DegreeVector):Prop:=a.y ≤ b.y∧a.r ≤ b.r∧a.z ≤ b.z
def dot (a b:DegreeVector):ℕ:=a.y*b.y+a.r*b.r+a.z*b.z
theorem dot_comm (a b:DegreeVector):dot a b=dot b a:=by
 simp only [dot]
 ring
theorem dot_mono_left {a b:DegreeVector} (c:DegreeVector) (h:vectorLE a b):
   dot a c ≤ dot b c:=
 Nat.add_le_add
   (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1) (Nat.mul_le_mul_right c.r h.2.1))
   (Nat.mul_le_mul_right c.z h.2.2)
theorem dot_sum_left {I:Type} [Fintype I] (v:I → DegreeVector) (a:DegreeVector):
   dot (sumVector v) a=∑ i,dot (v i) a:=by
 simp only [dot,sumVector,Finset.sum_add_distrib,Finset.sum_mul]
theorem dot_sum_right {I:Type} [Fintype I] (v:I → DegreeVector) (a:DegreeVector):
   dot a (sumVector v)=∑ i,dot a (v i):=by
 rw [dot_comm,dot_sum_left]
 apply Finset.sum_congr rfl
 intro i _
 exact dot_comm (v i) a
def cutCoefficients:DegreeVector:=
 ⟨cutNumerator unitY,cutNumerator unitR,cutNumerator unitZ⟩
def wholeCoefficients:DegreeVector:=
 ⟨wholeNumerator unitY,wholeNumerator unitR,wholeNumerator unitZ⟩
def envelopeCoefficients:DegreeVector:=
 ⟨max (cutNumerator unitY) (wholeNumerator unitY),
   max (cutNumerator unitR) (wholeNumerator unitR),
   max (cutNumerator unitZ) (wholeNumerator unitZ)⟩
def regularSurface:DegreeVector:=⟨yCap,slopeCap,seedTotalCap⟩
def implicitAggregateCost:DegreeVector:=
 ⟨algebraicCap,2*implicitYCap*algebraicCap,implicitYCap⟩
def implicitCoefficients:DegreeVector:=
 ⟨(n-w)*liftedAgreement.y,(n-w)*liftedAgreement.r,
   (n-w)*liftedAgreement.z+(errors+1)*gap⟩
def implicitCoreNumerator:ℕ:=
 (n-w)*mixed liftedSurface implicitCut liftedAgreement+
   (errors+1)*gap*mixed liftedSurface implicitCut unitZ
theorem implicit_bound_eq_dot (v:DegreeVector):
   (n-w)*dot liftedAgreement v+(errors+1)*gap*v.z=
     dot v implicitCoefficients:=by
 simp only [implicitCoefficients,dot]
 ring
theorem implicit_aggregate_eq_core:
   dot implicitAggregateCost implicitCoefficients=implicitCoreNumerator:=by
 simp only [implicitAggregateCost,implicitCoefficients,implicitCoreNumerator,
   dot,mixed,liftedSurface,implicitCut,unitZ]
 ring
theorem sum_implicit_counts_bound {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:∀ i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z):
   (∑ i,count i)*gap ≤ implicitCoreNumerator:=by
 calc
   _=∑ i,count i*gap:=Finset.sum_mul _ _ _
   _ ≤ ∑ i,dot (cost i) implicitCoefficients:=by
     apply Finset.sum_le_sum
     intro i _
     rw [←implicit_bound_eq_dot]
     exact hcount i
   _=dot (sumVector cost) implicitCoefficients:=(dot_sum_left _ _).symm
   _ ≤ dot implicitAggregateCost implicitCoefficients:=dot_mono_left _ ⟨hy,hr,hz⟩
   _=implicitCoreNumerator:=implicit_aggregate_eq_core
theorem lifted_singular_padding:
   liftedSingularNumerator=
     (implicitCoreNumerator+2*algebraicCap^2*gap)+
       gap*(algebraicCap+mixed liftedSurface implicitCut liftedLastTail):=by
 simp only [liftedSingularNumerator,implicitCoreNumerator]
 ring
theorem implicit_with_exceptions_bound {I:Type} [Fintype I]
   (count:I → ℕ) (cost:I → DegreeVector) (exceptions:ℕ)
   (hy:(∑ i,(cost i).y) ≤ algebraicCap)
   (hr:(∑ i,(cost i).r) ≤ 2*implicitYCap*algebraicCap)
   (hz:(∑ i,(cost i).z) ≤ implicitYCap)
   (hcount:∀ i,count i*gap ≤
     (n-w)*dot liftedAgreement (cost i)+
       (errors+1)*gap*(cost i).z)
   (hexceptions:exceptions ≤ 2*algebraicCap^2):
   ((∑ i,count i)+exceptions)*gap ≤ liftedSingularNumerator:=by
 have hmain:=sum_implicit_counts_bound count cost hy hr hz hcount
 calc
   _=(∑ i,count i)*gap+exceptions*gap:=Nat.add_mul _ _ _
   _ ≤ implicitCoreNumerator+2*algebraicCap^2*gap:=
     Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
   _ ≤ liftedSingularNumerator:=by
     rw [lifted_singular_padding]
     exact Nat.le_add_right _ _
end ProximityPrize.SubmissionLower.RCN070
end PackedLegacy_B2

/-! Packed from ProximityPrize.SubmissionLower.BV. -/
section PackedLegacy_BV
namespace ProximityPrize.SubmissionLower.RCN170
open scoped Classical BigOperators
open RCN051 RCN168 RCN068 RCN070 RCN169 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def pairCost (A G:MvPolynomial (Fin 4) K):DegreeVector:=
 ⟨pairYCost ⟨A,G⟩,pairRCost ⟨A,G⟩,pairZCost ⟨A,G⟩⟩
def geometricPairCost (A:MvPolynomial (Fin 4) K)
   (g:MvPolynomial (Fin 3) Ω):DegreeVector:=
 ⟨g.degreeOf 1*A.degreeOf 3,
   g.degreeOf 0*A.degreeOf 3+g.degreeOf 2*A.degreeOf 1,
   g.degreeOf 1*A.degreeOf 1⟩
theorem capAt_dot (a b:DegreeVector):
   (∑ i:Fin 3,capAt a i*capAt b i)=dot a b:=by
 simp [Fin.sum_univ_three,capAt,dot]
theorem coordinateMixedDegree_le_geometricPairCost
   (φ:Polynomial K →+*Ω) (A:MvPolynomial (Fin 4) K)
   (hAR:A.degreeOf 2=0) (g:MvPolynomial (Fin 3) Ω) (i:Fin 3):
   coordinateMixedDegree Ω g (surfaceMap φ A) i ≤ capAt (geometricPairCost A g) i:=by
 have hTY:(surfaceMap φ A).degreeOf (0:Fin 3) ≤ A.degreeOf (1:Fin 4):=
   surfaceMap_degreeOf_le φ A (0:Fin 3)
 have hTRle:(surfaceMap φ A).degreeOf (1:Fin 3) ≤ A.degreeOf (2:Fin 4):=
   surfaceMap_degreeOf_le φ A (1:Fin 3)
 rw [hAR] at hTRle
 have hTR:(surfaceMap φ A).degreeOf (1:Fin 3)=0:=
   Nat.eq_zero_of_le_zero hTRle
 have hTZ:(surfaceMap φ A).degreeOf (2:Fin 3) ≤ A.degreeOf (3:Fin 4):=
   surfaceMap_degreeOf_le φ A (2:Fin 3)
 fin_cases i
 · simpa [coordinateMixedDegree_zero,hTR,capAt,geometricPairCost] using
     Nat.mul_le_mul_left (g.degreeOf 1) hTZ
 · have h:=Nat.add_le_add
     (Nat.mul_le_mul_right (g.degreeOf 2) hTY)
     (Nat.mul_le_mul_left (g.degreeOf 0) hTZ)
   simpa [coordinateMixedDegree_one,capAt,geometricPairCost,
     Nat.mul_comm,Nat.add_comm] using h
 · simpa [coordinateMixedDegree_two,hTR,capAt,geometricPairCost,Nat.mul_comm] using
     Nat.mul_le_mul_right (g.degreeOf 1) hTY
theorem sum_geometricPairCost_le
   (φ:Polynomial K →+*Ω) (hφ:Function.Injective φ)
   (A G:MvPolynomial (Fin 4) K) (hG:G≠0) (i:Fin 3):
   (∑ g∈surfaceFactors φ G,capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i:=by
 have hY:=surfaceFactors_degree_budget φ hφ G hG (0:Fin 3)
 have hR:=surfaceFactors_degree_budget φ hφ G hG (1:Fin 3)
 have hZ:=surfaceFactors_degree_budget φ hφ G hG (2:Fin 3)
 fin_cases i
 · simpa [capAt,geometricPairCost,pairCost,pairYCost, ←Finset.sum_mul] using
     Nat.mul_le_mul_right (A.degreeOf 3) hR
 · simpa [capAt,geometricPairCost,pairCost,pairRCost,
     Finset.sum_add_distrib, ←Finset.sum_mul] using
     Nat.add_le_add (Nat.mul_le_mul_right (A.degreeOf 3) hY)
       (Nat.mul_le_mul_right (A.degreeOf 1) hZ)
 · simpa [capAt,geometricPairCost,pairCost,pairZCost, ←Finset.sum_mul] using
     Nat.mul_le_mul_right (A.degreeOf 1) hR
theorem canonical_selectedPoint_surface_evaluation
   (selected:K → Polynomial K) (γ:K) (F:MvPolynomial (Fin 4) K):
   MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected γ)
     (surfaceMap (polynomialEmbedding K) F)=
       polynomialEmbedding K (specialization K (selected γ) γ F):=by
 rw [selectedPoint_evaluation]
 exact evaluation_at_initialPoint K (selected γ) γ F
theorem geometric_factor_proper_cut
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (g:MvPolynomial (Fin 3) (GenericField K))
   (hg:g∈surfaceFactors (polynomialEmbedding K) G):
   ¬ g∣surfaceMap (polynomialEmbedding K) A:=by
 obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec (polynomialEmbedding K) G g hg
 have hpos:0 < G.degreeOf 1+G.degreeOf 2+G.degreeOf 3:=by omega
 have hgeo:g∣geometricSurfaceMap K (GenericField K) G:=by
   simpa only [canonical_geometricSurfaceMap] using hdiv
 intro h
 apply hproper
 apply (geometric_factor_dvd_iff K (GenericField K) G A hG hpos g hgi hgeo).mp
 simpa only [canonical_geometricSurfaceMap] using h
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound_fixed
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (hAbox:A∈globalCoefficientBox K implicitWeightedCap w algebraicCap 0)
   (hGbox:G∈globalCoefficientBox K implicitWeightedCap w algebraicCap 1)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K prime]
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap ≤ (n-w)*dot liftedAgreement (pairCost A G)+
     (errors+1)*gap*pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitWeightedCap w algebraicCap 0
   (by norm_num [w]) hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitWeightedCap w algebraicCap 1
   (by norm_num [w]) hGbox
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) implicitCut:=by
   intro i
   fin_cases i
   · exact (surfaceMap_degreeOf_le φ A 0).trans hAGcaps.1
   · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [canonical_selectedPoint_surface_evaluation,hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [canonical_selectedPoint_surface_evaluation,hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ (polynomialEmbedding_injective K)
     G hG.ne_zero (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*gap ≤
       (n-w)*(∑ i:Fin 3,
         capAt liftedAgreement i*capAt (geometricPairCost A g) i)+
         (errors+1)*gap*capAt (geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g liftedSurface:=by
     intro i
     fin_cases i
     · exact (hfacdegree 0).trans hGGcaps.1
     · exact (hfacdegree 1).trans hGGcaps.2.1
     · exact (hfacdegree 2).trans hGGcaps.2.2
   have hgates:=fixed_implicit_characteristic_gates g (surfaceMap φ A) hgcaps hAcaps
   have hreg:∀ γ∈seedsFor g,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
       (RCN231.polynomialPoint (φ.comp Polynomial.C)
         (selected γ) γ (φ Polynomial.X)) (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i))
       liftedAgreement:=
     fixed_implicit_agreement_caps φ G hGGcaps.1 hGGcaps.2.1 hGGcaps.2.2 (x i) (u₀ i) (u₁ i)
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (geometric_factor_proper_cut A G hG hGR hproper g hg) selected (seedsFor g)
     nodes x u₀ u₁ hinj prime w agreements errors
     (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,agreements])
     (by rw [hnodes];norm_num [agreements,n]) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w errors (hsub g) hnoPencil)
     (capAt liftedAgreement) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=coordinateMixedDegree_le_geometricPairCost φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt liftedAgreement i) (hδ i))))
     (Nat.mul_le_mul_left ((errors+1)*gap) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,capAt (geometricPairCost A g) i) ≤ capAt (pairCost A G) i:=
   sum_geometricPairCost_le φ (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt liftedAgreement i*capAt (geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt liftedAgreement i*
         (∑ g∈factors,capAt (geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*gap ≤ (∑ g∈factors,(seedsFor g).card)*gap:=Nat.mul_le_mul_right gap hcard
   _=∑ g∈factors,(seedsFor g).card*gap:=by rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt liftedAgreement i*capAt (geometricPairCost A g) i)+
         (errors+1)*gap*capAt (geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt liftedAgreement i*
       (∑ g∈factors,capAt (geometricPairCost A g) i))+
         (errors+1)*gap*(∑ g∈factors,capAt (geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*
       (∑ i:Fin 3,capAt liftedAgreement i*capAt (pairCost A G) i)+
       (errors+1)*gap*capAt (pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt liftedAgreement i) (hbudget i))))
       (Nat.mul_le_mul_left ((errors+1)*gap) (hbudget 2))
   _=(n-w)*dot liftedAgreement (pairCost A G)+
       (errors+1)*gap*pairZCost ⟨A,G⟩:=by
     rw [capAt_dot]
     rfl
end
end ProximityPrize.SubmissionLower.RCN170
end PackedLegacy_BV

/-! Packed from ProximityPrize.SubmissionLower.BW. -/
section PackedLegacy_BW
namespace ProximityPrize.SubmissionLower.RCN172
open scoped Classical BigOperators
open RCN169 RCN136 RCN135 RCN138 RCN137 RCN238 RCN243 RCN081 RCN174 RCN319 RCN001 RCN068
noncomputable section
variable {K:Type} [Field K]
 {ι:Type*}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq ι:=Classical.decEq ι
theorem implicit_pair_seed_bound
   (A G:MvPolynomial (Fin 4) K) (hG:Irreducible G)
   (hGR:G.degreeOf 2=1) (hproper:¬ G∣A)
   (implicitD w jY jZ p n a e:ℕ)
   (hAbox:A∈globalCoefficientBox K implicitD w jZ 0)
   (hGbox:G∈globalCoefficientBox K implicitD w jZ 1)
   (hjY:(implicitD-1)/w=jY)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP K p]
   (hw:1 ≤ w) (hchar:w < p) (hwa:w < a) (han:a ≤ n)
   (hjYsmall:jY < p) (hjZsmall:jZ < p)
   (hmixedSmall:2*jY*jZ < p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolutionA:∀ γ∈Γ,specialization K (selected γ) γ A=0)
   (hsolutionG:∀ γ∈Γ,specialization K (selected γ) γ G=0)
   (hregular:∀ γ∈Γ,
     specialization K (selected γ) γ (MvPolynomial.pderiv (2:Fin 4) G)≠0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i =>
       (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e):
   Γ.card*(a-w) ≤
     (n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
 classical
 let φ:=polynomialEmbedding K
 let factors:=surfaceFactors φ G
 let seedsFor:=fun g:MvPolynomial (Fin 3) (GenericField K) =>
   Γ.filter (fun γ => MvPolynomial.eval (selectedPoint φ selected γ) g=0)
 let surfaceCap:RCN051.DegreeVector:=⟨jY,1,jZ⟩
 let cutCap:RCN051.DegreeVector:=⟨jY,0,jZ⟩
 let agreementCap:RCN051.DegreeVector:=
   ⟨1+2*w*jY,w,2*w*jZ+1⟩
 have hsub (g):seedsFor g ⊆ Γ:=Finset.filter_subset _ _
 have hAGcaps:=degree_bounds_of_mem_box A implicitD w jZ 0 hw hAbox
 have hGGcaps:=degree_bounds_of_mem_box G implicitD w jZ 1 hw hGbox
 have hAY:A.degreeOf 1 ≤ jY:=hAGcaps.1.trans_eq hjY
 have hGY:G.degreeOf 1 ≤ jY:=hGGcaps.1.trans_eq hjY
 have hAR:A.degreeOf 2=0:=Nat.eq_zero_of_le_zero hAGcaps.2.1
 have hAcaps:HasCaps (surfaceMap φ A) cutCap:=by
   intro i
   fin_cases i
   · exact (surfaceMap_degreeOf_le φ A 0).trans hAY
   · exact (surfaceMap_degreeOf_le φ A 1).trans hAGcaps.2.1
   · exact (surfaceMap_degreeOf_le φ A 2).trans hAGcaps.2.2
 have hFzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ G)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionG γ hγ,map_zero]
 have hAzero:∀ γ∈Γ,
     MvPolynomial.eval (selectedPoint φ selected γ) (surfaceMap φ A)=0:=by
   intro γ hγ
   rw [RCN170.canonical_selectedPoint_surface_evaluation,
     hsolutionA γ hγ,map_zero]
 have hcover:Γ ⊆ factors.biUnion seedsFor:=by
   intro γ hγ
   obtain ⟨g,hg,hz⟩:=exists_surfaceFactor_zero φ
     (polynomialEmbedding_injective K) G hG.ne_zero
     (selectedPoint φ selected γ) (hFzero γ hγ)
   exact Finset.mem_biUnion.mpr ⟨g,hg,Finset.mem_filter.mpr ⟨hγ,hz⟩⟩
 have hcard:Γ.card ≤ ∑ g∈factors,(seedsFor g).card:=
   (Finset.card_le_card hcover).trans Finset.card_biUnion_le
 have hsingle (g:MvPolynomial (Fin 3) (GenericField K)) (hg:g∈factors):
     (seedsFor g).card*(a-w) ≤
       (n-w)*(∑ i:Fin 3,
         capAt agreementCap i*
           capAt (RCN170.geometricPairCost A g) i)+
         (e+1)*(a-w)*
           capAt (RCN170.geometricPairCost A g) 2:=by
   obtain ⟨hgi,hdiv⟩:=surfaceFactors_spec φ G g hg
   have hfacdegree (i:Fin 3):g.degreeOf i ≤ G.degreeOf i.succ:=
     (coordinate_degree_le_of_dvd i g (surfaceMap φ G) hdiv
       (surfaceMap_ne_zero φ (polynomialEmbedding_injective K) G hG.ne_zero)).trans
         (surfaceMap_degreeOf_le φ G i)
   have hgcaps:HasCaps g surfaceCap:=by
     intro i
     fin_cases i
     · exact (hfacdegree 0).trans hGY
     · exact (hfacdegree 1).trans hGGcaps.2.1
     · exact (hfacdegree 2).trans hGGcaps.2.2
   have hsurfaceSmall:∀ j,capAt surfaceCap j < p:=by
     intro j
     fin_cases j
     · simpa [surfaceCap,capAt] using hjYsmall
     · simpa [surfaceCap,capAt] using lt_of_le_of_lt hw hchar
     · simpa [surfaceCap,capAt] using hjZsmall
   have hgates:=actual_characteristic_gates g (surfaceMap φ A)
     surfaceCap cutCap p hgcaps hAcaps hsurfaceSmall
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitY] using hjZsmall)
     (by
       simp [RCN051.mixed,surfaceCap,cutCap,
         RCN051.unitR]
       rw [show jY*jZ+jZ*jY=2*jY*jZ by ring]
       exact hmixedSmall)
     (by simpa [RCN051.mixed,surfaceCap,cutCap,
       RCN051.unitZ] using hjYsmall)
   have hreg:∀ γ∈seedsFor g,
       MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
         (RCN231.polynomialPoint (φ.comp Polynomial.C)
           (selected γ) γ (φ Polynomial.X))
         (MvPolynomial.pderiv (2:Fin 4) G)≠0:=by
     intro γ hγ
     exact (initialPoint_regular_iff K G (selected γ) γ).mpr
       (hregular γ (hsub g hγ))
   have hcap (i:ι):HasCaps
       (agreementPolynomial φ G w (x i) (u₀ i) (u₁ i)) agreementCap:=by
     have h:=surface_agreement_caps φ G jY 1 jZ (by decide)
       hGY hGGcaps.2.1 hGGcaps.2.2 w
       (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i)
     simpa [agreementPolynomial,agreementCaps,agreementCap] using h
   have hcount:=proper_cut_seed_bound φ G g (surfaceMap φ A) hgi hdiv
     (RCN170.geometric_factor_proper_cut
       A G hG hGR hproper g hg)
     selected (seedsFor g) nodes x u₀ u₁ hinj p w a e hw hchar hwa
     (by simpa [hnodes] using han) hgates.1 hgates.2
     (fun γ hγ => hdegree γ (hsub g hγ))
     (fun γ hγ => hsolutionG γ (hsub g hγ)) hreg
     (fun γ hγ => (Finset.mem_filter.mp hγ).2)
     (fun γ hγ => hAzero γ (hsub g hγ))
     (fun γ hγ => hagreement γ (hsub g hγ))
     (noLargeSelectedPencil_mono selected Γ (seedsFor g) w e (hsub g) hnoPencil)
     (capAt agreementCap) (fun i _ => hcap i)
   rw [hnodes] at hcount
   have hδ (i:Fin 3):=
     RCN170.coordinateMixedDegree_le_geometricPairCost
       φ A hAR g i
   exact hcount.trans (Nat.add_le_add
     (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hδ i))))
     (Nat.mul_le_mul_left ((e+1)*(a-w)) (hδ 2)))
 have hbudget (i:Fin 3):
     (∑ g∈factors,
       capAt (RCN170.geometricPairCost A g) i) ≤
         capAt (RCN170.pairCost A G) i:=
   RCN170.sum_geometricPairCost_le φ
     (polynomialEmbedding_injective K) A G hG.ne_zero i
 have hfubini:
     (∑ g∈factors,∑ i:Fin 3,capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)=
       ∑ i:Fin 3,capAt agreementCap i*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) i):=by
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i _
   rw [Finset.mul_sum]
 calc
   Γ.card*(a-w) ≤ (∑ g∈factors,(seedsFor g).card)*(a-w):=
     Nat.mul_le_mul_right (a-w) hcard
   _=∑ g∈factors,(seedsFor g).card*(a-w):=by
     rw [Finset.sum_mul]
   _ ≤ ∑ g∈factors,((n-w)*(∑ i:Fin 3,
       capAt agreementCap i*
         capAt (RCN170.geometricPairCost A g) i)+
       (e+1)*(a-w)*
         capAt (RCN170.geometricPairCost A g) 2):=
     Finset.sum_le_sum (fun g hg => hsingle g hg)
   _=(n-w)*(∑ i:Fin 3,capAt agreementCap i*
       (∑ g∈factors,
         capAt (RCN170.geometricPairCost A g) i))+
       (e+1)*(a-w)*
         (∑ g∈factors,
           capAt (RCN170.geometricPairCost A g) 2):=by
     rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum,hfubini]
   _ ≤ (n-w)*(∑ i:Fin 3,capAt agreementCap i*
       capAt (RCN170.pairCost A G) i)+
       (e+1)*(a-w)*
         capAt (RCN170.pairCost A G) 2:=
     Nat.add_le_add (Nat.mul_le_mul_left (n-w) (Finset.sum_le_sum
       (fun i _ => Nat.mul_le_mul_left (capAt agreementCap i) (hbudget i))))
       (Nat.mul_le_mul_left ((e+1)*(a-w)) (hbudget 2))
   _=(n-w)*
       ((1+2*w*jY)*pairYCost ⟨A,G⟩+
         w*pairRCost ⟨A,G⟩+
         (2*w*jZ+1)*pairZCost ⟨A,G⟩)+
       (e+1)*(a-w)*pairZCost ⟨A,G⟩:=by
     simp [Fin.sum_univ_three,capAt,agreementCap,
       RCN170.pairCost]
end
end ProximityPrize.SubmissionLower.RCN172
end PackedLegacy_BW

/-! Packed from ProximityPrize.SubmissionLower.CD. -/
section PackedLegacy_CD
namespace ProximityPrize.SubmissionLower.RCN306
open scoped Classical BigOperators
open RCN051 RCN068 RCN136 RCN238 RCN243 RCN065 RCN231 RCN319 RCN001
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
def unitAt:Fin 3 → DegreeVector:=![unitY,unitR,unitZ]
def degreeVector (G:MvPolynomial (Fin 3) Ω):DegreeVector:=
 ⟨G.degreeOf 0,G.degreeOf 1,G.degreeOf 2⟩
def fiberNumerator (n w a e:ℕ) (g E:DegreeVector):ℕ:=
 (n-w)*mixed g E E+(e+1)*(a-w)*mixed g E unitZ
variable [IsAlgClosed Ω]
 (φ:Polynomial K →+*Ω)
 {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
end
end ProximityPrize.SubmissionLower.RCN306
end PackedLegacy_CD

/-! Packed from ProximityPrize.SubmissionLower.DB. -/
section PackedLegacy_DB
namespace ProximityPrize.SubmissionLower
open Polynomial Polynomial.Bivariate Matrix
open scoped BigOperators
variable {F:Type} [Field F]
private theorem natDegree_det_le_of_perm_products_le
   {ι:Type} [Fintype ι] [DecidableEq ι]
   (M:Matrix ι ι F[X]) {N:ℕ}
   (h:∀ σ:Equiv.Perm ι,(∏ i:ι,M (σ i) i).natDegree ≤ N):
   M.det.natDegree ≤ N:=by
 classical
 rw [Matrix.det_apply']
 apply Polynomial.natDegree_sum_le_of_forall_le
 intro σ _
 exact (Polynomial.natDegree_C_mul_le
   ((Equiv.Perm.sign σ:ℤ):F) (∏ i:ι,M (σ i) i)).trans (h σ)
namespace CornerStaircase
def surfaceHeight (i:ℕ):ℕ:=
 if i ≤ 24 then 178-i else if i=25 then 5 else 0
def tailHeight (K j:ℕ):ℕ:=
 if j=0 then 178*K
 else if j ≤ 24*K+1 then 178*K+1-j
 else if j ≤ 25*K+1 then 3730*K+149-149*j
 else 0
def rowPrice (K r:ℕ):ℤ:=
 178-((r-1:ℕ):ℤ)-
   148*((r-(24*K+25):ℕ):ℤ)
def rowPotential (K:ℕ) (r:Fin (25+(25*K+1))):ℤ:=
 rowPrice K r
def scaledColumnPotential (K:ℕ) (b:Fin 25):ℤ:=
 178*(K:ℤ)-178+(b:ℕ)
def surfaceColumnPrice (K a:ℕ):ℤ:=
 ((a-1:ℕ):ℤ)+
   148*((a-(24*K+1):ℕ):ℤ)
def surfaceColumnPotential (K:ℕ) (a:Fin (25*K+1)):ℤ:=
 surfaceColumnPrice K a
def partialBudget (K m:ℕ):ℤ:=
 (∑ row:Fin (25+m),rowPrice K row)+
   (∑ b:Fin 25,scaledColumnPotential K b)+
   (∑ a:Fin m,surfaceColumnPrice K a)
def rowPotentialUpTo (K m:ℕ) (row:Fin (25+m)):ℤ:=
 rowPrice K row
def surfaceColumnPotentialUpTo (K m:ℕ) (a:Fin m):ℤ:=
 surfaceColumnPrice K a
private def basePotential (K:ℕ):ℤ:=
 (∑ row∈Finset.range 25,rowPrice K row)+
   ∑ b:Fin 25,scaledColumnPotential K b
private def pairPotential (K a:ℕ):ℤ:=
 rowPrice K (25+a)+surfaceColumnPrice K a
end CornerStaircase
theorem bivariate_resultant_natDegree_le_totalDegree
   (B H:F[X][Y]) (n m:ℕ):
   (Polynomial.resultant B H n m).natDegree ≤
     m*totalDegree B+n*totalDegree H-m*n:=by
 classical
 let M:Matrix (Fin (n+m)) (Fin (n+m)) F[X]:=
   Polynomial.sylvester B H n m
 rw [Polynomial.resultant]
 change M.det.natDegree ≤ _
 apply natDegree_det_le_of_perm_products_le (M:=M)
 intro σ
 by_cases hzero:∃ i:Fin (n+m),M (σ i) i=0
 · rcases hzero with ⟨i,hi⟩
   have hprod:(∏ i:Fin (n+m),M (σ i) i)=0:=
     Finset.prod_eq_zero (Finset.mem_univ i) hi
   simp [hprod]
 · have hne (i:Fin (n+m)):M (σ i) i≠0:=by
     intro hi
     exact hzero ⟨i,hi⟩
   let lidx:Fin n → ℕ:=fun j =>
     ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)
   let ridx:Fin m → ℕ:=fun j =>
     ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)
   let ldeg:Fin n → ℕ:=fun j =>
     (M (σ (Fin.castAdd m j)) (Fin.castAdd m j)).natDegree
   let rdeg:Fin m → ℕ:=fun j =>
     (M (σ (Fin.natAdd n j)) (Fin.natAdd n j)).natDegree
   have hleft_Icc (j:Fin n):
       ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+m):=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+m)
         then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.castAdd m j) (by simp [hentry,hc])
   have hright_Icc (j:Fin m):
       ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
         Set.Icc (j:ℕ) ((j:ℕ)+n):=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
             Set.Icc (j:ℕ) ((j:ℕ)+n)
         then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
         else 0:=by
       simp [M,Polynomial.sylvester]
     by_contra hc
     exact hne (Fin.natAdd n j) (by simp [hentry,hc])
   have hleft (j:Fin n):lidx j+ldeg j ≤ totalDegree H:=by
     have hentry:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
         H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.castAdd m j)) (Fin.castAdd m j)=
           if ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+m)
           then H.coeff (((σ (Fin.castAdd m j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hleft_Icc j)]
     have hcoeff:H.coeff (lidx j)≠0:=by
       have hh:=hne (Fin.castAdd m j)
       rw [hentry] at hh
       simpa only [lidx] using hh
     have hsupp:lidx j∈H.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:ldeg j=(H.coeff (lidx j)).natDegree:=by
       dsimp [ldeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le H hsupp
   have hright (j:Fin m):ridx j+rdeg j ≤ totalDegree B:=by
     have hentry:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
         B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ)):=by
       have hh:M (σ (Fin.natAdd n j)) (Fin.natAdd n j)=
           if ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)∈
               Set.Icc (j:ℕ) ((j:ℕ)+n)
           then B.coeff (((σ (Fin.natAdd n j):Fin (n+m)):ℕ)-(j:ℕ))
           else 0:=by
         simp [M,Polynomial.sylvester]
       rw [hh,if_pos (hright_Icc j)]
     have hcoeff:B.coeff (ridx j)≠0:=by
       have hh:=hne (Fin.natAdd n j)
       rw [hentry] at hh
       simpa only [ridx] using hh
     have hsupp:ridx j∈B.support:=Polynomial.mem_support_iff.mpr hcoeff
     have hdegree:rdeg j=(B.coeff (ridx j)).natDegree:=by
       dsimp [rdeg]
       rw [hentry]
     rw [hdegree]
     simpa only [Nat.add_comm] using coeff_totalDegree_le B hsupp
   have hleft_sum:
       (∑ j:Fin n,(lidx j+ldeg j)) ≤ n*totalDegree H:=by
     calc
       _ ≤ ∑ _j:Fin n,totalDegree H:=
         Finset.sum_le_sum (fun j _ => hleft j)
       _=n*totalDegree H:=by simp
   have hright_sum:
       (∑ j:Fin m,(ridx j+rdeg j)) ≤ m*totalDegree B:=by
     calc
       _ ≤ ∑ _j:Fin m,totalDegree B:=
         Finset.sum_le_sum (fun j _ => hright j)
       _=m*totalDegree B:=by simp
   have hidxsum:
       (∑ j:Fin n,lidx j)+(∑ j:Fin m,ridx j)=m*n:=by
     have hleft_row (j:Fin n):
         ((σ (Fin.castAdd m j):Fin (n+m)):ℕ)=(j:ℕ)+lidx j:=by
       dsimp [lidx]
       have hle:=(Set.mem_Icc.mp (hleft_Icc j)).1
       omega
     have hright_row (j:Fin m):
         ((σ (Fin.natAdd n j):Fin (n+m)):ℕ)=(j:ℕ)+ridx j:=by
       dsimp [ridx]
       have hle:=(Set.mem_Icc.mp (hright_Icc j)).1
       omega
     have hsum_left_rows:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin n,lidx j):=by
       calc
         _=∑ j:Fin n,((j:ℕ)+lidx j):=
           Finset.sum_congr rfl (fun j _ => hleft_row j)
         _=_:=Finset.sum_add_distrib
     have hsum_right_rows:
         (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin m,(j:ℕ))+(∑ j:Fin m,ridx j):=by
       calc
         _=∑ j:Fin m,((j:ℕ)+ridx j):=
           Finset.sum_congr rfl (fun j _ => hright_row j)
         _=_:=Finset.sum_add_distrib
     have hperm_sum:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           ∑ i:Fin (n+m),(i:ℕ):=by
       simpa using (Equiv.sum_comp σ (fun i:Fin (n+m) => (i:ℕ)))
     have hrows_split:
         (∑ i:Fin (n+m),((σ i:Fin (n+m)):ℕ))=
           (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ)):=by
       simpa using (Fin.sum_univ_add
         (fun i:Fin (n+m) => ((σ i:Fin (n+m)):ℕ)))
     have hcols_split:
         (∑ i:Fin (n+m),(i:ℕ))=
           (∑ j:Fin n,(j:ℕ))+(∑ j:Fin m,(n+(j:ℕ))):=by
       simpa using (Fin.sum_univ_add (fun i:Fin (n+m) => (i:ℕ)))
     have hright_cols:
         (∑ j:Fin m,(n+(j:ℕ)))=
           m*n+∑ j:Fin m,(j:ℕ):=by
       simp [Finset.sum_add_distrib,Finset.sum_const]
     have hmain:
         (∑ j:Fin n,((σ (Fin.castAdd m j):Fin (n+m)):ℕ))+
             (∑ j:Fin m,((σ (Fin.natAdd n j):Fin (n+m)):ℕ))=
           (∑ j:Fin n,(j:ℕ))+
             (m*n+∑ j:Fin m,(j:ℕ)):=by
       rw [←hrows_split,hperm_sum,hcols_split,hright_cols]
     omega
   have hsum:
       ((∑ j:Fin n,lidx j)+(∑ j:Fin n,ldeg j))+
           ((∑ j:Fin m,ridx j)+(∑ j:Fin m,rdeg j)) ≤
         n*totalDegree H+m*totalDegree B:=by
     simpa only [Finset.sum_add_distrib] using Nat.add_le_add hleft_sum hright_sum
   have hdeg_parts:
       (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j) ≤
         m*totalDegree B+n*totalDegree H-m*n:=by
     omega
   have hsum_deg_split:
       (∑ i:Fin (n+m),(M (σ i) i).natDegree)=
         (∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=by
     simpa only [ldeg,rdeg] using
       (Fin.sum_univ_add (fun i:Fin (n+m) => (M (σ i) i).natDegree))
   calc
     (∏ i:Fin (n+m),M (σ i) i).natDegree ≤
         ∑ i:Fin (n+m),(M (σ i) i).natDegree:=by
       simpa using Polynomial.natDegree_prod_le Finset.univ
         (fun i:Fin (n+m) => M (σ i) i)
     _=(∑ j:Fin n,ldeg j)+(∑ j:Fin m,rdeg j):=hsum_deg_split
     _ ≤ _:=hdeg_parts
end ProximityPrize.SubmissionLower
end PackedLegacy_DB

/-! Packed from ProximityPrize.SubmissionLower.AY. -/
section PackedLegacy_AY
namespace ProximityPrize.SubmissionLower.RCN012
open Polynomial Polynomial.Bivariate RCN002 RCN005 RCN371 RCN011 RCN009 RCN013
noncomputable section
variable {A:Type} [Field A]
end
end ProximityPrize.SubmissionLower.RCN012
end PackedLegacy_AY
end Compact_PackedLegacyCore1
