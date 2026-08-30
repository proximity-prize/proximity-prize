import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BS
namespace ProximityPrize.SubmissionLower.RCN079
open RCN136 RCN082 RCN290
open RCN293 RCN081 RCN319
noncomputable section
variable {K:Type*} [Field K]
def swapYR (K:Type*) [Field K]:MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K:=
 MvPolynomial.renameEquiv K (Equiv.swap (1:Fin 4) 2)
@[simp] theorem swapYR_twice (F:MvPolynomial (Fin 4) K):swapYR K (swapYR K F)=F:=by
 simp [swapYR,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_rename,Function.comp_def]
 exact MvPolynomial.rename_id_apply F
theorem swapYR_ne_zero (F:MvPolynomial (Fin 4) K) (hF:F≠0):swapYR K F≠0:=by
 intro h
 apply hF
 apply (swapYR K).injective
 simpa only [map_zero] using h
theorem swapYR_degree_Y (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 1=F.degreeOf 2:=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (2:Fin 4))
theorem swapYR_degree_R (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 2=F.degreeOf 1:=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (1:Fin 4))
theorem swapYR_degree_Z (F:MvPolynomial (Fin 4) K):
   (swapYR K F).degreeOf 3=F.degreeOf 3:=by
 have hfix:Equiv.swap (1:Fin 4) 2 (3:Fin 4)=3:=by decide
 simpa only [swapYR,MvPolynomial.renameEquiv_apply,hfix] using
   (MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (1:Fin 4) 2).injective
     (p:=F) (3:Fin 4))
theorem swapYR_pderiv_Y (F:MvPolynomial (Fin 4) K):
   MvPolynomial.pderiv (1:Fin 4) (swapYR K F)=
     swapYR K (MvPolynomial.pderiv (2:Fin 4) F):=by
 simpa [swapYR,MvPolynomial.renameEquiv_apply] using
   (MvPolynomial.pderiv_rename (Equiv.swap (1:Fin 4) 2).injective (2:Fin 4) F)
theorem coordinate_weight_degree (F:MvPolynomial (Fin 4) K) (i:Fin 4):
   MvPolynomial.weightedTotalDegree (Pi.single i 1) F=F.degreeOf i:=by
 rw [MvPolynomial.weightedTotalDegree,MvPolynomial.degreeOf_eq_sup]
 apply congrArg (fun f:(Fin 4 →₀ ℕ) → ℕ => F.support.sup f)
 funext d
 exact Finsupp.weight_single_one_apply i d
def exceptionalAuxiliary (J:MvPolynomial (Fin 4) K):MvPolynomial (Fin 4) K:=
 swapYR K (singularAuxiliary (swapYR K J))
theorem exceptionalAuxiliary_nonzero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (j p:ℕ) [CharP K p]
   (hY:J.degreeOf 1 ≤ j) (hsmall:j < p):exceptionalAuxiliary J≠0:=by
 apply swapYR_ne_zero
 apply singularAuxiliary_nonzero (swapYR K J) (swapYR_ne_zero J hJ) p
 rw [swapYR_degree_R]
 exact hY.trans_lt hsmall
theorem exceptionalAuxiliary_Y_degree_zero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (j p:ℕ) [CharP K p]
   (hY:J.degreeOf 1 ≤ j) (hsmall:j < p):(exceptionalAuxiliary J).degreeOf 1=0:=by
 rw [exceptionalAuxiliary,swapYR_degree_Y]
 apply singularAuxiliary_R_degree (swapYR K J) (swapYR_ne_zero J hJ) p
 rw [swapYR_degree_R]
 exact hY.trans_lt hsmall
theorem exceptionalAuxiliary_R_degree_zero
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j:ℕ) (hj:1 ≤ j) (hY:J.degreeOf 1 ≤ j):(exceptionalAuxiliary J).degreeOf 2=0:=by
 have hRswap:(swapYR K J).degreeOf 2 ≤ j:=by rw [swapYR_degree_R];exact hY
 have hb:=singularAuxiliary_weight_le (Pi.single (1:Fin 4) 1)
   (swapYR K J) (swapYR_ne_zero J hJ) j hj hRswap
 rw [coordinate_weight_degree,coordinate_weight_degree,swapYR_degree_Y,hR,mul_zero] at hb
 rw [exceptionalAuxiliary,swapYR_degree_R]
 exact Nat.eq_zero_of_le_zero hb
theorem exceptionalAuxiliary_Z_degree_le
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0)
   (j:ℕ) (hj:1 ≤ j) (hY:J.degreeOf 1 ≤ j):
   (exceptionalAuxiliary J).degreeOf 3 ≤ (2*j-1)*J.degreeOf 3:=by
 have hRswap:(swapYR K J).degreeOf 2 ≤ j:=by rw [swapYR_degree_R];exact hY
 have hb:=singularAuxiliary_weight_le (Pi.single (3:Fin 4) 1)
   (swapYR K J) (swapYR_ne_zero J hJ) j hj hRswap
 rw [coordinate_weight_degree,coordinate_weight_degree,swapYR_degree_Z] at hb
 rw [exceptionalAuxiliary,swapYR_degree_Z]
 exact hb
theorem exceptionalAuxiliary_data
   (J:MvPolynomial (Fin 4) K) (hJ:J≠0) (hR:J.degreeOf 2=0)
   (j p:ℕ) [CharP K p] (hj:1 ≤ j) (hsmall:j < p)
   (hY:J.degreeOf 1 ≤ j) (hZ:J.degreeOf 3 ≤ j):
   exceptionalAuxiliary J≠0∧(exceptionalAuxiliary J).degreeOf 1=0∧
     (exceptionalAuxiliary J).degreeOf 2=0∧
     (exceptionalAuxiliary J).degreeOf 3 ≤ (2*j-1)*j∧
     (exceptionalAuxiliary J).degreeOf 3 ≤ 2*j^2:=by
 have hz:=(exceptionalAuxiliary_Z_degree_le J hJ j hj hY).trans (Nat.mul_le_mul_left _ hZ)
 refine ⟨exceptionalAuxiliary_nonzero J hJ j p hY hsmall,
   exceptionalAuxiliary_Y_degree_zero J hJ j p hY hsmall,
   exceptionalAuxiliary_R_degree_zero J hJ hR j hj hY,hz,?_⟩
 calc
   _ ≤ (2*j-1)*j:=hz
   _ ≤ (2*j)*j:=Nat.mul_le_mul_right j (Nat.sub_le _ _)
   _=2*j^2:=by ring
def originalImplicitFactors (J:MvPolynomial (Fin 4) K):Finset (MvPolynomial (Fin 4) K):=by
 classical
 exact (activeFactors (swapYR K J)).image (swapYR K)
theorem swapYR_dvd_swapYR_iff (F J:MvPolynomial (Fin 4) K):
   swapYR K F∣swapYR K J ↔ F∣J:=by
 constructor
 · rintro ⟨T,hT⟩
   refine ⟨swapYR K T,?_⟩
   have hh:=congrArg (swapYR K) hT
   simpa only [map_mul,swapYR_twice] using hh
 · rintro ⟨T,hT⟩
   exact ⟨swapYR K T,by rw [hT,map_mul]⟩
theorem originalImplicitFactors_spec (J A:MvPolynomial (Fin 4) K)
   (hA:A∈originalImplicitFactors J):Irreducible A∧A∣J:=by
 classical
 obtain ⟨F,hF,rfl⟩:=Finset.mem_image.mp hA
 have hf:=activeFactors_spec (swapYR K J) F hF
 refine ⟨(MulEquiv.irreducible_iff (swapYR K)).mpr hf.1,?_⟩
 have hh:=(swapYR_dvd_swapYR_iff F (swapYR K J)).mpr hf.2.1
 simpa only [swapYR_twice] using hh
theorem originalImplicitFactors_product_dvd (J:MvPolynomial (Fin 4) K) (hJ:J≠0):
   (∏ A∈originalImplicitFactors J,A)∣J:=by
 classical
 have hi:Set.InjOn (swapYR K) (activeFactors (swapYR K J)):=(swapYR K).injective.injOn
 have heq:(∏ A∈originalImplicitFactors J,A)=
     swapYR K (∏ F∈activeFactors (swapYR K J),F):=by
   rw [originalImplicitFactors,Finset.prod_image hi,map_prod]
 rw [heq]
 have hh:=(swapYR_dvd_swapYR_iff (∏ F∈activeFactors (swapYR K J),F) (swapYR K J)).mpr
   (activeFactors_product_dvd (swapYR K J) (swapYR_ne_zero J hJ))
 simpa only [swapYR_twice] using hh
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
