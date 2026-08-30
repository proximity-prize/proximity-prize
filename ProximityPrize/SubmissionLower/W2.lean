import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.X8
namespace ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open scoped BigOperators
noncomputable section
variable {K:Type*} [Field K] [DecidableEq K]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem pow_card_dvd_det_of_eval_columns_eq_zero
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (columns:Finset ι)
   (hzero:∀ j∈columns,∀ i,(M i j).eval alpha=0):
   (Polynomial.X-Polynomial.C alpha)^columns.card∣M.det:=by
 classical
 rw [Matrix.det_apply']
 apply Finset.dvd_sum
 intro permutation _
 have hpart:
     (∏ j∈columns,(Polynomial.X-Polynomial.C alpha))∣
       ∏ j∈columns,M (permutation j) j:=by
   apply Finset.prod_dvd_prod_of_dvd
   intro j hj
   exact Polynomial.dvd_iff_isRoot.mpr (hzero j hj (permutation j))
 have hfull:
     (∏ j∈columns,M (permutation j) j)∣
       ∏ j:ι,M (permutation j) j:=
   Finset.prod_dvd_prod_of_subset columns Finset.univ
     (fun j => M (permutation j) j) (Finset.subset_univ columns)
 have hproduct:
     (Polynomial.X-Polynomial.C alpha)^columns.card∣
       ∏ j:ι,M (permutation j) j:=by
   simpa using hpart.trans hfull
 exact dvd_mul_of_dvd_right hproduct _
theorem pow_corank_dvd_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K):
   (Polynomial.X-Polynomial.C alpha)^
       (Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank)∣
     M.det:=by
 classical
 let evalMatrix:Matrix ι ι (Polynomial K) →+*Matrix ι ι K:=
   (Polynomial.evalRingHom alpha).mapMatrix
 let constMatrix:Matrix ι ι K →+*Matrix ι ι (Polynomial K):=
   (Polynomial.C:K →+*Polynomial K).mapMatrix
 let evaluated:Matrix ι ι K:=evalMatrix M
 obtain ⟨V,U,e,hV,hU,hnormal⟩:=Matrix.exists_rank_normal_form evaluated
 let transformed:Matrix ι ι (Polynomial K):=constMatrix V*M*constMatrix U
 have heval_const (B:Matrix ι ι K):evalMatrix (constMatrix B)=B:=by
   ext i j
   simp [evalMatrix,constMatrix,RingHom.mapMatrix_apply,Matrix.map_apply]
 have heval:evalMatrix transformed=
     (Matrix.fromBlocks 1 0 0 0).submatrix e e:=by
   change evalMatrix (constMatrix V*M*constMatrix U)=_
   rw [map_mul,map_mul,heval_const,heval_const]
   exact hnormal
 let zeroEmbedding:Fin (Fintype.card ι-evaluated.rank) ↪ ι:={
   toFun:=fun j => e.symm (Sum.inr j)
   inj':=by
     intro i j hij
     exact Sum.inr.inj (e.symm.injective hij)
 }
 let zeroColumns:Finset ι:=Finset.univ.map zeroEmbedding
 have hcard:zeroColumns.card=Fintype.card ι-evaluated.rank:=by
   simp [zeroColumns]
 have hzero:∀ j∈zeroColumns,∀ i,(transformed i j).eval alpha=0:=by
   intro j hj i
   obtain ⟨j0,_,rfl⟩:=Finset.mem_map.mp hj
   change evalMatrix transformed i (e.symm (Sum.inr j0))=0
   rw [heval]
   simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
   cases e i <;> rfl
 have hVdet:IsUnit (constMatrix V).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hV.map constMatrix)
 have hUdet:IsUnit (constMatrix U).det:=
   (Matrix.isUnit_iff_isUnit_det _).mp (hU.map constMatrix)
 have hdiv:=pow_card_dvd_det_of_eval_columns_eq_zero
   transformed alpha zeroColumns hzero
 rw [hcard] at hdiv
 change (Polynomial.X-Polynomial.C alpha)^
     (Fintype.card ι-evaluated.rank)∣
       (constMatrix V*M*constMatrix U).det at hdiv
 rw [Matrix.det_mul,Matrix.det_mul] at hdiv
 exact hVdet.dvd_mul_left.mp (hUdet.dvd_mul_right.mp hdiv)
theorem corank_le_rootMultiplicity_det
   (M:Matrix ι ι (Polynomial K)) (alpha:K) (hdet:M.det≠0):
   Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank ≤
     M.det.rootMultiplicity alpha:=by
 exact (Polynomial.le_rootMultiplicity_iff hdet).mpr
   (pow_corank_dvd_det M alpha)
theorem sum_rootMultiplicity_le_natDegree
   (P:Polynomial K) (points:Finset K):
   (∑ alpha∈points,P.rootMultiplicity alpha) ≤ P.natDegree:=by
 classical
 have hselected:
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤ P.roots.card:=by
   let all:=points ∪ P.roots.toFinset
   calc
     (∑ alpha∈points,Multiset.count alpha P.roots) ≤
         ∑ alpha∈all,Multiset.count alpha P.roots:=
       Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
     _=∑ alpha∈P.roots.toFinset,Multiset.count alpha P.roots:=by
       symm
       apply Finset.sum_subset (Finset.subset_union_right)
       intro alpha _ hnot
       exact Multiset.count_eq_zero.mpr (by simpa using hnot)
     _=P.roots.card:=Multiset.toFinset_sum_count_eq P.roots
 calc
   (∑ alpha∈points,P.rootMultiplicity alpha)=
       ∑ alpha∈points,Multiset.count alpha P.roots:=by
     apply Finset.sum_congr rfl
     intro alpha _
     exact (Polynomial.count_roots P).symm
   _ ≤ P.roots.card:=hselected
   _ ≤ P.natDegree:=Polynomial.card_roots' P
theorem sum_coranks_le_natDegree_det
   (M:Matrix ι ι (Polynomial K)) (points:Finset K) (hdet:M.det≠0):
   (∑ alpha∈points,
     (Fintype.card ι-((Polynomial.evalRingHom alpha).mapMatrix M).rank)) ≤
     M.det.natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,M.det.rootMultiplicity alpha:=
     Finset.sum_le_sum fun alpha _ => corank_le_rootMultiplicity_det M alpha hdet
   _ ≤ M.det.natDegree:=sum_rootMultiplicity_le_natDegree M.det points
theorem sylvester_corank_le_rootMultiplicity_resultant
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank ≤
     (Polynomial.resultant P Q m n).rootMultiplicity alpha:=by
 simpa only [Fintype.card_fin,Polynomial.resultant,
   ←Polynomial.sylvester_map_map] using
   corank_le_rootMultiplicity_det (Polynomial.sylvester P Q m n) alpha hresultant
theorem sum_sylvester_coranks_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset K)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ alpha∈points,(m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(Polynomial.resultant P Q m n).rootMultiplicity alpha:=
     Finset.sum_le_sum fun alpha _ =>
       sylvester_corank_le_rootMultiplicity_resultant P Q m n alpha hresultant
   _ ≤ (Polynomial.resultant P Q m n).natDegree:=
     sum_rootMultiplicity_le_natDegree (Polynomial.resultant P Q m n) points
theorem sum_sylvester_coranks_le_bidegree_bound
   {F:Type} [Field F] [DecidableEq F]
   (P Q:Polynomial (Polynomial F)) (m n:ℕ) (points:Finset F)
   (hresultant:Polynomial.resultant P Q m n≠0):
   (∑ alpha∈points,(m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 have hdegree:=bivariate_resultant_natDegree_le (F:=F) P Q m n
 exact Nat.le_trans
   (sum_sylvester_coranks_le_resultant_natDegree P Q m n points hresultant) hdegree
end
end ProximityPrize.SubmissionLower.MatrixRootMultiplicity
