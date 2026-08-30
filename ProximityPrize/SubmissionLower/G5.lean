import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.W2
namespace ProximityPrize.SubmissionLower.PlaneResultantPointCount
open scoped BigOperators
noncomputable section
variable {K:Type} [Field K] [DecidableEq K]
def evaluationOn (N:ℕ) (roots:Finset K):
   Polynomial.degreeLT K N →ₗ[K] (roots → K) where
 toFun P x:=(P:Polynomial K).eval (x:K)
 map_add' _ _:=funext fun _ => Polynomial.eval_add
 map_smul' _ _:=funext <| by simp
theorem evaluationOn_surjective (N:ℕ) (roots:Finset K)
   (hcard:roots.card ≤ N):Function.Surjective (evaluationOn N roots):=by
 let E:=Lagrange.funEquivDegreeLT (s:=roots) (v:=fun x:K => x)
   (Set.injOn_id (roots:Set K))
 intro values
 let small:=E.symm values
 have hsmall:(small:Polynomial K).degree < (roots.card:WithBot ℕ):=
   Polynomial.mem_degreeLT.mp small.property
 have hlarge:(small:Polynomial K).degree < (N:WithBot ℕ):=
   hsmall.trans_le (by exact_mod_cast hcard)
 refine ⟨⟨(small:Polynomial K),Polynomial.mem_degreeLT.mpr hlarge⟩,?_⟩
 change E small=values
 exact E.apply_symm_apply values
theorem finrank_degreeLT (N:ℕ):
   Module.finrank K (Polynomial.degreeLT K N)=N:=by
 simpa using Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K N)
theorem sylvester_rank_eq_finrank_range
   (p q:Polynomial K) (m n:ℕ)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n):
   (Polynomial.sylvester p q m n).rank=
     Module.finrank K (LinearMap.range (Polynomial.sylvesterMap p q hp hq)):=by
 have hmatrix:LinearMap.toMatrix
     (Polynomial.degreeLT.basisProd K m n)
     (Polynomial.degreeLT.basis K (m+n))
     (Polynomial.sylvesterMap p q hp hq)=Polynomial.sylvester p q m n:=
   Polynomial.toMatrix_sylvesterMap' p q hp hq
 rw [Matrix.rank_eq_finrank_range_toLin _
   (Polynomial.degreeLT.basis K (m+n)) (Polynomial.degreeLT.basisProd K m n)]
 rw [←hmatrix,Matrix.toLin_toMatrix]
theorem common_roots_card_le_cap
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n:=by
 rcases hnonzero with hp0 | hq0
 · have hcard:roots.card ≤ p.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hp0).mpr (hroots x hx).1
   omega
 · have hcard:roots.card ≤ q.natDegree:=by
     apply Polynomial.card_le_degree_of_subset_roots
     intro x hx
     exact (Polynomial.mem_roots hq0).mpr (hroots x hx).2
   omega
theorem common_roots_card_le_sylvester_corank
   (p q:Polynomial K) (m n:ℕ) (roots:Finset K)
   (hp:p.natDegree ≤ m) (hq:q.natDegree ≤ n)
   (hnonzero:p≠0∨q≠0)
   (hroots:∀ x∈roots,p.eval x=0∧q.eval x=0):
   roots.card ≤ m+n-(Polynomial.sylvester p q m n).rank:=by
 let E:=evaluationOn (m+n) roots
 let L:=Polynomial.sylvesterMap p q hp hq
 have hsurj:Function.Surjective E:=
   evaluationOn_surjective (m+n) roots
     (common_roots_card_le_cap p q m n roots hp hq hnonzero hroots)
 have hcontain:LinearMap.range L ≤ LinearMap.ker E:=by
   rintro P ⟨input,rfl⟩
   rw [LinearMap.mem_ker]
   ext x
   change (p*(input.2:Polynomial K)+q*(input.1:Polynomial K)).eval
     (x:K)=0
   simp only [Polynomial.eval_add,Polynomial.eval_mul,
     (hroots x x.property).1,(hroots x x.property).2,zero_mul,zero_add]
 have hevalrank:Module.finrank K (LinearMap.range E)=roots.card:=by
   rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,
     Module.finrank_fintype_fun_eq_card,Fintype.card_coe]
 have hnull:=LinearMap.finrank_range_add_finrank_ker E
 rw [hevalrank,finrank_degreeLT] at hnull
 have hmono:=Submodule.finrank_mono hcontain
 have hmatrix:=sylvester_rank_eq_finrank_range p q m n hp hq
 change (Polynomial.sylvester p q m n).rank=
   Module.finrank K (LinearMap.range L) at hmatrix
 omega
theorem common_fiber_card_le_sylvester_corank
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (alpha:K) (roots:Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hnonzero:P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ beta∈roots,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   roots.card ≤ m+n-(Polynomial.sylvester
     (P.map (Polynomial.evalRingHom alpha))
     (Q.map (Polynomial.evalRingHom alpha)) m n).rank:=by
 apply common_roots_card_le_sylvester_corank
 · exact Polynomial.natDegree_map_le.trans hP
 · exact Polynomial.natDegree_map_le.trans hQ
 · exact hnonzero
 · exact hroots
theorem sum_common_fiber_cards_le_resultant_natDegree
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     (Polynomial.resultant P Q m n).natDegree:=by
 calc
   _ ≤ ∑ alpha∈points,(m+n-(Polynomial.sylvester
       (P.map (Polynomial.evalRingHom alpha))
       (Q.map (Polynomial.evalRingHom alpha)) m n).rank):=by
     apply Finset.sum_le_sum
     intro alpha halpha
     exact common_fiber_card_le_sylvester_corank P Q m n alpha (fibers alpha)
       hP hQ (hnonzero alpha halpha) (hroots alpha halpha)
   _ ≤ _:=MatrixRootMultiplicity.sum_sylvester_coranks_le_resultant_natDegree
     P Q m n points hresultant
theorem sum_common_fiber_cards_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ)
   (points:Finset K) (fibers:K → Finset K)
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ alpha∈points,
     P.map (Polynomial.evalRingHom alpha)≠0∨
     Q.map (Polynomial.evalRingHom alpha)≠0)
   (hroots:∀ alpha∈points,∀ beta∈fibers alpha,
     (P.map (Polynomial.evalRingHom alpha)).eval beta=0∧
     (Q.map (Polynomial.evalRingHom alpha)).eval beta=0):
   (∑ alpha∈points,(fibers alpha).card) ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 exact Nat.le_trans
   (sum_common_fiber_cards_le_resultant_natDegree P Q m n points fibers
     hP hQ hresultant hnonzero hroots)
   (bivariate_resultant_natDegree_le (F:=K) P Q m n)
def pointFiber (points:Finset (K × K)) (alpha:K):Finset K:=
 (points.filter (fun point => point.1=alpha)).image Prod.snd
theorem card_eq_sum_pointFiber (points:Finset (K × K)):
   points.card=∑ alpha∈points.image Prod.fst,(pointFiber points alpha).card:=by
 rw [Finset.card_eq_sum_card_image Prod.fst points]
 apply Finset.sum_congr rfl
 intro alpha _
 change (points.filter (fun point => point.1=alpha)).card=
   ((points.filter (fun point => point.1=alpha)).image Prod.snd).card
 symm
 apply Finset.card_image_of_injOn
 intro u hu v hv huv
 apply Prod.ext
 · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
 · exact huv
theorem common_points_card_le_bidegree_bound
   (P Q:Polynomial (Polynomial K)) (m n:ℕ) (points:Finset (K × K))
   (hP:P.natDegree ≤ m) (hQ:Q.natDegree ≤ n)
   (hresultant:Polynomial.resultant P Q m n≠0)
   (hnonzero:∀ point∈points,
     P.map (Polynomial.evalRingHom point.1)≠0∨
     Q.map (Polynomial.evalRingHom point.1)≠0)
   (hroots:∀ point∈points,
     (P.map (Polynomial.evalRingHom point.1)).eval point.2=0∧
     (Q.map (Polynomial.evalRingHom point.1)).eval point.2=0):
   points.card ≤
     n*Polynomial.Bivariate.degreeX P+m*Polynomial.Bivariate.degreeX Q:=by
 rw [card_eq_sum_pointFiber points]
 apply sum_common_fiber_cards_le_bidegree_bound P Q m n
   (points.image Prod.fst) (pointFiber points) hP hQ hresultant
 · intro alpha halpha
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp halpha
   exact hnonzero point hpoint
 · intro alpha _ beta hbeta
   obtain ⟨point,hpoint,rfl⟩:=Finset.mem_image.mp hbeta
   obtain ⟨hpoint,hfirst⟩:=Finset.mem_filter.mp hpoint
   simpa only [hfirst] using hroots point hpoint
end
end ProximityPrize.SubmissionLower.PlaneResultantPointCount
