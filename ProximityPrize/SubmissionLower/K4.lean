import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BM
namespace ProximityPrize.SubmissionLower.RCN161
noncomputable section
open scoped Function
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000
variable {K:Type*} [Field K]
theorem nodal_dvd_of_eval_eq_zero
   {ι:Type*} (I:Finset ι) (x:ι → K)
   (hinj:Set.InjOn x I) (P:Polynomial K)
   (hzero:∀ i∈I,P.eval (x i)=0):
   Lagrange.nodal I x∣P:=by
 classical
 rw [Lagrange.nodal_eq]
 apply Finset.prod_dvd_of_coprime
 · intro i hi j hj hij
   exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
     (sub_ne_zero.mpr (fun hxy => hij (hinj hi hj hxy))).isUnit
 · intro i hi
   rw [Polynomial.dvd_iff_isRoot,Polynomial.IsRoot]
   exact hzero i hi
theorem exists_affine_nodal_residual
   {ι:Type*} (I:Finset ι) (x u0 u1:ι → K)
   (w:ℕ) (hIw:I.card ≤ w) (hinj:Set.InjOn x I)
   (gamma:K) (S:Polynomial K) (hS:S.natDegree ≤ w)
   (hvalues:∀ i∈I,S.eval (x i)=u0 i+gamma*u1 i):
   ∃ P0 P1 C:Polynomial K,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     C.natDegree ≤ w-I.card∧
     S=P0+Polynomial.C gamma*P1+Lagrange.nodal I x*C:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 let P0:Polynomial K:=Lagrange.interpolate I x u0
 let P1:Polynomial K:=Lagrange.interpolate I x u1
 have hpredw:I.card-1 ≤ w:=(Nat.sub_le I.card 1).trans hIw
 have hP0:P0.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u0 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hP1:P1.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u1 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 let D:=S-(P0+Polynomial.C gamma*P1)
 have hDdegree:D.natDegree ≤ w:=by
   apply (Polynomial.natDegree_sub_le _ _).trans
   exact max_le hS ((Polynomial.natDegree_add_le _ _).trans
     (max_le hP0 ((Polynomial.natDegree_C_mul_le gamma P1).trans hP1)))
 have hDeval:∀ i∈I,D.eval (x i)=0:=by
   intro i hi
   simp only [D,Polynomial.eval_sub,Polynomial.eval_add,
     Polynomial.eval_mul,Polynomial.eval_C]
   rw [Lagrange.eval_interpolate_at_node u0 hinj hi,
     Lagrange.eval_interpolate_at_node u1 hinj hi,hvalues i hi]
   ring
 obtain ⟨C,hC⟩:=nodal_dvd_of_eval_eq_zero I x hinj D hDeval
 have hCdegree:C.natDegree ≤ w-I.card:=by
   by_cases hC0:C=0
   · simp [hC0]
   · have hdegmul:(Lagrange.nodal I x*C).natDegree=
         I.card+C.natDegree:=by
       rw [(Lagrange.nodal_monic (s:=I) (v:=x)).natDegree_mul' hC0,
         Lagrange.natDegree_nodal]
     have hmul:(Lagrange.nodal I x*C).natDegree ≤ w:=by
       rw [←hC]
       exact hDdegree
     rw [hdegmul] at hmul
     omega
 refine ⟨P0,P1,C,hP0,hP1,hCdegree,?_⟩
 change S=P0+Polynomial.C gamma*P1+Lagrange.nodal I x*C
 change S-(P0+Polynomial.C gamma*P1)=
   Lagrange.nodal I x*C at hC
 linear_combination hC
variable {L:Type*} [Field L]
theorem map_nodal (coefficients:K →+*L)
   {ι:Type*} (I:Finset ι) (x:ι → K):
   (Lagrange.nodal I x).map coefficients=
     Lagrange.nodal I (fun i↦coefficients (x i)):=by
 classical
 simp only [Lagrange.nodal_eq,Polynomial.map_prod,Polynomial.map_sub,
   Polynomial.map_X,Polynomial.map_C]
theorem exists_basefield_affine_nodal_residual
   (coefficients:K →+*L)
   {ι:Type*} (I:Finset ι) (x u0 u1:ι → K)
   (w:ℕ) (hIw:I.card ≤ w) (hinj:Set.InjOn x I)
   (gamma:L) (S:Polynomial L) (hS:S.natDegree ≤ w)
   (hvalues:∀ i∈I,
     S.eval (coefficients (x i))=
       coefficients (u0 i)+gamma*coefficients (u1 i)):
   ∃ P0 P1:Polynomial K,∃ C:Polynomial L,
     P0.natDegree ≤ w∧P1.natDegree ≤ w∧
     C.natDegree ≤ w-I.card∧
     S=P0.map coefficients+Polynomial.C gamma*P1.map coefficients+
       (Lagrange.nodal I x).map coefficients*C:=by
 classical
 letI:DecidableEq ι:=Classical.decEq ι
 let P0:Polynomial K:=Lagrange.interpolate I x u0
 let P1:Polynomial K:=Lagrange.interpolate I x u1
 have hpredw:I.card-1 ≤ w:=(Nat.sub_le I.card 1).trans hIw
 have hP0:P0.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u0 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 have hP1:P1.natDegree ≤ w:=by
   apply Polynomial.natDegree_le_of_degree_le
   exact (Lagrange.degree_interpolate_le u1 hinj).trans
     (WithBot.coe_le_coe.mpr hpredw)
 let D:=S-(P0.map coefficients+
   Polynomial.C gamma*P1.map coefficients)
 have hDdegree:D.natDegree ≤ w:=by
   apply (Polynomial.natDegree_sub_le _ _).trans
   exact max_le hS ((Polynomial.natDegree_add_le _ _).trans
     (max_le (Polynomial.natDegree_map_le.trans hP0)
       ((Polynomial.natDegree_C_mul_le gamma _).trans
         (Polynomial.natDegree_map_le.trans hP1))))
 have hmapinj:Set.InjOn (fun i↦coefficients (x i)) I:=by
   intro i hi j hj hij
   exact hinj hi hj (coefficients.injective hij)
 have hDeval:∀ i∈I,D.eval (coefficients (x i))=0:=by
   intro i hi
   simp only [D,Polynomial.eval_sub,Polynomial.eval_add,
     Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map_apply]
   rw [Lagrange.eval_interpolate_at_node u0 hinj hi,
     Lagrange.eval_interpolate_at_node u1 hinj hi,hvalues i hi]
   ring
 obtain ⟨C,hC⟩:=nodal_dvd_of_eval_eq_zero I
   (fun i↦coefficients (x i)) hmapinj D hDeval
 have hCdegree:C.natDegree ≤ w-I.card:=by
   by_cases hC0:C=0
   · simp [hC0]
   · have hdegmul:
         (Lagrange.nodal I (fun i↦coefficients (x i))*C).natDegree=
           I.card+C.natDegree:=by
       rw [(Lagrange.nodal_monic
         (s:=I) (v:=fun i↦coefficients (x i))).natDegree_mul' hC0,
         Lagrange.natDegree_nodal]
     have hmul:
         (Lagrange.nodal I (fun i↦coefficients (x i))*C).natDegree ≤ w:=by
       rw [←hC]
       exact hDdegree
     rw [hdegmul] at hmul
     omega
 refine ⟨P0,P1,C,hP0,hP1,hCdegree,?_⟩
 rw [map_nodal]
 change S=P0.map coefficients+Polynomial.C gamma*P1.map coefficients+
   Lagrange.nodal I (fun i↦coefficients (x i))*C
 change S-(P0.map coefficients+Polynomial.C gamma*P1.map coefficients)=
   Lagrange.nodal I (fun i↦coefficients (x i))*C at hC
 linear_combination hC
end
end ProximityPrize.SubmissionLower.RCN161
