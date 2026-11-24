import ProximityPrize.SubmissionLower.R6961MarkedPrimitiveMinor

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Module Matrix LinearMap Finset
open scoped Polynomial Matrix BigOperators
open P1_7_1_1_2 (exists_full_minor)
variable {k K I J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Fintype I] [Fintype J] [DecidableEq J]

/-- Distinct abscissas can all be translates of one transcendental variable.
There is already a nonzero coordinate minor of the desired size after evaluating
that variable at zero. The shifts lie in the original ground field k. -/
theorem translated_minor (P:Matrix I J (Polynomial K)) (li:LinearIndependent K P.col) :
    ∃ N:ℕ, ∃ shifts:Fin N ↪ k, ∃ rows:J↪(Fin N×I),
      (Matrix.of (fun u v:J=>Polynomial.taylor (algebraMap k K (shifts (rows u).1)) (P (rows u).2 v))).det≠0 := by
  classical
  let m:=Finset.univ.sup (fun ij:I×J=>(P ij.1 ij.2).natDegree)
  let pts:Fin (m+1)↪k := Fin.valEmbedding.trans (Infinite.natEmbedding k)
  let val:Fin (m+1)↪K := pts.trans ⟨_,(algebraMap k K).injective⟩
  let V:=degreeLT K (m+1)
  let C (j:J) (i:I):V:=⟨P i j,mem_degreeLT.mpr (degree_le_natDegree.trans_lt
    (by exact_mod_cast Nat.lt_succ_of_le (show (P i j).natDegree≤m from Finset.le_sup (f:=fun ij:I×J=>(P ij.1 ij.2).natDegree) (Finset.mem_univ (i,j)))))⟩
  let proj:(I→V) →ₗ[K] (I→(Polynomial K)) := LinearMap.pi (fun i=>V.subtype.comp (LinearMap.proj i))
  have ic:LinearIndependent K C := LinearIndependent.of_comp proj li
  let eval:(I→V) →ₗ[K] ((Fin (m+1)×I)→K) := LinearMap.pi (fun i=>
    (Polynomial.leval (val i.1)).comp (V.subtype.comp (LinearMap.proj i.2)))
  have inj:Function.Injective eval := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u zero
    funext i;apply Subtype.ext
    by_contra nz
    let S:=Finset.univ.map val
    have roots : S⊆(u i).val.roots.toFinset := by
      intro x hx
      obtain ⟨a,_,rfl⟩:=Finset.mem_map.mp hx
      exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (congrFun zero (a,i)))
    have high:= (Finset.card_le_card roots).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
    have d:=(natDegree_lt_iff_degree_lt nz).mpr (mem_degreeLT.mp (u i).property)
    have card : S.card=m+1 := by simp [S]
    omega
  let test : Matrix (Fin (m+1)×I) J K := fun i j=>(P i.2 j).eval (val i.1)
  have independent : LinearIndependent K test.transpose.row := ic.map' eval (LinearMap.ker_eq_bot.mpr inj)
  obtain ⟨rows,good⟩:=P1_7_1_1_2.exists_full_minor test.transpose independent
  refine ⟨m+1,pts,rows,?_⟩
  intro vanish
  let M := Matrix.of (fun u v:J=>Polynomial.taylor (algebraMap k K (pts (rows u).1)) (P (rows u).2 v))
  have eq:(evalRingHom (0:K)).mapMatrix M=(test.transpose.submatrix _root_.id rows).transpose := by
    ext i j
    change (Polynomial.taylor _ _).eval 0=_
    rw [taylor_eval,zero_add];rfl
  apply good
  rw [←Matrix.det_transpose,←eq,←RingHom.map_det]
  exact (congrArg (evalRingHom (0:K)) vanish).trans (map_zero _)

#print axioms translated_minor
end Lower6961.MarkedEvaluation
