import ProximityPrize.SubmissionLower.Zz5zkKe
set_option Elab.async false
set_option autoImplicit true
namespace P5_7_7
noncomputable section
open Polynomial Finset
open P5 (K)
open P5_7 (NativeSeedBound OneSeedEquation)
open cu (FX jz)
private theorem c8H {f g:OneSeedEquation} {u v :ℕ}
    (hf :NativeSeedBound f u) (hg:NativeSeedBound g v) :
    (f.resultant g).natDegree≤f.natDegree*v+g.natDegree*u:= by
  classical
  let m:=f.natDegree
  let n:=g.natDegree
  let A:=sylvester f g m n
  let cap:Fin (m+n)→ℕ:= fun i=>i.addCases (fun _=>v) (fun _=>u)
  have hentry (i j:Fin (m+n)) : (A i j).natDegree≤ cap j:= by
    refine Fin.addCases ?_ ?_ j
    · intro a
      simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_left]
      split
      · exact hg _
      · simp
    · intro a
      simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_right]
      split
      · exact hf _
      · simp
  change A.det.natDegree≤ m*v+n*u
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro π _
  have hp: (∏ i,A (π i) i).natDegree≤ m*v+n*u :=
    (natDegree_prod_le _ _).trans (calc
      _ ≤ ∑ i,cap i:=sum_le_sum fun i _=>hentry (π i) i
      _ = _:= by rw [Fin.sum_univ_add]; simp [cap])
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;> simpa [hh] using hp
theorem ePy {f g:OneSeedEquation} {u v :ℕ} {T:Finset K} {z :K→K} {y :K→FX}
    (hf :NativeSeedBound f u) (hg:NativeSeedBound g v) (hdeg:0<f.natDegree)
    (hcop:IsCoprime (ek f) (ek g)) (hz :Set.InjOn z (T:Set K))
    (hfr : ∀ γ∈T,nativeEval (z γ) (y γ) f=0)
    (hgr : ∀ γ∈T,nativeEval (z γ) (y γ) g=0) :
    T.card≤f.natDegree*v+g.natDegree*u:= by
  have hi:=IsFractionRing.injective FX[X] (FractionRing FX[X])
  unfold ek at hcop
  have hne :=resultant_ne_zero _ _ hcop
  rw [natDegree_map_eq_of_injective hi,natDegree_map_eq_of_injective hi,
    resultant_map_map] at hne
  have hr :f.resultant g≠0:= fun h=>hne (by rw [h,map_zero])
  refine (countRoots T (jz ∘ z) (seedEmbedding_injective.comp_injOn hz)
      _ hr ?_).trans (c8H hf hg)
  intro γ hγ
  obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant f g
    (le_refl _) (le_refl _) (Or.inl hdeg.ne')
  have he :=congrArg (nativeEval (z γ) (y γ)) hab
  rw [map_add,map_mul,map_mul,hfr γ hγ,hgr γ hγ,zero_mul,zero_mul,zero_add] at he
  simpa only [nativeEval,coe_eval₂RingHom,eval₂_C,coe_evalRingHom,Function.comp_apply] using he.symm
end
end P5_7_7
