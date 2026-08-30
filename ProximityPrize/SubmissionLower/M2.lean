import ProximityPrize.SubmissionLower.CQ
import ProximityPrize.SubmissionLower.D7
namespace ProximityPrize.SubmissionLower.RCN196
open scoped Classical BigOperators
open Module
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {R M ι:Type*}
variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
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
