import Mathlib.Algebra.Polynomial.Homogenize
import ProximityPrize.SubmissionLower.Zz5zkKe
set_option Elab.async false
open _root_ renaming Fin.prod_univ_two→ oj,Finsupp.prod_fintype→nq,Irreducible→c9,MvPolynomial.C→cy,MvPolynomial.X→aU,MvPolynomial.aeval→nI,MvPolynomial.algHom_ext→n5,MvPolynomial.totalDegree_X→nX,MvPolynomial.totalDegree_mul_of_isDomain→ oq,Polynomial.aeval_homogenize_X_one→lz,Polynomial.isHomogeneous_homogenize→lV,Polynomial.natDegree_eq_zero_of_isUnit→mD,left_ne_zero_of_mul→lI,right_ne_zero_of_mul→lJ
set_option autoImplicit true
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace qwGrtCa
noncomputable section
open Polynomial Finset
section Binary
variable {R:Type*} [CommRing R]
local notation "B" => MvPolynomial (Fin 2) R
private def subst (a b c d:R) :B →ₐ[R] B :=
 nI ![cy a*aU 0+MvPolynomial.C b*aU 1,
  cy c*aU 0+MvPolynomial.C d*aU 1]
private def ew:B →ₐ[R] R[X] :=nI ![Polynomial.X (R:=R),1]
def form (a b:R) :R[X] :=C b+C a*Polynomial.X (R:=R)
def transform (a b c d:R) (n:ℕ) (f :R[X]) :R[X] :=
 ew (subst a b c d (f.homogenize n))
private theorem eval_binary {A:Type*} [CommSemiring A] (g:R →+* A) (x y :A)
  (n:ℕ) (f :R[X]) :
  MvPolynomial.eval₂Hom g ![x,y] (f.homogenize n) =
    ∑ i∈range (n+1),g (f.coeff i)*x^i*y^(n-i) := by
 simp only [homogenize,map_sum,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
 apply sum_congr rfl
 intro i hi
 simp [MvPolynomial.eval₂Hom_monomial,nq,oj,mul_assoc]
theorem transform_sum (a b c d:R) (n:ℕ) (f :R[X]) :
   transform a b c d n f = ∑ i∈range (n+1),C (f.coeff i) *
     form a b^i*form c d^(n-i) := by
 unfold transform subst
 rw [MvPolynomial.comp_aeval_apply]
 have h: (fun i:Fin 2=>ew (![cy a*aU 0 +
     cy b*aU 1,cy c*aU 0 +
     cy d*aU 1] i)) = ![form a b,form c d] := by
   funext i
   fin_cases i <;> simp [ew,form,add_comm]
 rw [h]
 exact eval_binary C _ _ _ _
private theorem subst_comp (a b c d e f g h:R) :
  (subst a b c d).comp (subst e f g h) =
    subst (e*a+f*c) (e*b+f*d) (g*a+h*c) (g*b+h*d) := by
 apply n5
 intro i
 fin_cases i <;> simp [subst,map_add,map_mul] <;> ring
private theorem subst_id :subst (1 :R) 0 0 1=AlgHom.id R B:= by
 apply n5
 intro i
 fin_cases i <;> simp [subst]
private def changeEquiv (a b c d u:R) (hu:u*(a*d-b*c)=1) :B ≃ₐ[R] B :=
  AlgEquiv.ofAlgHom (subst a b c d) (subst (u*d) (-(u*b)) (-(u*c)) (u*a))
    (by
      rw [subst_comp,show u*d*a+(-(u*b))*c=1 by linear_combination hu,
        show u*d*b+(-(u*b))*d=0 by ring,show (-(u*c))*a+u*a*c=0 by ring,
        show (-(u*c))*b+u*a*d = 1 by linear_combination hu,subst_id])
    (by
      rw [subst_comp,show a*(u*d)+b*(-(u*c))=1 by linear_combination hu,
        show a*(-(u*b))+b*(u*a)=0 by ring,show c*(u*d)+d*(-(u*c))=0 by ring,
        show c*(-(u*b))+d*(u*a)=1 by linear_combination hu,subst_id])
private theorem subst_homogeneous {q:B} {n:ℕ} (hq:q.IsHomogeneous n) (a b c d:R) :
  (subst a b c d q).IsHomogeneous n:= by
 have h (v :R) (i:Fin 2) : (cy v*aU i).IsHomogeneous 1 :=
  MvPolynomial.isHomogeneous_C_mul_X v i
 simpa only [subst,one_mul] using hq.aeval _ (n:=1) (by
  intro i
  fin_cases i
  · exact (h a 0).add (h b 1)
  · exact (h c 0).add (h d 1))
private theorem rehom (a b c d:R) (n:ℕ) (f :R[X]) :
  (transform a b c d n f).homogenize n=subst a b c d (f.homogenize n) :=
 homogenize_eq_of_isHomogeneous (subst_homogeneous (lV f) a b c d) rfl
theorem transform_inverse (a b c d u:R) (hu:u*(a*d-b*c)=1) {n:ℕ} {f :R[X]}
  (hf :f.natDegree≤n) :
  transform (u*d) (-(u*b)) (-(u*c)) (u*a) n (transform a b c d n f)=f := by
 change ew (subst (u*d) (-(u*b)) (-(u*c)) (u*a) ((transform a b c d n f).homogenize n))=f
 rw [rehom]
 have he :=(changeEquiv a b c d u hu).symm_apply_apply (f.homogenize n)
 change subst (u*d) (-(u*b)) (-(u*c)) (u*a) (subst a b c d (f.homogenize n))= _ at he
 rw [he]
 exact lz f hf
private theorem dehom_degree (q:B) : (ew q).natDegree≤q.totalDegree := by
 conv_lhs=>rw [q.as_sum]
 rw [map_sum]
 refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
 have h:=MvPolynomial.le_totalDegree (p:=q) hm
 rw [Finsupp.sum_fintype _ _ (by simp),Fin.sum_univ_two] at h
 exact (show (ew (MvPolynomial.monomial m (q.coeff m))).natDegree≤ m 0 by
   simpa [ew,MvPolynomial.aeval_monomial,nq,oj,
     ← C_eq_algebraMap] using natDegree_C_mul_X_pow_le (q.coeff m) (m 0)).trans (by omega)
variable [IsDomain R]
private theorem homog_irred {f :R[X]} (hf :c9 f) :
   c9 (f.homogenize f.natDegree) := by
 let q:=f.homogenize f.natDegree
 have hde :ew q=f :=lz f le_rfl
 have hq:q≠0:= fun h=>hf.ne_zero (by rw [← hde,h,map_zero])
 have hdeg:q.totalDegree=f.natDegree :=(lV f).totalDegree hq
 have unit_of_deg (p:B) (hu:IsUnit (ew p)) (hd:p.totalDegree=0) :IsUnit p:= by
   have hr :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd
   have hv :IsUnit (C (p.coeff 0)) := by
     simpa [ew] using (show IsUnit (ew (cy (p.coeff 0))) from hr ▸ hu)
   exact hr.symm ▸ (isUnit_C.mp hv).map cy
 refine ⟨fun hu=>hf.not_isUnit (hde ▸ hu.map ew),?_⟩
 intro p r he
 change q=p*r at he
 have hpr :p*r≠0:=he ▸ hq
 have hm:f=ew p*ew r := by rw [← hde,he,map_mul]
 have hdepr :ew p*ew r≠0:=hm ▸ hf.ne_zero
 have hsum:=oq
   (lI hpr) (lJ hpr)
 have hsum' := natDegree_mul (lI hdepr) (lJ hdepr)
 rw [← he,hdeg] at hsum
 rw [← hm] at hsum'
 have hp:=dehom_degree p
 have hr :=dehom_degree r
 rcases hf.isUnit_or_isUnit hm with hu | hu
 · exact Or.inl (unit_of_deg p hu (by have :=mD hu; omega))
 · exact Or.inr (unit_of_deg r hu (by have :=mD hu; omega))
theorem transform_irred (a b c d u:R) (hu:u*(a*d-b*c)=1)
   {f :R[X]} (hf :c9 f) (hn:2≤f.natDegree) :
   c9 (transform a b c d f.natDegree f) ∧
     (transform a b c d f.natDegree f).natDegree=f.natDegree := by
 let g:=transform a b c d f.natDegree f
 let q:=subst a b c d (f.homogenize f.natDegree)
 have hi:c9 q:=(MulEquiv.irreducible_iff (changeEquiv a b c d u hu).toRingEquiv.toMulEquiv).mpr
   (homog_irred hf)
 have hqd:q.totalDegree=f.natDegree :=
   (subst_homogeneous (lV f) a b c d).totalDegree hi.ne_zero
 have he :g.homogenize f.natDegree=q:=rehom a b c d _ _
 have hd:g.natDegree≤f.natDegree :=(dehom_degree q).trans_eq hqd
 have hd' : g.natDegree=f.natDegree := by
   by_contra! h
   have hlt:g.natDegree≤f.natDegree-1 := by omega
   have hh:=homogenize_mul g (1 :R[X]) hlt (show (1 :R[X]).natDegree≤1 by simp)
   rw [mul_one,Nat.sub_add_cancel (by omega),homogenize_one,pow_one,he] at hh
   rcases hi.isUnit_or_isUnit hh with h₁ | h₂
   · have h₀:=(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h₁).2
     have hs :=oq h₁.ne_zero (MvPolynomial.X_ne_zero 1)
     rw [← hh,hqd,h₀,nX] at hs
     omega
   · have h₀:=(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp h₂).2
     rw [nX] at h₀
     omega
 have hnu : ¬ IsUnit g:= fun h=> by have :=mD h; omega
 refine ⟨⟨hnu,?_⟩,hd'⟩
 intro p r hp
 have hg:g≠0:= fun hz=> by rw [hz,homogenize_zero] at he; exact hi.ne_zero he.symm
 have hpr :p*r≠0:=hp ▸ hg
 have hh:=homogenize_mul p r le_rfl le_rfl
 rw [← natDegree_mul (lI hpr) (lJ hpr),← hp,hd',he] at hh
 exact (hi.isUnit_or_isUnit hh).imp
   (fun h=> by simpa only [ew,lz p le_rfl] using h.map ew)
   (fun h=> by simpa only [ew,lz r le_rfl] using h.map ew)
end Binary
end
end qwGrtCa
