import ProximityPrize.SubmissionLower.Z1qPXJc
set_option Elab.async false
open _root_ renaming CommRing → za6, Function.Injective → zq4, Polynomial.X → z7y, Polynomial.map_dvd_map → z2Q, Polynomial.map_prod → zeg, Polynomial.map_sub → z3A, Polynomial.map_zero → zgY, PowerSeries → zpm, PowerSeries.coeff → z2o, PowerSeries.coeff_zero_eq_constantCoeff_apply → zW1, PowerSeries.constantCoeff → zbO, RingHom.injective → zyB
set_option backward.isDefEq.respectTransparency false
namespace qnSUPza
noncomputable section
open Polynomial
open cu (L)
open qAW6lac (Index jo Eliminant aMp spectral)
open qfzuawb (deform extract extract_coeff ic dM coeffs SimpleFiber)
open qZu9hjc (atPair)
open q8Z6NHc (Slot form)
open scoped Classical
private def collect {F:Type} [za6 F] :
  (zpm F)[X] →+* zpm (F[X]) :=
 eval₂RingHom (PowerSeries.map C) (PowerSeries.C z7y)
private theorem coeff_collect {F:Type} [za6 F] (p: (zpm F)[X]) (n i:ℕ) :
   (z2o n (collect p)).coeff i=z2o n (p.coeff i) := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq=>simp only [map_add,coeff_add,hp,hq]
 | monomial k a =>
   rw [collect,coe_eval₂RingHom,eval₂_monomial,← map_pow,PowerSeries.coeff_mul_C,
     PowerSeries.coeff_map,C_mul_X_pow_eq_monomial,coeff_monomial,coeff_monomial]
   split <;> simp
private theorem collect_injective {F:Type} [za6 F] :
  zq4 (collect (F:=F)) := by
 intro p q h
 ext i:1
 apply PowerSeries.ext
 intro n
 rw [← coeff_collect,h,coeff_collect]
private theorem reduce_collect {F:Type} [za6 F] (p: (zpm F)[X]) :
  zbO (collect p)=p.map PowerSeries.constantCoeff := by
 ext i
 simp only [← zW1,coeff_collect,coeff_map]
private theorem leading_product {F:Type} [Field F] (p M: (zpm F)[X])
   (hp:p≠0) (hM:M.Monic) (hdiv :M∣p) :
   ∃ n:ℕ,z2o n (collect p)≠0 ∧
     M.map zbO∣z2o n (collect p) := by
 obtain ⟨q,hq⟩:=hdiv
 let S:=collect q
 have hS:S≠0:= fun h=>hp (by
   have hq0:=collect_injective (h.trans (map_zero collect).symm)
   simp [hq,hq0])
 let n:=S.order.toNat
 let U:=S.divXPowOrder
 have hU:zbO U≠0 :=
   PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hS
 have hSU: (PowerSeries.X:zpm (F[X]))^n*U=S :=
   PowerSeries.X_pow_order_mul_divXPowOrder
 have hs :collect p=PowerSeries.X ^n*(collect M*U) := by
   rw [mul_left_comm,hSU,hq,map_mul]
 have he :z2o n (collect p) =
     M.map zbO*zbO U:= by
   rw [hs]
   simpa only [Nat.zero_add,zW1,map_mul,
     reduce_collect] using (PowerSeries.coeff_X_pow_mul (collect M*U) n 0)
 exact ⟨n,he ▸ mul_ne_zero (hM.map _).ne_zero hU,he.symm ▸ dvd_mul_right _ _⟩
variable {B:Type} [Field B]
local notation "Ω" => AlgebraicClosure B
local notation "j" => (algebraMap B (AlgebraicClosure B))
local notation "ct" => (PowerSeries.constantCoeff :Germ B →+* Ω)
private def toGerm:B[X] →+* Germ B :=
 (PowerSeries.map j).comp Polynomial.coeToPowerSeries.ringHom
private theorem toGerm_coeff (q:B[X]) (n:ℕ) :
  z2o n (toGerm q)=j (q.coeff n) := by
 simp [toGerm]
private theorem toGerm_injective :zq4 (toGerm (B:=B)) := by
 intro p q h
 ext n
 apply (zyB j)
 rw [← toGerm_coeff,h,toGerm_coeff]
@[local simp] private theorem toGerm_C (a :B) :toGerm (C a)=PowerSeries.C (j a) := by
  simp [toGerm]
@[local simp] private theorem toGerm_X:toGerm (z7y:B[X])=PowerSeries.X:= by
  simp [toGerm]
variable [Algebra L B] in
private theorem eval_deform {d D W:ℕ} (α:Index d D W→B) (δ:Index d D W→L)
    (P:jo d D W) (v :Germ B) :
    ((deform α δ P).map toGerm).eval v =
      P.eval₂ ((PowerSeries.C.comp j).comp (algebraMap L B))
        (fun i=>motion (α i) (δ i) - if i=spectral d D W then v else 0) := by
  let k :=(evalRingHom v).comp (mapRingHom (toGerm (B:=B)))
  change k (deform α δ P)= _
  rw [deform,MvPolynomial.hom_eval₂]
  congr 1
  · ext a
    simp [k]
  · funext i
    by_cases hi:i=spectral d D W <;> simp [k,ic,motion,hi]
variable [Algebra L B] in
private theorem third_zero {d D W:ℕ} (α:Index d D W→B) (δ:Index d D W→L)
    (xy :Germ B×Germ B) :
    aMp (fun i=>motion (α (.inr (.inr i))) (δ (.inr (.inr i))) -
      if Sum.inr (Sum.inr i)=spectral d D W then branchValue α δ xy else 0)
        xy.1 xy.2=0:= by
  let o:Slot (d-1) D (W-D) :=⟨(0,0),by simp⟩
  have ho:spectral d D W = .inr (.inr o) :=rfl
  rw [branchValue,ho,aMp]
  simp only [Sum.inr.injEq,sub_mul,Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  symm
  rw [Finset.sum_eq_single o]
  · simp [o,aMp]
  · intro i _ hi
    simp [hi]
  · simp
theorem form_eq {d D W:ℕ} (Q:B[X][X]) (hQ:dM Q D d W) :
    form (d:=d) (s :=D) (a :=W) (fun i=>(Q.coeff i.val.1).coeff i.val.2)= Q:= by
  ext i:1
  ext k :1
  simp only [form,finsetSum_coeff,coeff_monomial]
  by_cases h:i≤d∧k+i*D ≤W
  · let o:Slot d D W:=⟨(⟨i,by omega⟩,⟨k,by omega⟩),h.2⟩
    rw [Finset.sum_eq_single o]
    · simp [o]
    · intro a _ ha
      have he : ¬ ((a.val.1 :ℕ)=i∧(a.val.2 :ℕ)=k) := by
        intro hh
        apply ha
        apply Subtype.ext
        exact Prod.ext (Fin.ext hh.1) (Fin.ext hh.2)
      by_cases hi: (a.val.1 :ℕ)=i
      · have hk : (a.val.2 :ℕ)≠k := fun hk=>he ⟨hi,hk⟩
        simp [coeff_monomial,hi,hk]
      · simp [hi]
    · simp
  · have hz : (Q.coeff i).coeff k=0:= by
      by_contra hn
      exact h (hQ i k hn)
    rw [hz]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hi: (a.val.1 :ℕ)=i
    · by_cases hk : (a.val.2 :ℕ)=k
      · exact (h ⟨by have :=a.val.1.isLt; omega,by simpa only [hi,hk] using a.prop⟩).elim
      · simp [coeff_monomial,hi,hk]
    · simp [hi]
private theorem at_form {d D W:ℕ} (Q:B[X][X]) (hQ:dM Q D d W) (x y :Ω) :
    aMp (d:=d) (s :=D) (W:=W)
        (fun i=>j ((Q.coeff i.val.1).coeff i.val.2)) x y=atPair j x y Q:= by
  conv_rhs=>rw [← form_eq Q hQ]
  simp only [atPair,form,aMp,eval₂_finsetSum,eval₂_monomial,coe_eval₂RingHom]
variable [Algebra L B] in
theorem specialize {d D W:ℕ} (f g Q:B[X][X]) (N :B[X])
   (hQ:dM Q D (d-1) (W-D)) (T:SimpleFiber f g Q N) (P:Eliminant d D W)
   (δ:Index d D W→L) (hd:deform (coeffs f g Q) δ P.poly≠0)
   (xy :Fin T.size→Germ B×Germ B)
   (hxy : ∀ i,(ct (xy i).1,ct (xy i).2)=T.point i)
   (hf : ∀ i,aMp (fun k=>motion (coeffs f g Q (.inl k)) (δ (.inl k)))
     (xy i).1 (xy i).2=0)
   (hg : ∀ i,aMp (fun k=>motion (coeffs f g Q (.inr (.inl k))) (δ (.inr (.inl k))))
     (xy i).1 (xy i).2=0)
   (hv :zq4 (fun i=>branchValue (coeffs f g Q) δ (xy i))) :
   ∃ n,extract (coeffs f g Q) δ P.poly n≠0∧N∣extract (coeffs f g Q) δ P.poly n:= by
 let α:Index d D W→B:=coeffs f g Q
 let F:=(deform α δ P.poly).map toGerm
 let v (i:Fin T.size) :=branchValue α δ (xy i)
 let M := ∏ i,((z7y: (Germ B)[X]) - C (v i))
 let:Algebra L (Germ B) :=((PowerSeries.C.comp j).comp (algebraMap L B)).toAlgebra
 have hF:F≠0:= fun hz=>hd (map_injective _ toGerm_injective (hz.trans (zgY _).symm))
 have hz (i:Fin T.size) :F.eval (v i)=0:= by
   rw [eval_deform]
   apply P.aiq (F:=Germ B) _ (xy i).1 (xy i).2
   · simpa [spectral] using hf i
   · simpa [spectral] using hg i
   · exact third_zero α δ (xy i)
 have hm:M.Monic:=monic_prod_of_monic _ _ fun i _=>monic_X_sub_C (v i)
 let K:=FractionRing (Germ B)
 let u:=algebraMap (Germ B) K
 have hu:zq4 u:=IsFractionRing.injective (Germ B) K
 have hdiv :M∣F:= by
   apply (z2Q u hu hm).mp
   rw [zeg]
   simp only [z3A,map_X,map_C]
   apply Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C (hu.comp hv))
   intro i
   apply dvd_iff_isRoot.mpr
   change (F.map u).eval (u (v i))=0
   rw [eval_map_apply,hz,map_zero]
 obtain ⟨n,hn,hnd⟩:=leading_product F M hF hm hdiv
 have he :z2o n (collect F)=(extract α δ P.poly n).map j:= by
   ext i
   rw [coeff_collect,coeff_map,toGerm_coeff,coeff_map,extract_coeff]
 have hs (i:Fin T.size) :ct (v i)=atPair j (T.point i).1 (T.point i).2 Q:= by
   have hx :ct (xy i).1=(T.point i).1 :=congrArg Prod.fst (hxy i)
   have hy :ct (xy i).2=(T.point i).2 :=congrArg Prod.snd (hxy i)
   simpa only [v,α,branchValue,aMp,motion,map_sum,map_add,map_mul,map_pow,
     PowerSeries.constantCoeff_C,PowerSeries.constantCoeff_X,mul_zero,add_zero,
     qfzuawb.coeffs,hx,hy] using (at_form Q hQ (T.point i).1 (T.point i).2)
 have hN :M.map ct=N.map j:= by
   rw [T.product]
   simp only [M,zeg,z3A,map_X,map_C,hs]
 refine ⟨n,fun h=>hn (by rw [he,h,zgY]),?_⟩
 have hNm:N.Monic:=monic_of_injective (zyB j) (hN ▸ hm.map ct)
 exact (z2Q j (zyB j) hNm).mp (by simpa only [hN,he] using hnd)
end
end qnSUPza
