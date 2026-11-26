import ProximityPrize.SubmissionLower.R6960LineEulerFree
import ProximityPrize.SubmissionLower.R6960HornerScalar

set_option Elab.async false

-- merged module R6960HornerDeterminant
section Merged_R6960HornerDeterminant
set_option Elab.async false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.Horner
noncomputable section
open Polynomial LaurentPolynomial
open LineEuler (Laurent infinityEmbedding)
open scoped Polynomial BigOperators
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
private theorem prod_T (s : Finset ι) (n : ι→ℤ) :
    (∏ i∈s,(T (n i):Laurent k))=T (∑ i∈s,n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj,Finset.sum_insert hj,ih,T_add]
private theorem coeff_C_product (c : k) (p : Laurent k) (i : ℤ) :
    (LaurentPolynomial.C c*p).coeff i=c*p.coeff i := by
  rw [←single_eq_C,AddMonoidAlgebra.coeff_single_zero_mul]
theorem determinant_budget (G : Matrix ι ι (Laurent k)) (unit : IsUnit G)
    (P Q : Matrix ι ι (Polynomial k)) (width : ι→ℕ) (independent : P.det≠0)
    (join : P.map (Polynomial.toLaurent (R:=k)) = G * (Q.map (infinityEmbedding (k:=k))) *
      Matrix.diagonal (fun i=>T (R:=k) (width i : ℤ))) :
    ∃ d : ℤ, G.det.degree=(d:WithBot ℤ) ∧ -d≤∑ i,(width i : ℤ) := by
  let D : ℤ := ∑ i,(width i : ℤ)
  obtain ⟨c,d,cn,dc⟩ := LineEuler.unit_monomial G.det ((Matrix.isUnit_iff_isUnit_det G).mp unit)
  have lhs : (P.map (Polynomial.toLaurent (R:=k))).det=P.det.toLaurent :=
    (RingHom.map_det (Polynomial.toLaurent (R:=k)) P).symm
  have rhs : (Q.map (infinityEmbedding (k:=k))).det=infinityEmbedding Q.det :=
    ((infinityEmbedding (k:=k)).toRingHom.map_det Q).symm
  have det := congrArg Matrix.det join
  rw [lhs,Matrix.det_mul,Matrix.det_mul,rhs,Matrix.det_diagonal,prod_T,dc] at det
  have eq : P.det.toLaurent=LaurentPolynomial.C c*(T (d+D)*infinityEmbedding Q.det) := calc
    _ = (LaurentPolynomial.C c*T d)*infinityEmbedding Q.det*T D := det
    _ = _ := by rw [T_add]; ring
  let n : ℤ := P.det.natDegree
  have coeff : P.det.toLaurent.coeff n≠0 := Finsupp.mem_support_iff.mp (by
    rw [support_coeff_toLaurent]
    exact Finset.mem_map.mpr ⟨_,natDegree_mem_support_of_nonzero independent,rfl⟩)
  have bounded : infinityEmbedding Q.det∈AddMonoidAlgebra.supported k k (Set.Iic (0:ℤ)) := by
    change infinityEmbedding Q.det∈AddMonoidAlgebra.supported k k (Set.Iic ((0:ℕ):ℤ))
    rw [←LineEuler.range_shiftPolynomial 0]
    exact ⟨Q.det,by rw [LineEuler.shiftPolynomial_apply,Nat.cast_zero,T_zero,one_mul]⟩
  refine ⟨d,by rw [dc,degree_C_mul_T _ _ cn],?_⟩
  change -d≤D
  by_contra bad
  have near : ¬n-(d+D)∈Set.Iic (0:ℤ) := by
    change ¬n-(d+D)≤0
    have nn : 0≤n := Int.natCast_nonneg _
    omega
  have outside := AddMonoidAlgebra.mem_supported'.mp bounded _ near
  rw [eq,coeff_C_product,LineEuler.coeff_shift,outside,mul_zero] at coeff
  exact coeff rfl
end
end Lower6960.Horner

end Merged_R6960HornerDeterminant

-- merged module R6960HornerNative
section Merged_R6960HornerNative
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.Horner
noncomputable section
open Polynomial LaurentPolynomial Module
open LineEuler
open scoped Polynomial BigOperators Matrix
variable {k : Type*} [Field k]
def rationalLaurent : Laurent k →+* RatFunc k :=
  LaurentPolynomial.eval₂ RatFunc.C (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
@[simp] theorem rationalLaurent_T (n : ℕ) :
    rationalLaurent (T (n:ℤ) : Laurent k)=(RatFunc.X:RatFunc k)^n :=
  LaurentPolynomial.eval₂_T_n _ _ n
theorem rationalLaurent_finite :
    (rationalLaurent (k:=k)).comp (chartEmbedding false).toRingHom=algebraMap (Polynomial k) (RatFunc k) := by
  apply RingHom.ext
  intro p
  change rationalLaurent p.toLaurent=algebraMap (Polynomial k) (RatFunc k) p
  rw [rationalLaurent,LaurentPolynomial.eval₂_toLaurent]
  exact RatFunc.aeval_X_left_eq_algebraMap p
theorem rationalLaurent_infinity :
    (rationalLaurent (k:=k)).comp (chartEmbedding true).toRingHom=MonicChart.AtInfinity k := by
  apply Polynomial.ringHom_ext
  · intro c
    change rationalLaurent (infinityEmbedding (Polynomial.C c))=MonicChart.AtInfinity k (Polynomial.C c)
    rw [infinityEmbedding_apply,Polynomial.toLaurent_C,invert_C,rationalLaurent,LaurentPolynomial.eval₂_C]
    exact (Polynomial.aeval_C _ _).symm
  · change rationalLaurent (infinityEmbedding (Polynomial.X : (Polynomial k)))=MonicChart.AtInfinity k (Polynomial.X : (Polynomial k))
    rw [infinityEmbedding_apply,Polynomial.toLaurent_X,invert_T]
    have neg := LaurentPolynomial.eval₂_T_neg_n (RatFunc.C : k→+*RatFunc k)
      (Units.mk0 (RatFunc.X:RatFunc k) RatFunc.X_ne_zero) 1
    have atNeg : rationalLaurent (T (R:=k) (-1))=(RatFunc.X:RatFunc k)⁻¹ := by
      simpa only [rationalLaurent, Int.natCast_one, pow_one, Units.val_inv_eq_inv_val, Units.val_mk0] using neg
    rw [atNeg]
    exact (Polynomial.aeval_X _).symm
variable {E : Type*} [Field E] [Algebra (RatFunc k) E]
scoped instance rationalLaurentAlgebra : Algebra (Laurent k) E :=
  ((algebraMap (RatFunc k) E).comp rationalLaurent).toAlgebra
private theorem chart_finite_eq (q : (Polynomial k)) :
    algebraMap (Laurent k) E (chartEmbedding false q)=finiteScalar q :=
  congrArg (algebraMap (RatFunc k) E) (RingHom.congr_fun rationalLaurent_finite q)
private theorem chart_infinity_eq (q : (Polynomial k)) :
    algebraMap (Laurent k) E (chartEmbedding true q)=infinityScalar q :=
  congrArg (algebraMap (RatFunc k) E) (RingHom.congr_fun rationalLaurent_infinity q)
theorem finite_chart_algebra :
    ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom).toAlgebra =
      (finiteScalar (k:=k) (E:=E)).toAlgebra :=
  congrArg RingHom.toAlgebra (RingHom.ext chart_finite_eq)
private theorem infinity_chart_algebra :
    ((algebraMap (Laurent k) E).comp (chartEmbedding true).toRingHom).toAlgebra =
      (infinityScalar (k:=k) (E:=E)).toAlgebra :=
  congrArg RingHom.toAlgebra (RingHom.ext chart_infinity_eq)
private theorem sectionDet_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bf : Basis ι (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (x : ι→chartOrder (k:=k) (E:=E) false)
    (independent : LinearIndependent (RatFunc k) (fun i=>(x i:E))) : (chartMatrix bf x).det≠0 := by
  let j := algebraMap (Polynomial k) (RatFunc k)
  let P := chartMatrix bf x
  let M := P.map j
  let B := Pi.basisFun (RatFunc k) ι
  let synth := B.constr (RatFunc k) (fun i=>(bf i:E))
  let sections := B.constr (RatFunc k) (fun i=>(x i:E))
  let A := (chartOrder (k:=k) (E:=E) false)
  let : Algebra (Polynomial k) E := ((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom).toAlgebra
  have expansion (i : ι) : (∑ u, j (P u i) • (bf u:E))=(x i:E) := by
    have eq := bf.equivFun.symm_apply_apply (x i)
    rw [Basis.equivFun_symm_apply,Basis.equivFun_apply] at eq
    have mapEq := congrArg (A.val.toRingHom) eq
    rw [map_sum] at mapEq
    refine (Finset.sum_congr rfl fun u _=>?_).trans mapEq
    change j (P u i) • (bf u:E)=(↑(bf.repr (x i) u • bf u):E)
    rw [Algebra.smul_def,Algebra.smul_def]
    change finiteScalar (bf.repr (x i) u)*(bf u:E)=
      algebraMap (Laurent k) E (chartEmbedding false (bf.repr (x i) u))*(bf u:E)
    rw [chart_finite_eq]
  have composition : synth.comp (Matrix.toLin' M)=sections := by
    apply B.ext
    intro i
    change synth (Matrix.toLin' M (B i))=sections (B i)
    rw [show B i=Pi.single i 1 from Pi.basisFun_apply _ _ i,Matrix.toLin'_apply,Matrix.mulVec_single_one]
    rw [show Pi.single i (1:RatFunc k)=B i from (Pi.basisFun_apply _ _ i).symm]
    change B.constr (RatFunc k) (fun j=>(bf j:E)) (M.col i)=_
    rw [Basis.constr_basis,Basis.constr_apply_fintype]
    exact expansion i
  have inv : Function.Injective (Matrix.toLin' M) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have h := congrArg synth hv
    rw [map_zero,←LinearMap.comp_apply,composition] at h
    change B.constr (RatFunc k) (fun i=>(x i:E)) v=0 at h
    rw [Basis.constr_apply_fintype] at h
    have sum : (∑ i,v i • (x i:E))=0 := h
    exact funext fun i=>Fintype.linearIndependent_iff.mp independent v sum i
  have nonzero := ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp inv)).ne_zero
  intro z
  apply nonzero
  rw [show M.det=j P.det from (RingHom.map_det j P).symm,z,map_zero]
theorem actual_horner_budget (p : (Polynomial (Polynomial k))) (v : ℕ) (ep : 0<p.natDegree)
    (width : ∀ j,(p.coeff j).natDegree≤v) (y : E)
    (root : aeval y (p.map (algebraMap (Polynomial k) (RatFunc k)))=0)
    (degree : (minpoly (RatFunc k) y).natDegree=p.natDegree)
    (bf : Basis (Fin p.natDegree) (Polynomial k) (chartOrder (k:=k) (E:=E) false))
    (bi : Basis (Fin p.natDegree) (Polynomial k) (chartOrder (k:=k) (E:=E) true)) :
    ∃ d : ℤ,(normalizedTransition bf bi).det.degree=(d:WithBot ℤ) ∧
      -d≤((p.natDegree-1:ℕ):ℤ)*(v:ℤ) := by
  classical
  let j := algebraMap (Polynomial k) (RatFunc k)
  let Xinf := algebraMap (RatFunc k) E (RatFunc.X⁻¹)
  let sec (i : Fin p.natDegree) := aeval y ((sectionPoly p i).map j)
  let w (i : Fin p.natDegree) : ℕ := if i.val=0 then 0 else v
  have intf (i : Fin p.natDegree) : IntegralOver (finiteScalar (k:=k) (E:=E)) (sec i) := by
    by_cases h0 : i.val=0
    · have eq1 : sec i=1 := by simp [sec,sectionPoly,h0]
      rw [eq1]
      let : Algebra (Polynomial k) E := (finiteScalar (k:=k) (E:=E)).toAlgebra
      exact isIntegral_one
    · let d := p.natDegree-i.val+1
      have dpos : 0<d := by dsimp [d]; omega
      have eq : sec i=horner finiteScalar p d y := by
        simp [sec,sectionPoly,h0,d,horner,aeval_def,eval₂_map,j]
      rw [eq]
      exact (scalar_horner_charts p v width dpos y root).1
  have inti (i : Fin p.natDegree) : IntegralOver (infinityScalar (k:=k) (E:=E)) (Xinf^(w i)*sec i) := by
    by_cases h0 : i.val=0
    · have eq1 : Xinf^(w i)*sec i=1 := by simp [sec,w,sectionPoly,h0]
      rw [eq1]
      let : Algebra (Polynomial k) E := (infinityScalar (k:=k) (E:=E)).toAlgebra
      exact isIntegral_one
    · let d := p.natDegree-i.val+1
      have dpos : 0<d := by dsimp [d]; omega
      have eq : sec i=horner finiteScalar p d y := by
        simp [sec,sectionPoly,h0,d,horner,aeval_def,eval₂_map,j]
      rw [eq,show w i=v by simp [w,h0]]
      exact (scalar_horner_charts p v width dpos y root).2
  let x (i : Fin p.natDegree) : chartOrder (k:=k) (E:=E) false := ⟨sec i,by
    change @IsIntegral (Polynomial k) E _ _ (((algebraMap (Laurent k) E).comp (chartEmbedding false).toRingHom).toAlgebra) _
    rw [finite_chart_algebra]
    exact intf i⟩
  let z (i : Fin p.natDegree) : chartOrder (k:=k) (E:=E) true := ⟨Xinf^(w i)*sec i,by
    change @IsIntegral (Polynomial k) E _ _ (((algebraMap (Laurent k) E).comp (chartEmbedding true).toRingHom).toAlgebra) _
    rw [infinity_chart_algebra]
    exact inti i⟩
  have agree (i : Fin p.natDegree) : (x i:E)=algebraMap (Laurent k) E (T (w i:ℤ))*(z i:E) := by
    change sec i=algebraMap (RatFunc k) E (rationalLaurent (T (w i:ℤ)))*(Xinf^(w i)*sec i)
    rw [rationalLaurent_T,map_pow,←mul_assoc,←mul_pow]
    change sec i=(algebraMap (RatFunc k) E (RatFunc.X:RatFunc k)*algebraMap (RatFunc k) E (RatFunc.X⁻¹))^(w i)*sec i
    rw [←map_mul,mul_inv_cancel₀ RatFunc.X_ne_zero,map_one,one_pow,one_mul]
  have det : (chartMatrix bf x).det≠0 := sectionDet_ne_zero bf x
    (sections_independent j (IsFractionRing.injective (Polynomial k) (RatFunc k)) p y degree)
  obtain ⟨d,hd,bd⟩ := determinant_budget _ (normalizedTransition_unit bf bi) _ _ w det
    (normalized_join bf bi x z w agree)
  let j0 : Fin p.natDegree := ⟨0,ep⟩
  have sum : ∑ i : Fin p.natDegree,(w i:ℤ)=((p.natDegree-1:ℕ):ℤ)*(v:ℤ) := by
    have subtract : (∑ i : Fin p.natDegree,(w i:ℤ))=
        (∑ _ : Fin p.natDegree,(v:ℤ))-(∑ i : Fin p.natDegree,if i=j0 then (v:ℤ) else 0) := by
      rw [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have eq : i=j0 ↔ i.val=0 := Fin.ext_iff
      by_cases h : i.val=0 <;> simp [w,h,eq]
    rw [subtract,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Int.natCast_sub (by omega : 1≤p.natDegree)]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Int.natCast_one]
    ring
  exact ⟨d,hd,by rwa [sum] at bd⟩
end
end Lower6960.Horner

end Merged_R6960HornerNative
