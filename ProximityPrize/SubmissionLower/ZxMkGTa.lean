import Mathlib.LinearAlgebra.Eigenspace.Zero
import ProximityPrize.SubmissionLower.ZhEC96c
import ProximityPrize.SubmissionLower.Zk6yNvb
set_option Elab.async false
open _root_ renaming Int.natCast_nonneg → zbO, MvPolynomial → z3y, Polynomial.C → z1z, Polynomial.X → z7y
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qfbIfsd
noncomputable section
open Polynomial Finset qNu3xvc
open P5_7_1_7_4_3_4 (Pencil relativePolar bix)
open qFD8jve (sheetPole)
open E7 (CurvePlace)
open cu (L)
open scoped Classical WithZero
open private efc adG cTA aMX b4s bHf from ProximityPrize.SubmissionLower.Y
open private gauss₂ gauss₂_C from ProximityPrize.SubmissionLower.ZhEC96c
def c1 :Prop :=
  ∀ (s :ℕ) (b e :Fin 3→ℕ),(∀ t,0<e t)→0<b 1 →
    ∃ R:z3y (Vars s b e) L,R≠0∧R.totalDegree≤ kK s b e∧Detects R
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E),2≤A.d → ∀ C:Pencil A,
    ∀ R:z3y (Index A) L,R≠0→Detects R →
    ∃ (z :Index A→L) (n:ℕ),
      let P:=(deform R (actual C) z).coeff n
      P≠0∧bix C.base (relativePolar C) C.finite ∣
        P.map (algebraMap E[X] (RatFunc E))
variable {E :Type} [Field E]
private def rat₂:E[X][X] →+* RatFunc (RatFunc E) :=
 (algebraMap (RatFunc E)[X] (RatFunc (RatFunc E))).comp
   (mapRingHom (algebraMap E[X] (RatFunc E)))
private def gauss₃ (v :Valuation E ℤᵐ⁰) :Valuation E[X][X][X] ℤᵐ⁰ :=
 (efc (b4s (b4s v))).comap (mapRingHom rat₂)
private theorem gauss₃_C (v :Valuation E ℤᵐ⁰) (a :E[X][X]) :
  gauss₃ v (z1z a)=gauss₂ v a := by
 change adG (b4s (b4s v)) ((z1z a).map rat₂)= _
 rw [map_C,cTA]
 exact bHf _ _
private theorem coeff_le_gauss₃ (v :Valuation E ℤᵐ⁰) (P:E[X][X][X]) (n:ℕ) :
  gauss₂ v (P.coeff n)≤gauss₃ v P:= by
 have h:=aMX (b4s (b4s v)) (P.map rat₂) n
 rw [coeff_map] at h
 exact (bHf _ _).symm.trans_le h
private theorem gauss_X {F:Type} [Field F] (v :Valuation F ℤᵐ⁰) :
  adG v (z7y:F[X])=1 := by
 simp [adG,support_X]
private theorem gauss₂_X (v :Valuation E ℤᵐ⁰) :gauss₂ v z7y=1 := by
 change adG (b4s v) ((z7y:E[X][X]).map _)= _
 rw [map_X,gauss_X]
private theorem gauss₂_inner (v :Valuation E ℤᵐ⁰) :
  gauss₂ v (z1z (z7y:E[X]))=1 := by
 change adG (b4s v) ((z1z (z7y:E[X])).map _)= _
 rw [map_C,cTA,bHf,gauss_X]
private theorem gauss₃_X (v :Valuation E ℤᵐ⁰) :gauss₃ v z7y=1 := by
 change adG (b4s (b4s v)) ((z7y:E[X][X][X]).map _)= _
 rw [map_X,gauss_X]
variable [Algebra L E]
private theorem constant_le (w:CurvePlace L E) (a :L) :
   w.value (algebraMap L E a)≤1 := by
 obtain rfl | h:=eq_or_ne a 0
 · simp
 exact (w.on_constants a h).le
omit [Algebra L E] in
private theorem cast_le (v :Valuation E ℤᵐ⁰) (n:ℕ) :v (n:E)≤1 := by
 induction n with
 | zero=>simp
 | succ n ih=>rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)
private theorem actual_le {A:Equation E} (C:Pencil A) (w:CurvePlace L E)
    (r :Index A) :gauss₂ w.value (actual C r)≤WithZero.exp (sheetPole w.value A.f :ℤ) := by
  let B:=WithZero.exp (sheetPole w.value A.f :ℤ)
  have hB:1≤B:=WithZero.one_le_exp_iff.mpr (zbO _)
  rcases r with ⟨t,⟨i,j⟩⟩
  fin_cases t
  · change gauss₂ w.value (const₂ ((A.f.coeff i).coeff j))≤B
    rw [show ∀ a :E,gauss₂ w.value (const₂ a)=w.value a from gauss₂_C w.value]
    exact qrezXJe.sheet_bound w.value A.f i j
  · change gauss₂ w.value (const₂ ((C.num.coeff i).coeff j) -
        const₂ ((C.den.coeff i).coeff j)*z1z (z7y:E[X]))≤B
    apply (gauss₂ w.value).map_sub_le
    · exact (gauss₂_C w.value _).trans_le (C.num_height w i j)
    · rw [map_mul,gauss₂_inner,mul_one]
      exact (gauss₂_C w.value _).trans_le (C.den_height w i j)
  · change gauss₂ w.value (const₂ ((A.f.derivative.coeff i).coeff j) -
        const₂ (algebraMap L E (if (j:ℕ)=0 then (gaugeForm C.tilt A.d).coeff i else 0)) *
          z7y)≤B
    apply (gauss₂ w.value).map_sub_le
    · rw [show ∀ a :E,gauss₂ w.value (const₂ a)=w.value a from gauss₂_C w.value,
        coeff_derivative,← Nat.cast_succ,← C_eq_natCast,coeff_mul_C,map_mul]
      simpa only [mul_one] using
        mul_le_mul' (qrezXJe.sheet_bound w.value A.f (i.val+1) j)
          (cast_le w.value (i.val+1))
    · rw [map_mul,gauss₂_X,mul_one,
        show ∀ a :E,gauss₂ w.value (const₂ a)=w.value a from gauss₂_C w.value]
      exact (constant_le w _).trans hB
private theorem deform_le {ι:Type} (R:z3y ι L)
   (w:CurvePlace L E) (a :ι→E[X][X]) (z :ι→L) (H D:ℕ)
   (ha : ∀ i,gauss₂ w.value (a i)≤WithZero.exp (H :ℤ)) (hD:R.totalDegree≤D) :
   gauss₃ w.value (deform R a z)≤WithZero.exp ((D*H :ℕ) :ℤ) := by
 let v :=gauss₃ w.value
 let B:=WithZero.exp (H :ℤ)
 have hB:1≤B:=WithZero.one_le_exp_iff.mpr (zbO _)
 have q0 (c:L) :v (z1z (const₂ (algebraMap L E c)))≤1 := by
   dsimp [v]
   rw [gauss₃_C,show ∀ d:E,gauss₂ w.value (const₂ d)=w.value d from gauss₂_C w.value]
   exact constant_le w c
 have harg (i:ι) :v (deformArg (a i) (z i))≤B:= by
   unfold deformArg
   apply v.map_add_le
   · simpa only [v,gauss₃_C] using ha i
   · rw [map_mul,show v z7y=1 from gauss₃_X w.value,mul_one]
     exact (q0 _).trans hB
 change v (MvPolynomial.eval₂ _ _ R)≤_
 rw [MvPolynomial.eval₂_eq]
 apply v.map_sum_le
 intro m hm
 rw [map_mul,map_prod]
 calc
   _≤1 * ∏ i∈m.support,B^m i :=
     mul_le_mul' (q0 _) (prod_le_prod fun i _=> by rw [map_pow]; exact pow_le_pow_left' (harg i) _)
   _=WithZero.exp ((m.sum (fun _ n=>n)*H :ℕ) :ℤ) := by
     rw [one_mul,prod_pow_eq_pow_sum,← WithZero.exp_nsmul]
     simp [Finsupp.sum]
   _≤_:=WithZero.exp_le_exp.mpr (Int.ofNat_le.mpr
     (Nat.mul_le_mul_right H ((MvPolynomial.le_totalDegree hm).trans hD)))
private theorem value_const_ne {A:Equation E} (C:Pencil A) :
  (bix C.base (relativePolar C) C.finite).coeff 0≠0:= by
 let _:=C.base.toAlgebra
 let _:=C.finite
 have hq:relativePolar C≠0:=div_ne_zero C.polar_ne (pow_ne_zero _ C.gauge_ne)
 intro h
 obtain ⟨x,hx,hzero⟩:=(LinearMap.charpoly_constantCoeff_eq_zero_iff _).mp h
 exact (mul_ne_zero hq hx) hzero
private theorem remove_zero {F:Type} [Field F] (q:F[X]) (hq:q.coeff 0≠0) :
   IsCoprime q Polynomial.X:= by
 let a :F[X] :=z1z (q.coeff 0)⁻¹
 refine ⟨a,-(a*q.divX),?_⟩
 calc
   _=a*(q - q.divX*z7y) := by ring
   _=a*z1z (q.coeff 0) := by
     rw [sub_eq_iff_eq_add.mpr ((divX_mul_X_add q).symm.trans (add_comm _ _))]
   _=1 := by simp [a,← Polynomial.C_mul,hq]
private theorem strip {A:Equation E} (C:Pencil A) (P:E[X][X]) (hP:P≠0)
    (h:bix C.base (relativePolar C) C.finite ∣
      P.map (algebraMap E[X] (RatFunc E))) :
    ∃ Q:E[X][X],Q.coeff 0≠0 ∧
      bix C.base (relativePolar C) C.finite ∣
        Q.map (algebraMap E[X] (RatFunc E)) ∧
      ∀ i,Q.coeff i=P.coeff (i+P.natTrailingDegree) := by
  let n:=P.natTrailingDegree
  let Q:=P /ₘ (z7y:E[X][X])^n
  have he :z7y ^n*Q=P:= by
    simpa only [sub_zero,map_zero,rootMultiplicity_eq_natTrailingDegree',Q,n] using
      (pow_mul_divByMonic_rootMultiplicity_eq P (0:E[X]))
  have hc (i:ℕ) :Q.coeff i=P.coeff (i+n) := by
    rw [← he,coeff_X_pow_mul]
  refine ⟨Q,?_,?_,hc⟩
  · simpa only [hc,zero_add,n] using coeff_natTrailingDegree_ne_zero.mpr hP
  · rw [← he,Polynomial.map_mul,Polynomial.map_pow,map_X] at h
    have hi:=remove_zero _ (value_const_ne C)
    have hp (m:ℕ) :IsCoprime (bix C.base (relativePolar C) C.finite)
        (z7y ^m) := by
      induction m with
      | zero=>simpa using isCoprime_one_right
      | succ m ih=>rw [pow_succ]; exact ih.mul_right hi
    exact (hp n).dvd_of_dvd_mul_left h
end
end qfbIfsd
