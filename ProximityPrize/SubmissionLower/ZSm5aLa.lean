import ProximityPrize.SubmissionLower.ZEdS9yd
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qoGY3we
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys)
open q2TwyLa (i5 diffPoly)
open scoped Classical WithZero
abbrev cc:Series →+* FX:=PowerSeries.constantCoeff
private abbrev x :FX:=phys (Polynomial.X:L[X])
private def evalInv :L[X] →+* FX:=eval₂RingHom (algebraMap L FX) x⁻¹
private theorem chart_reduce (b:Bool) :
    cc.comp (bY b)=(if b then evalInv else phys).comp reduce := by
  cases b <;> apply Polynomial.ringHom_ext
  all_goals
    first
    | intro a
      simp only [RingHom.comp_apply,bY,Bool.false_eq_true,↓reduceIte,reduce,
        coe_mapRingHom,map_C,coe_eval₂RingHom,eval₂_C,evalInv,← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_map]
      all_goals rfl
    | simp [bY,evalInv,x]
theorem finite_reduce :cc.comp (bY false)=phys.comp reduce :=chart_reduce false
theorem integral_reduce {z :Series} (hz : (bY false).IsIntegralElem z) :
  ∃ q:L[X],phys q=cc z := by
 have h:=hz.map cc
 rw [chart_reduce false] at h
 exact IsIntegrallyClosed.algebraMap_eq_of_integral h.of_comp
private theorem phys_ne {q:L[X]} (hq:q≠0) :phys q≠0 :=
 (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).2 hq
private theorem clear_den {N B U:L[X]} (hb:B≠0) (hc:IsCoprime N B)
  (h : ∃ q:L[X],phys q=phys U*(phys N/phys B)) :B∣U:= by
 obtain ⟨q,hq⟩:=h
 have he :q*B=U*N := by
  apply IsFractionRing.injective L[X] FX
  change phys (q*B)=phys (U*N)
  rw [map_mul,map_mul,hq,mul_assoc,div_mul_cancel₀ _ (phys_ne hb)]
 exact hc.symm.dvd_of_dvd_mul_right ⟨q,by simpa only [mul_comm B q] using he.symm⟩
theorem finite_den (A:Cover) {P N B:L[X]} (J:LocalRoot A.f A.r P)
   (hb:B≠0) (hc:IsCoprime N B) (hr :phys N/phys B=seedTangent A.f P)
   (h1 : (bY false).IsIntegralElem (bY false A.g*J.logSeed))
   (h2 : (bY false).IsIntegralElem
     (bY false A.g.derivative*J.logSeed - bY false (diffPoly A.g)*J.logPhys)) :
   B∣EuclideanDomain.gcd (reduce A.g) (reduce A.g).derivative := by
 have h (q:i5[X]) :cc (bY false q)=phys (reduce q) :=
   RingHom.congr_fun (chart_reduce false) q
 have hd:reduce A.g.derivative=(reduce A.g).derivative :=(derivative_map _ _).symm
 obtain ⟨q₁,hq₁⟩:=integral_reduce h1
 obtain ⟨q₂,hq₂⟩:=integral_reduce h2
 simp only [map_mul,map_sub,h,hd] at hq₁ hq₂
 let H :=P - C A.r
 apply EuclideanDomain.dvd_gcd
 · apply clear_den hb hc
   refine ⟨q₁*H,?_⟩
   rw [map_mul,hq₁,mul_assoc,J.seed_res,hr]
 · apply clear_den hb hc
   refine ⟨q₂*H+reduce (diffPoly A.g)*P.derivative,?_⟩
   rw [map_add,map_mul,map_mul,hq₂,sub_mul,mul_assoc _ (cc J.logSeed),
     mul_assoc _ (cc J.logPhys),J.seed_res,J.phys_res,sub_add_cancel,hr]
private abbrev toRat :FX ≃ₐ[L[X]] RatFunc L:=FractionRing.algEquiv L[X] (RatFunc L)
private def infVal:Valuation FX ℤᵐ⁰:=(RatFunc.inftyValuation L).comap toRat.toRingHom
private theorem inf_poly {q:L[X]} (hq:q≠0) :
  infVal (phys q)=WithZero.exp (q.natDegree :ℤ) := by
 change RatFunc.inftyValuation L (toRat (algebraMap L[X] FX q))= _
 rw [toRat.commutes,RatFunc.inftyValuation_apply]
 exact RatFunc.inftyValuation.polynomial L hq
private theorem inf_const (c:L) (hc:c≠0) :infVal (algebraMap L FX c)=1 := by
 rw [IsScalarTower.algebraMap_apply L L[X] FX]
 exact (inf_poly (C_ne_zero.mpr hc)).trans (by simp)
private theorem inf_x :infVal x⁻¹<1 := by
 rw [map_inv₀,inf_poly Polynomial.X_ne_zero,natDegree_X,← WithZero.exp_neg,
  ← WithZero.exp_zero,WithZero.exp_lt_exp]
 decide
private theorem evalInv_le (q:L[X]) :infVal (evalInv q)≤1 := by
 let O:=infVal.valuationSubring
 let c:=(algebraMap L FX).codRestrict O.toSubring (fun a=> by
   change infVal (algebraMap L FX a)≤1
   by_cases ha :a=0
   · simp [ha]
   · exact (inf_const a ha).le)
 let k :=eval₂RingHom c (⟨x⁻¹,inf_x.le⟩:O)
 have hk :O.subtype.comp k=evalInv := by
   apply Polynomial.ringHom_ext
   · intro a
     change ((k (C a) :O) :FX)= _
     rw [show k (C a)=c a from eval₂_C _ _]
     exact (eval₂_C _ _).symm
   · change ((k Polynomial.X:O) :FX)= _
     rw [show k Polynomial.X=⟨x⁻¹,inf_x.le⟩ from eval₂_X _ _]
     exact (eval₂_X _ _).symm
 rw [← RingHom.congr_fun hk q]
 exact (k q).property
private theorem evalInv_unit {q:L[X]} (hq:q.coeff 0≠0) :infVal (evalInv q)=1 := by
  have hq' : evalInv q=x⁻¹*evalInv q.divX+algebraMap L FX (q.coeff 0) := by
    calc
      _=evalInv (Polynomial.X*q.divX+C (q.coeff 0)) :=congrArg evalInv (X_mul_divX_add q).symm
      _ = _:= by
        rw [map_add,map_mul]
        simp only [evalInv,coe_eval₂RingHom,eval₂_X,eval₂_C]
  rw [hq',infVal.map_add_eq_of_lt_right]
  · exact inf_const _ hq
  · rw [map_mul,inf_const _ hq]
    calc
      _≤ infVal x⁻¹*1 :=mul_le_mul_of_nonneg_left (evalInv_le _) zero_le
      _<1 := by simpa only [mul_one] using inf_x
theorem awayChart (A:Cover) :
  ∃ j:Away A →+* Series,j.comp (algebraMap i5[X] (Away A))=bY true := by
 have h:cc (bY true A.g.reverse)=evalInv (reduce A.g.reverse) :=
  RingHom.congr_fun (chart_reduce true) _
 have hn:cc (bY true A.g.reverse)≠0:= by
  intro hz
  have he :=evalInv_unit (radical_coeff A)
  rw [← h,hz,map_zero] at he
  exact zero_ne_one he
 have hu:IsUnit (bY true A.g.reverse) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hn)
 exact ⟨IsLocalization.Away.lift A.g.reverse hu,IsLocalization.Away.lift_comp _ _⟩
private theorem infinity_reduce (A:Cover) (j:Away A →+* Series)
   (hj:j.comp (algebraMap i5[X] (Away A))=bY true)
   {z :Series} (hz :j.IsIntegralElem z) :infVal (cc z)≤1 := by
 let O:=infVal.valuationSubring
 let k :=(evalInv.comp reduce).codRestrict O.toSubring (fun q=>evalInv_le (reduce q))
 have hu:IsUnit (k A.g.reverse) :=
   (Valuation.valuationSubring.integers infVal).isUnit_iff_valuation_eq_one.mpr (evalInv_unit (radical_coeff A))
 let jO:Away A →+* O:=IsLocalization.Away.lift A.g.reverse hu
 have he :cc.comp j=O.subtype.comp jO:= by
   apply IsLocalization.ringHom_ext (Submonoid.powers A.g.reverse)
   rw [RingHom.comp_assoc,hj,chart_reduce true,RingHom.comp_assoc,
     IsLocalization.Away.lift_comp]
   rfl
 have hh:=hz.map cc
 rw [he] at hh
 exact (Valuation.valuationSubring.integers infVal).isIntegral_iff_v_le_one.mp hh.of_comp
theorem aNb (A:Cover) {P N B:L[X]} (J:LocalRoot A.f A.r P)
   (j:Away A →+* Series) (hj:j.comp (algebraMap i5[X] (Away A))=bY true)
   (hz :j.IsIntegralElem J.logSeed) {D:ℕ} (hP:P.natDegree≤D)
   (hR:P - C A.r≠0) (hB:B≠0) (hr :phys N/phys B=seedTangent A.f P) :
   N.natDegree≤D+B.natDegree := by
 by_cases hN :N=0
 · simp [hN]
 have h:=infinity_reduce A j hj hz
 have hd: (P - C A.r).natDegree≤D :=
   (natDegree_sub_le _ _).trans (max_le hP (by simp))
 have hv :infVal (phys N/phys B)≤WithZero.exp (D:ℤ) := by
   rw [hr,← J.seed_res,map_mul,inf_poly hR]
   exact (mul_le_mul_of_nonneg_right h zero_le).trans (by
     rw [one_mul,WithZero.exp_le_exp]
     exact_mod_cast hd)
 rw [infVal.map_div,inf_poly hN,inf_poly hB,← WithZero.exp_sub,WithZero.exp_le_exp] at hv
 omega
end
end qoGY3we
