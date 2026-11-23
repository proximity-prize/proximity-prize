import ProximityPrize.SubmissionLower.ZsazLcd
import ProximityPrize.SubmissionLower.Z5rjxle
import ProximityPrize.SubmissionLower.ZOb5aoe
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
namespace q7KvxZa
noncomputable section
open Polynomial Finset q82zwcd qxDtRld
open P5 (K I p)
open cu (L)
open Cu (sQ)
open E7 (CurvePlace)
open qb0hmCe (SiteTarget)
open q1kuFjb (power_residue)
open qFD8jve (aFA seedPole polarResultant)
open qbnx7gb (targetA targetB)
open qwGrtCa (form transform transform_sum transform_irred)
open qERExMc (transform_degree transform_top transform_scale)
open scoped WithZero
open private result_nonzero from ProximityPrize.SubmissionLower.ZEy78Hb
open private gauss efe gauss_X coeff_gauss gauss_taylor const_bound target_bound from ProximityPrize.SubmissionLower.ZlnMfEd
open private adG cTA efc from ProximityPrize.SubmissionLower.Y
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
 {z :K→K} {q:sQ} {J:WordChart D w U s} {F:DualSheet J q z}
private theorem centre_ne (F:DualSheet J q z) (R:SiteTarget) :
   F.f.map (evalRingHom (algebraMap L F.curve.E R.center))≠0:= by
 intro hz
 let x :=algebraMap L F.curve.E R.center
 have hd:C (Polynomial.X (R:=F.curve.E) - C x)∣F.f := by
   apply (C_dvd_iff_dvd_coeff _ _).mpr
   intro i
   apply dvd_iff_isRoot.mpr
   simpa only [coeff_map,coe_evalRingHom,coeff_zero,IsRoot,x] using
     congrArg (fun f :F.curve.E[X]=>f.coeff i) hz
 exact (irreducible_X_sub_C x).not_isUnit (F.primitive _ hd)
private theorem complement (V:Variation F) (R:SiteTarget) :
   ∃ t:L,(F.f.map (evalRingHom (algebraMap L F.curve.E R.center))).eval
     (algebraMap L F.curve.E t)≠0 ∧
     ∀ γ∈V.good,targetHit J z R γ→t*resB R z γ - resA R z γ≠0:= by
 classical
 let a :=algebraMap L F.curve.E
 let f :=F.f.map (evalRingHom (a R.center))
 let B:=V.good.image (fun γ=>resA R z γ/resB R z γ)
 have hroot : (a ⁻¹' {u | f.IsRoot u}).Finite :=
   (finite_setOfPred_isRoot (centre_ne F R)).preimage a.injective.injOn
 obtain ⟨t,ht⟩:=(hroot.union B.finite_toSet).exists_notMem
 refine ⟨t,fun hz=>ht (Or.inl hz),?_⟩
 intro γ hγ hm hd
 have hn:resB R z γ≠0:= by
   intro hz
   have ha :resA R z γ=0:= by simpa [hz] using hd
   exact (hm.1.resolve_right (fun hn=>hn hz)) ha
 exact ht (Or.inr (mem_image.mpr ⟨γ,hγ,((eq_div_iff hn).mpr (sub_eq_zero.mp hd)).symm⟩))
private theorem determinant (R:SiteTarget) (t:L) {γ:K} (hγ:γ∈U)
   (ht:t*resB R z γ - resA R z γ≠0) :
   algebraMap L F.curve.E t*targetB F.curve R - targetA F.curve R≠0:= by
 intro hz
 obtain ⟨arc,ha,hr,_⟩:=F.arc γ hγ
 let a :=F.atPlace γ hγ
 let A:=PowerSeries.C R.a+PowerSeries.C R.b*arc R.coord
 let B:=PowerSeries.C R.c+PowerSeries.C R.d*arc R.coord
 have hseed :a (F.curve.seed R.coord)=(arc R.coord:LaurentSeries L) :=ha _
 have he : ((PowerSeries.C t*B - A:PowerSeries L) :LaurentSeries L)=0:= by
   simpa only [A,B,targetA,targetB,map_zero,map_sub,map_add,map_mul,a.commutes,
     hseed,PowerSeries.coe_add,PowerSeries.coe_mul,PowerSeries.coe_sub,PowerSeries.coe_C,
     LaurentSeries.algebraMap_apply] using congrArg a hz
 have h:=power_residue 0 _ he.symm
 exact ht (by simpa only [A,B,resA,resB,HahnSeries.coeff_zero,map_sub,map_mul,map_add,
   PowerSeries.constantCoeff_C,hr] using h.symm)
private theorem shape (R:SiteTarget) (t:L) (hp:F.d<p)
    (ht: (F.f.map (evalRingHom (algebraMap L F.curve.E R.center))).eval
      (algebraMap L F.curve.E t)≠0)
    (hdet:algebraMap L F.curve.E t*targetB F.curve R - targetA F.curve R≠0) :
    (Go F R t).natDegree=F.d∧(Go F R t).leadingCoeff.coeff 0≠0 ∧
      polarResultant (Go F R t)≠0:= by
  let m:=algebraMap L F.curve.E
  let e :=(taylorEquiv (m R.center)).toRingEquiv
  let f :=F.f.map e.toRingHom
  let G:=Go F R t
  have hf :f.natDegree=F.d:=natDegree_map_eq_of_injective e.injective _
  have hG:G=transform (C (m t)) (C (targetA F.curve R)) 1 (C (targetB F.curve R)) F.d f :=rfl
  have htop: (G.coeff F.d).coeff 0≠0:= by
    have he (g:F.curve.E[X]) : (e.toRingHom g).eval 0=g.eval (m R.center) := by
      change (taylor (m R.center) g).eval 0= _
      rw [taylor_eval,zero_add]
    rw [hG,transform_top,coeff_zero_eq_eval_zero]
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_map_le :
      (F.f.map (evalRingHom (m R.center))).natDegree≤F.d))] at ht
    change (evalRingHom (0:F.curve.E))
      (∑ i∈range (F.d+1),f.coeff i*C (m t)^i*(1 :F.curve.E[X])^(F.d-i))≠0
    simpa only [map_sum,map_mul,map_pow,map_one,one_pow,mul_one,f,coeff_map,
      coe_evalRingHom,he,eval_C] using ht
  have hd:G.natDegree=F.d:=le_antisymm (hG ▸ transform_degree _ _ _ _ _ _)
    (le_natDegree_of_ne_zero fun h=>htop (by rw [h,coeff_zero]))
  have hFpos :0<F.d:= by
    have h:=natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible F.irreducible)
    rwa [natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _] at h
  have hpos :0<G.natDegree :=hd.symm ▸ hFpos
  change G.natDegree=F.d∧G.leadingCoeff.coeff 0≠0∧polarResultant G≠0
  refine ⟨hd,by simpa only [leadingCoeff,hd] using htop,result_nonzero G hpos (hd ▸ hp) ?_⟩
  by_cases h:2≤F.d
  · let B:=m t*targetB F.curve R - targetA F.curve R
    have hu:C B⁻¹*(C (m t)*C (targetB F.curve R) - C (targetA F.curve R)*1)=1 := by
      simpa only [map_mul,map_sub,map_one,mul_one,B] using
        congrArg (C:F.curve.E →+* F.curve.E[X]) (inv_mul_cancel₀ hdet)
    have hF:=(F.primitive.irreducible_iff_irreducible_map_fraction_map
      (K:=FractionRing F.curve.E[X])).mpr F.irreducible
    have hi:Irreducible f :=(MulEquiv.irreducible_iff (Polynomial.mapEquiv e).toMulEquiv).mpr hF
    have hr :Irreducible G:= by
      rw [hG,← hf]
      exact (transform_irred _ _ _ _ _ hu hi (hf ▸ h)).1
    exact ((hr.isPrimitive hpos.ne').irreducible_iff_irreducible_map_fraction_map
      (K:=FractionRing F.curve.E[X])).mp hr
  · apply irreducible_of_degree_eq_one
    apply (degree_eq_iff_natDegree_eq_of_pos (by decide)).mpr
    rw [natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _,hd]
    exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge h)) hFpos
private theorem form_bound {E :Type} [Field E] (v :Valuation E ℤᵐ⁰)
   {a b:E[X]} {B:ℤᵐ⁰} (ha :adG v a≤B) (hb:adG v b≤B) :
   gauss v (form a b)≤B:= by
 unfold form
 apply (gauss v).map_add_le
 · rwa [efe]
 · rwa [map_mul,gauss_X,mul_one,efe]
private theorem chart_bound {E :Type} [Field E] [Algebra L E] (v :CurvePlace L E)
    (f :E[X][X]) (x t:L) (a b:E) (n:ℕ) {h k :ℕ}
    (hf :aFA v.value f h) (ha :v.value a≤WithZero.exp (k :ℤ))
    (hb:v.value b≤WithZero.exp (k :ℤ)) :
    aFA v.value (transform (C (algebraMap L E t)) (C a) 1 (C b) n
      (f.map (taylorAlgHom (algebraMap L E x)).toRingHom)) (h+n*k) := by
  let g:=gauss v.value
  let H :=WithZero.exp (h:ℤ)
  let B:=WithZero.exp (k :ℤ)
  let f' := f.map (taylorAlgHom (algebraMap L E x)).toRingHom
  let P:=form (C (algebraMap L E t)) (C a)
  let Q:=form (1 :E[X]) (C b)
  have hB:1≤B:=WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg _)
  have hP:g P≤B:=form_bound v.value
    ((cTA _ _).trans_le ((const_bound v t).trans hB)) ((cTA _ _).trans_le ha)
  have hQ:g Q≤B:=form_bound v.value (by
    change efc v.value 1≤B
    rwa [map_one]) ((cTA _ _).trans_le hb)
  intro i j
  refine (coeff_gauss v.value _ i j).trans ?_
  change g (transform (C (algebraMap L E t)) (C a) 1 (C b) n f')≤_
  have hF:g (transform (C (algebraMap L E t)) (C a) 1 (C b) n f')≤H*B^n:= by
    rw [transform_sum]
    apply g.map_sum_le
    intro l hl
    have hTi:g (C (f'.coeff l))≤H := by
      rw [efe,coeff_map]
      exact gauss_taylor v.value (const_bound v x) (hf l)
    change g (C (f'.coeff l)*P^l*Q^(n-l))≤_
    rw [map_mul,map_mul,map_pow,map_pow]
    calc
      _≤H*B^l*B^(n-l) :=mul_le_mul'
        (mul_le_mul' hTi (pow_le_pow_left' hP _)) (pow_le_pow_left' hQ _)
      _ = _:= by rw [mul_assoc,← pow_add,Nat.add_sub_of_le (mem_range_succ_iff.mp hl)]
  simpa only [H,B,← WithZero.exp_nsmul,← WithZero.exp_add,Nat.cast_add,Nat.cast_mul,
    nsmul_eq_mul,mul_comm (k :ℤ)] using hF
theorem proof :qxDtRld.c1 := by
  classical
  intro D w U s z q J F V hp R hm
  obtain ⟨t,ht,ha⟩:=complement V R
  obtain ⟨γ,hγ,hr⟩:=hm
  obtain ⟨hd,hl,hs⟩:=shape R t hp ht
    (determinant R t (mem_filter.mp (V.Bp hγ)).1 (ha γ hγ hr))
  refine ⟨t,hd,hl,hs,ha,?_,?_⟩
  · intro v
    apply chart_bound v F.f R.center t _ _ F.d (qrezXJe.sheet_bound v.value F.f)
    all_goals
      by_cases hz :R.b=0∧R.d=0
      · rw [seedPole,ite_eq_left hz]
        simpa only [targetA,targetB,hz.1,hz.2,map_zero,
          zero_mul,add_zero,Nat.cast_zero,WithZero.exp_zero] using const_bound v _
      · apply target_bound
        rw [seedPole,ite_eq_right hz]
        exact WithZero.le_exp_of_log_le (Int.self_le_toNat _)
  · intro γ hγ _
    let hU:=(mem_filter.mp (V.Bp hγ)).1
    let v :=F.place γ
    let u:F.curve.E :=F.scale γ
    obtain ⟨arc,hs,_,_⟩:=F.arc γ hU
    have hseed :v.value (F.curve.seed R.coord)≤WithZero.exp (0:ℤ) := by
      rw [WithZero.exp_zero,F.value γ hU,hs]
      exact (LaurentSeries.val_le_one_iff_eq_coe L _).mpr ⟨arc R.coord,rfl⟩
    have hf :aFA v.value (nY u F.f) 0:= by
      intro i j
      simpa only [nY,coeff_C_mul,Nat.cast_zero,WithZero.exp_zero] using F.integral γ hU i j
    let τ:=(taylorAlgHom (algebraMap L F.curve.E R.center)).toRingHom
    have hτ: (nY u F.f).map τ=C (C u)*F.f.map τ:= by
      rw [nY,Polynomial.map_mul,Polynomial.map_C,show τ (C u)=C u from taylor_C _ _]
    have h:=chart_bound v (nY u F.f) R.center t (targetA F.curve R) (targetB F.curve R) F.d hf
      (target_bound v hseed R.a R.b) (target_bound v hseed R.c R.d)
    change aFA v.value (transform (C (algebraMap L F.curve.E t)) (C (targetA F.curve R))
      1 (C (targetB F.curve R)) F.d ((nY u F.f).map τ)) (0+F.d*0) at h
    rw [hτ,transform_scale,Nat.mul_zero,Nat.add_zero] at h
    exact h
end
end q7KvxZa
end
