import ProximityPrize.SubmissionLower.ZvFqJTb
import ProximityPrize.SubmissionLower.ZhyMlza
import ProximityPrize.SubmissionLower.ZTNQi7d
import ProximityPrize.SubmissionLower.ZXTI5ee
import ProximityPrize.SubmissionLower.ZfWgThc
import ProximityPrize.SubmissionLower.ZZpExZa
set_option Elab.async false
open _root_ renaming IsFractionRing.injective → zxb, Polynomial.X → z7y, Polynomial.map_injective → zTo, Polynomial.map_mul → zNl, Polynomial.map_zero → zgY
section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace qOj34lc
noncomputable section
open Polynomial Finset
open P5 (p)
open cu (L)
open qziIa4d (scaledChart)
open qFD8jve (polarResultant aaD)
open qwGrtCa (transform form transform_sum transform_irred transform_inverse)
open private subst subst_comp rehom ew dehom_degree subst_homogeneous from ProximityPrize.SubmissionLower.ZjSNLAa
open private top from ProximityPrize.SubmissionLower.ZvFqJTb
variable {E :Type} [Field E]
private theorem transform_map {A B:Type} [CommRing A] [CommRing B] (m:A →+* B)
  (a b c d:A) (n:ℕ) (f :A[X]) :
  (transform a b c d n f).map m=transform (m a) (m b) (m c) (m d) n (f.map m) := by
 simp only [transform_sum,Polynomial.map_sum,zNl,Polynomial.map_pow,
  Polynomial.map_C,coeff_map,form,Polynomial.map_add,Polynomial.map_X]
private theorem transform_scale {A:Type} [CommRing A] (a b c d u:A) (n:ℕ) (f :A[X]) :
  transform a b c d n (C u*f)=C u*transform a b c d n f := by
 simp only [transform_sum,coeff_C_mul,map_mul,Finset.mul_sum,mul_assoc]
private def GV (f :E[X][X]) (x :E) :E[X][X] :=
 f.map (taylorAlgHom x).toRingHom
private theorem centered_degree (f :E[X][X]) (x :E) :
  (GV f x).natDegree=f.natDegree :=
 natDegree_map_eq_of_injective (taylorEquiv x).injective _
private def ic (f :E[X][X]) (x a b:E) :E[X][X] :=
 transform (C b*z7y) (C a) 0 (C b) f.natDegree (GV f x)
private theorem scaled_eq (f :E[X][X]) (x t a b:E) :
   scaledChart f x t a b =
     transform (C a+C (b*t)*z7y) (C b*z7y) (C b) 0 f.natDegree (GV f x) := by
 rw [scaledChart,transform_sum,sum_over_range]
 · simp only [GV,coeff_map,AlgHom.toRingHom_eq_coe,
     form,map_zero,zero_add]
   rfl
 · simp
private theorem scaled_comp (f :E[X][X]) (x t a b:E) :
  scaledChart f x t a b=transform (C t) 1 1 0 f.natDegree (ic f x a b) := by
 rw [scaled_eq]
 unfold ic
 change
  ew (subst _ _ _ _ ((GV f x).homogenize f.natDegree)) =
  ew (subst _ _ _ _ ((transform _ _ _ _ _ _).homogenize f.natDegree))
 rw [rehom,← AlgHom.comp_apply (subst (C t) 1 1 0) (subst (C b*z7y) (C a) 0 (C b)),
  subst_comp]
 simp only [mul_zero,zero_mul,mul_one,add_zero,zero_add]
 rw [show C b*z7y*C t+C a=C a+C (b*t)*z7y by
  rw [Polynomial.C_mul]
  ring]
private theorem strip (H :E[X][X]) (hH :H≠0) :
  ∃ n:ℕ,∃ J:E[X][X],H=C ((z7y:E[X])^n)*J∧aaD J≠0:= by
 classical
 have hx : ∃ j:ℕ,∃ i:ℕ,((H.coeff i).coeff j)≠0:= by
  obtain ⟨i,hi⟩:=support_nonempty.mpr hH
  obtain ⟨j,hj⟩:=support_nonempty.mpr (mem_support_iff.mp hi)
  exact ⟨j,i,mem_support_iff.mp hj⟩
 let n:=Nat.find hx
 have hd:C ((z7y:E[X])^n)∣H := by
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply X_pow_dvd_iff.mpr
  intro j hj
  by_contra h
  exact Nat.find_min hx hj ⟨i,h⟩
 obtain ⟨J,hJ⟩:=hd
 refine ⟨n,J,hJ,?_⟩
 obtain ⟨i,hi⟩:=Nat.find_spec hx
 intro hz
 apply hi
 have h:=congrArg (fun F:E[X]=>F.coeff i) hz
 have he :=congrArg (fun F:E[X][X]=>(F.coeff i).coeff (0+n)) hJ
 change (H.coeff i).coeff (0+n)=((C ((z7y:E[X])^n)*J).coeff i).coeff (0+n) at he
 rw [coeff_C_mul,coeff_X_pow_mul,zero_add] at he
 refine he.trans ?_
 simpa only [aaD,coeff_map,coe_evalRingHom,coeff_zero,coeff_zero_eq_eval_zero] using h
theorem choose_chart (f :E[X][X]) (x a b:E) (hb:b≠0) (bad:Finset L)
    [Algebra L E] (hf :f≠0) :
    ∃ t:L,t∉bad ∧ ∃ n:ℕ,∃ G:E[X][X],
      scaledChart f x (algebraMap L E t) a b=C ((z7y:E[X])^n)*G ∧
      G.natDegree=f.natDegree∧G.leadingCoeff.coeff 0≠0:= by
  classical
  let g:=GV f x
  let H :=ic f x a b
  let i:E[X] →+* FractionRing E[X] :=algebraMap _ _
  have hi:=zxb E[X] (FractionRing E[X])
  have hH :H≠0:= by
    intro h
    have hmap :H.map i=0:= by rw [h,zgY]
    change (transform (C b*z7y) (C a) 0 (C b) f.natDegree g).map i=0 at hmap
    rw [transform_map,map_zero] at hmap
    let D:=i (C b*z7y)*i (C b) - i (C a)*0
    have hD:D ≠0:= by
      simp only [D,mul_zero,sub_zero]
      exact mul_ne_zero ((map_ne_zero_iff i hi).mpr (mul_ne_zero (C_ne_zero.mpr hb) X_ne_zero))
        ((map_ne_zero_iff i hi).mpr (C_ne_zero.mpr hb))
    have hinv :=transform_inverse _ _ _ _ _ (inv_mul_cancel₀ hD)
      (f :=g.map i) ((natDegree_map_eq_of_injective hi g).trans (centered_degree f x)).le
    change transform _ _ _ _ _ (transform (i (C b*z7y)) (i (C a)) 0 (i (C b))
      f.natDegree (g.map i))= _ at hinv
    rw [hmap] at hinv
    have hz :g.map i=0:= by
      rw [← hinv,transform,homogenize_zero,map_zero,map_zero]
    have hg:g=0:=zTo i hi (hz.trans (zgY i).symm)
    apply hf
    apply zTo (taylorAlgHom x).toRingHom (taylor_injective x)
    rw [zgY]
    exact hg
  obtain ⟨n,J,hJ,hj⟩:=strip H hH
  let m:=algebraMap L E
  have hroots : (m ⁻¹' {u | (aaD J).IsRoot u}).Finite :=
    (finite_setOfPred_isRoot hj).preimage m.injective.injOn
  obtain ⟨t,_,ht⟩:=(Set.infinite_univ : (Set.univ :Set L).Infinite).exists_notMem_finite
    (hroots.union bad.finite_toSet)
  let G:=transform (C (m t)) 1 1 0 f.natDegree J
  have hJle :J.natDegree≤f.natDegree := by
    have he :H.natDegree=J.natDegree := by rw [hJ,natDegree_C_mul (pow_ne_zero n X_ne_zero)]
    rw [← he]
    exact (dehom_degree _).trans ((subst_homogeneous (isHomogeneous_homogenize g) _ _ _ _).totalDegree_le)
  obtain ⟨hle,htop⟩:=top (C (m t)) (1 :E[X]) 0 _ J hJle
  have hz : (G.coeff f.natDegree).coeff 0≠0:= by
    rw [show G.coeff f.natDegree= _ from htop,coeff_zero_eq_eval_zero]
    rw [← coe_evalRingHom,← eval_map_apply,coe_evalRingHom,eval_C]
    exact fun h=>ht (Or.inl h)
  have hdeg:G.natDegree=f.natDegree :=
    hle.antisymm (le_natDegree_of_ne_zero fun h=>hz (by rw [h,coeff_zero]))
  refine ⟨t,fun h=>ht (Or.inr h),n,G,?_,hdeg,?_⟩
  · rw [scaled_comp,← show H=ic f x a b from rfl,hJ,transform_scale]
  · simpa only [leadingCoeff,hdeg] using hz
theorem chart_separant [CharP E p] {f G:E[X][X]} (x t a b:E) (hb:b≠0)
    (hf :Irreducible f) (hd:0<f.natDegree) (hp:f.natDegree<p)
    {n:ℕ} (hG:scaledChart f x t a b=C ((z7y:E[X])^n)*G)
    (hdeg:G.natDegree=f.natDegree) :polarResultant G≠0:= by
  let i:E[X] →+* FractionRing E[X] :=algebraMap _ _
  have hi:=zxb E[X] (FractionRing E[X])
  let _:CharP (FractionRing E[X]) p:=charP_of_injective_ringHom hi p
  let f₀:=GV f x
  let g:=f₀.map i
  have hd₀:f₀.natDegree=f.natDegree :=centered_degree f x
  have hdg:g.natDegree=f.natDegree :=(natDegree_map_eq_of_injective hi _).trans hd₀
  have hdG: (G.map i).natDegree=f.natDegree :=(natDegree_map_eq_of_injective hi _).trans hdeg
  have hpos :0<(G.map i).natDegree :=hdG ▸ hd
  have hgi:Irreducible (G.map i) := by
    by_cases htwo:2≤f.natDegree
    · have hir₀:Irreducible f₀ :=
        (MulEquiv.irreducible_iff (Polynomial.mapEquiv (taylorEquiv x).toRingEquiv).toMulEquiv).mpr hf
      have hir :Irreducible g :=
        ((hir₀.isPrimitive (hd₀ ▸ hd).ne').irreducible_iff_irreducible_map_fraction_map
          (K:=FractionRing E[X])).mp hir₀
      have he :=congrArg (Polynomial.map i) hG
      rw [scaled_eq,transform_map,map_zero,zNl,Polynomial.map_C] at he
      let D:=i (C a+C (b*t)*z7y)*0-i (C b*z7y)*i (C b)
      have hD:D ≠0:= by
        simp only [D,mul_zero,zero_sub,neg_ne_zero]
        exact mul_ne_zero ((map_ne_zero_iff i hi).mpr (mul_ne_zero (C_ne_zero.mpr hb) X_ne_zero))
          ((map_ne_zero_iff i hi).mpr (C_ne_zero.mpr hb))
      have hT:=(transform_irred _ _ _ _ _ (inv_mul_cancel₀ hD) hir (hdg ▸ htwo)).1
      rw [hdg] at hT
      rw [he] at hT
      have hu:IsUnit (C (i ((z7y:E[X])^n))) :=
        isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff i hi).mpr (pow_ne_zero n X_ne_zero)))
      exact (irreducible_isUnit_mul hu).mp hT
    · apply irreducible_of_degree_eq_one
      rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hpos),hdG]
      exact_mod_cast (show f.natDegree=1 by omega)
  have hder :=qrezXJe.bD9 hpos (hdG ▸ hp)
  have hs : (G.map i).Separable :=(separable_iff_derivative_ne_zero hgi).mpr fun hz=> by
    have h:=coeff_derivative (G.map i) ((G.map i).natDegree-1)
    rw [hz,coeff_zero,← Nat.cast_succ,Nat.succ_eq_add_one,Nat.sub_add_cancel hpos,← leadingCoeff] at h
    exact (mul_ne_zero (leadingCoeff_ne_zero.mpr hgi.ne_zero)
      (qrezXJe.cast_ne_zero hpos (hdG ▸ hp))) h.symm
  have hr :=resultant_ne_zero _ _ hs
  rw [hder,natDegree_map_eq_of_injective hi G,derivative_map,resultant_map_map] at hr
  exact fun h=>hr (by change i (polarResultant G)=0; rw [h,map_zero])
end
end qOj34lc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qOj34lc
noncomputable section
open Polynomial Finset
open scoped WithZero
open P5 (K p)
open cu (L j9)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet targetHit)

open qb0hmCe (CurveModel SiteTarget)
open qFD8jve (seedPole)
open E7 (CurvePlace)
variable {q:PlaneCurve} {C₀:CurveModel q} {z :K→K} {S:K→K[X]}
private theorem coords (F:Sheet C₀ z S) (R:SiteTarget) {γ:K} (hγ:γ∈F.marks) :
   let m:=algebraMap L C₀.E
   let s :=C₀.seed R.coord
   let a :=m R.a+m R.b*s
   let b:=m R.c+m R.d*s
   (F.place γ).value a≤1∧(F.place γ).value b≤1 ∧
     (targetHit R z S γ→b≠0) := by
 obtain ⟨g,hg,hres,_⟩:=F.arc γ hγ
 let φ:=F.atPlace γ hγ
 let m:=algebraMap L C₀.E
 let s :=C₀.seed R.coord
 have h (u v :L) :
     φ (m u+m v*s)=((PowerSeries.C u+PowerSeries.C v*g R.coord:PowerSeries L) :LaurentSeries L) := by
   rw [map_add,map_mul,φ.commutes,φ.commutes,show φ s= _ from hg R.coord]
   simp only [PowerSeries.coe_add,PowerSeries.coe_mul,PowerSeries.coe_C,
     LaurentSeries.algebraMap_apply]
 have hint (u v :L) : (F.place γ).value (m u+m v*s)≤1 := by
   rw [F.value γ hγ,show F.atPlace γ hγ (m u+m v*s)= _ from h u v]
   exact (LaurentSeries.val_le_one_iff_eq_coe L _).mpr ⟨_,rfl⟩
 refine ⟨hint _ _,hint _ _,fun hh hb=>hh.1 ?_⟩
 have he :=(h R.c R.d).symm.trans (show φ (m R.c+m R.d*s)=0 by rw [hb,map_zero])
 have he' := (q1kuFjb.power_residue (0:LaurentSeries L) _ (by simpa only [eq_comm] using he))
 simpa only [HahnSeries.coeff_zero,map_add,map_mul,PowerSeries.constantCoeff_C,hres,
   eq_comm] using he'
private theorem const_bound (w:CurvePlace L C₀.E) (u:L) :
   w.value (algebraMap L C₀.E u)≤1 := by
 by_cases hu:u=0
 · simp [hu]
 · exact (w.on_constants u hu).le
theorem proof :qziIa4d.c1 := by
  classical
  intro q C₀ z S F V hp R hm
  let m:=algebraMap L C₀.E
  let s :=C₀.seed R.coord
  let a :=m R.a+m R.b*s
  let b:=m R.c+m R.d*s
  let bad:=V.marks.image fun γ=>(j9 (S γ)).derivative.eval R.center
  obtain ⟨γ,hg,hh⟩:=hm
  have hb:b≠0:=(coords F R (V.Bp hg)).2.2 hh
  obtain ⟨t,ht,n,G,he,hdeg,hlead⟩ :=
    choose_chart F.f (m R.center) a b hb bad F.irreducible.ne_zero
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let _:CharP C₀.E p:=charP_of_injective_ringHom m.injective p
  refine ⟨⟨t,n,G,he,?_,hdeg,hlead,
    chart_separant _ _ _ _ hb F.irreducible F.positive hp he hdeg,?_,?_⟩⟩
  · intro η hη _ h
    exact ht (mem_image.mpr ⟨η,hη,h⟩)
  · intro w
    let B:=WithZero.exp (seedPole C₀ R w.value :ℤ)
    have hB:1≤B:= by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (Int.natCast_nonneg _)
    have h (u v :L) (hv :v=0 ∨ ¬ (R.b=0∧R.d=0)) :
        w.value (m u+m v*s)≤B:= by
      rcases hv with rfl | hv
      · simpa only [map_zero,zero_mul,add_zero] using (const_bound w u).trans hB
      · have hs :w.value s≤B:= by
          dsimp [B]
          rw [seedPole,ite_eq_right hv]
          exact WithZero.le_exp_of_log_le (Int.self_le_toNat _)
        apply w.value.map_add_le ((const_bound w u).trans hB)
        rw [map_mul,← one_mul B]
        exact mul_le_mul' (const_bound w v) hs
    exact chart_bound w.value (qrezXJe.sheet_bound _ _) (const_bound w _) (const_bound w _)
      (h _ _ (or_iff_not_imp_left.mpr fun h hb=>h hb.1))
      (h _ _ (or_iff_not_imp_left.mpr fun h hb=>h hb.2)) he
  · intro η hη _
    let w:=F.place η
    have ⟨ha,hb,_⟩:=coords F R (V.Bp hη)
    simpa only [Nat.mul_zero,Nat.add_zero] using
      chart_bound w.value (h:=0) (k :=0)
        (fun i j=> by simpa using F.integral η (V.Bp hη) i j)
        (const_bound w _) (const_bound w _) (by simpa using ha) (by simpa using hb) he
end
end qOj34lc
end
