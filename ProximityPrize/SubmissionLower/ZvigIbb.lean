import ProximityPrize.SubmissionLower.ZkL5N7c
set_option Elab.async false
open _root_ renaming Function.Injective → zq4, IsFractionRing.injective → zxb, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.mapRingHom → zhd, Polynomial.map_add → zS4, Polynomial.map_mul → zNl, Polynomial.map_neg → zsq, Polynomial.map_sum → zWe, Polynomial.map_zero → zgY, PowerSeries → zpm, PowerSeries.constantCoeff → zbO, PowerSeries.constantCoeff_C → zr8, RingHom.id → zz4
set_option maxHeartbeats 750000
section
set_option backward.isDefEq.respectTransparency false
namespace q1XeJwa
noncomputable section
open Polynomial Finset
open P5 (K I)
open cu (L)
open E7 (CurveField CurvePlace axV poleOrder KB)
open agN (b27)
open q82zwcd (WordChart)
open qb0hmCe (coeffHeight)
open qFD8jve (sheetPole)
open qwGrtCa (transform_sum form)
open private gauss₂ gauss₂_normal coeff_le_gauss₂ from ProximityPrize.SubmissionLower.ZhEC96c
open private adG cTA cTB b4s bHf from ProximityPrize.SubmissionLower.Y
open scoped WithZero
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
variable {E :Type} [Field E]
private theorem gauss_const (v :Valuation E ℤᵐ⁰) (a :E[X]) :
  gauss₂ v (C a)=adG v a := by
 change adG (b4s v) ((C a :E[X][X]).map _)= _
 rw [map_C,cTA,bHf]
private theorem gauss_X (v :Valuation E ℤᵐ⁰) :gauss₂ v (z7y:E[X][X])=1 := by
 change adG (b4s v) ((z7y:E[X][X]).map _)= _
 simp [adG]
variable [Algebra L E]
private theorem gauss_changed (v :CurvePlace L E) (J:WordChart D w U s) (f :E[X][X]) :
  gauss₂ v.value (changed J f)≤gauss₂ v.value f := by
 let m:=zhd (algebraMap L E)
 let u:=gauss₂ v.value
 have hc (a :L[X]) :u (C (m a))≤1 := by
  change gauss₂ v.value (C (a.map (algebraMap L E)))≤1
  rw [gauss_const]
  by_cases h:a=0
  · simp [h,adG]
  · exact (cTB v a h).le
 have hform (a b:L[X]) :u (form (m a) (m b))≤1 := by
  unfold form
  apply (u.map_add _ _).trans
  rw [map_mul,show u (z7y:E[X][X])=1 from gauss_X v.value,mul_one]
  exact max_le (hc b) (hc a)
 have hf (i:ℕ) :u (C (f.coeff i))≤u f := by
  change gauss₂ v.value (C (f.coeff i))≤_
  rw [gauss_const]
  exact Finset.sup_le fun j _=>coeff_le_gauss₂ v.value f i j
 unfold changed
 rw [transform_sum]
 change u (∑ i∈range (f.natDegree+1),C (f.coeff i) *
  form (m J.b₀) (-m J.b₁)^i*form (-m J.a₀) (m J.a₁)^(f.natDegree-i))≤u f
 apply u.map_sum_le
 intro i _
 simp only [map_mul,map_pow,← map_neg m]
 have hn (a b:L[X]) (n:ℕ) :u (form (m a) (m b))^n≤1 :=
  pow_le_one₀ zero_le (hform a b)
 calc
  _≤u f*1*1 :=mul_le_mul' (mul_le_mul' (hf i) (hn _ _ _)) (hn _ _ _)
  _ = _:= by simp
theorem height_le (J:WordChart D w U s) (f G:E[X][X]) (a :E[X])
   (hF:f.leadingCoeff.leadingCoeff=1) (hG:G.leadingCoeff.leadingCoeff=1)
   (ha :a≠0) (he :changed J f=C a*G) (hc:CurveField L E) :
   coeffHeight G≤ coeffHeight f := by
 obtain ⟨j,hj⟩:=Polynomial.support_nonempty.mpr ha
 have hj' := Polynomial.mem_support_iff.mp hj
 let t:=a.coeff j
 let P (v :CurvePlace L E) :=sheetPole v.value f
 let Q (v :CurvePlace L E) :=sheetPole v.value G
 let A (v :CurvePlace L E) :=poleOrder v.value t
 let B (v :CurvePlace L E) :=KB v.value t
 have hlocal (v :CurvePlace L E) :A v+Q v≤P v+B v := by
   let u:=gauss₂ v.value
   have ht:v.value t≤u (C a) := by
     simpa only [t,coeff_C_zero] using coeff_le_gauss₂ v.value (C a) 0 j
   have h:=gauss_changed v J f
   rw [he,map_mul,gauss₂_normal v.value G hG,gauss₂_normal v.value f hF] at h
   have h' : v.value t*WithZero.exp (Q v :ℤ)≤WithZero.exp (P v :ℤ) :=
     (mul_le_mul' ht le_rfl).trans h
   conv_lhs at h' => rw [← WithZero.exp_log (v.value.ne_zero_iff.mpr hj'),← WithZero.exp_add]
   rw [WithZero.exp_le_exp] at h'
   change WithZero.log (v.value t)+(Q v :ℤ)≤(P v :ℤ) at h'
   change (WithZero.log (v.value t)).toNat+Q v≤P v+(-WithZero.log (v.value t)).toNat
   omega
 have hdiv :axV L E :=aFU.of_children
   bRt.proof bRu.proof L E hc
 obtain ⟨hA,hB,hab,_⟩:=hdiv t
 have hP:P.HasFiniteSupport:=b27 hdiv _
 have hQ:Q.HasFiniteSupport:=b27 hdiv _
 have h:=finsum_le_finsum (hA.add hQ) (hP.add hB) hlocal
 change (∑ᶠ v,(A v+Q v))≤(∑ᶠ v,(P v+B v)) at h
 rw [finsum_add_distrib hA hQ,finsum_add_distrib hP hB,← hab,add_comm (∑ᶠ v,P v)] at h
 exact Nat.le_of_add_le_add_left h
end
end q1XeJwa
end
section
set_option backward.isDefEq.respectTransparency false
namespace q1XeJwa
noncomputable section
open Polynomial
open P5 (K I)
open cu (L)
open q82zwcd (WordChart)
open qwGrtCa (transform transform_sum transform_irred)
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
variable {E :Type} [Field E] [Algebra L E]
theorem changed_irreducible (J:WordChart D w U s) (f :E[X][X])
    (hf :Irreducible (f.map (algebraMap E[X] (FractionRing E[X]))))
    (hd:2≤f.natDegree) :
    Irreducible ((changed J f).map (algebraMap E[X] (FractionRing E[X]))) ∧
      (changed J f).natDegree=f.natDegree := by
  let ι:E[X] →+* FractionRing E[X] :=algebraMap _ _
  let m:=(zhd (algebraMap L E))
  let η:=ι.comp m
  have hi:zq4 ι:=zxb E[X] (FractionRing E[X])
  have he : (f.map ι).natDegree=f.natDegree :=natDegree_map_eq_of_injective hi f
  obtain ⟨c,hc,hJ⟩:=J.determinant
  have hn:J.a₀*J.b₁-J.a₁*J.b₀≠0:= by
    rw [hJ]
    exact mul_ne_zero (C_ne_zero.mpr hc) (q20JTGa.locator_ne Finset.univ)
  have hn' : η J.b₀*η J.a₁-(-η J.b₁)*(-η J.a₀)≠0:= by
    have hdet:η J.b₀*η J.a₁-(-η J.b₁)*(-η J.a₀) =
        -η (J.a₀*J.b₁-J.a₁*J.b₀) := by
      simp only [map_sub,map_mul]
      ring
    rw [hdet]
    have hm:zq4 m:=Polynomial.map_injective _ (algebraMap L E).injective
    exact neg_ne_zero.mpr ((map_ne_zero_iff η (hi.comp hm)).mpr hn)
  have hm: (changed J f).map ι =
      transform (η J.b₀) (-η J.b₁) (-η J.a₀) (η J.a₁) (f.map ι).natDegree (f.map ι) := by
    rw [he,changed,transform_sum,transform_sum,zWe]
    apply Finset.sum_congr rfl
    intro i _
    simp only [zNl,Polynomial.map_pow,qwGrtCa.form,zS4,
      map_C,zsq,map_neg,map_X,coeff_map,RingHom.comp_apply,η,m]
  obtain ⟨hf',hd'⟩:=transform_irred _ _ _ _ _ (inv_mul_cancel₀ hn') hf (he.symm ▸ hd)
  rw [← hm,natDegree_map_eq_of_injective hi,he] at hd'
  exact ⟨hm ▸ hf',hd'⟩
omit [Algebra L E] in
theorem ccE (F:E[X][X])
   (hF:Irreducible (F.map (algebraMap E[X] (FractionRing E[X])))) :
   ∃ (G:E[X][X]) (a :E[X]),a≠0∧F=C a*G ∧
     G.IsPrimitive∧Irreducible (G.map (algebraMap E[X] (FractionRing E[X]))) ∧
     G.leadingCoeff.leadingCoeff=1∧G.natDegree=F.natDegree := by
 let ι:E[X] →+* FractionRing E[X] :=algebraMap _ _
 have hF0:F≠0:= fun h=>hF.ne_zero (by rw [h,zgY])
 let:NormalizationMonoid E[X] :=Classical.arbitrary _
 let:NormalizedGCDMonoid E[X] :=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
 let f :=F.primPart
 have h:=F.eq_C_content_mul_primPart
 have hf :f≠0:=right_ne_zero_of_mul (h ▸ hF0)
 have hc:F.content≠0:=C_ne_zero.mp (left_ne_zero_of_mul (h ▸ hF0))
 let c:=f.leadingCoeff.leadingCoeff
 have hc' : c≠0:=leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf)
 let G:=qZfVj1b.normalize f
 let a :=F.content*C c
 have ha :a≠0:=mul_ne_zero hc (C_ne_zero.mpr hc')
 have hG:F=C a*G:= by
   change F=C (F.content*C c)*(C (C c⁻¹)*f)
   rw [← mul_assoc,← map_mul,mul_assoc,← map_mul,mul_inv_cancel₀ hc',
     map_one,mul_one]
   exact h
 have hI:Irreducible (G.map ι) := by
   have hu:IsUnit (C (ι a)) :=
     isUnit_C.mpr (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff ι (zxb E[X] (FractionRing E[X]))).mpr ha))
   apply (irreducible_isUnit_mul hu).mp
   rwa [← map_C,← zNl,← hG]
 have hp:G.IsPrimitive := by
   apply isPrimitive_of_dvd F.isPrimitive_primPart
   refine ⟨C (C c),?_⟩
   change f=C (C c⁻¹)*f*C (C c)
   rw [mul_right_comm,← map_mul,← map_mul,inv_mul_cancel₀ hc',map_one,map_one,one_mul]
 have hnorm:G.leadingCoeff.leadingCoeff=1 := by
   change (C (C c⁻¹)*f).leadingCoeff.leadingCoeff=1
   rw [leadingCoeff_mul,leadingCoeff_C,leadingCoeff_mul,leadingCoeff_C,
     inv_mul_cancel₀ hc']
 exact ⟨G,a,ha,hG,hp,hI,hnorm,by rw [hG,natDegree_C_mul ha]⟩
end
end q1XeJwa
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace q1XeJwa
noncomputable section
open Polynomial Finset
open scoped Classical WithZero
open P5 (K p)
open cu (L)
open E7 (CurvePlace)
open Cu


open q82zwcd (WordChart DualSheet)

open qZfVj1b (ChartPlace gRK)
open qb0hmCe (CurveModel coeffHeight cLN specialize)
open q1kuFjb (small_valuation)
open quN7Z4a (Sheet)
open qBajpRb (cls)




open private normal_degree normal_monic normal_irreducible from ProximityPrize.SubmissionLower.ZPaaHRd
attribute [local instance] gRK
local notation "normal" => qZfVj1b.normalize
set_option backward.isDefEq.respectTransparency true in
def c1 :Prop :=
  ∀ {D w U s z q g H J} [Fact (Irreducible q)] (C:WordChart D w U s)
    (S:Sheet q J g H U z s) (G: (oO q)[X][X])
    (a : (oO q)[X]),a≠0 →
    changed C (normal S.root.equation)=z1z a*G →
    ∀ γ (hγ:γ∈U) (A:ChartPlace S.bY (S.onBase γ hγ)),
      ∃ u: (oO q)ˣ,
        (∀ i j,A.place.value ((u:oO q)*((G.coeff i).coeff j))≤1) ∧
        cLN A.map 0 (z1z (z1z (u:oO q))*G)≠0 ∧
        specialize (cLN A.map 0 (z1z (z1z (u:oO q))*G))
          (C.P γ) (C.Q γ)=0
private theorem same_label {q:sQ} (Cq:CurveModel q)
   {z t:K} {v :CurvePlace L Cq.E} (a b:Cq.E →ₐ[L] LaurentSeries L)
   (ha : ∀ c,v.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c))
   (hb : ∀ c,v.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (b c))
   (A B:zpm L) (hA:a (Cq.seed 0)=(A:LaurentSeries L))
   (hB:b (Cq.seed 0)=(B:LaurentSeries L))
   (hz :zbO A=algebraMap K L z)
   (ht:zbO B=algebraMap K L t) :z=t:= by
 let c:=Cq.seed 0-algebraMap L Cq.E (algebraMap K L z)
 have hs (m:Cq.E →ₐ[L] LaurentSeries L) (S:zpm L)
     (h:m (Cq.seed 0)=(S:LaurentSeries L)) :
     m c=((S-PowerSeries.C (algebraMap K L z) :zpm L) :LaurentSeries L) := by
   rw [show c= _ from rfl,map_sub,h,m.commutes,PowerSeries.coe_sub,PowerSeries.coe_C,
     LaurentSeries.algebraMap_apply]
 have h:v.value c≤WithZero.exp (-1) := by
   rw [ha,hs a A hA,small_valuation,map_sub,hz,zr8,sub_self]
 rw [hb,hs b B hB,small_valuation,map_sub,ht,zr8,sub_eq_zero] at h
 exact (algebraMap K L).injective h.symm
private theorem dual_sheet (height:qZfVj1b.c2)
    (lift:qZfVj1b.c3) (immerse :qZfVj1b.c4) (localRoot:c1)
    {D w U s z q g H J} [Fact (Irreducible q)] (C:WordChart D w U s)
    (S:Sheet q J g H U z s) (hz :Set.InjOn z (U:Set K))
    (hg:3≤g) (hchar :q.totalDegree*g<p) :
    ∃ F:DualSheet C q z,F.d=g∧F.h≤H := by
  have hg0:0<g:= by omega
  have hq:=(Nat.le_mul_of_pos_right q.totalDegree hg0).trans_lt hchar
  obtain ⟨v,hc,hh⟩:=qxblDlc.curve_field q hq
  let Cq:=seedCurve hc hh
  let f :Cq.E[X][X] :=normal S.root.equation
  have hd:f.natDegree=g:=normal_degree S
  have hp:f.natDegree≠0:=hd.symm ▸ hg0.ne'
  have hf :Irreducible f :=normal_irreducible S
  have hi:=((hf.isPrimitive hp).irreducible_iff_irreducible_map_fraction_map
    (K:=FractionRing Cq.E[X])).mp hf
  obtain ⟨hi',hd'⟩:=changed_irreducible C f hi (hd.symm ▸ (by omega :2≤g))
  obtain ⟨G,a,ha,he,hG,hI,hn,hdeg⟩:=ccE _ hi'
  have hH :coeffHeight G≤H :=
    (height_le C f G a (normal_monic S) hn ha he Cq.curve).trans (height S.bY hc S.height)
  let A (γ:K) (hγ:γ∈U) :=
    Classical.choice (lift S.bY hq hc (z γ) (S.parameter γ) (S.onBase γ hγ))
  let place (γ:K) :=if hγ:γ∈U then (A γ hγ).place else v
  have hv (γ:K) (hγ:γ∈U) :place γ=(A γ hγ).place :=dite_eq_left hγ
  let arc (γ:K) (hγ:γ∈U) (i:Fin 2) :=
    (A γ hγ).series (cls S.bY (MvPolynomial.X (Sum.inl i)))
  have hmap γ (hγ:γ∈U) (i:Fin 2) : (A γ hγ).map (Cq.seed i)=(arc γ hγ i:LaurentSeries L) := by
    rw [show (arc γ hγ i:LaurentSeries L)= _ from (A γ hγ).lift_eq _,
      qBajpRb.incl_cls]
    simp [qBajpRb.ek,Cq,seedCurve]
    rfl
  have hres γ (hγ:γ∈U) (i:Fin 2) :
      zbO (arc γ hγ i)=DP.Z7 (z γ) i:= by
    change zbO ((A γ hγ).series _)= _
    rw [(A γ hγ).reduce,qBajpRb.atMark_cls,MvPolynomial.eval_X]
    rfl
  let scale (γ:K) :=if hγ:γ∈U then Classical.choose (localRoot C S G a ha he γ hγ (A γ hγ)) else 1
  have hscale γ (hγ:γ∈U) :scale γ =
      Classical.choose (localRoot C S G a ha he γ hγ (A γ hγ)) :=dite_eq_left hγ
  let F:DualSheet C q z := {
    curve :=Cq,f :=G,primitive :=hG,irreducible :=hI
    normalized:=hn,atPlace := fun γ hγ=>(A γ hγ).map,place :=place
    distinct := by
      intro γ hγ δ hδ h
      have heq :=(hv γ hγ).symm.trans (h.trans (hv δ hδ))
      exact hz hγ hδ (same_label Cq (A γ hγ).map (A δ hδ).map (A γ hγ).value
        (fun c=>(congrArg (fun v=>CurvePlace.value v c) heq).trans ((A δ hδ).value c))
        (arc γ hγ 0) (arc δ hδ 0) (hmap γ hγ 0) (hmap δ hδ 0)
        (hres γ hγ 0) (hres δ hδ 0))
    value := fun γ hγ c=>(congrArg (fun v=>CurvePlace.value v c) (hv γ hγ)).trans ((A γ hγ).value c)
    arc := fun γ hγ=>⟨arc γ hγ,hmap γ hγ,hres γ hγ,fun h =>
      immerse _ hq (S.onSeed γ hγ) h _ _ (A γ hγ).value _ (hmap γ hγ) (hres γ hγ)⟩
    scale :=scale
    integral:= by
      intro γ hγ i j
      rw [hv γ hγ,hscale γ hγ]
      exact (Classical.choose_spec (localRoot C S G a ha he γ hγ (A γ hγ))).1 i j
    reduction_ne := by
      intro γ hγ
      rw [hscale γ hγ]
      exact (Classical.choose_spec (localRoot C S G a ha he γ hγ (A γ hγ))).2.1
    root := by
      intro γ hγ
      rw [hscale γ hγ]
      exact (Classical.choose_spec (localRoot C S G a ha he γ hγ (A γ hγ))).2.2 }
  exact ⟨F,hdeg.trans (hd'.trans hd),hH⟩
end
end q1XeJwa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qtqYUDc
noncomputable section
open Polynomial Finset
open P5 (K I)
open cu (L FX j9)
open q82zwcd (WordChart)
open P5_7_7 (phys)
open qwGrtCa (transform transform_sum transform_inverse form)
open qb0hmCe (specialize)
open q1kuFjb (mapTwice)
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
variable {R T:Type} [CommRing R] [CommRing T]
def changeAt (J:WordChart D w U s) (b:L →+* R) (n:ℕ) (f :R[X][X]) :R[X][X] :=
 let m:=zhd b
 transform (m J.b₀) (-m J.b₁) (-m J.a₀) (m J.a₁) n f
theorem change_map (J:WordChart D w U s) (b:L →+* R) (m:R →+* T) (n:ℕ)
  (f :R[X][X]) :mapTwice m (changeAt J b n f) =
    changeAt J (m.comp b) n (mapTwice m f) := by
 simp only [changeAt,transform_sum,map_sum,map_mul,map_pow]
 apply sum_congr rfl
 intro i _
 simp only [mapTwice,coe_mapRingHom,map_C,coeff_map,form,zS4,
  zNl,zsq,map_X,Polynomial.map_map]
theorem change_scale (J:WordChart D w U s) (b:L →+* R) (n:ℕ)
  (c:R) (f :R[X][X]) :
  changeAt J b n (C (C c)*f)=C (C c)*changeAt J b n f := by
 simp only [changeAt,transform_sum,coeff_C_mul,map_mul,Finset.mul_sum,mul_assoc]
theorem word_ne (J:WordChart D w U s) (n:ℕ) {f :L[X][X]}
   (hf :f≠0) (hn:f.natDegree≤n) :
   changeAt J (zz4 L) n f≠0:= by
 let a :=phys J.b₀
 let b := -phys J.b₁
 let c := -phys J.a₀
 let d:=phys J.a₁
 have hphys :zq4 phys :=zxb L[X] FX
 obtain ⟨t,ht,hJ⟩:=J.determinant
 have hdet:a*d-b*c≠0:= by
   have h:a*d-b*c = -phys (J.a₀*J.b₁-J.a₁*J.b₀) := by
     simp only [a,b,c,d,map_sub,map_mul]
     ring
   rw [h,hJ]
   exact neg_ne_zero.mpr ((map_ne_zero_iff phys hphys).mpr
     (mul_ne_zero (C_ne_zero.mpr ht) (q20JTGa.locator_ne univ)))
 have hm (g:L[X][X]) : (changeAt J (zz4 L) n g).map phys =
     transform a b c d n (g.map phys) := by
   rw [changeAt,transform_sum,transform_sum,zWe]
   apply sum_congr rfl
   intro i _
   simp [a,b,c,d,form]
 intro h
 have h0:=transform_inverse a b c d (a*d-b*c)⁻¹ (inv_mul_cancel₀ hdet)
   (n:=n) (f :=f.map phys) (by rwa [natDegree_map_eq_of_injective hphys])
 rw [← hm,h,zgY,transform_sum] at h0
 simp only [coeff_zero,map_zero,zero_mul,Finset.sum_const_zero] at h0
 exact hf ((map_injective _ hphys) (h0.symm.trans (zgY _).symm))
theorem word_root (J:WordChart D w U s) (n:ℕ) (f :L[X][X])
   (hn:f.natDegree≤n) {γ:K} (hγ:γ∈U)
   (hr :f.eval (j9 (s γ))=0) :
   specialize (changeAt J (zz4 L) n f) (J.P γ) (J.Q γ)=0:= by
 let y :=phys (J.P γ)/phys (J.Q γ)
 let r :=phys (j9 (s γ))
 let B:=phys J.a₁ - phys J.a₀*y
 let N :=phys J.b₀*y - phys J.b₁
 let ev :=eval₂RingHom phys y
 have hnum :=congrArg phys (J.numerator_id γ hγ)
 have hden:=congrArg phys (J.denominator_id γ hγ)
 simp only [map_mul,map_add] at hnum hden
 have hq:=(map_ne_zero_iff phys (zxb L[X] FX)).mpr (J.denominator γ hγ)
 have hratio: (phys J.a₀*r+phys J.b₀)*y=phys J.a₁*r+phys J.b₁:= by
   dsimp only [r]
   rw [← hden,← hnum,mul_assoc,show phys (J.Q γ)*y=phys (J.P γ) by
     exact mul_div_cancel₀ _ hq]
 have hNB:N=r*B:= by dsimp only [N,B]; linear_combination hratio
 have eN :ev (form J.b₀ (-J.b₁))=N := by simp [ev,form,N,sub_eq_add_neg,add_comm]
 have eB:ev (form (-J.a₀) J.a₁)=B:= by simp [ev,form,B,sub_eq_add_neg]
 have eC (p:L[X]) :ev (C p)=phys p:=eval₂_C phys y
 have hroot :f.eval₂ phys r=0:= calc
   _=phys (f.eval (j9 (s γ))) := by rw [← eval₂_id,hom_eval₂,RingHom.comp_id]
   _=0:= by rw [hr,map_zero]
 change ev (changeAt J (zz4 L) n f)=0
 calc
   _=f.eval₂ phys r*B^n:= by
     rw [changeAt,transform_sum,map_sum,eval₂_eq_sum_range' phys (Nat.lt_succ_of_le hn) r,sum_mul]
     apply sum_congr rfl
     intro i hi
     have hp:=Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hi))
     simp only [coe_mapRingHom,Polynomial.map_id,map_mul,map_pow,eN,eB,eC,hNB,mul_pow]
     rw [mul_assoc _ (_ *_),mul_assoc (_^i),← pow_add,hp,← mul_assoc]
   _=0:= by rw [hroot,zero_mul]
end
end qtqYUDc
end
