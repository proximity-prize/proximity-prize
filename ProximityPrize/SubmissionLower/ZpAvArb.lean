import ProximityPrize.SubmissionLower.ZsS78jd
import ProximityPrize.SubmissionLower.ZnGdvBe
import ProximityPrize.SubmissionLower.ZvigIbb
import ProximityPrize.SubmissionLower.Zg1hxlb
import ProximityPrize.SubmissionLower.ZPKTqyb
import ProximityPrize.SubmissionLower.ZRSdJhe
import ProximityPrize.SubmissionLower.ZSOuZfa
import ProximityPrize.SubmissionLower.ZwLbCYa
import ProximityPrize.SubmissionLower.ZBcmVie
import ProximityPrize.SubmissionLower.AU
import ProximityPrize.SubmissionLower.E6
import ProximityPrize.SubmissionLower.Z5h1PTd
import ProximityPrize.SubmissionLower.ZO2xefe
import ProximityPrize.SubmissionLower.Zmk5EEe
import ProximityPrize.SubmissionLower.ZS2Jire
import ProximityPrize.SubmissionLower.ZS4VEna
import ProximityPrize.SubmissionLower.ZpWrDCd
import ProximityPrize.SubmissionLower.ZQTNHBe
import ProximityPrize.SubmissionLower.ZULJdud
import ProximityPrize.SubmissionLower.AP
import ProximityPrize.SubmissionLower.B6
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.CI
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E4
import ProximityPrize.SubmissionLower.P6Defs
import ProximityPrize.SubmissionLower.Z2fdgla
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.Z409zke
import ProximityPrize.SubmissionLower.ZBRA0Kc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZPfxqxd
import ProximityPrize.SubmissionLower.ZSWmOqa
import ProximityPrize.SubmissionLower.ZV6zyia
import ProximityPrize.SubmissionLower.ZZMyKHc
import ProximityPrize.SubmissionLower.ZaQt7ib
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, Field → zrb, Function.Injective → zq4, Function.comp_apply → z3s, IsFractionRing.injective → zxb, MvPolynomial → z3y, MvPolynomial.eval₂_comp_left → zqI, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.map_injective → zTo, Polynomial.map_zero → zgY, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO, RingHom.ext → zz4
set_option maxHeartbeats 600000
section
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qvWbALd
noncomputable section
open Polynomial Finset
open P5 (K p)
open cu (L)
open Cu (sQ oO)
open E7 (CurveField Gb)
open quN7Z4a (Sheet)
open qRoCwuc (genericDisc)
open private good_subset leading_exceptions from ProximityPrize.SubmissionLower.ZXGF8Ec
def c1 :Prop :=
  ∀ {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
    (S:Sheet C₀ J 2 H T z s),
    CurveField L (oO C₀) ∧
    Gb L (oO C₀) S.bY.coordinate≤H
def c2 :Prop :=
  ∀ {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
    (S:Sheet C₀ J 2 H T z s),
    CurveField L (oO C₀)→Set.InjOn z (T:Set K) →
    Nonempty (MarkedPlaces S)
theorem of_children (h1 :c1) (h2 :c2) :qrsE1ie.c2 := by
 classical
 intro C₀ _ J T z s H S hd hn hz
 obtain ⟨hc,hh⟩:=h1 S
 obtain ⟨M⟩:=h2 S hc hz
 have hd' : (genericDisc S).natDegree<p:= by
  rw [scaled_disc,natDegree_C_mul (pow_ne_zero 2 S.bY.scale.ne_zero)]
  exact hd
 have hgood:=count S M hc hh hd' (not_constantOddPart S hn)
 have hbad:=leading_exceptions S hz
 have ht:=card_sdiff_add_card_eq_card (good_subset S)
 omega
end
end qvWbALd
end
section
set_option autoImplicit true
namespace qDall2c
theorem proof :qxblDlc.c2 :=quwKLBd.proof
end qDall2c
end
section
set_option backward.isDefEq.respectTransparency false
namespace qtqYUDc
noncomputable section
open Polynomial Finset
open scoped WithZero
open P5 (K)
open cu (L)
open Cu (oO)
open E7 (CurvePlace)
open qZfVj1b (gRK)
local notation "normal" => qZfVj1b.normalize

open qBajpRb (cls incl incl_injective yq equation equation_generic equation_mark)
open qb0hmCe (cLN specialize)
open q1kuFjb (IntSeries residue expansion_coeff mapTwice Ua liftAt_reduce map_liftAt)
open private b5S from ProximityPrize.SubmissionLower.ZPaaHRd
open private adG aMX b4t cNC from ProximityPrize.SubmissionLower.Y
attribute [local instance] gRK
private theorem twice_comp {R S T:Type} [za6 R] [za6 S] [za6 T]
  (g:S →+* T) (f :R →+* S) (p:R[X][X]) :
  mapTwice g (mapTwice f p)=mapTwice (g.comp f) p:= by
 simp only [mapTwice,coe_mapRingHom,Polynomial.map_map,mapRingHom_comp]
private theorem twice_inj {R S:Type} [za6 R] [za6 S] {f :R →+* S}
  (hf :zq4 f) :zq4 (mapTwice f) :=
 zTo _ (zTo _ hf)
variable {E :Type} [zrb E] [zZE L E]
private theorem scale (v :CurvePlace L E) (m:E →ₐ[L] LaurentSeries L)
    (f :E[X][X]) (hf :f≠0) :
    ∃ u:Eˣ,(∀ i j,v.value ((u:E)*((f.coeff i).coeff j))≤1) ∧
      cLN m 0 (C (C (u:E))*f)≠0:= by
  obtain ⟨i,hi,hmax⟩:=Finset.exists_mem_eq_sup' (Polynomial.support_nonempty.mpr hf)
    (fun i=>adG v.value (f.coeff i))
  rw [Finset.sup'_eq_sup] at hmax
  obtain ⟨j,hj,_⟩:=cNC v.value (f.coeff i) (mem_support_iff.mp hi)
  have hv :v.value ((f.coeff i).coeff j)≠0:= by
    rw [hj]
    exact b4t v.value (mem_support_iff.mp hi)
  let u:=Units.mk0 ((f.coeff i).coeff j)⁻¹ (inv_ne_zero (v.value.ne_zero_iff.mp hv))
  refine ⟨u,fun a b => ?_,fun hz => ?_⟩
  · have hh:v.value ((f.coeff a).coeff b)≤v.value ((f.coeff i).coeff j) := by
      by_cases ha :f.coeff a=0
      · simp [ha]
      exact (aMX v.value (f.coeff a) b).trans
        ((Finset.le_sup (f := fun i=>adG v.value (f.coeff i))
          (mem_support_iff.mpr ha)).trans (hmax.trans hj.symm).le)
    simp only [u,Units.val_mk0,map_mul,map_inv₀]
    exact (mul_le_mul' le_rfl hh).trans_eq (inv_mul_cancel₀ hv)
  · have h:=congrArg (fun p:L[X][X]=>(p.coeff i).coeff j) hz
    simp only [expansion_coeff,coeff_C_mul,u,Units.val_mk0,
      inv_mul_cancel₀ (v.value.ne_zero_iff.mp hv),map_one,HahnSeries.coeff_one,eq_self,ite_true,
      coeff_zero,one_ne_zero] at h
private theorem reduce_scale {F G:IntSeries[X][X]} {c:LaurentSeries L}
  (h:mapTwice IntSeries.subtype F=C (C c)*mapTwice IntSeries.subtype G)
  (hG:mapTwice residue G≠0) :
  ∃ b:L,mapTwice residue F=C (C b)*mapTwice residue G:= by
 obtain ⟨i,hi⟩:=Polynomial.support_nonempty.mpr hG
 obtain ⟨j,hj⟩:=Polynomial.support_nonempty.mpr (mem_support_iff.mp hi)
 let x :=(G.coeff i).coeff j
 have hr :residue x≠0:= by
  simpa only [mapTwice,coe_mapRingHom,coeff_map] using mem_support_iff.mp hj
 let e :=LaurentSeries.powerSeriesEquivSubring L
 have hx :IsUnit (e.symm x) :=PowerSeries.isUnit_iff_constantCoeff.mpr hr.isUnit
 have hu:IsUnit x := by
  have hh:=hx.map e.toRingHom
  change IsUnit (e (e.symm x)) at hh
  rwa [e.apply_symm_apply] at hh
 let b:=(F.coeff i).coeff j*(↑hu.unit⁻¹:IntSeries)
 have he :=congrArg (fun p: (LaurentSeries L)[X][X]=>(p.coeff i).coeff j) h
 simp only [mapTwice,coe_mapRingHom,coeff_map,coeff_C_mul] at he
 have hb:IntSeries.subtype b=c:= by
  rw [show IntSeries.subtype b= _ from map_mul IntSeries.subtype _ _,he,mul_assoc]
  rw [← map_mul,hu.unit.mul_inv_of_eq hu.unit_spec,map_one,mul_one]
 have hF:F=C (C b)*G:=(twice_inj (f :=IntSeries.subtype) Subtype.val_injective) (by
  rw [h,map_mul]
  change _=(C (C b)).map (mapRingHom IntSeries.subtype)*_
  simp only [map_C,coe_mapRingHom,hb])
 exact ⟨residue b,by simp only [hF,map_mul,mapTwice,coe_mapRingHom,map_C]⟩
private theorem survives {R S T:Type} [za6 R] [za6 S] [za6 T]
  [Nontrivial T] {n:ℕ} (f :R →+* S) (hf :zq4 f) (r :R →+* T)
  (a b:Fin n→R) (c d:Fin n→S) (hc : ∀ i,f (a i)=c i)
  (hd : ∀ i,f (b i)=d i) (h: (∑ i,c i*d i)=1) :
  ∃ i,r (b i)≠0:= by
 have he : (∑ i,a i*b i)=1 :=hf (by simpa only [map_sum,map_mul,map_one,hc,hd] using h)
 by_contra! hz
 have hr :=congrArg r he
 simp only [map_sum,map_mul,hz,mul_zero,sum_const_zero,map_one,zero_ne_one] at hr
private theorem chart_nonzero {U:Finset K} {s :K→K[X]} {z :K→K}
   {q:Cu.sQ} [Fact (Irreducible q)] {J:Ideal gT.kM}
   {g H :ℕ} (S:quN7Z4a.Sheet q J g H U z s) {γ:K} (hγ:γ∈U) :
   DQ.specialize S.bY.equation (S.parameter γ)≠0:= by
 let x (i:Fin S.n) :=cls S.bY (MvPolynomial.X (Sum.inr i))
 have ix (i:Fin S.n) :incl S.bY (x i)=S.bY.coordinate i:= by
   simp only [x,qBajpRb.incl_cls,qBajpRb.ek,
     MvPolynomial.eval₂Hom_X',Sum.elim_inr]
 obtain ⟨ℓ,hℓ⟩:=S.bY.normalized
 let r :=yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ)
 obtain ⟨i,hi⟩:=survives (incl S.bY) (incl_injective S.bY) r.toRingHom
   (fun i=>cls S.bY (MvPolynomial.C (ℓ i))) x
   (Cu.zT q ∘ ℓ) S.bY.coordinate
   (fun i=> by rw [qBajpRb.incl_cls,qBajpRb.ek,MvPolynomial.eval₂Hom_C]; rfl) ix hℓ
 obtain ⟨k,a,hk⟩:=S.bY.coordinates_are_coefficients i
 have he : ((equation S.bY).coeff k).coeff a=x i:= by
   apply incl_injective S.bY
   have hh:=congrArg (fun p: (oO q)[X][X]=>(p.coeff k).coeff a) (equation_generic S.bY)
   simpa only [coeff_map,coe_mapRingHom,ix] using hh.trans hk.symm
 intro hz
 apply hi
 have hh:=congrArg (fun p:L[X][X]=>(p.coeff k).coeff a) (equation_mark S.bY (S.onBase γ hγ))
 simpa only [coeff_map,coe_mapRingHom,he,hz,coeff_zero] using hh
theorem proof :q1XeJwa.c1 := by
  intro D w U s z q g H J _ Cw S G a ha he γ hγ A
  let E :=oO q
  let e :=LaurentSeries.powerSeriesEquivSubring L
  let ι:=IntSeries.subtype
  let m:=A.map.toRingHom
  let j:=e.toRingHom.comp A.series.toRingHom
  let b:=e.toRingHom.comp PowerSeries.C
  have hιj:ι.comp j=m.comp (incl S.bY) :=zz4 fun x=>A.lift_eq x
  have hιb:ι.comp b=m.comp (algebraMap L E) := by
    apply zz4
    intro x
    change ((e (PowerSeries.C x) :IntSeries) :LaurentSeries L)=A.map (algebraMap L E x)
    rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,PowerSeries.coe_C,A.map.commutes,
      LaurentSeries.algebraMap_apply]
  have hr (x :PowerSeries L) :residue (e x)=zbO x :=
    congrArg zbO (e.symm_apply_apply x)
  have hρj:residue.comp j=(yq S.bY (z γ) (S.parameter γ) (S.onBase γ hγ)).toRingHom :=
    zz4 fun x=>(hr _).trans (A.reduce x)
  have hρb:residue.comp b=RingHom.id L :=
    zz4 fun x=>(hr _).trans (PowerSeries.constantCoeff_C x)
  let f :=normal S.root.equation
  let n:=f.natDegree
  let F:=mapTwice j (equation S.bY)
  let f₀:=DQ.specialize S.bY.equation (S.parameter γ)
  have hf₀:mapTwice residue F=f₀:= by
    rw [twice_comp,hρj]
    exact equation_mark S.bY (S.onBase γ hγ)
  have hf₀ne :f₀≠0:=chart_nonzero S hγ
  let t:E :=(S.bY.scale :E)*S.root.equation.leadingCoeff.leadingCoeff
  have ht:t≠0:=mul_ne_zero S.bY.scale.ne_zero (b5S S)
  have hF:mapTwice ι F=mapTwice m (C (C t)*f) := by
    rw [twice_comp,hιj,← twice_comp]
    congr 1
    change (equation S.bY).map (mapRingHom (incl S.bY))= _
    rw [equation_generic]
    dsimp only [f,qZfVj1b.normalize,t]
    rw [← mul_assoc,← C.map_mul,← C.map_mul,mul_assoc,mul_inv_cancel₀ (b5S S),mul_one]
  have injdeg {R T:Type} [za6 R] [za6 T] (b:R →+* T)
      (hb:zq4 b) (p:R[X][X]) : (mapTwice b p).natDegree=p.natDegree :=
    natDegree_map_eq_of_injective (f :=mapRingHom b) (zTo b hb) p
  have hn:f₀.natDegree≤n:= by
    rw [← hf₀]
    refine natDegree_map_le.trans ?_
    rw [← injdeg ι Subtype.val_injective F,hF,injdeg _ A.map.injective,natDegree_C_mul (C_ne_zero.mpr ht)]
  let T:=changeAt Cw b n F
  have hT:mapTwice ι T=mapTwice m (C (C t)*(C a*G)) := by
    rw [change_map,hιb,hF,← change_map,change_scale]
    exact congrArg (fun p=>mapTwice m (C (C t)*p)) he
  have hT₀:mapTwice residue T=changeAt Cw (RingHom.id L) n f₀:= by
    rw [change_map,hρb,hf₀]
  have hTne :mapTwice residue T≠0:=hT₀.symm ▸ word_ne Cw n hf₀ne hn
  let ev :=eval₂RingHom P5_7_7.phys (P5_7_7.phys (Cw.P γ)/P5_7_7.phys (Cw.Q γ))
  have hTroot :ev (mapTwice residue T)=0:= by
    rw [hT₀]
    exact word_root Cw n f₀ hn hγ (S.identity γ hγ)
  have hGne :G≠0:= by
    intro hz
    apply hTne
    have h:=(twice_inj (f :=ι) Subtype.val_injective) (by
      simpa [hz] using hT:mapTwice ι T=mapTwice ι 0)
    rw [h,map_zero]
  obtain ⟨u,hu,hG₀⟩:=scale A.place A.map G hGne
  obtain ⟨v,hv,hB₀⟩:=scale A.place A.map (C a) (C_ne_zero.mpr ha)
  let uG:=C (C (u:E))*G
  let va :=C (C (v :E)*a)
  have hInt (f :E[X][X]) (c:E) (h : ∀ i j,A.place.value (c*((f.coeff i).coeff j))≤1) :
      ∀ i j,(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (A.map (((C (C c)*f).coeff i).coeff j))≤1 := by
    intro i j
    rw [← A.value,coeff_C_mul,coeff_C_mul]
    exact h i j
  let G₁:=Ua A.map uG (hInt G u hu)
  let B:=Ua A.map va (by simpa only [va,map_mul] using hInt (C a) v hv)
  have hG₁:mapTwice ι G₁=mapTwice m uG:=map_liftAt _ _ _
  have hB:mapTwice ι B=mapTwice m va :=map_liftAt _ _ _
  have hB_C:B=C (B.coeff 0) := by
    apply twice_inj (f :=ι) Subtype.val_injective
    have h:mapTwice ι (C (B.coeff 0))=C ((mapTwice ι B).coeff 0) := by
      simp only [mapTwice,map_C,coeff_map,coe_mapRingHom]
    rw [h,hB]
    simp only [va,mapTwice,coe_mapRingHom,map_C,coeff_C_zero]
  let c:E :=(v :E)*(u:E)*t⁻¹
  have hc:c*t=(v :E)*(u:E) := by
    dsimp only [c]
    rw [mul_assoc,inv_mul_cancel₀ ht,mul_one]
  have hprod:mapTwice ι (B*G₁)=C (C (m c))*mapTwice ι T:= calc
    _=mapTwice m (va*uG) := by
      rw [map_mul,hB,hG₁]
      exact ((mapTwice m).map_mul va uG).symm
    _=mapTwice m (C (C (c*t))*(C a*G)) := by
      apply congrArg (mapTwice m)
      rw [hc]
      simp only [va,uG,map_mul]
      ring
    _ = _:= by
      have hm:mapTwice m (C (C c))=C (C (m c)) := by
        change (C (C c)).map (mapRingHom m)= _
        rw [map_C,coe_mapRingHom,map_C]
      rw [hT,← hm,← (mapTwice m).map_mul,← mul_assoc (C (C c)),← C.map_mul,← C.map_mul]
  obtain ⟨d,hd⟩:=reduce_scale hprod hTne
  refine ⟨u,hu,hG₀,?_⟩
  have hB₁:mapTwice residue B≠0:= by
    have hh:mapTwice residue B=cLN A.map 0 va :=liftAt_reduce _ _ _
    rw [hh]
    simpa only [va,map_mul] using hB₀
  have hBsp:ev (mapTwice residue B)≠0:= by
    rw [hB_C] at hB₁ ⊢
    simp only [mapTwice,coe_mapRingHom,map_C] at hB₁ ⊢
    change (C ((B.coeff 0).map residue)).eval₂ P5_7_7.phys _≠0
    rw [eval₂_C]
    exact (map_ne_zero_iff P5_7_7.phys (zxb L[X] cu.FX)).mpr
      (C_ne_zero.mp hB₁)
  have hh:=congrArg ev hd
  rw [map_mul,map_mul,map_mul,hTroot,mul_zero] at hh
  exact (liftAt_reduce A.map uG _ ▸ (mul_eq_zero.mp hh).resolve_left hBsp)
end
end qtqYUDc
end
end
section
section
namespace q7P6kQb
noncomputable section
open Polynomial qNu3xvc P5_7_1_7_4_3_4 qfbIfsd
open cu (L)
open scoped BigOperators
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
abbrev tu (E :Type) [zrb E] :=RatFunc E
abbrev Closure (E :Type) [zrb E] :=AlgebraicClosure (tu E)
abbrev Series (E :Type) [zrb E] :=PowerSeries (Closure E)
def Xm:E[X] →+* Series E :=
 (PowerSeries.C.comp (algebraMap (tu E) (Closure E))).comp (algebraMap E[X] (tu E))
def args (C:Pencil A) (z :Index A→L) (v :Series E) (i:Index A) :Series E :=
  (eval₂RingHom Xm v) (actual C i) +
    Xm (E :=E) (z1z (algebraMap L E (z i))) *
     PowerSeries.X
def afe (C:Pencil A) (i:Index A) :tu E :=
 algebraMap E[X] (tu E) ((actual C i).coeff 0)
def block (C:Pencil A) (t:Fin 3) : (tu E)[X][X] :=
  ∑ i:Slot A.s (baseCap A t) (ordCap A t),
    monomial i.1.val (monomial i.2.val (afe C ⟨t,i⟩))
theorem aMq (C:Pencil A) (t:Fin 3) (x y :Closure E) :
  qZu9hjc.atPair (algebraMap (tu E) (Closure E)) x y (block C t) =
   form (fun i=>algebraMap (tu E) (Closure E) (afe C i)) t x y := by
 simp [qZu9hjc.atPair,block,form,eval₂_finsetSum,eval₂_monomial]
def gaugeAt (C:Pencil A) (y :Closure E) :Closure E :=
 1+algebraMap (tu E) (Closure E) (RatFunc.C (algebraMap L E C.tilt))*y
structure Fiber (C:Pencil A) where
 size :ℕ
 point :Fin size→Closure E×Closure E
 value :Fin size→Closure E
 distinct :zq4 point
 realized : ∀ i,∃ σ:EC A →+* Closure E,
  σ.comp C.base=algebraMap (tu E) (Closure E) ∧
  point i=(σ (amm A),σ (jU A false))∧value i=σ (relativePolar C)
 simple : ∀ i,qZu9hjc.jacobian (algebraMap (tu E) (Closure E))
  (point i).1 (point i).2 (block C 0) (block C 1)≠0
 zero₀ : ∀ i,form (fun k=>algebraMap (tu E) (Closure E) (afe C k))
  0 (point i).1 (point i).2=0
 zero₁ : ∀ i,form (fun k=>algebraMap (tu E) (Closure E) (afe C k))
  1 (point i).1 (point i).2=0
 unitGauge : ∀ i,gaugeAt C (point i).2≠0
 product : (bix C.base (relativePolar C) C.finite).map
    (algebraMap (tu E) (Closure E)) =
  ∏ i,((z7y: (Closure E)[X])-Polynomial.C (value i))
def Ak {C:Pencil A} (F:Fiber C) :Prop :=
  ∀ i j,i≠j→F.value i=F.value j →
    ∃ k :Slot A.s (baseCap A 2) (ordCap A 2),k.1.val<A.d - 1 ∧
      (F.point i).1^k.2.val*(F.point i).2^k.1.val /
          gaugeAt C (F.point i).2^(A.d-2) ≠
        (F.point j).1^k.2.val*(F.point j).2^k.1.val /
          gaugeAt C (F.point j).2^(A.d-2)
structure Arc {C:Pencil A} (F:Fiber C) (z :Index A→L) where
 xy :Fin F.size→Series E×Series E
 center : ∀ i,(zbO (xy i).1,
  zbO (xy i).2)=F.point i
 zero₀ : ∀ i,form (args C z 0) 0 (xy i).1 (xy i).2=0
 zero₁ : ∀ i,form (args C z 0) 1 (xy i).1 (xy i).2=0
end
end q7P6kQb
end
section
set_option backward.isDefEq.respectTransparency false
namespace q7P6kQb
noncomputable section
open Polynomial qNu3xvc P5_7_1_7_4_3_4 qfbIfsd
open q2tSkEc (DetectsValue L4)
open cu (L)
open scoped Classical
open private collect coeff_collect leading_product from ProximityPrize.SubmissionLower.ZSOuZfa
open private linear_product from ProximityPrize.SubmissionLower.ZRSdJhe
def c1 :Prop :=
  ∀ {E :Type} [zrb E] [zZE L E] (A:Equation E),2≤A.d →
    ∀ C:Pencil A,C.tilt≠0→Nonempty (Fiber C)
def c2 :Prop :=
  ∀ {E :Type} [zrb E] [zZE L E] (A:Equation E),2≤A.d →
    ∀ (C:Pencil A),C.tilt≠0 → ∀ F:Fiber C,Ak F
def c3:Prop :=
  ∀ {E :Type} [zrb E] [zZE L E] (A:Equation E) (C:Pencil A)
    (F:Fiber C) (z :Index A→L),Nonempty (Arc F z)
def c4 :Prop :=
  ∀ {E :Type} [zrb E] [zZE L E] (A:Equation E),2≤A.d →
    ∀ (C:Pencil A),C.tilt≠0 → ∀ (F:Fiber C),Ak F →
    ∀ (R:z3y (Index A) L) (z :Index A→L),
      deform R (actual C) z≠0 → ∀ u:Arc F z,
      ∃ (z' : Index A→L) (v :Fin F.size→Series E),
        deform R (actual C) z' ≠ 0∧zq4 v ∧
        (∀ i,zbO (v i)=F.value i) ∧
        ∀ i,form (args C z' (v i)) 0 (u.xy i).1 (u.xy i).2=0 ∧
          form (args C z' (v i)) 1 (u.xy i).1 (u.xy i).2=0 ∧
          L4 (args C z' (v i)) (u.xy i).1 (u.xy i).2=0
variable {E :Type} [zrb E] [zZE L E] {A:Equation E}
private theorem map_deform {B:Type} [CommSemiring B] (f :E[X][X][X] →+* B)
    (R:z3y (Index A) L) (a :Index A→E[X][X]) (z :Index A→L) :
    f (deform R a z) =
      R.eval₂ (f.comp (Polynomial.C.comp (const₂.comp (algebraMap L E))))
        (f ∘ fun i=>deformArg (a i) (z i)) :=
  by
    unfold deform
    exact zqI (S₁:=E[X][X][X]) (S₂:=B) f
      (Polynomial.C.comp (const₂.comp (algebraMap L E))) (fun i=>deformArg (a i) (z i)) R
private theorem direction (C:Pencil A) (R:z3y (Index A) L) (hR:R≠0) :
  ∃ z,deform R (actual C) z≠0:= by
 let j:=algebraMap L E
 let f :E[X][X] →+* E :=(evalRingHom (0:E)).comp (evalRingHom (0:E[X]))
 let ev :E[X][X][X] →+* E :=f.comp (evalRingHom (1 :E[X][X]))
 let S (i:Index A) :=Set.range (fun a :L=>f (actual C i)+j a)
 have hS (i:Index A) : (S i).Infinite :=
  Set.infinite_range_of_injective fun a b h=>j.injective (add_left_cancel h)
 by_contra! h
 apply hR
 apply MvPolynomial.map_injective _ j.injective
 rw [map_zero]
 apply MvPolynomial.funext_set S hS
 intro x hx
 choose z hz using fun i=>hx i (Set.mem_univ i)
 have he :=(map_deform ev R (actual C) z).symm.trans (by rw [h z,map_zero])
 have hc:ev.comp (Polynomial.C.comp (const₂.comp j))=j:= by
  ext a
  simp [ev,f,const₂]
 have hv :ev ∘ (fun i=>deformArg (actual C i) (z i))=x := by
  funext i
  simpa [ev,f,deformArg,const₂,j] using hz i
 rw [MvPolynomial.eval_map,map_zero,← hv,← hc]
 exact he
private def extend (E :Type) [zrb E] :E[X][X][X] →+* (Series E)[X] :=
 eval₂RingHom (mapRingHom (Xm (E :=E))) (z1z PowerSeries.X)
omit [zZE L E] in
private theorem collect_extend (p:E[X][X][X]) (n i:ℕ) :
   (z2o n (collect (extend E p))).coeff i =
     algebraMap (tu E) (Closure E) (algebraMap E[X] (tu E) ((p.coeff n).coeff i)) := by
 induction p using Polynomial.induction_on' with
 | add p q hp hq =>
   simp only [map_add,coeff_add,hp,hq]
 | monomial k a =>
   rw [extend,coe_eval₂RingHom,eval₂_monomial,← map_pow,coeff_collect,coeff_mul_C]
   simp only [coe_mapRingHom,coeff_map,coeff_monomial,Xm,RingHom.comp_apply,
     PowerSeries.coeff_C_mul_X_pow]
   by_cases h:n=k
   · subst k
     simp
   · simp [h,Ne.symm h]
private theorem roots (C:Pencil A) (R:z3y (Index A) L) (z :Index A→L)
   (hR:DetectsValue R) (x y v :Series E)
   (h0:form (args C z v) 0 x y=0) (h1 :form (args C z v) 1 x y=0)
   (h2 :L4 (args C z v) x y=0) :
   (extend E (deform R (actual C) z)).eval v=0:= by
 let k :=(evalRingHom v).comp (extend E)
 let m:L →+* Series E :=Xm.comp (Polynomial.C.comp (algebraMap L E))
 change k (deform R (actual C) z)=0
 have hkC (a :E[X][X]) :k (z1z a)=eval₂RingHom Xm v a := by
   simp [k,extend,coe_eval₂RingHom,eval_map]
 have hkX:k z7y=PowerSeries.X:= by
   simp [k,extend,coe_eval₂RingHom]
 have hc:k.comp (Polynomial.C.comp (const₂.comp (algebraMap L E)))=m:= by
   apply zz4
   intro a
   change k (z1z (const₂ (algebraMap L E a)))=m a
   rw [hkC]
   simp [const₂,m,coe_eval₂RingHom]
 have ha :k ∘ (fun i=>deformArg (actual C i) (z i))=args C z v := by
   funext i
   change k (deformArg (actual C i) (z i))=args C z v i
   simp [deformArg,args,const₂,hkC,hkX,coe_eval₂RingHom]
 rw [map_deform,hc,ha]
 let S:=Series E
 let j:=algebraMap S (FractionRing S)
 apply (map_eq_zero_iff j (zxb S _)).mp
 refine (zqI j m (args C z v) R).trans ?_
 apply hR (j.comp m) (j ∘ args C z v) (j x) (j y)
 · simpa only [form,map_sum,map_mul,map_pow,z3s,map_zero] using congrArg j h0
 · simpa only [form,map_sum,map_mul,map_pow,z3s,map_zero] using congrArg j h1
 · have hnat :j (A.d:S)=(A.d:FractionRing S) :=map_natCast j _
   simpa only [L4,form,q2tSkEc.top,map_add,map_sub,map_sum,map_mul,
     map_pow,hnat,z3s,map_zero,apply_ite] using congrArg j h2
theorem of_children (fiber :c1) (bwk :c2) (lift:c3) (chooseValues :c4) :
  q2tSkEc.c2 := by
 intro E _ _ A hd C htilt R hR hdetect
 obtain ⟨F⟩:=fiber A hd C htilt
 obtain ⟨z₀,hz₀⟩:=direction C R hR
 obtain ⟨u⟩:=lift A C F z₀
 obtain ⟨z,v,hz,hv,hcenter,heq⟩ :=
  chooseValues A hd C htilt F (bwk A hd C htilt F) R z₀ hz₀ u
 let P:=deform R (actual C) z
 let N :=bix C.base (relativePolar C) C.finite
 let j:=algebraMap (tu E) (Closure E)
 let b:=algebraMap E[X] (tu E)
 have hb:=RatFunc.algebraMap_injective E
 let V := ∏ i,((z7y: (Series E)[X])-Polynomial.C (v i))
 have hV:V.Monic:=monic_prod_X_sub_C _ _
 have hP:extend E P≠0:= by
  intro h
  apply hz
  ext n:1
  ext i:1
  apply hb
  apply j.injective
  have hi:=collect_extend P n i
  rw [h,map_zero,map_zero,coeff_zero] at hi
  simpa only [coeff_zero,map_zero] using hi.symm
 have hdiv :V∣extend E P:=linear_product v hv _ fun i =>
  roots C R z hdetect _ _ _ (heq i).1 (heq i).2.1 (heq i).2.2
 obtain ⟨n,hn,hnd⟩:=leading_product (extend E P) V hP hV hdiv
 have hc:z2o n (collect (extend E P))=((P.coeff n).map b).map j:= by
  ext i
  simp only [collect_extend,coeff_map,j,b]
 have hVN :V.map zbO=N.map j:= by
  rw [F.product]
  simp only [V,Polynomial.map_prod,Polynomial.map_sub,map_X,map_C,hcenter]
 have hN :N.Monic:= by
  let _:=C.base.toAlgebra
  let _:=C.finite
  exact LinearMap.charpoly_monic _
 refine ⟨z,n,fun h=>hn (by rw [hc,h,zgY,zgY]),?_⟩
 exact (map_dvd_map j j.injective hN).mp (by simpa only [hc,hVN] using hnd)
end
end q7P6kQb
end
section
namespace qaiVg1b
open Polynomial Finset
open cu (L)
open E7 (KB)
open qrGSFbd (pencilVal pencilVal_poly pencilVal_const)
open P5_7_1_7_4_3_4 (adG)
open qXARP7c (eFi integral_norm_order order_le_normalization debit_le_trailing)
open scoped WithZero
theorem proof :qrGSFbd.c4 := by
 classical
 intro E F _ _ _ w m q hf hs hq P hp hcoeff hdvd ι S v hinj hsur hgauss
 let H :=RatFunc E
 let _:zZE H F:=m.toAlgebra
 let _:Module.Finite H F:=hf
 let _:Algebra.IsSeparable H F:=hs
 let u:=pencilVal w.value
 have hpoly (g:E[X]) :u (algebraMap E[X] H g)=adG w.value g :=
   pencilVal_poly w.value g
 let j:=RatFunc.C.comp (algebraMap L E)
 have hj (c:L) (hc:c≠0) :u (j c)=1 :=
   (pencilVal_const w.value _).trans (w.on_constants c hc)
 have hu:Function.Surjective u:= by
   intro a
   obtain ⟨x,hx⟩:=w.normalized a
   exact ⟨RatFunc.C x,(pencilVal_const w.value x).trans hx⟩
 choose e he hv using fun i:S=>hgauss i i.2
 have hscale (i:S) (x :H) :v i (algebraMap H F x)=u x^e i:= by
   change v i (m x)= _
   induction x using RatFunc.induction_on with
   | _ g d hd =>
     rw [map_div₀,(v i).map_div,u.map_div,div_pow,hpoly,hpoly,hv,hv]
 obtain ⟨c,hc,hb,hbI,hn⟩:=eFi u j hj q hq
 let b:=q/(algebraMap H F (j c) - q)
 have hsum:=integral_norm_order u hu (univ :Finset S) (fun i=>v i) e
   (fun i _=>hsur i i.2) (fun i _=>he i) (fun i _=>hscale i)
   (fun i _ k _ h=>Subtype.ext (hinj i.2 k.2 h)) b hb hbI
 let N :=(Algebra.lmul H F q).charpoly
 let R:=P.map (algebraMap E[X] H)
 have hm:N.Monic:=LinearMap.charpoly_monic _
 have hR₀:R.coeff 0≠0:= by
   rw [show R.coeff 0=algebraMap E[X] H (P.coeff 0) from coeff_map _ _,
     map_ne_zero_iff _ (zxb E[X] H)]
   exact hp
 have hR:R≠0:= fun h=>hR₀ (by simp [h])
 have hInt (i:ℕ) :u (R.coeff i)≤1 := by
   change u ((P.map (algebraMap E[X] H)).coeff i)≤1
   rw [coeff_map,hpoly]
   exact Finset.sup_le (fun k _=> by simpa using hcoeff i k)
 have hD:N^1∣R:= by
   rw [pow_one]
   exact hdvd
 have hbound:=debit_le_trailing u hm.ne_zero hR hInt hD
 rw [one_mul,trailingCoeff_eq_coeff_zero hR₀,KB,coeff_map,hpoly] at hbound
 rw [← Finset.sum_attach S,Finset.attach_eq_univ]
 calc
   (∑ i:S,KB (v i) q) ≤ ∑ i:S,KB (v i) b:= by
     apply sum_le_sum
     intro i _
     apply order_le_normalization (v i) hq
     rw [hscale,hj c hc,one_pow]
   _≤_:=hsum.trans (hn.trans_le hbound)
end qaiVg1b
end
end
