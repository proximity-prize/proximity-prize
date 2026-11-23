import ProximityPrize.SubmissionLower.ZvbAI4c
import ProximityPrize.SubmissionLower.ZW8Nc6b
import ProximityPrize.SubmissionLower.ZQTNHBe
set_option Elab.async false
section
namespace qZn79Eb
noncomputable section
open Polynomial
open scoped WithZero
open P5 (K)
open cu (L FX)
open P5_7_7 (phys)
open qqi5QRb (pointVal)
open qb0hmCe (CurveModel)
open qNu3xvc (seedDerivative)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet)
open qLXroAb (Pencil Chart evalXY dx)
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
def shift (A:Pencil F) (x :L) :A.M :=
 A.x-algebraMap Cq.E A.M (algebraMap L Cq.E x)
def slope (A:Pencil F) :A.M :=
 -evalXY (dx F.f) A.x A.y/A.polar
def numerator (A:Pencil F) (D:Derivation L Cq.E Cq.E) :A.M :=
 -evalXY (seedDerivative D F.f) A.x A.y
def variation (A:Pencil F) (D:Derivation L Cq.E Cq.E) :A.M :=
 numerator A D /A.polar
structure MarkLocal {A:Pencil F} {γ:K} {hγ:γ∈F.marks} {B:L[X]}
   (T:Chart A γ hγ B) (x :L) where
 ring :Subring A.M
 fractions : ∀ a :A.M,a∈ring ↔ ∃ b c:A.bY γ,
   pointVal x (T.map c)=1∧a=(b:A.M)/(c:A.M)
 map :ring →+* FX
 regular : ∀ a,pointVal x (map a)≤1
 ic:L→ ring
 gqx : ∀ r,(ic r :A.M)=shift A r
 shifted_map : ∀ r,map (ic r)=phys (Polynomial.X-Polynomial.C r)
 shifted_inv : ∀ r,r≠x→(shift A r)⁻¹∈ring
 x_mem:A.x∈ring
 y_mem:A.y∈ring
 slope_mem:slope A∈ring
structure LocalFormula {A:Pencil F} {γ:K} {hγ:γ∈F.marks} {B:L[X]}
  {T:Chart A γ hγ B} {x :L}
  (J:MarkLocal T x) (D:Derivation L Cq.E Cq.E) (N :L[X]) where
 num :J.ring
 sep:J.ring
 num_eq : (num :A.M)=numerator A D
 sep_eq : (sep:A.M)=A.polar
 simple :J.map sep≠0
 formula :J.map num/J.map sep=phys N/phys B
def TrivialSeed (A:Pencil F) (v :Valuation A.M ℤᵐ⁰) :Prop :=
 ∀ c:Cq.E,c≠0→v (algebraMap Cq.E A.M c)=1
def a8p (A:Pencil F) (v :Valuation A.M ℤᵐ⁰) (h:TrivialSeed A v) :
    Cq.E →+* v.valuationSubring :=
  (algebraMap Cq.E A.M).codRestrict v.valuationSubring.toSubring fun c=> by
    by_cases hc:c=0
    · simp [hc]
    · exact (h c hc).le
end
end qZn79Eb
end
section
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
namespace qZn79Eb
noncomputable section
open Polynomial WithZero
open P5 (K p)
open cu (L)
open E7 (KB)

open qqi5QRb (pointVal)
open qb0hmCe (CurveModel)
open qNu3xvc (seedDerivative)
open qypA4Sc (SeparableResidue)
open qoCymac (LocalDerivation)
open qkgz7gb (PlaneCurve)
open P5_7_3_5_2 (Sheet Variation)
open qxPDCsa (UnitAt)
open qLXroAb (Pencil Chart Vertical evalXY dx)
open private val_uniformizer val_poly exp_uniformizer_pow small_value from ProximityPrize.SubmissionLower.ZsE91Ed
open private chain₂ from ProximityPrize.SubmissionLower.Z5cOcra
variable {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
 {F:Sheet Cq z S}
def c1 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (A:Pencil F) (V:Variation F) (γ:K) (hγ:γ∈V.marks)
    (T:Chart A γ (V.Bp hγ) (V.den γ)) (x :L) (D:Derivation L Cq.E Cq.E),
    (V.den γ).eval x=0→LocalDerivation (F.atPlace γ (V.Bp hγ)) (F.place γ) D →
    ∃ J:MarkLocal T x,Nonempty (LocalFormula J D (V.num γ))
def c2 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} {A:Pencil F} {γ:K} {hγ:γ∈F.marks} {B:L[X]}
    {T:Chart A γ hγ B} {x :L} (J:MarkLocal T x) (b:A.M),
    ¬ IsIntegral J.ring b →
    ∃ v :Valuation A.M ℤᵐ⁰,Function.Surjective v ∧
      (∀ a :J.ring,v (a :A.M)≤1)∧1<v b ∧
      (TrivialSeed A v ∨ ∃ w:Vertical A (F.place γ),w.value=v)
def c3:Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (A:Pencil F),
    F.d<p→F.f.discr≠0→F.f.discr.natDegree<p →
    ∀ (v :Valuation A.M ℤᵐ⁰) (h:TrivialSeed A v),Function.Surjective v →
      v A.x≤1→v A.y≤1→v A.polar<1→SeparableResidue (a8p A v h)
def c4 :Prop :=
  ∀ {q:PlaneCurve} {Cq:CurveModel q} {z :K→K} {S:K→K[X]}
    {F:Sheet Cq z S} (A:Pencil F) (γ:K),γ∈F.marks →
    F.d<p→UnitAt F γ F.f.discr.leadingCoeff →
    ∀ w:Vertical A (F.place γ),
      w.value A.x≤1→w.value A.y≤1→w.value A.polar<1 →
      ∃ r :L,w.value (shift A r)<1
private theorem Oj {A:Pencil F} (D:Derivation L Cq.E Cq.E)
    (v :Valuation A.M ℤᵐ⁰) (hv :Function.Surjective v) (h:TrivialSeed A v)
    (hsep:SeparableResidue (a8p A v h)) (hx :v A.x≤1) (hy :v A.y≤1)
    (hs :v (slope A)≤1) (hq:v A.polar<1) :v (variation A D)≤1 := by
  let O:=v.valuationSubring
  let i:=a8p A v h
  let x :O:=⟨A.x,hx⟩
  let y :O:=⟨A.y,hy⟩
  let j:=eval₂RingHom i x
  let φ:=eval₂RingHom j y
  have hj:O.subtype.comp j=eval₂RingHom (algebraMap Cq.E A.M) A.x := by
    apply Polynomial.ringHom_ext
    · intro e
      change O.subtype ((C e).eval₂ i x)=(C e).eval₂ (algebraMap Cq.E A.M) A.x
      rw [eval₂_C,eval₂_C]
      rfl
    · change O.subtype (Polynomial.X.eval₂ i x) =
        Polynomial.X.eval₂ (algebraMap Cq.E A.M) A.x
      rw [eval₂_X,eval₂_X]
      rfl
  have hφ (g:Cq.E[X][X]) : (φ g:A.M)=evalXY g A.x A.y := by
    change O.subtype (g.eval₂ j y)= _
    rw [hom_eval₂,hj]
    rfl
  let a :=φ F.f.derivative
  let b:=φ (dx F.f)
  let n:=φ (seedDerivative D F.f)
  have ha :a≠0:= by
    intro he
    apply A.polar_ne
    exact (hφ F.f.derivative).symm.trans (congrArg Subtype.val he)
  have hpos :0<v (a :A.M) :=v.pos_iff.mpr (by simpa only [a,hφ] using A.polar_ne)
  obtain ⟨D',hD'⟩:=qrrOjma.proof v hv i D a ha (by simpa only [a,hφ] using hq) hsep
  let I:Ideal O:=Ideal.span {a}
  let π:=Ideal.Quotient.mk I
  have hb:π b=0:= by
    have hle :v (-(b:A.M)/(a :A.M))≤1 := by simpa only [a,b,hφ,slope] using hs
    rw [map_div₀,v.map_neg,div_le_one₀ hpos] at hle
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ((Valuation.valuationSubring.integers v).dvd_iff_le.mpr hle))
  have hpa :π a=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
  have hz :π (φ F.f)=0:= by
    rw [show φ F.f=0 from Subtype.ext ((hφ _).trans A.equation),map_zero]
  have hπ (g:Cq.E[X][X]) :
      π (φ g)=g.eval₂ (eval₂RingHom (π.comp i) (π x)) (π y) := by
    change π (g.eval₂ j y)= _
    rw [hom_eval₂]
    congr 1
    apply Polynomial.ringHom_ext
    · intro e
      change π ((C e).eval₂ i x)=(C e).eval₂ (π.comp i) (π x)
      simp only [eval₂_C,RingHom.comp_apply]
    · change π (Polynomial.X.eval₂ i x)=Polynomial.X.eval₂ (π.comp i) (π x)
      rw [eval₂_X,eval₂_X]
  have hn:=chain₂ D D' (π.comp i) hD' (π x) (π y) F.f
  dsimp only at hn
  rw [← hπ,← hπ,← hπ,← hπ,hz,D'.map_zero,← show n=φ (seedDerivative D F.f) from rfl,
    ← show b=φ (qNu3xvc.physicalDerivative F.f) from rfl,
    ← show a=φ F.f.derivative from rfl,hb,hpa,zero_mul,zero_mul,add_zero,add_zero] at hn
  have hdvd:a∣n:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hn.symm)
  have hnle :=(Valuation.valuationSubring.integers v).dvd_iff_le.mp hdvd
  have hquot:v (-(n:A.M)/(a :A.M))≤1 := by
    rw [map_div₀,v.map_neg,div_le_one₀ hpos]
    exact hnle
  simpa only [a,n,hφ,variation,numerator] using hquot
private theorem integral_specializes {A:Pencil F} {γ:K} {hγ:γ∈F.marks}
  {B:L[X]} {T:Chart A γ hγ B} {x :L} (J:MarkLocal T x)
  (b g:J.ring) (hg:J.map g≠0)
  (hi:IsIntegral J.ring ((b:A.M)/g)) :
  pointVal x (J.map b/J.map g)≤1 := by
 let j:J.ring →+* A.M:=algebraMap _ _
 let jO:=J.map.codRestrict (pointVal x).valuationSubring.toSubring J.regular
 have hj:Function.Injective j:=Subtype.val_injective
 have hg' : g≠0:= fun e=>hg (by simp [e])
 obtain ⟨f,hf,hzero⟩:=hi
 have hscaled:=scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero hj hzero
  (mem_nonZeroDivisors_iff_ne_zero.mpr hg')
 have he : (f.scaleRoots g).eval b=0:= by
  apply hj
  rw [← eval₂_id,hom_eval₂,RingHom.comp_id,map_zero]
  exact hscaled
 have hs :=congrArg J.map he
 rw [← eval₂_id,hom_eval₂,RingHom.comp_id,map_zero] at hs
 have hm:J.map g*(J.map b/J.map g)=J.map b:= by
  rw [← mul_div_assoc,mul_comm (J.map g),mul_div_cancel_right₀ _ hg]
 have hh:=scaleRoots_eval₂_mul (p:=f) J.map (J.map b/J.map g) g
 rw [hm] at hh
 have hf' : f.eval₂ J.map (J.map b/J.map g)=0 :=
  (mul_eq_zero.mp (hh.symm.trans hs)).resolve_left (pow_ne_zero _ hg)
 apply ((Valuation.valuationSubring.integers (pointVal x)).isIntegral_iff_v_le_one).mp
 refine ⟨f.map jO,hf.map _,?_⟩
 rw [eval₂_map]
 exact hf'
private theorem specialized_pole {A:Pencil F} {V:Variation F} {γ:K} {hγ:γ∈V.marks}
  {T:Chart A γ (V.Bp hγ) (V.den γ)} {x :L} {J:MarkLocal T x}
  {D:Derivation L Cq.E Cq.E} (U:LocalFormula J D (V.num γ))
  (hx : (V.den γ).eval x=0) {m:ℕ} (hm:m<(V.den γ).rootMultiplicity x) :
  1<pointVal x (J.map ((J.ic x)^m*U.num)/J.map U.sep) := by
 have hn : ¬ (V.num γ).IsRoot x := by
  intro hn
  obtain ⟨a,b,h⟩:=V.reduced γ hγ
  have h' := congrArg (fun f :L[X]=>f.eval x) h
  change (V.num γ).eval x=0 at hn
  simp only [eval_add,eval_mul,hn,hx,mul_zero,add_zero,eval_one,zero_ne_one] at h'
 have hn' : V.num γ≠0:= fun h=>hn (by simp [h])
 rw [map_mul,map_pow,mul_div_assoc,U.formula,map_mul,map_pow,J.shifted_map,
  val_uniformizer,map_div₀,val_poly x _ hn',val_poly x _ (V.den_ne γ hγ),
  rootMultiplicity_eq_zero hn,Nat.cast_zero,neg_zero,exp_zero,exp_uniformizer_pow,
  ← mul_div_assoc,mul_one]
 apply (one_lt_div₀ exp_pos).2
 exact exp_lt_exp.mpr (neg_lt_neg (by exact_mod_cast hm))
private theorem charge_order {A:Pencil F} (v :Valuation A.M ℤᵐ⁰)
  (D:Derivation L Cq.E Cq.E) {x :L} {m:ℕ}
  (hx :v (shift A x)<1) (hn:v (numerator A D)≤1)
  (h:1<v ((shift A x)^m*variation A D)) :
  m<KB v A.polar := by
 by_contra! hle
 have hlog : -(m:ℤ)≤log (v A.polar) := by
  unfold KB at hle
  omega
 have hp:=(v.ne_zero_iff).2 A.polar_ne
 have hp' := (le_log_iff_exp_le hp).mp hlog
 rw [variation,← mul_div_assoc,map_div₀,map_mul,map_pow] at h
 apply ((one_lt_div₀ (zero_lt_iff.mpr hp)).mp h).not_ge
 calc
  _≤v (shift A x)^m:=mul_le_of_le_one_right' hn
  _≤exp (-1 :ℤ)^m:=pow_le_pow_left₀ zero_le (small_value hx) _
  _≤_:=exp_uniformizer_pow m ▸ hp'
theorem of_children (at_mark :c1) (bwk :c2) (residue :c3) (vertical:c4) :qLXroAb.c6:= by
 intro q Cq z S F V A hd hδ hδp γ hγ hunit T x hx
 obtain ⟨D,hD⟩:=q5eiIAb.proof (F.place γ) (F.atPlace γ (V.Bp hγ))
   Cq.curve (F.value γ (V.Bp hγ))
 obtain ⟨J,⟨U⟩⟩:=at_mark A V γ hγ T x D hx hD
 let k :=(V.den γ).rootMultiplicity x
 let m:=k - 1
 let b:=(J.ic x)^m*U.num
 let u:A.M:=(b:A.M)/U.sep
 have hk :0<k :=(rootMultiplicity_pos (V.den_ne γ hγ)).mpr hx
 have hm:m<k := by dsimp only [m]; omega
 have hnon : ¬ IsIntegral J.ring u:= fun h =>
   (specialized_pole (hγ:=hγ) U hx hm).not_ge (integral_specializes J b U.sep U.simple h)
 obtain ⟨v,hv,hreg,hbad,htype⟩:=bwk J u hnon
 have hu:u=(shift A x)^m*variation A D:= by
   simp only [u,b,Subring.coe_mul,Subring.coe_pow,J.gqx,U.sep_eq,
     U.num_eq,variation,mul_div_assoc]
 rw [hu] at hbad
 have hvar :1<v (variation A D) := by
   refine hbad.trans_le ?_
   rw [map_mul,map_pow]
   exact mul_le_of_le_one_left' (pow_le_one₀ zero_le (J.gqx x ▸ hreg (J.ic x)))
 have hnum :v (numerator A D)≤1 :=U.num_eq ▸ hreg U.num
 have hpolar :v A.polar<1 := by
   rw [variation,map_div₀] at hvar
   exact ((one_lt_div₀ (v.pos_iff.mpr A.polar_ne)).mp hvar).trans_le hnum
 have hnonhor (h:TrivialSeed A v) :False := by
   have hX:=hreg ⟨_,J.x_mem⟩
   have hY:=hreg ⟨_,J.y_mem⟩
   exact hvar.not_ge (Oj D v hv h (residue A hd hδ hδp v h hv hX hY hpolar)
     hX hY (hreg ⟨_,J.slope_mem⟩) hpolar)
 obtain ⟨w,hw⟩:=htype.resolve_left hnonhor
 subst v
 obtain ⟨r,hr⟩:=vertical A γ (V.Bp hγ) hd hunit w (hreg ⟨_,J.x_mem⟩)
   (hreg ⟨_,J.y_mem⟩) hpolar
 have hrx :r=x := by
   by_contra hne
   have h:=hreg ⟨_,J.shifted_inv r hne⟩
   change w.value ((shift A r)⁻¹)≤1 at h
   rw [map_inv₀] at h
   have hne' : shift A r≠0:= by
     intro hz
     apply A.independent
     rw [show A.x= _ from sub_eq_zero.mp hz]
     exact isAlgebraic_algebraMap _
   exact (not_le_of_gt ((one_lt_inv₀ (w.value.pos_iff.mpr hne')).mpr hr)) h
 have hsmall:w.value (shift A x)<1 :=hrx ▸ hr
 have hcharge :=charge_order w.value D hsmall hnum hbad
 exact ⟨w,hsmall,by change k≤_; omega⟩
end
end qZn79Eb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qeBKasb
noncomputable section
open Polynomial
open scoped WithZero

open cu (L)

open q1kuFjb (IntSeries integralSeries residue fWQ)
open q14iMuc (discr_map coeff_nonzero_of_val_eq)
open qLXroAb (evalXY)

open private laurent_sub eval_map₂ from ProximityPrize.SubmissionLower.ZfwYtia
theorem vertical:qZn79Eb.c4 := by
  classical
  intro q Cq z S F A γ hγ _ hunit w hx hy hpolar
  let a :=F.atPlace γ hγ
  let w₀:=(F.place γ).value
  let O:=w₀.valuationSubring
  let V:=w.value.valuationSubring
  let κ:=IsLocalRing.ResidueField V
  let π:V →+* κ:=IsLocalRing.residue V
  let e :=algebraMap Cq.E A.M
  have hscale (c:Cq.E) :w.value (e c)=(w₀ c)^w.ramification := by
    by_cases hc:c=0
    · simp [hc,w.positive.ne']
    · simpa [e,w₀,support_C hc] using w.overGauss (Polynomial.C c)
  let j:O →+* L:=residue.comp ((a.toRingHom.comp O.subtype).codRestrict IntSeries (fun c =>
    (integralSeries (a c) ((F.value γ hγ c).symm ▸ c.property)).property))
  have hj (c:O) :j c=(a c).coeff 0:=fWQ _
  let i:O →+* V:=(e.comp O.subtype).codRestrict V.toSubring (fun c=> by
    change w.value (e c)≤1
    rw [hscale]
    exact pow_le_one₀ zero_le c.property)
  let cV:L →+* V:=(e.comp (algebraMap L Cq.E)).codRestrict V.toSubring (fun c=> by
    change w.value (e (algebraMap L Cq.E c))≤1
    rw [hscale]
    by_cases hc:c=0
    · simp [hc,w.positive.ne']
    · rw [show w₀ (algebraMap L Cq.E c)=1 from (F.place γ).on_constants c hc,one_pow])
  let cκ:=π.comp cV
  have hsmall (b:V) :π b=0↔w.value (b:A.M)<1 :=
    (IsLocalRing.residue_eq_zero_iff b).trans w.value.mem_maximalIdeal_iff
  have hres :π.comp i=cκ.comp j:= by
    apply RingHom.ext
    intro c
    change π (i c)=π (cV (j c))
    rw [← sub_eq_zero,← map_sub,hsmall]
    change w.value (e (c:Cq.E)-e (algebraMap L Cq.E (j c)))<1
    rw [← map_sub,hscale,show w₀=(F.place γ).value from rfl,F.value γ hγ,hj]
    exact pow_lt_one₀ zero_le (laurent_sub a c ((F.value γ hγ c).symm ▸ c.property)) w.positive.ne'
  let x :V:=⟨A.x,hx⟩
  let y :V:=⟨A.y,hy⟩
  let:Algebra L κ:=cκ.toAlgebra
  by_contra hconst
  have ht:Transcendental L (π x) := by
    intro ha
    have hi:=isAlgebraic_iff_isIntegral.mp ha
    obtain ⟨c,hc⟩:=minpoly.mem_range_of_degree_eq_one L (π x)
      (IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible hi))
    apply hconst
    refine ⟨c,(hsmall (x - cV c)).mp ?_⟩
    rw [map_sub,sub_eq_zero]
    exact hc.symm
  let k :=eval₂RingHom cκ (π x)
  have hk :Function.Injective k :=transcendental_iff_injective.mp ht
  let ι:=mapRingHom O.subtype
  let ρ:=mapRingHom j
  obtain ⟨g,hg⟩ : ∃ g:O[X][X],g.map ι=F.f :=
    (mem_map_range ι).mpr (fun n =>
      (mem_map_range O.subtype).mpr (fun m=>⟨⟨_,F.integral γ hγ n m⟩,rfl⟩))
  have hι:Function.Injective ι:=Polynomial.map_injective O.subtype O.subtype_injective
  have hd:g.natDegree=F.d:= by
    change g.natDegree=F.f.natDegree
    rw [← hg,natDegree_map_eq_of_injective hι]
  have hpos :0<g.natDegree :=hd.symm ▸ F.positive
  have hlead:ρ g.leadingCoeff≠0:= by
    let n:=(F.f.coeff F.d).natDegree
    have h:O.subtype (g.leadingCoeff.coeff n)=1 := by
      have h' := congrArg (fun f :Cq.E[X][X]=>(f.coeff F.d).coeff n) hg
      have hn:g.leadingCoeff=g.coeff F.d:= by rw [← hd,coeff_natDegree]
      rw [hn]
      exact (show O.subtype ((g.coeff F.d).coeff n)=(F.f.coeff F.d).leadingCoeff by
        simpa only [coeff_map,ι,coe_mapRingHom,n,coeff_natDegree] using h').trans F.normalized
    have hone :g.leadingCoeff.coeff n = 1 :=O.subtype_injective (h.trans (map_one _).symm)
    intro hz
    have :=congrArg (fun f :L[X]=>f.coeff n) hz
    exact one_ne_zero (by simpa only [ρ,coe_mapRingHom,coeff_map,coeff_zero,hone,map_one] using this)
  have hdiscr :ρ g.discr≠0:= by
    have hdmap :ι g.discr=F.f.discr := by rw [← discr_map ι hι g hpos,hg]
    let n:=F.f.discr.natDegree
    have h:=congrArg (fun f :Cq.E[X]=>f.coeff n) hdmap
    simp only [ι,coe_mapRingHom,coeff_map] at h
    change O.subtype (g.discr.coeff n)=F.f.discr.leadingCoeff at h
    have hu:w₀ (g.discr.coeff n:Cq.E)=1 := by
      change w₀ (O.subtype (g.discr.coeff n))=1
      rw [h]
      exact hunit
    have hn:j (g.discr.coeff n)≠0:= by
      rw [hj]
      exact coeff_nonzero_of_val_eq ((F.value γ hγ _).symm.trans hu)
    intro hz
    apply hn
    simpa only [ρ,coe_mapRingHom,coeff_map,coeff_zero] using
      congrArg (fun f :L[X]=>f.coeff n) hz
  have hs :ρ (g.resultant g.derivative g.natDegree (g.natDegree-1))≠0:= by
    rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos),map_mul,map_mul,
      map_pow,map_neg,map_one]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) hlead) hdiscr
  let ev :=eval₂RingHom (eval₂RingHom i x) y
  have hev (f :O[X][X]) : (ev f :A.M)=evalXY (f.map ι) A.x A.y := by
    change V.subtype (f.eval₂ (eval₂RingHom i x) y)= _
    rw [eval_map₂ O.subtype i e V.subtype rfl]
    rfl
  have hmap (f :O[X][X]) :π (ev f)=(f.map (k.comp ρ)).eval (π y) := by
    change π (f.eval₂ (eval₂RingHom i x) y)= _
    rw [eval_map₂ j i cκ π hres,eval₂_eq_eval_map,Polynomial.map_map]
  have hr : (g.map (k.comp ρ)).eval (π y)=0:= by
    rw [← hmap,show ev g=0 from Subtype.ext (by rw [hev,hg]; exact A.equation),map_zero]
  have hp: (g.map (k.comp ρ)).derivative.eval (π y)=0:= by
    rw [derivative_map,← hmap,hsmall,hev,← derivative_map,hg]
    exact hpolar
  exact (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero
    (k.comp ρ) g le_rfl hpos ((map_ne_zero_iff k hk).mpr hs) (π y) hr) hp
end
end qeBKasb
end
section
set_option autoImplicit true
namespace qeBKasb
def c1 :Prop :=qZn79Eb.c1
def c2 :Prop :=qZn79Eb.c2
def c3:Prop :=qZn79Eb.c3
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) :q0mTRkc.c6 :=
 qZn79Eb.of_children h1 h2 h3 vertical
end qeBKasb
end
