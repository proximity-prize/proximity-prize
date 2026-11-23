import ProximityPrize.SubmissionLower.ZMNM9Ma
import ProximityPrize.SubmissionLower.ZsE91Ed
set_option Elab.async false
set_option maxRecDepth 4000
namespace qoCymac
noncomputable section
open Polynomial WithZero
open P5 (K p)
open cu (L)
open E7 (CurveField CurvePlace KB)
open P5_7_7 (phys)
open qNu3xvc
open qqi5QRb (pointVal)
open private val_poly_lt val_uniformizer val_poly exp_uniformizer_pow small_value from ProximityPrize.SubmissionLower.ZsE91Ed
open scoped Classical
def c1 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (w:CurvePlace L E)
    (a :E →ₐ[L] LaurentSeries L),CurveField L E →
    (∀ c,w.value c=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰) (a c)) →
    ∃ δ:Derivation L E E,LocalDerivation a w δ
def c2 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (S:Sections A)
    (γ:K) (hγ:γ∈S.marks) (δ:Derivation L E E),
    LocalDerivation (S.atPlace γ hγ) (S.place γ) δ →
    ∀ x :L,∃ r :Bool,Nonempty (MarkChart A S γ hγ δ x r)
def c3:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (S:Sections A)
    (γ:K),γ∈S.marks→2≤A.d→A.d<p →
    ∀ (r :Bool) (v :GraphVal A r),SeedScale v (S.place γ) →
    v.val (polar A r)<1→ResidueConstant v (amm A)
def c4 :Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (w:CurvePlace L E),
    CurveField L E → ∀ r :Bool,IsNoetherianRing (Normal A w r) ∧
      Module.Finite (Chart A w r) (Normal A w r)
def c5:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (w:CurvePlace L E)
    (r :Bool),IsNoetherianRing (Normal A w r) →
    ∀ (M:Ideal (Chart A w r)) [M.IsPrime] (u:EC A),
      (∀ a :Chart A w r,a∉M → ¬ IsIntegral (Chart A w r) ((a :EC A)*u)) →
      ∃ P:Ideal (Normal A w r),P.IsPrime∧P.height = 1 ∧
        P.comap (algebraMap (Chart A w r) (Normal A w r))≤M ∧ ¬ NormalRegular P u
def c6:Prop :=
  ∀ {E :Type} [Field E] [Algebra L E] (A:Equation E) (w:CurvePlace L E),
    CurveField L E → ∀ r :Bool,IsNoetherianRing (Normal A w r) →
    Module.Finite (Chart A w r) (Normal A w r) →
    ∀ (P:Ideal (Normal A w r)),P.IsPrime→P.height = 1 →
      ∃ v :GraphVal A r,
        (∀ a :Chart A w r,v.val (a :EC A)≤1) ∧
        (∀ a :Chart A w r,
          v.val (a :EC A)<1↔algebraMap (Chart A w r) (Normal A w r) a∈P) ∧
        (∀ u:EC A,v.val u≤1↔NormalRegular P u) ∧
        (SeedScale v w→ResidueConstant v (amm A) →
          ¬ ResidueConstant v (jU A r) ∨ ¬ ResidueConstant v (jet A r))
variable {E :Type} [Field E] [Algebra L E] {A:Equation E} {S:Sections A}
 {γ:K} {hγ:γ∈S.marks} {δ:Derivation L E E} {x :L} {r :Bool}
private abbrev R:=Chart A (S.place γ) r
private def atIntegers (T:MarkChart A S γ hγ δ x r) :
  R (S:=S) (γ:=γ) (r :=r) →+* (pointVal x).valuationSubring :=
 T.map.toRingHom.codRestrict (pointVal x).valuationSubring.toSubring T.regular
private def center (T:MarkChart A S γ hγ δ x r) :Ideal (R (S:=S) (γ:=γ) (r :=r)) :=
 (IsLocalRing.maximalIdeal (pointVal x).valuationSubring).comap (atIntegers T)
private instance (T:MarkChart A S γ hγ δ x r) : (center T).IsPrime := by
 unfold center
 infer_instance
private theorem bsx (T:MarkChart A S γ hγ δ x r)
   (a :R (S:=S) (γ:=γ) (r :=r)) :
   a∈center T↔pointVal x (T.map a)<1 :=
 (pointVal x).mem_maximalIdeal_iff (a :=atIntegers T a)
private theorem integral_specializes (T:MarkChart A S γ hγ δ x r)
  (b g:R (S:=S) (γ:=γ) (r :=r)) (hg:T.map g≠0)
  (hi:IsIntegral (R (S:=S) (γ:=γ) (r :=r)) ((b:EC A)/g)) :
  pointVal x (T.map b/T.map g)≤1 := by
 let j:R (S:=S) (γ:=γ) (r :=r) →+* EC A:=algebraMap _ _
 obtain ⟨f,hf,hzero⟩:=hi
 have hg' : g≠0:= fun e=>hg (by simp [e])
 have hscaled:=scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero
  (show Function.Injective j from Subtype.val_injective) hzero
  (mem_nonZeroDivisors_iff_ne_zero.mpr hg')
 have he : (f.scaleRoots g).eval b=0:= by
  apply (show Function.Injective j from Subtype.val_injective)
  rw [← eval₂_id,hom_eval₂,RingHom.comp_id,map_zero]
  exact hscaled
 have hs :=congrArg T.map he
 change T.map.toRingHom ((f.scaleRoots g).eval b)= _ at hs
 rw [← eval₂_id,hom_eval₂,RingHom.comp_id,map_zero] at hs
 have hh:=scaleRoots_eval₂_mul (p:=f) T.map.toRingHom (T.map b/T.map g) g
 rw [show T.map.toRingHom g=T.map g from rfl,
  show T.map g*(T.map b/T.map g)=T.map b by field_simp] at hh
 have hf' : f.eval₂ T.map.toRingHom (T.map b/T.map g)=0 :=
  (mul_eq_zero.mp (hh.symm.trans hs)).resolve_left (pow_ne_zero _ hg)
 apply ((Valuation.valuationSubring.integers (pointVal x)).isIntegral_iff_v_le_one).mp
 refine ⟨f.map (atIntegers T),hf.map _,?_⟩
 rw [eval₂_map]
 exact hf'
private theorem mark_phys (T:MarkChart A S γ hγ δ x r) (y :L) :
  T.map (xSub A (S.place γ) r y)=phys (Polynomial.X - C y) := by
 rw [xSub,map_sub,T.physical_eq,AlgHom.commutes,map_sub]
 rfl
private theorem specialized_pole (T:MarkChart A S γ hγ δ x r)
  (hx : (S.den γ).IsRoot x) {m:ℕ} (hm:m<(S.den γ).rootMultiplicity x) :
  1<pointVal x (T.map ((xSub A (S.place γ) r x)^m*T.num)/T.map T.sep) := by
 have hn : ¬ (S.num γ).IsRoot x := by
  intro hn
  obtain ⟨a,b,h⟩:=S.reduced γ hγ
  have q:=congrArg (fun f :L[X]=>f.eval x) h
  change (S.num γ).eval x=0 at hn
  change (S.den γ).eval x=0 at hx
  simp only [eval_add,eval_mul,hn,hx,mul_zero,add_zero,eval_one,zero_ne_one] at q
 have hn' : S.num γ≠0:= fun h=>hn (by simp [h])
 obtain ⟨u,hu,he⟩:=T.gK6
 rw [map_mul,map_pow,mul_div_assoc,he,map_mul,map_pow,mark_phys,val_uniformizer,
  map_mul,hu,one_mul,map_div₀,val_poly x _ hn',val_poly x _ (S.den_ne γ hγ),
  rootMultiplicity_eq_zero hn,Nat.cast_zero,neg_zero,exp_zero,exp_uniformizer_pow,
  ← mul_div_assoc,mul_one]
 apply (one_lt_div₀ exp_pos).2
 exact exp_lt_exp.mpr (neg_lt_neg (by exact_mod_cast hm))
private theorem restriction (v :GraphVal A r) (w:CurvePlace L E)
   (hreg : ∀ a :Chart A w r,v.val (a :EC A)≤1)
   (hvert : ¬ (∀ a :E,a≠0→v.val (seed A a)=1)) :SeedScale v w:= by
 obtain ⟨t,ht⟩:=w.normalized (exp (-1 :ℤ))
 have ht0:t≠0:= fun e=>exp_ne_zero (by rw [← ht,e,map_zero])
 have hw (a :E) (ha :w.value a≤1) :v.val (seed A a)≤1 :=
   hreg (aee A w r ⟨a,ha⟩)
 have ht1 :=hw t (ht ▸ (exp_le_one_iff.mpr (by decide : (-1 :ℤ)≤0)))
 have hu (a :E) (ha :w.value a=1) :v.val (seed A a)=1 := by
   have hi:=hw a⁻¹ (by rw [map_inv₀,ha,inv_one])
   rw [map_inv₀,map_inv₀,inv_le_one₀ (by
     exact (v.val.pos_iff).mpr ((_root_.map_ne_zero (seed A)).mpr (by rintro rfl; simp at ha)))] at hi
   exact le_antisymm (hw a ha.le) hi
 have hrep (a :E) (ha :a≠0) :
     v.val (seed A a)=v.val (seed A t)^(-log (w.value a)) := by
   let k :=log (w.value a)
   have hwk :w.value a=exp k :=(exp_log (w.value.ne_zero_iff.mpr ha)).symm
   have htK:w.value (a*t^k)=1 := by
     rw [map_mul,map_zpow₀,ht,hwk,← exp_zsmul,← exp_add]
     simp only [Int.zsmul_eq_mul,mul_neg,mul_one,add_neg_cancel,exp_zero]
   have h:=hu (a*t^k) htK
   rw [map_mul (seed A),map_zpow₀ (seed A),map_mul,map_zpow₀] at h
   exact (eq_inv_of_mul_eq_one_left h).trans (zpow_neg _ _).symm
 have htlt:v.val (seed A t)<1 := by
   refine lt_of_le_of_ne ht1 fun he=>hvert fun a ha => ?_
   rw [hrep a ha,he,one_zpow]
 have htn:v.val (seed A t)≠0:=(v.val.ne_zero_iff).mpr ((_root_.map_ne_zero (seed A)).mpr ht0)
 let n:=(-log (v.val (seed A t))).toNat
 have hn0:=(log_lt_log htn one_ne_zero).mpr htlt
 rw [log_one] at hn0
 have hn: (n:ℤ) = -log (v.val (seed A t)) :=Int.toNat_of_nonneg (by omega)
 refine ⟨n,by omega,fun a => ?_⟩
 by_cases ha :a=0
 · rw [ha,map_zero,map_zero,map_zero,zero_pow (by omega :n≠0)]
 · nth_rw 1 [← exp_log (w.value.ne_zero_iff.mpr ha)]
   rw [hrep a ha,← exp_log htn,← exp_zsmul,← exp_nsmul,Int.zsmul_eq_mul,nsmul_eq_mul,hn]
   rw [neg_mul,neg_mul,mul_comm]
private theorem charge_order (v :GraphVal A r) (T:MarkChart A S γ hγ δ x r)
  {m:ℕ} (hx :v.val (amm A - constant A x)<1)
  (hn:v.val (T.num :EC A)≤1) (hp:polar A r≠0)
  (h:1<v.val ((amm A - constant A x)^m*variation A r δ)) :
  m<poleCharge v := by
 by_contra! hle
 have hlog : -(m:ℤ)≤log (v.val (polar A r)) := by
  unfold poleCharge KB at hle
  omega
 have hp' : v.val (polar A r)≠0:=(v.val.ne_zero_iff).2 hp
 have hp'' := (le_log_iff_exp_le hp').mp hlog
 rw [variation,← T.num_eq,← mul_div_assoc,map_div₀,map_mul,map_pow] at h
 apply ((one_lt_div₀ (zero_lt_iff.mpr hp')).mp h).not_ge
 calc
  _≤v.val (amm A - constant A x)^m:=mul_le_of_le_one_right' hn
  _≤exp (-1 :ℤ)^m:=pow_le_pow_left₀ zero_le (small_value hx) _
  _≤_:=exp_uniformizer_pow m ▸ hp''
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
   qNu3xvc.c3:= by
 intro E _ _ A S hcurve hd hp Oj γ hγ x hx
 let w:=S.place γ
 obtain ⟨δ,hδ⟩:=h1 w (S.atPlace γ hγ) hcurve (S.value γ hγ)
 obtain ⟨r,⟨T⟩⟩:=h2 A S γ hγ δ hδ x
 let k :=(S.den γ).rootMultiplicity x
 let m:=k-1
 let b:=(xSub A w r x)^m*T.num
 let u:EC A:=(b:EC A)/T.sep
 let M:=center T
 have hx' := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)
 have hk :0<k :=(rootMultiplicity_pos (S.den_ne γ hγ)).mpr hx'
 have hmark :1<pointVal x (T.map b/T.map T.sep) :=
   specialized_pole T hx' (by change k-1<k; omega)
 have hnon (a :Chart A w r) (ha :a∉M) : ¬ IsIntegral (Chart A w r) ((a :EC A)*u) := by
   intro hi
   have hval :pointVal x (T.map a)=1 :=
     le_antisymm (T.regular a) (le_of_not_gt (fun h=>ha ((bsx T a).mpr h)))
   have h' := integral_specializes T (a*b) T.sep T.simple
     (by simpa only [u,Subalgebra.coe_mul,mul_div_assoc] using hi)
   rw [map_mul,mul_div_assoc,map_mul,hval,one_mul] at h'
   exact hmark.not_ge h'
 obtain ⟨hnoeth,hfin⟩:=h4 A w hcurve r
 obtain ⟨P,hP,hht,hPM,hnonP⟩:=h5 A w r hnoeth M u hnon
 obtain ⟨v,hbounded,hv,hreg,hcurveRes⟩:=h6 A w hcurve r hnoeth hfin P hP hht
 have hu:u=(amm A - constant A x)^m*variation A r δ:= by
   simp only [u,b,Subalgebra.coe_mul,Subalgebra.coe_pow,coe_xSub,variation,T.sep_eq,
     T.num_eq,mul_div_assoc]
 have hlarge :1<v.val ((amm A - constant A x)^m*variation A r δ) := by
   rw [← hu]
   exact lt_of_not_ge (fun h=>hnonP ((hreg u).mp h))
 have hvar :1<v.val (variation A r δ) := by
   refine hlarge.trans_le ?_
   rw [map_mul,map_pow]
   exact mul_le_of_le_one_left' (pow_le_one₀ zero_le (coe_xSub A w r x ▸ hbounded (xSub A w r x)))
 have hsep:polar A r≠0:= fun e=>T.simple (by
   rw [show T.sep=0 from Subtype.ext (T.sep_eq.trans e),map_zero])
 have hpolar :v.val (polar A r)<1 := by
   rw [variation,← T.num_eq,map_div₀] at hvar
   exact ((one_lt_div₀ (v.val.pos_iff.mpr hsep)).mp hvar).trans_le (hbounded T.num)
 have hscale :=restriction v w hbounded (fun h=>hvar.not_ge (Oj r v δ h))
 obtain ⟨y,hy⟩:=h3 A S γ hγ hd hp r v hscale hpolar
 have hxy :=(bsx T (xSub A w r y)).mp
   (hPM ((hv _).mp (by rwa [coe_xSub])))
 rw [mark_phys,val_poly_lt,IsRoot.def,eval_sub,eval_X,eval_C,sub_eq_zero] at hxy
 have hsmall:v.val (amm A - constant A x)<1 :=hxy ▸ hy
 have hcharge :=charge_order v T hsmall (hbounded T.num) hsep hlarge
 exact ⟨r,v,⟨hscale,hsmall,hcurveRes hscale ⟨x,hsmall⟩⟩,by change k≤poleCharge v; omega⟩
end
end qoCymac
