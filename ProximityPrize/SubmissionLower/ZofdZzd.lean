import ProximityPrize.SubmissionLower.ZL8fo3b
set_option Elab.async false
open _root_ renaming MvPolynomial.C → znf, MvPolynomial.eval → zY9, MvPolynomial.eval_C → z9X, MvPolynomial.totalDegree_C → ziW, MvPolynomial.totalDegree_add → zdH, MvPolynomial.totalDegree_mul → zhM, Nat.mul_le_mul_right → ztf, Polynomial.map_mul → zNl, Polynomial.map_pow → z5m
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace qRoCwuc
noncomputable section
open Polynomial Finset
open P5 (K I node blockLength p)
open P5_7 (midAgreement)
open cu (L j9 jz)
open DQ (DT)
open Cu
open quN7Z4a (Sheet OF)
open private line_bound from ProximityPrize.SubmissionLower.ZFh47Da
variable {C₀:sQ} [Fact (Irreducible C₀)] {J H T z s}
private theorem generic_nonsquare (S:Sheet C₀ J 2 H T z s) (Q: (oO C₀)[X]) :
   genericDisc S≠Q^2 := by
 intro hs
 let e :=F5 C₀
 have heinj:Function.Injective e :=
   IsFractionRing.injective (oO C₀)[X] (y7 C₀)
 let a (j:ℕ) :=e ((coeff S j).map (coord S))
 let:CharP (y7 C₀) p :=
   charP_of_injective_ringHom ((Mr C₀).comp jz).injective p
 let:NeZero (2 :y7 C₀) :=
   ⟨fun h=>(by decide : ¬ p∣2) ((CharP.cast_eq_zero_iff _ p 2).mp h)⟩
 have h2 :S.root.equation.coeff 2≠0:= by
   have hc:=congrArg (fun j:ℕ=>S.root.equation.coeff j) S.root.degree
   rw [coeff_natDegree] at hc
   exact hc ▸ leadingCoeff_ne_zero.mpr S.root.primitive.ne_zero
 have ha :a 2≠0:= by
   change e _≠0
   rw [map_ne_zero_iff _ heinj,coeff_generic]
   exact mul_ne_zero (C_ne_zero.mpr S.bY.scale.ne_zero) h2
 have hdisc:discrim (a 2) (a 1) (a 0)=e Q*e Q:= by
   have h:=congrArg e hs
   simpa only [genericDisc,disc,discrim,a,Polynomial.map_sub,zNl,
     z5m,Polynomial.map_ofNat,map_sub,map_mul,map_pow,map_ofNat,pow_two] using h
 obtain ⟨x,hx⟩:=exists_quadratic_eq_zero ha ⟨e Q,hdisc⟩
 let f :=S.root.equation.map e
 have hdeg:f.natDegree=2 :=
   (natDegree_map_eq_of_injective heinj _).trans S.root.degree
 apply S.root.irreducible.not_isRoot_of_natDegree_ne_one (by change f.natDegree≠1; omega) (x :=x)
 have he :=congrArg (fun F: ((oO C₀)[X])[X]=>(F.map e).eval x)
   S.bY.generic_eq
 rw [zNl,Polynomial.map_C,eval_mul,eval_C] at he
 have hf :=congrArg (fun F:DQ.XO S.n =>
   ((F.map (mapRingHom (coord S))).map e).eval x) (quad_form S.bY.degree.1)
 have hz : (((S.bY.equation.map (mapRingHom (coord S))).map e).eval x)=0:= by
   refine hf.trans ?_
   simpa only [Polynomial.map_add,zNl,Polynomial.map_C,Polynomial.map_X,
     z5m,coe_mapRingHom,eval_add,eval_mul,eval_pow,eval_C,eval_X,
     coeff,a,pow_two] using hx
 have he' := he
 change ((S.bY.equation.map (mapRingHom (coord S))).map e).eval x =
   e (C (S.bY.scale :oO C₀))*f.eval x at he'
 rw [hz] at he'
 exact (mul_eq_zero.mp he'.symm).resolve_left
   ((map_ne_zero_iff _ heinj).mpr (C_ne_zero.mpr S.bY.scale.ne_zero))
theorem genericDisc_ne_zero (S:Sheet C₀ J 2 H T z s) :genericDisc S≠0:= by
 simpa only [zero_pow (by decide :2≠0)] using generic_nonsquare S 0
private def anH (S:Sheet C₀ J 2 H T z s) (j:ℕ) (x :L) :DT S.n :=
 (coeff S j).eval (znf x)
private theorem atNode_map (S:Sheet C₀ J 2 H T z s) (j:ℕ) (x :L) :
  coord S (anH S j x)=((coeff S j).map (coord S)).eval (zT C₀ x) := by
 simpa only [anH,show coord S (MvPolynomial.C x)=zT C₀ x by simp [coord]]
  using (eval_map_apply (p:=coeff S j) (coord S) (MvPolynomial.C x)).symm
private theorem atNode_degree (S:Sheet C₀ J 2 H T z s) (j:ℕ) (x :L) :
  (anH S j x).totalDegree≤1 := by
 classical
 rw [anH,eval_eq_sum_range]
 apply MvPolynomial.totalDegree_finsetSum_le
 intro i _
 exact (zhM _ _).trans (by
  simpa only [coeff,← map_pow,ziW,add_zero] using S.bY.degree.2 j i)
private theorem scaled_degree {n:ℕ} (y :L) {q:DT n} {h:ℕ}
   (hq:q.totalDegree≤h) : (znf y*q).totalDegree≤h :=
 (zhM _ _).trans (by simpa only [ziW,zero_add] using hq)
private theorem atNode_primitive (S:Sheet C₀ J 2 H T z s) (x :L)
   (ha :coord S (anH S 2 x)=0) (hb:coord S (anH S 1 x)=0)
   (hc:coord S (anH S 0 x)=0) :False := by
 let t:=zT C₀ x
 have extract (j:ℕ) (h:coord S (anH S j x)=0) :
     (Polynomial.X - C t)∣S.root.equation.coeff j:= by
   rw [dvd_iff_isRoot,IsRoot.def]
   rw [atNode_map,coeff_generic,eval_mul,eval_C] at h
   exact (mul_eq_zero.mp h).resolve_left S.bY.scale.ne_zero
 apply not_isUnit_X_sub_C t
 apply S.root.primitive
 apply (C_dvd_iff_dvd_coeff _ _).mpr
 intro i
 by_cases hi:i≤2
 · interval_cases i
   exacts [extract _ hc,extract _ hb,extract _ ha]
 · have hlt:S.root.equation.natDegree< i:=S.root.degree.trans_lt (Nat.lt_of_not_ge hi)
   rw [coeff_eq_zero_of_natDegree_lt hlt]
   exact dvd_zero _
private theorem marked_at (S:Sheet C₀ J 2 H T z s) {γ:K} (hγ:γ∈T) (x :L) :
  let y :=(j9 (s γ)).eval x
  let r :=zY9 (S.parameter γ)
  r (anH S 2 x)*y^2+r (anH S 1 x)*y+r (anH S 0 x)=0:= by
 have he (j:ℕ) : ((coeff S j).map (zY9 (S.parameter γ))).eval x =
    zY9 (S.parameter γ) (anH S j x) := by
  simpa only [anH,z9X] using
    eval_map_apply (p:=coeff S j) (zY9 (S.parameter γ)) (znf x)
 simpa only [map_add,map_mul,map_pow,map_zero,coe_evalRingHom,he] using
  congrArg (evalRingHom x) (marked_eq S hγ)
private def form {R:Type*} [Semiring R] (a b c x :R) :R:=a*x^2+b*x+c
private def sep {R:Type*} [Semiring R] (a b x :R) :R:=2*a*x+b
private theorem map_form {R R' : Type*} [Semiring R] [Semiring R'] (e :R →+* R') (a b c x :R) :
 e (form a b c x)=form (e a) (e b) (e c) (e x) := by simp [form]
private theorem map_sep {R R' : Type*} [Semiring R] [Semiring R'] (e :R →+* R') (a b x :R) :
 e (sep a b x)=sep (e a) (e b) (e x) := by simp only [sep,map_add,map_mul,map_ofNat]
private theorem map_discrim {R R' : Type*} [Ring R] [Ring R'] (e :R →+* R') (a b c:R) :
 e (discrim a b c)=discrim (e a) (e b) (e c) := by simp only [discrim,map_sub,map_pow,map_mul,map_ofNat]
private theorem constant_eval_square {F:Type*} [Field F] {Δ:F[X]} {t r :F}
  (hn : ∀ Q,Δ≠Q^2) (hc:ConstantOddPart Δ) (hr :Δ.eval t=r^2) :r=0:= by
 obtain ⟨a,Q,hf⟩:=hc
 rw [hf,eval_mul,eval_pow,eval_C] at hr
 by_contra hnz
 have hQ:Q.eval t≠0:= by
  intro he
  exact (pow_ne_zero 2 hnz) (by simpa [he] using hr.symm)
 have ha :a=(r/Q.eval t)^2 := by
  rw [div_pow,eq_div_iff (pow_ne_zero 2 hQ)]
  exact hr
 apply hn (C (r/Q.eval t)*Q)
 rw [hf,ha,mul_pow,map_pow]
private theorem double_root (S:Sheet C₀ J 2 H T z s)
  (hconst:ConstantOddPart (genericDisc S)) (x :L) {y :oO C₀}
  (h:form (coord S (anH S 2 x)) (coord S (anH S 1 x)) (coord S (anH S 0 x)) y=0) :
  sep (coord S (anH S 2 x)) (coord S (anH S 1 x)) y=0:= by
 apply constant_eval_square (generic_nonsquare S) hconst (t:=zT C₀ x)
 change evalRingHom _ (mapRingHom (coord S) (discrim _ _ _))= _
 rw [map_discrim,map_discrim]
 simp only [coe_mapRingHom,coe_evalRingHom,← atNode_map,sep]
 exact discrim_eq_sq_of_quadratic_eq_zero (by simpa only [form,pow_two] using h)
private theorem miss_zero {R:Type*} [CommRing R] [IsDomain R] {a b c w v :R}
  (hw:form a b c w=0) (hs :sep a b w=0) (hv :form a b c v=0) (hne :v≠w) :
  a=0:= by
 have h:a*(v-w)^2=0:= by
  simp only [form,sep] at hw hs hv
  linear_combination hv - hw-(v-w)*hs
 exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 (sub_ne_zero.mpr hne))
private def wordCut (S:Sheet C₀ J 2 H T z s) (i:I) (w:K) :DT S.n :=
 let x :=algebraMap K L (node i)
 form (anH S 2 x) (anH S 1 x) (anH S 0 x) (znf (algebraMap K L w))
private theorem node_counts (S:Sheet C₀ J 2 H T z s) (hz :Set.InjOn z (T:Set K))
    (hconst:ConstantOddPart (genericDisc S)) (i:I) (w:K) :
    (coord S (wordCut S i w)≠0→(T.filter fun γ=>(s γ).eval (node i)=w).card≤H) ∧
    (coord S (wordCut S i w)=0→(T.filter fun γ=>(s γ).eval (node i)≠w).card≤H) := by
  classical
  let x :=algebraMap K L (node i)
  let y :=algebraMap K L w
  let a :=anH S 2 x
  let b:=anH S 1 x
  let c:=anH S 0 x
  let q:=wordCut S i w
  let r :=sep a b (znf y)
  have markval (γ:K) (hγ:γ∈T) :
      let e :=zY9 (S.parameter γ)
      form (e a) (e b) (e c) (algebraMap K L ((s γ).eval (node i)))=0:= by
    have h:=marked_at S hγ x
    dsimp only at h
    rw [show (j9 (s γ)).eval x=algebraMap K L ((s γ).eval (node i)) from eval_map_apply _ _] at h
    exact h
  constructor
  · intro hproper
    change coord S q≠0 at hproper
    have dq:q.totalDegree≤1 := by
      change (form a b c (znf y)).totalDegree≤1
      rw [form,← map_pow,mul_comm a,mul_comm b]
      exact (zdH _ _).trans (max_le
        ((zdH _ _).trans
          (max_le (scaled_degree _ (atNode_degree S 2 x)) (scaled_degree _ (atNode_degree S 1 x))))
        (atNode_degree S 0 x))
    refine (dSG S hz q hproper _ (filter_subset _ _) ?_).trans
      ((ztf H dq).trans_eq (one_mul _))
    intro γ hγ
    obtain ⟨hγ,hy⟩:=mem_filter.mp hγ
    change (zY9 (S.parameter γ)) (form a b c (znf y))=0
    rw [map_form,z9X]
    simpa only [hy] using markval γ hγ
  · intro hq
    change coord S q=0 at hq
    have hq' : form (coord S a) (coord S b) (coord S c) (coord S (znf y))=0:= by
      change coord S (form a b c (znf y))=0 at hq
      rwa [map_form] at hq
    have hr :coord S r=0:= by
      rw [show r= _ from rfl,map_sep]
      exact double_root S hconst x hq'
    have ha :coord S a≠0:= by
      intro ha
      have h:=hr
      rw [show r= _ from rfl,map_sep] at h
      have hb:coord S b=0:= by simpa only [sep,ha,mul_zero,zero_mul,zero_add] using h
      have hc:coord S c=0:= by simpa only [form,ha,hb,zero_mul,zero_add] using hq'
      exact atNode_primitive S x ha hb hc
    refine (dSG S hz a ha _ (filter_subset _ _) ?_).trans
      ((ztf H (atNode_degree S 2 x)).trans_eq (one_mul _))
    intro γ hγ
    obtain ⟨hγ,hne⟩:=mem_filter.mp hγ
    have hq'' := marked_zero S q hq hγ
    have hr' := marked_zero S r hr hγ
    change (zY9 (S.parameter γ)) (form a b c (znf y))=0 at hq''
    rw [map_form,z9X] at hq''
    rw [show r= _ from rfl,map_sep,z9X] at hr'
    exact miss_zero hq'' hr' (markval γ hγ) ((algebraMap K L).injective.ne hne)
theorem dO2 (S:Sheet C₀ J 2 H T z s) (hz :Set.InjOn z (T:Set K))
   {w:I→K} {D:ℕ} (W:OF T s w D) (hD:D < midAgreement)
   (hconst:ConstantOddPart (genericDisc S)) :
   (T.card:ℚ)≤3*(blockLength:ℚ)/(midAgreement-D:ℕ)*H+1 := by
 classical
 let sites :=univ.filter fun i=>coord S (wordCut S i (w i))=0
 apply line_bound W hD sites
 · intro i hi
   exact (node_counts S hz hconst i (w i)).1 (fun h=>hi (mem_filter.mpr ⟨mem_univ _,h⟩))
 · intro i hi
   exact (node_counts S hz hconst i (w i)).2 (mem_filter.mp hi).2
end
end qRoCwuc
