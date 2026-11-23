import ProximityPrize.SubmissionLower.ZpQKUZd
import ProximityPrize.SubmissionLower.ZR3mCBd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, CommRing → za6, Field → zrb, Finset.mem_image_of_mem → zPV, Function.Injective → zq4, IsLocalization.Away.lift → ztx, IsLocalization.Away.lift_eq → zaz, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.map_prod → zeg, Polynomial.map_sub → z3A, RingHom.comp_apply → zQb, RingHom.comp_assoc → zxS, RingHom.congr_fun → zLs, RingHom.ext → zz4, RingHom.id → zz5
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qApzjua
noncomputable section
open Polynomial Finset qNu3xvc
open cu (L)
open P5_7_1_7_4_3_4 (Pencil relativePolar bix)
open qv2t4Be (CommonField charpoly_split)
open qZu9hjc (Slice atPair jacobian)
open scoped Classical
local notation "sliceGauge" => qZu9hjc.gauge
variable {E F:Type} [zrb E] [zrb F] [zZE (RatFunc E) F]
variable {z :E} (T:Specialization (F:=F) z)
theorem residue_ne (a :T.ring) (h: (a :F)≠0) (hi: (a :F)⁻¹∈T.ring) :
  T.eval a≠0:= by
 have ht:a*(⟨(a :F)⁻¹,hi⟩:T.ring)=1 :=Subtype.ext (mul_inv_cancel₀ h)
 intro hz
 have hh:=congrArg T.eval ht
 rw [map_mul,hz,zero_mul,map_one] at hh
 exact zero_ne_one hh
def liftedConstant:E →+* T.ring :=T.base.comp z1z
theorem cTK :
  T.ring.subtype.comp (liftedConstant T)=(algebraMap (RatFunc E) F).comp RatFunc.C:= by
 rw [liftedConstant,← zxS,T.ek]
 apply zz4
 intro a
 simp only [zQb,RatFunc.algebraMap_C]
theorem special_constant:T.eval.comp (liftedConstant T)=algebraMap E (AlgebraicClosure E) := by
 rw [liftedConstant,← zxS,T.special]
 apply zz4
 intro a
 simp only [zQb,coe_evalRingHom,eval_C]
theorem generic_parameter :
  (T.base z7y:F)=algebraMap (RatFunc E) F RatFunc.X:= by
 change T.ring.subtype (T.base z7y)= _
 simpa only [zQb,RatFunc.algebraMap_X] using zLs T.ek z7y
theorem special_parameter :
  T.eval (T.base z7y)=algebraMap E (AlgebraicClosure E) z := by
 simpa only [zQb,coe_evalRingHom,eval_X] using zLs T.special z7y
private def specializePolynomial (z :E) (N : (RatFunc E)[X]) :E[X] :=
 ∑ j∈N.support,monomial j (RatFunc.eval (zz5 E) z (N.coeff j))
private theorem coeff_specializePolynomial (z :E) (N : (RatFunc E)[X]) (j:ℕ) :
   (specializePolynomial z N).coeff j=RatFunc.eval (zz5 E) z (N.coeff j) := by
 rw [specializePolynomial,finsetSum_coeff]
 simp only [coeff_monomial,Finset.sum_ite_eq']
 split_ifs with h
 · rfl
 · simp [Polynomial.notMem_support_iff.mp h]
variable [zZE L E] {A:Equation E}
theorem from_specialization (C:Pencil A) (a :ℕ) (ha :A.b+A.d*A.s≤a) (ht:C.tilt≠0)
    (hJac:pencilJac (KM A false) A.f C.num C.den (C.base RatFunc.X)≠0)
    (hs :letI:=C.base.toAlgebra; Specializes E (CommonField (RatFunc E) (EC A))) :
    ∃ bad:Finset L,∀ z∉bad,∃ S:Slice A.f A.s a,∀ j,
      S.N.coeff j=RatFunc.eval (zz5 E) (algebraMap L E z)
        ((bix C.base (relativePolar C) C.finite).coeff j) := by
  classical
  let _:=C.base.toAlgebra
  let _:=C.finite
  let _:=C.separable
  let Ω:Type :=CommonField (RatFunc E) (EC A)
  let I:=EC A →ₐ[RatFunc E] Ω
  let N :=bix C.base (relativePolar C) C.finite
  let J:=pencilJac (KM A false) A.f C.num C.den (C.base RatFunc.X)
  let x (i:I) :=i (amm A)
  let y (i:I) :=i (jU A false)
  let q (i:I) :=i (relativePolar C)
  let Sij (i j:I) :Finset Ω :=
    {x i,y i,q i,(i (P5_7_1_7_4_3_4.gauge A C.tilt))⁻¹,(i (polar A false))⁻¹,
      (i J)⁻¹,(x i-x j)⁻¹,(y i-y j)⁻¹}
  let S:=univ.biUnion fun i=>univ.biUnion (Sij i)
  let U:=N.support.image N.coeff
  obtain ⟨bad,hbad⟩:=hs S U
  let κ:=algebraMap L E
  refine ⟨bad.preimage κ κ.injective.injOn,fun z hz => ?_⟩
  obtain ⟨T,hS,hU⟩:=hbad (κ z) (fun h=>hz (mem_preimage.mpr h))
  have mem (i j:I) {v :Ω} (hv :v∈Sij i j) :v∈T.ring :=
    hS v (mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨j,mem_univ _,hv⟩⟩)
  let xx (i:I) :T.ring :=⟨x i,mem i i (by simp [Sij])⟩
  let yy (i:I) :T.ring :=⟨y i,mem i i (by simp [Sij])⟩
  let qq (i:I) :T.ring :=⟨q i,mem i i (by simp [Sij])⟩
  let e :=liftedConstant T
  let t:=T.base z7y
  let ev (i:I) :=pairEval e (xx i) (yy i)
  let pt (i:I) :=(T.eval (xx i),T.eval (yy i))
  let ev' (i:I) :=pairEval (algebraMap E (AlgebraicClosure E)) (pt i).1 (pt i).2
  have hseed (i:I) :
      i.toRingHom.comp (seed A)=(algebraMap (RatFunc E) Ω).comp RatFunc.C:= by
    apply zz4
    intro c
    exact (congrArg i (C.base_seed c).symm).trans (i.commutes (RatFunc.C c))
  have hgen (i:I) :T.ring.subtype.comp (ev i)=i.toRingHom.comp (KM A false) := by
    dsimp only [ev,e]
    rw [pairEval_comp,← root_coordinates,pairEval_comp,cTK,hseed]
    rfl
  have hsp (i:I) :T.eval.comp (ev i)=ev' i:= by
    dsimp only [ev,e]
    rw [pairEval_comp,special_constant]
  have gen (i:I) (g:E[X][X]) : (ev i g:Ω)=i (KM A false g) :=
    zLs (hgen i) g
  have sp (i:I) (g:E[X][X]) :T.eval (ev i g)=ev' i g :=
    zLs (hsp i) g
  have hParam (i:I) : (t:Ω)=i (C.base RatFunc.X) :=
    (generic_parameter T).trans (i.commutes RatFunc.X).symm
  have hFit (i:I) :ev i A.f=0:= by
    apply Subtype.ext
    change (ev i A.f :Ω)=0
    rw [gen,root_zero,map_zero]
  have hCut (i:I) :ev i C.num - t*ev i C.den=0:= by
    apply Subtype.ext
    change (ev i C.num :Ω)-(t:Ω)*(ev i C.den:Ω)=0
    rw [gen,gen,hParam i,← map_mul,← map_sub,C.base_X,
      div_mul_cancel₀ _ C.den_ne,sub_self,map_zero]
  let w (i:I) :T.ring :=1+e (κ C.tilt)*yy i
  have hw (i:I) : (w i:Ω)=i (P5_7_1_7_4_3_4.gauge A C.tilt) := by
    have hh:=zLs (cTK T) (κ C.tilt)
    change (e (κ C.tilt) :Ω)=algebraMap (RatFunc E) Ω (RatFunc.C (κ C.tilt)) at hh
    change (1 :Ω)+(e (κ C.tilt) :Ω)*y i= _
    have hi:=zLs (hseed i) (κ C.tilt)
    simp only [zQb] at hi
    rw [hh,← hi]
    simp only [P5_7_1_7_4_3_4.gauge,constant,y,κ,map_add,map_one,map_mul]
    rfl
  have hw' (i:I) :T.eval (w i)=sliceGauge 1 C.tilt (pt i).2 := by
    have hh:=zLs (special_constant T) (κ C.tilt)
    change T.eval (e (κ C.tilt))= _ at hh
    simp only [w,map_add,map_one,map_mul,hh,qZu9hjc.gauge,pt]
    rw [IsScalarTower.algebraMap_apply L E (AlgebraicClosure E)]
  have hGauge (i:I) :T.eval (w i)≠0 :=
    residue_ne T (w i) (by rw [hw]; exact (map_ne_zero_iff _ i.injective).mpr C.gauge_ne)
      (by rw [hw]; exact mem i i (by simp [Sij]))
  have hPolar (i:I) :T.eval (ev i A.f.derivative)≠0:= by
    have hp: (ev i A.f.derivative :Ω)=i (polar A false) :=gen i _
    exact residue_ne T _ (hp.symm ▸ (map_ne_zero_iff _ i.injective).mpr C.polar_ne)
      (hp.symm ▸ mem i i (by simp [Sij]))
  have hQ (i:I) :T.eval (qq i) =
      ev' i A.f.derivative/sliceGauge 1 C.tilt (pt i).2^(A.d-2) := by
    have hh:qq i*w i^(A.d-2)=ev i A.f.derivative := by
      apply Subtype.ext
      change q i*(w i:Ω)^(A.d-2)= _
      dsimp only [q]
      rw [hw,gen,← map_pow,← map_mul,relativePolar,
        div_mul_cancel₀ _ (pow_ne_zero _ C.gauge_ne)]
      rfl
    have he :=congrArg T.eval hh
    rw [map_mul,map_pow,hw',sp] at he
    exact (eq_div_iff (pow_ne_zero _ (hw' i ▸ hGauge i))).mpr he
  have hSimple (i:I) :jacobian (algebraMap E _) (pt i).1 (pt i).2 A.f (cut C z)≠0:= by
    let j:=pencilJac (ev i) A.f C.num C.den t
    have hj: (j:Ω)=i J:= by
      change T.ring.subtype j= _
      dsimp only [j]
      rw [map_pencilJac,hgen]
      change pencilJac (i.toRingHom.comp (KM A false)) A.f C.num C.den (t:Ω)=i J
      rw [hParam i]
      exact (map_pencilJac i.toRingHom (KM A false) A.f C.num C.den (C.base RatFunc.X)).symm
    have hj' := residue_ne T j (hj.symm ▸ (map_ne_zero_iff _ i.injective).mpr hJac)
      (hj.symm ▸ mem i i (by simp [Sij]))
    dsimp only [j] at hj'
    rw [map_pencilJac,hsp,special_parameter] at hj'
    exact (jac_cut (algebraMap E (AlgebraicClosure E)) (pt i).1 (pt i).2 C z).symm ▸ hj'
  have hinj:zq4 pt:= by
    intro i j h
    have hx :x i=x j:= by
      by_contra hne
      exact residue_ne T (xx i - xx j) (sub_ne_zero.mpr hne)
        (show (x i-x j)⁻¹∈T.ring from mem i j (by simp [Sij]))
        (by rw [map_sub,sub_eq_zero]; exact congrArg Prod.fst h)
    have hy :y i=y j:= by
      by_contra hne
      exact residue_ne T (yy i - yy j) (sub_ne_zero.mpr hne)
        (show (y i-y j)⁻¹∈T.ring from mem i j (by simp [Sij]))
        (by rw [map_sub,sub_eq_zero]; exact congrArg Prod.snd h)
    exact AlgHom.coe_ringHom_injective (root_hom_ext ((hseed i).trans (hseed j).symm) hx hy)
  let P:T.ring[X] := ∏ i:I,(z7y-Polynomial.C (qq i))
  let c:E →+* RatFunc E :=RatFunc.C
  let _:Infinite (RatFunc E) :=Infinite.of_injective (c.comp κ) (c.injective.comp κ.injective)
  have hP:P.map T.ring.subtype=N.map (algebraMap (RatFunc E) Ω) := by
    change _=(Algebra.lmul (RatFunc E) (EC A) (relativePolar C)).charpoly.map _
    dsimp only [P]
    rw [zeg,charpoly_split (q:=relativePolar C)]
    simp only [z3A,Polynomial.map_X,Polynomial.map_C]
    rfl
  let M:=specializePolynomial (κ z) N
  have hM:M.map (algebraMap E (AlgebraicClosure E))=P.map T.eval := by
    ext j
    simp only [coeff_map,M,coeff_specializePolynomial]
    have hj:=congrArg (fun f :Polynomial Ω=>f.coeff j) hP
    simp only [coeff_map] at hj
    by_cases h:j∈N.support
    · obtain ⟨v,hv,hres⟩:=hU (N.coeff j) (mem_image_of_mem _ h)
      rw [← hres,show v=P.coeff j from Subtype.ext (hv.trans hj.symm)]
    · rw [notMem_support_iff.mp h] at hj ⊢
      have he :P.coeff j=0:=Subtype.ext (hj.trans (map_zero _))
      simp [he]
  have hProd:M.map (algebraMap E (AlgebraicClosure E)) =
      ∏ i:I,(z7y-Polynomial.C (T.eval (qq i))) := by
    rw [hM]
    dsimp only [P]
    rw [zeg]
    simp only [z3A,Polynomial.map_X,Polynomial.map_C]
  have hMono:M.Monic:=(algebraMap E (AlgebraicClosure E)).injective.monic_map_iff.mpr
    (hProd.symm ▸ monic_prod_X_sub_C _ _)
  have hQN (i:I) :T.eval (qq i)≠0:= by
    rw [hQ]
    refine div_ne_zero ?_ (pow_ne_zero _ ?_)
    · rw [← sp]
      exact hPolar i
    · rw [← hw']
      exact hGauge i
  have hConst:M.coeff 0≠0:= by
    intro hz
    have hh:=congrArg (fun P: (AlgebraicClosure E)[X]=>P.coeff 0) hProd
    simp only [coeff_map,hz,map_zero,coeff_zero_prod,coeff_sub,coeff_X_zero,
      coeff_C_zero,zero_sub] at hh
    exact (prod_ne_zero_iff.mpr (fun i _=>neg_ne_zero.mpr (hQN i))) hh.symm
  let fI:=(Fintype.equivFin I).symm
  obtain ⟨hd,hweight,hcommon⟩:=dSE C z ha
  refine ⟨⟨cut C z,hd,hweight,hcommon,1,C.tilt,ht,Fintype.card I,pt ∘ fI,
    hinj.comp fI.injective,?_,?_,fun i=>hSimple (fI i),?_,M,hMono,hConst,?_⟩,
    coeff_specializePolynomial _ _⟩
  · intro i
    change ev' (fI i) A.f=0
    rw [← sp,hFit,map_zero]
  · intro i
    change ev' (fI i) (cut C z)=0
    have ht' : T.eval t=algebraMap E (AlgebraicClosure E) (κ z) :=special_parameter T
    have hh:=congrArg T.eval (hCut (fI i))
    rw [map_sub,map_mul,sp,sp,ht',map_zero] at hh
    simpa [cut,ev',pairEval,κ] using hh
  · intro i
    exact hw' (fI i) ▸ hGauge (fI i)
  · rw [hProd]
    refine Fintype.prod_equiv fI.symm _ _ (fun i => ?_)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,ev',pairEval,atPair,
      coe_eval₂RingHom] using
      congrArg (fun v=>(z7y: (AlgebraicClosure E)[X])-Polynomial.C v) (hQ i)
end
end qApzjua
end
section
namespace qApzjua
open cu (L)
open qNu3xvc (Equation EC KM)
open P5_7_1_7_4_3_4 (Pencil)
open qv2t4Be (CommonField)
def c1 :Prop :=
  ∀ {E :Type} [zrb E] [zZE L E] (A:Equation E) (C:Pencil A),
    pencilJac (KM A false) A.f C.num C.den (C.base RatFunc.X)≠0
def c2 :Prop :=
  ∀ (E F:Type) [zrb E] [zrb F] [zZE (RatFunc E) F]
    [Module.Finite (RatFunc E) F] [zw7 (RatFunc E) F],
    Specializes E F
theorem of_children (ct4 :c1) (specialize :c2) :qrGSFbd.c5:= by
 intro E _ _ A C a _ _ ha ht
 let _:=C.base.toAlgebra
 let _:=C.finite
 let _:=C.separable
 let _:zw7 (RatFunc E) (CommonField (RatFunc E) (EC A)) := by
   apply (le_separableClosure_iff _ _ _).mp
   apply normalClosure_le_iff.mpr
   intro i
   let _:zw7 (RatFunc E) i.fieldRange :=
     AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i)
   exact le_separableClosure _ _ _
 exact from_specialization C a ha ht (ct4 A C)
   (specialize E (CommonField (RatFunc E) (EC A)))
end qApzjua
end
section
set_option backward.isDefEq.respectTransparency false
namespace q4izpTc
noncomputable section
open Polynomial TrivSqZeroExt
open qNu3xvc (EC KM a7W amm)
open qZu9hjc (physicalDeriv)
open qApzjua (pencilJac root_zero)
open q53i3jb (eval_false)
open private coeff_physical from ProximityPrize.SubmissionLower.ZpQKUZd
open private cLc from ProximityPrize.SubmissionLower.DB
open private aug dualLift lift_on aug_lift from ProximityPrize.SubmissionLower.ZR3mCBd
open scoped nonZeroDivisors
private def inner {E :Type} [zrb E] :Derivation ℤ E[X][X] E[X][X] :=
 PolynomialModule.equivPolynomialSelf.compDer
  ((Polynomial.derivative' (R:=E)).restrictScalars ℤ).mapCoeffs
private theorem inner_apply {E :Type} [zrb E] (g:E[X][X]) :
  inner g=physicalDeriv g:= by
 apply Polynomial.ext
 intro i
 exact (coeff_physical g i).symm
private theorem physical_C {E :Type} [zrb E] (q:E[X]) :
  physicalDeriv (z1z q)=z1z q.derivative := by
 apply Polynomial.ext
 intro i
 rw [coeff_physical,coeff_C,coeff_C]
 split <;> simp
private def HE {R:Type} [za6 R] (a b:R) (D D' : Derivation ℤ R R) :
 Derivation ℤ R R:=(a•D:Derivation ℤ R R) - b•D'
private theorem weighted_apply {R:Type} [za6 R] (a b:R) (D D' : Derivation ℤ R R)
  (x :R) :HE a b D D' x=a*D x - b*D' x := by
 simp only [HE,Derivation.sub_apply,Derivation.smul_apply,smul_eq_mul]
private def zD {E :Type} [zrb E] (f :E[X][X]) :Derivation ℤ E[X][X] E[X][X] :=
 HE f.derivative (physicalDeriv f) inner
  ((Polynomial.derivative' (R:=E[X])).restrictScalars ℤ)
private def jet {E F:Type} [zrb E] [zrb F] (e :E[X][X] →+* F) (f :E[X][X]) :
  E[X][X] →+* DualNumber F :=
 cLc e (zD f).toLinearMap.toAddMonoidHom (fun a b=> by
  change zD f (a*b)=a*zD f b+zD f a*b
  simpa only [smul_eq_mul,mul_comm b] using (zD f).leibniz a b)
private theorem jet_snd {E F:Type} [zrb E] [zrb F]
  (e :E[X][X] →+* F) (f g:E[X][X]) :
  (jet e f g).snd=e f.derivative*e (physicalDeriv g)-e (physicalDeriv f)*e g.derivative := by
 change e (zD f g)= _
 rw [zD,weighted_apply,inner_apply]
 change e (_ *_-_ *g.derivative)= _
 simp only [map_mul,map_sub]
theorem proof :qApzjua.c1 := by
  intro E _ _ A C hJac
  let F:=EC A
  let e :=KM A false
  let J:=jet e A.f
  have he (g:E[X][X]) :e g=a7W A g:=eval_false A g
  have hJ:J A.f=0:= by
    refine TrivSqZeroExt.ext (root_zero A) ?_
    rw [jet_snd,snd_zero,mul_comm (e A.f.derivative),sub_self]
  have hker :Ideal.span {A.f} ≤ RingHom.ker J :=
    (Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr hJ)
  let q:AdjoinRoot A.f →+* DualNumber F :=
    Ideal.Quotient.lift _ J (fun g hg=>RingHom.mem_ker.mp (hker hg))
  have hq (g:E[X][X]) :q (AdjoinRoot.mk A.f g)=J g:=rfl
  have hqfst: (aug F).comp q=(zz5 F).comp (algebraMap (AdjoinRoot A.f) F) := by
    apply zz4
    intro a
    obtain ⟨g,rfl⟩:=AdjoinRoot.mk_surjective a
    change (q (AdjoinRoot.mk A.f g)).fst=a7W A g
    rw [hq]
    exact he g
  let H :F →+* DualNumber F:=dualLift q (zz5 F) hqfst
  have hH (g:E[X][X]) :H (e g)=J g:= by
    rw [he]
    change dualLift q (zz5 F) hqfst
      (algebraMap (AdjoinRoot A.f) F (AdjoinRoot.mk A.f g))= _
    rw [lift_on,hq]
  have hfst (a :F) : (H a).fst=a :=zLs (aug_lift q (zz5 F) hqfst) a
  let t:F:=C.base RatFunc.X
  have htd:t*e C.den=e C.num :=(eq_div_iff C.den_ne).mp C.base_X
  have hsnd: (H (e C.num)).snd - t*(H (e C.den)).snd=0:= by
    have hz : -(pencilJac e A.f C.num C.den t)=0:= by
      rw [show pencilJac e A.f C.num C.den t=0 from hJac,neg_zero]
    rw [hH,hH,jet_snd,jet_snd,← hz]
    unfold pencilJac
    ring
  have hmul :H (e C.num)=inl t*H (e C.den) := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_mul,fst_inl,hfst,hfst,htd]
    · change _=t*(H (e C.den)).snd+0*(H (e C.den)).fst
      rw [zero_mul,add_zero]
      exact sub_eq_zero.mp hsnd
  have ht:H t=inl t:= by
    have hu:IsUnit (H (e C.den)) :=
      isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr (by rw [hfst]; exact C.den_ne))
    apply hu.mul_right_cancel
    rw [← map_mul,htd]
    exact hmul
  have hbase :H.comp C.base=(inlHom F F).comp C.base := by
    apply IsLocalization.ringHom_ext E[X]⁰
    apply Polynomial.ringHom_ext
    · intro a
      simp only [zQb,RatFunc.algebraMap_C,inlHom_apply]
      rw [C.base_seed a]
      change H (a7W A (z1z (z1z a))) =
        inl (a7W A (z1z (z1z a)))
      rw [← he,hH]
      refine TrivSqZeroExt.ext rfl ?_
      rw [jet_snd,snd_inl,physical_C]
      simp
    · simpa only [zQb,RatFunc.algebraMap_X,inlHom_apply] using ht
  let:zZE (RatFunc E) F:=C.base.toAlgebra
  let:zw7 (RatFunc E) F:=C.separable
  let:Algebra.FormallyUnramified (RatFunc E) F := .of_isSeparable _ _
  let:zZE (RatFunc E) (DualNumber F) :=((inlHom F F).comp C.base).toAlgebra
  let H₁:F →ₐ[RatFunc E] DualNumber F :=
    { H with commutes' := zLs hbase }
  let H₀:F →ₐ[RatFunc E] DualNumber F :=
    { inlHom F F with commutes' := fun _=>rfl }
  have hh:H₁=H₀:=Algebra.FormallyUnramified.ext' (aug F) ⟨2,kerIdeal_sq F F⟩
    H₁ H₀ hfst
  have hx : (H (amm A)).snd=0:=congrArg (fun g:F →ₐ[RatFunc E] DualNumber F =>
    (g (amm A)).snd) hh
  change (H (a7W A (z1z (z7y:E[X])))).snd=0 at hx
  rw [← he,hH,jet_snd,physical_C,derivative_X,derivative_C,Polynomial.C_1,
    map_one,map_zero,mul_one,mul_zero,sub_zero] at hx
  exact C.polar_ne hx
end
end q4izpTc
end
section
set_option backward.isDefEq.respectTransparency false
namespace qAv0Wab
noncomputable section
open Polynomial
open qApzjua (Specialization)
open scoped BigOperators
private theorem map_fraction {R K:Type} [za6 R] [zrb K]
    (i:R →+* K) (n d:R) (hd:IsUnit d) :
    i (n*(↑hd.unit⁻¹:R))=i n/i d:= by
  have h:i (↑hd.unit⁻¹:R)=(i d)⁻¹:= by
    apply eq_inv_of_mul_eq_one_left
    have hmul : (↑hd.unit⁻¹:R)*d = 1 := by
      calc
        _=(↑hd.unit⁻¹:R) * ↑hd.unit :=congrArg _ hd.unit_spec.symm
        _=1 := by simp
    rw [← map_mul,hmul,map_one]
  rw [map_mul,h,div_eq_mul_inv]
private theorem lift_injective {R K F:Type} [za6 R] [zrb K] [zrb F]
  [zZE K F] (i:R →+* K) (hi:zq4 i) (a :F) {p:R[X]}
  (hm:p.Monic) (hp:p.map i=minpoly K a)
  (ha :p.eval₂ ((algebraMap K F).comp i) a=0) :
  zq4 (AdjoinRoot.lift ((algebraMap K F).comp i) a ha) := by
 apply (injective_iff_map_eq_zero _).mpr
 intro v
 obtain ⟨g,rfl⟩:=AdjoinRoot.mk_surjective v
 intro h
 have he :aeval a (g.map i)=0:= by
  simpa only [aeval_def,eval₂_map,AdjoinRoot.lift_mk] using h
 apply AdjoinRoot.mk_eq_zero.mpr
 apply (modByMonic_eq_zero_iff_dvd hm).mp
 apply map_injective i hi
 rw [Polynomial.map_zero,map_modByMonic i hm,hp]
 exact (modByMonic_eq_zero_iff_dvd (hp ▸ hm.map i)).mpr (minpoly.dvd K a he)
theorem proof :qApzjua.c2 := by
  classical
  intro E F _ _ _ _ _ S U
  let K:=RatFunc E
  let b:=Field.powerBasisOfFiniteOfSeparable K F
  let a :=b.gen
  let m:=minpoly K a
  let repr (v :F) :K[X] :=(b.exists_eq_aeval' v).choose
  have hrepr (v :F) :aeval a (repr v)=v :=(b.exists_eq_aeval' v).choose_spec.symm
  let P:=insert m (S.image repr)
  let V:=U∪P.biUnion (fun p=>p.support.image p.coeff)
  let d:E[X] := ∏ u∈V,u.denom
  have hd:d≠0:=Finset.prod_ne_zero_iff.mpr fun u _=>u.denom_ne_zero
  let R:=Localization.Away d
  let l:E[X] →+* R:=algebraMap _ _
  let k :E[X] →+* K:=algebraMap _ _
  have hk :zq4 k :=RatFunc.algebraMap_injective E
  let i:R →+* K:=ztx d ((map_ne_zero_iff k hk).mpr hd).isUnit
  have hi (f :E[X]) :i (l f)=k f :=zaz d _ f
  have hi' : zq4 i:= by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers d) i).mpr
    intro f g
    change l f=l g↔i (l f)=i (l g)
    rw [hi,hi,hk.eq_iff]
    exact ⟨fun h=>hk ((hi f).symm.trans ((congrArg i h).trans (hi g))),congrArg l⟩
  have hunit (u:K) (hu:u∈V) :IsUnit (l u.denom) :=
    IsLocalization.Away.isUnit_of_dvd d (Finset.dvd_prod_of_mem RatFunc.denom hu)
  let aHW (u:K) (hu:u∈V) :R:=l u.num * ↑(hunit u hu).unit⁻¹
  have hfrac (u:K) (hu:u∈V) :i (aHW u hu)=u:= by
    dsimp only [aHW]
    rw [map_fraction,hi,hi]
    exact RatFunc.num_div_denom u
  have hlower (p:K[X]) (hp:p∈P) : ∃ q:R[X],q.map i=p:= by
    apply (mem_map_range i).mpr
    intro n
    by_cases hn:n∈p.support
    · have hu:p.coeff n∈V :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hp,zPV _ hn⟩)
      exact ⟨_,hfrac _ hu⟩
    · rw [notMem_support_iff.mp hn]
      exact i.range.zero_mem
  obtain ⟨p,hp⟩:=hlower m (Finset.mem_insert_self _ _)
  have hm:p.Monic:= by
    apply hi'.monic_map_iff.mpr
    rw [hp]
    exact minpoly.monic b.isIntegral_gen
  have hdeg:p.degree≠0:= by
    rw [← degree_map_eq_of_injective hi',hp]
    change (minpoly K b.gen).degree≠0
    rw [b.degree_minpoly]
    exact_mod_cast b.dim_pos.ne'
  let j:=(algebraMap K F).comp i
  have hpa :p.eval₂ j a=0:= by
    dsimp only [j]
    rw [← eval₂_map,hp,← aeval_def]
    exact minpoly.aeval K a
  let J:=AdjoinRoot.lift j a hpa
  have hJ:zq4 J:=lift_injective i hi' a hm hp hpa
  let e :=RingEquiv.ofBijective J.rangeRestrict
    ⟨fun _ _ h=>hJ (congrArg Subtype.val h),RingHom.rangeRestrict_surjective J⟩
  let base :=(AdjoinRoot.of p).comp l
  have hbase :J.comp base=(algebraMap K F).comp k := by
    apply zz4
    intro f
    change J (AdjoinRoot.of p (l f))=(algebraMap K F) (k f)
    simp only [J,AdjoinRoot.lift_of]
    exact congrArg (algebraMap K F) (hi f)
  refine ⟨d.roots.toFinset,fun z hz => ?_⟩
  have hd' : d.eval z≠0:= fun h=>hz (Multiset.mem_toFinset.mpr ((mem_roots hd).mpr h))
  let k' := (algebraMap E (AlgebraicClosure E)).comp (evalRingHom z)
  have hdk' : k' d≠0:=(map_ne_zero_iff _ (algebraMap E (AlgebraicClosure E)).injective).mpr hd'
  let s :R →+* AlgebraicClosure E :=ztx d hdk'.isUnit
  have hs (f :E[X]) :s (l f)=k' f :=zaz d _ f
  have hsp: (p.map s).degree≠0:= by
    rwa [degree_map_eq_of_leadingCoeff_ne_zero s (by simp [hm])]
  obtain ⟨c,hc⟩:=IsAlgClosed.exists_root (p.map s) hsp
  have hpc:p.eval₂ s c=0:=(eval_map s c).symm.trans hc
  let Q:=AdjoinRoot.lift s c hpc
  have hspecial:Q.comp base=k' := by
    apply zz4
    intro f
    change Q (AdjoinRoot.of p (l f))=k' f
    simp only [Q,AdjoinRoot.lift_of,hs]
  let T:Specialization (F:=F) z :=
    { ring :=J.range
      eval := Q.comp e.symm.toRingHom
      base :=e.toRingHom.comp base
      ek :=hbase
      special:= by
        apply zz4
        intro f
        change Q (e.symm (e (base f)))=k' f
        rw [RingEquiv.symm_apply_apply]
        exact zLs hspecial f }
  refine ⟨T,fun v hv => ?_,fun u hu => ?_⟩
  · obtain ⟨q,hq⟩:=hlower (repr v) (Finset.mem_insert_of_mem (zPV _ hv))
    refine ⟨AdjoinRoot.mk p q,?_⟩
    change J (AdjoinRoot.mk p q)=v
    simp only [J,AdjoinRoot.lift_mk,j]
    rw [← eval₂_map,hq,← aeval_def,hrepr]
  · let hu' : u∈V:=Finset.mem_union_left _ hu
    refine ⟨e (AdjoinRoot.of p (aHW u hu')),?_,?_⟩
    · change J (AdjoinRoot.of p (aHW u hu'))=algebraMap K F u
      simp only [J,AdjoinRoot.lift_of]
      exact congrArg (algebraMap K F) (hfrac u hu')
    · change Q (e.symm (e (AdjoinRoot.of p (aHW u hu'))))= _
      simp only [RingEquiv.symm_apply_apply,Q,AdjoinRoot.lift_of,aHW]
      rw [map_fraction,hs,hs]
      simp only [k',zQb,coe_evalRingHom,RatFunc.eval,eval₂_id,map_div₀]
end
end qAv0Wab
end
