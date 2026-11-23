import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.AdicCompletion.Completeness
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.FiniteType → zUK, Algebra.IsIntegral → zVK, CommRing → za6, Field → zrb, Function.Injective → zq4, IsFractionRing.injective → zxb, IsScalarTower → zsf, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, Module.Finite.of_injective → zfv, PowerSeries.C → zMG, PowerSeries.X_dvd_iff → zzu, PowerSeries.constantCoeff_C → zr8
section
set_option backward.isDefEq.respectTransparency false
namespace q6hv5Ed
noncomputable section
open scoped nonZeroDivisors
private def b35 (k A:Type) [zrb k] [IsAlgClosed k]
   [za6 A] [zZE k A] (p n:ℕ) [ExpChar k p] [ExpChar A p] :Subalgebra k A :=
 { (iterateFrobenius A p n).range.toSubsemiring with
   algebraMap_mem' r := by
     obtain ⟨s,hs⟩:=IsAlgClosed.exists_pow_nat_eq r (expChar_pow_pos k p n)
     exact ⟨algebraMap k A s,by rw [iterateFrobenius_def,← map_pow,hs]⟩ }
private theorem eaW (k A:Type) [zrb k] [IsAlgClosed k]
  [za6 A] [zZE k A] [zUK k A]
  (p n:ℕ) [ExpChar k p] [ExpChar A p] :zAa (b35 k A p n) A:= by
 let S:=b35 k A p n
 have :zUK S A:=Algebra.FiniteType.of_restrictScalars_finiteType k S A
 have :zVK S A:=⟨fun z=> by
  apply IsIntegral.of_pow (expChar_pow_pos A p n)
  let s :S:=⟨z^p^n,⟨z,rfl⟩⟩
  exact isIntegral_algebraMap (x :=s)⟩
 exact Algebra.IsIntegral.finite
private theorem finite_extension (k A K L:Type) [zrb k] [IsAlgClosed k]
    [za6 A] [IsDomain A] [zZE k A] [zUK k A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [zrb K] [zrb L]
    [zZE A K] [IsFractionRing A K] [zZE K L] [zZE A L] [zsf A K L]
    [zAa K L] :zAa A (integralClosure A L) := by
  let E :=separableClosure K L
  let B:=integralClosure A L
  let C:=integralClosure A E
  have :zsf A E L:=zsL fun _=>rfl
  have :zAa A C:=IsIntegralClosure.finite A K E C
  let p:=ringExpChar L
  have :ExpChar L p:=ringExpChar.expChar L
  have hAL:zq4 (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (zxb A K)
  have :ExpChar A p:=(algebraMap A L).expChar hAL p
  have :ExpChar k p:=(algebraMap k A).expChar (algebraMap k A).injective p
  have :ExpChar E p:=(algebraMap E L).expChar (algebraMap E L).injective p
  let n:=IsPurelyInseparable.exponent E L
  let S:=b35 k A p n
  have :zAa S A:=eaW k A p n
  let σ:A →+* S:=(iterateFrobenius A p n).rangeRestrict
  let e :A ≃+* S:=RingEquiv.ofBijective σ
    ⟨fun _ _ h=>iterateFrobenius_inj A p n (congrArg Subtype.val h),
      (iterateFrobenius A p n).rangeRestrict_surjective⟩
  have :RingHomInvPair (e :A →+* S) (e.symm:S →+* A) :=RingHomInvPair.of_ringEquiv e
  have :RingHomInvPair (e.symm:S →+* A) (e :A →+* S) :=RingHomInvPair.of_ringEquiv e.symm
  have :IsNoetherianRing S:=isNoetherianRing_of_ringEquiv A e
  have :zAa S C:=Module.Finite.trans A C
  have :IsNoetherian S C:=inferInstance
  let F:L →+* E :=IsPurelyInseparable.iterateFrobenius E L p (n:=n) le_rfl
  have hF (b:L) :algebraMap E L (F b)=b^p^n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius E p le_rfl b
  have hmem (b:B) :F b.val∈integralClosure A E := by
    change IsIntegral A (F b.val)
    apply (IntermediateField.coe_isIntegral_iff (R:=A)).mp
    change IsIntegral A (algebraMap E L (F b.val))
    rw [hF]
    exact (show IsIntegral A b.val from b.property).pow _
  let g:B →+* C :=
    (F.comp (integralClosure A L).val.toRingHom).codRestrict (integralClosure A E).toSubring hmem
  let f :B →ₛₗ[(e :A →+* S)] C :=
    { g with
      map_smul' a b:= by
        apply Subtype.ext
        apply (algebraMap E L).injective
        change algebraMap E L (F (a•b.val))=algebraMap E L ((a^p^n)•F b.val)
        simp only [Algebra.smul_def]
        rw [hF,mul_pow,map_mul,← IsScalarTower.algebraMap_apply A E L,map_pow,hF] }
  apply zfv f
  intro b b' hb
  apply Subtype.ext
  apply iterateFrobenius_inj L p n
  change b.val^p^n=b'.val^p^n
  rw [← hF,← hF]
  exact congrArg (fun c:C=>algebraMap E L c.val) hb
theorem finite_affine (k B F:Type) [zrb k] [IsAlgClosed k]
   [za6 B] [IsDomain B] [zZE k B] [zUK k B]
   [zrb F] [zZE B F] [IsFractionRing B F] :
   zAa B (integralClosure B F) := by
 obtain ⟨d,g,hg,hfin⟩:=exists_finite_inj_algHom_of_fg k B
 let P:=MvPolynomial (Fin d) k
 let K:=FractionRing P
 let:zZE P B:=g.toRingHom.toAlgebra
 let:zZE P F:=((algebraMap B F).comp g.toRingHom).toAlgebra
 let:zsf P B F:=zsL fun _=>rfl
 have :zAa P B:=hfin
 have :zVK P B:=Algebra.IsIntegral.of_finite P B
 have :Algebra.IsAlgebraic P B:=Algebra.IsAlgebraic.of_finite P B
 have :FaithfulSMul P B:=(faithfulSMul_iff_algebraMap_injective P B).mpr hg
 have :FaithfulSMul P F:=(faithfulSMul_iff_algebraMap_injective P F).mpr
   (show zq4 ((algebraMap B F).comp g.toRingHom) from
     (zxb B F).comp (show zq4 g.toRingHom from hg))
 let:zZE K F:=FractionRing.liftAlgebra P F
 have :zsf P K F:=FractionRing.isScalarTower_liftAlgebra P F
 have :IsLocalization (Algebra.algebraMapSubmonoid B P⁰) F:=inferInstance
 have :zAa K F:=Module.Finite.of_isLocalization P B P⁰
 have :zAa P (integralClosure P F) :=finite_extension k P K F
 let j:integralClosure B F →ₗ[P] integralClosure P F :=
   { toFun:= fun a=>⟨a,isIntegral_trans (R:=P) a.val a.property⟩
     map_add' := fun _ _=>rfl
     map_smul' := fun _ _=>rfl }
 have :zAa P (integralClosure B F) :=
   zfv j (fun _ _ h=>Subtype.ext (congrArg (fun a :integralClosure P F=>(a :F)) h))
 exact Module.Finite.of_restrictScalars_finite P B _
end
end q6hv5Ed
end
section
namespace qs5yTLd
noncomputable section
open Polynomial
abbrev dx {R:Type*} [za6 R] (f :R[X][X]) :R[X][X] :=
 f.sum fun i c=>monomial i c.derivative
private theorem bXI {R:Type*} [za6 R] (f :R[X][X]) (i:ℕ) :
   (dx f).coeff i=(f.coeff i).derivative := by
 classical
 by_cases h:i∈f.support
 · simp [dx,sum_def,coeff_monomial,h]
 · simp [dx,sum_def,coeff_monomial,h,notMem_support_iff.mp h]
theorem dx_map {R S:Type*} [za6 R] [za6 S] (φ:R →+* S) (f :R[X][X]) :
  dx (f.map (mapRingHom φ))=(dx f).map (mapRingHom φ) := by
 exact Polynomial.ext fun i=> by
  simp only [bXI,coeff_map,coe_mapRingHom,derivative_map]
private theorem cKs {R:Type*} [za6 R] (f :R[X][X]) (y :R) :
  (f.eval (C y)).derivative=(dx f).eval (C y) := by
 have hd: (dx f).natDegree≤f.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [bXI,coeff_eq_zero_of_natDegree_lt hi,derivative_zero]
 rw [eval_eq_sum_range,eval_eq_sum_range' (Nat.lt_succ_of_le hd),derivative_sum]
 apply Finset.sum_congr rfl
 intro i _
 rw [bXI,← C_pow,derivative_mul,derivative_C,mul_zero,add_zero]
private theorem linearize {R:Type*} [za6 R] (f :R[X][X]) (x y h k t:R)
   (hh:t∣h) (hk :t∣k) :
   t^2∣f.evalEval (x+h) (y+k) -
     (f.evalEval x y+(dx f).evalEval x y*h+f.derivative.evalEval x y*k) := by
 obtain ⟨a,ha⟩:=(f.eval (C y)).exists_mul_sq_add_linear_part_eq_eval_add x h
 rw [cKs] at ha
 obtain ⟨b,hb⟩ :=
   (f.map (evalRingHom (x+h))).exists_mul_sq_add_linear_part_eq_eval_add y k
 simp only [derivative_map,map_evalRingHom_eval] at hb
 have hc:t∣f.derivative.evalEval (x+h) y - f.derivative.evalEval x y := by
   apply dvd_trans hh
   simpa only [add_sub_cancel_left] using
     sub_dvd_eval_sub (x+h) x (f.derivative.eval (C y))
 have eq :f.evalEval (x+h) (y+k) -
     (f.evalEval x y+(dx f).evalEval x y*h+f.derivative.evalEval x y*k) =
     a*h^2+b*k^2+(f.derivative.evalEval (x+h) y - f.derivative.evalEval x y)*k := by
   rw [← hb]
   change b*k^2+f.derivative.evalEval (x+h) y*k+(f.eval (C y)).eval (x+h)-_ = _
   rw [← ha]
   change b*k^2+f.derivative.evalEval (x+h) y*k +
     (a*h^2+(dx f).evalEval x y*h+f.evalEval x y)-_ = _
   ring
 rw [eq]
 exact dvd_add (dvd_add (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hh 2) a)
   (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hk 2) b))
   (by simpa only [pow_two] using mul_dvd_mul hc hk)
private theorem dvd_eval_sub {R:Type*} [za6 R] (f :R[X][X])
  {t x y x' y' : R} (hx :t∣x'-x) (hy :t∣y'-y) :
  t∣f.evalEval x' y' - f.evalEval x y := by
 have h₁:=hx.trans (sub_dvd_eval_sub x' x (f.eval (C y')))
 have h₂:=hy.trans (sub_dvd_eval_sub y' y (f.map (evalRingHom x)))
 rw [map_evalRingHom_eval,map_evalRingHom_eval] at h₂
 change t∣f.evalEval x' y' - f.evalEval x y' at h₁
 simpa only [sub_add_sub_cancel] using dvd_add h₁ h₂
section
variable {F:Type*} [zrb F]
local notation "ε" => (PowerSeries.X:PowerSeries F)
local notation "ct" => (PowerSeries.constantCoeff :PowerSeries F →+* F)
local notation "S" => PowerSeries F
def det {R:Type*} [za6 R] (f g:R[X][X]) (x y :R) :R :=
 (dx f).evalEval x y*g.derivative.evalEval x y -
 f.derivative.evalEval x y*(dx g).evalEval x y
private def correction (a b c d u v :S) :S×S :=
 let r :=(a*d-b*c)⁻¹
 (r*(b*v-d*u),r*(c*u-a*v))
private theorem correction_spec (a b c d u v :S) {t:S} (hu:t∣u) (hv :t∣v)
   (hd:ct (a*d-b*c)≠0) :
   let z :=correction a b c d u v
   t∣z.1∧t∣z.2∧u+a*z.1+b*z.2=0∧v+c*z.1+d*z.2=0:= by
 dsimp only [correction]
 let r :=(a*d-b*c)⁻¹
 have hr : (a*d-b*c)*r=1 :=PowerSeries.mul_inv_cancel _ hd
 refine ⟨dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hv b)
   (dvd_mul_of_dvd_right hu d)) r,
   dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hu c)
     (dvd_mul_of_dvd_right hv a)) r,?_,?_⟩
 · calc
     _=u-((a*d-b*c)*r)*u:= by ring
     _=0:= by rw [hr,one_mul,sub_self]
 · calc
     _=v-((a*d-b*c)*r)*v := by ring
     _=0:= by rw [hr,one_mul,sub_self]
private def newton (f g:S[X][X]) (z :S×S) :S×S :=
 let w:=correction ((dx f).evalEval z.1 z.2) (f.derivative.evalEval z.1 z.2)
   ((dx g).evalEval z.1 z.2) (g.derivative.evalEval z.1 z.2)
   (f.evalEval z.1 z.2) (g.evalEval z.1 z.2)
 (z.1+w.1,z.2+w.2)
private theorem newton_step (f g:S[X][X]) (z :S×S) (n:ℕ)
   (hf :ε^(n+1)∣f.evalEval z.1 z.2) (hg:ε^(n+1)∣g.evalEval z.1 z.2)
   (hd:ct (det f g z.1 z.2)≠0) :
   let z' := newton f g z
   (ε^(n+1)∣z'.1-z.1)∧(ε^(n+1)∣z'.2-z.2) ∧
   (ε^(n+2)∣f.evalEval z'.1 z'.2)∧(ε^(n+2)∣g.evalEval z'.1 z'.2) := by
 obtain ⟨hx,hy,hF,hG⟩:=correction_spec _ _ _ _ _ _ hf hg hd
 dsimp only [newton]
 have hp:ε^(n+2)∣(ε^(n+1))^2 := by
   rw [← pow_mul]
   exact pow_dvd_pow ε (by omega)
 refine ⟨by simpa only [add_sub_cancel_left] using hx,
   by simpa only [add_sub_cancel_left] using hy,?_,?_⟩
 · simpa only [hF,sub_zero] using hp.trans (linearize f z.1 z.2 _ _ _ hx hy)
 · simpa only [hG,sub_zero] using hp.trans (linearize g z.1 z.2 _ _ _ hx hy)
private theorem limit (u:ℕ→S) (hs : ∀ n,ε^(n+1)∣u (n+1)-u n) :
   ∃ x,∀ n,ε^n∣x-u n:= by
 let I:Ideal S:=Ideal.span {ε}
 have congr_dvd {n:ℕ} {x y :S} :
     x ≡ y [SMOD (I^n • ⊤ : Submodule S S)]↔ε^n∣x-y := by
   simp only [I,SModEq.sub_mem,smul_eq_mul,Ideal.mul_top,Ideal.span_singleton_pow,
     Ideal.mem_span_singleton]
 have hC {m n:ℕ} (hmn:m≤n) :u m ≡ u n [SMOD (I^m • ⊤ : Submodule S S)] := by
   induction n,hmn using Nat.le_induction with
   | base=>rfl
   | succ n hmn ih =>
     exact ih.trans (congr_dvd.mpr ((pow_dvd_pow ε (by omega)).trans (hs n))).symm
 obtain ⟨x,hx⟩:=(inferInstance :IsPrecomplete I S).prec hC
 exact ⟨x,fun n=>congr_dvd.mp (hx n).symm⟩
private theorem ct_eq_of_dvd {x y :S} {n:ℕ} (h:ε^(n+1)∣x-y) :ct x=ct y := by
 have h₁:=(pow_dvd_pow ε (show 1≤n+1 by omega)).trans h
 simpa only [pow_one,zzu,map_sub,sub_eq_zero] using h₁
private theorem c8z (f :S[X][X]) (x y :S) :
   ct (f.evalEval x y)=(f.map (mapRingHom ct)).evalEval (ct x) (ct y) :=
 (map_mapRingHom_evalEval ct f x y).symm
private theorem residue_det (f g:S[X][X]) (x y :S) :
  ct (det f g x y)=det (f.map (mapRingHom ct)) (g.map (mapRingHom ct)) (ct x) (ct y) := by
 simp only [det,map_sub,map_mul,c8z,dx_map,derivative_map]
theorem aOv (f g:S[X][X]) (a b:F)
    (hf : (f.map (mapRingHom ct)).evalEval a b=0)
    (hg: (g.map (mapRingHom ct)).evalEval a b=0)
    (hd:det (f.map (mapRingHom ct)) (g.map (mapRingHom ct)) a b≠0) :
    ∃ z :S×S,(ct z.1,ct z.2)=(a,b) ∧
      f.evalEval z.1 z.2=0∧g.evalEval z.1 z.2=0:= by
  let u:ℕ→S×S:=Nat.rec (zMG a,zMG b) fun _=>newton f g
  have hd' (z :S×S) (hx :ct z.1=a) (hy :ct z.2=b) :
      ct (det f g z.1 z.2)≠0:= by rwa [residue_det,hx,hy]
  have hu (n:ℕ) :ct (u n).1=a∧ct (u n).2=b ∧
      (ε^(n+1)∣f.evalEval (u n).1 (u n).2)∧(ε^(n+1)∣g.evalEval (u n).1 (u n).2) := by
    induction n with
    | zero =>
      have base (p:S[X][X]) (h: (p.map (mapRingHom ct)).evalEval a b=0) :
          ε^(0+1)∣p.evalEval (zMG a) (zMG b) := by
        simpa only [zero_add,pow_one,zzu,c8z,
          zr8] using h
      exact ⟨zr8 _,zr8 _,base f hf,base g hg⟩
    | succ n ih =>
      obtain ⟨hx,hy,hF,hG⟩:=newton_step f g (u n) n ih.2.2.1 ih.2.2.2
        (hd' (u n) ih.1 ih.2.1)
      exact ⟨(ct_eq_of_dvd hx).trans ih.1,(ct_eq_of_dvd hy).trans ih.2.1,hF,hG⟩
  have hs (n:ℕ) : (ε^(n+1)∣(u (n+1)).1-(u n).1) ∧
      (ε^(n+1)∣(u (n+1)).2-(u n).2) :=
    let h:=hu n
    let step:=newton_step f g (u n) n h.2.2.1 h.2.2.2 (hd' (u n) h.1 h.2.1)
    ⟨step.1,step.2.1⟩
  obtain ⟨x,hx⟩:=limit (fun n=>(u n).1) (fun n=>(hs n).1)
  obtain ⟨y,hy⟩:=limit (fun n=>(u n).2) (fun n=>(hs n).2)
  have hzero (p:S[X][X]) (hp : ∀ n,ε^(n+1)∣p.evalEval (u n).1 (u n).2) :
      p.evalEval x y=0:= by
    apply PowerSeries.ext
    intro n
    have h₁:=dvd_eval_sub p (hx (n+1)) (hy (n+1))
    have h₂:=(pow_dvd_pow ε (Nat.le_succ (n+1))).trans (hp (n+1))
    have hz :ε^(n+1)∣p.evalEval x y := by simpa using dvd_add h₁ h₂
    simpa using PowerSeries.X_pow_dvd_iff.mp hz n (Nat.lt_succ_self n)
  exact ⟨(x,y),Prod.ext ((ct_eq_of_dvd (n:=0) (hx 1)).trans (hu 1).1)
    ((ct_eq_of_dvd (n:=0) (hy 1)).trans (hu 1).2.1),
    hzero f (fun n=>(hu n).2.2.1),hzero g (fun n=>(hu n).2.2.2)⟩
end
end
end qs5yTLd
end
