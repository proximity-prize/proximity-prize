import ProximityPrize.SubmissionLower.ZoOOLsc
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.AdicCompletion.Completeness
import ProximityPrize.SubmissionLower.ZmXR7Cb
import ProximityPrize.SubmissionLower.ZEdS9yd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.FormallyEtale → zk2, Algebra.IsSeparable → zw7, CommRing → za6, Function.Injective → zq4, Ideal.Quotient.mk → zVv, Ideal.mem_span_singleton → zxV, Ideal.neg_mem_iff → z0X, Ideal.one_eq_top → zjK, Ideal.pow_le_pow_right → zdr, Ideal.smul_eq_mul → zHM, Ideal.span → zye, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsLocalization.map_units → z0j, IsScalarTower → zsf, IsScalarTower.algebraMap_apply → zG3, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, Module.IsTorsionFree → zYo, Polynomial.induction_on' → zCU, Polynomial.map_injective → zTo, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.coeff → z2o, RingHom.IsIntegralElem.of_map → zjs, RingHom.comp_apply → zQb, RingHom.ext → zz4, Submodule.sum_mem → zo3
set_option maxHeartbeats 800000
section
section
set_option backward.isDefEq.respectTransparency false
namespace qkjFxXb
noncomputable section
open Polynomial
open cu (L FX)
open P5_7_7 (phys)
open qoGY3we (Series bY Cover LocalRoot)
open q2TwyLa (i5 aQ diffPoly)
open scoped nonZeroDivisors
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
abbrev R:=i5[X]
abbrev B:=aQ[X]
abbrev F:=FractionRing R
abbrev E :=LaurentSeries FX
abbrev seriesIn:Series →+* E :=algebraMap _ _
private theorem bcr (q:R) (n:ℕ) :
   z2o n (bY false q) =
    phys (q.sum fun i a=>monomial i (z2o n a)) := by
 induction q using zCU with
 | add f g hf hg =>
   rw [map_add,map_add,hf,hg,sum_add_index,map_add] <;> simp
 | monomial i a =>
   rw [sum_monomial_index _ _ (by simp)]
   rw [← C_mul_X_pow_eq_monomial (a :=z2o n a),map_mul,map_pow]
   simp only [bY,Bool.false_eq_true,↓reduceIte,coe_eval₂RingHom,eval₂_monomial,
    ← map_pow,PowerSeries.coeff_mul_C,PowerSeries.coeff_map]
   rfl
theorem cFm:zq4 (bY false) := by
 apply (injective_iff_map_eq_zero (bY false)).mpr
 intro q hq
 apply Polynomial.ext
 intro i
 apply PowerSeries.ext
 intro n
 have h:=congrArg (z2o n) hq
 rw [bcr,map_zero] at h
 have hp:=(zxb L[X] FX) (h.trans (map_zero phys).symm)
 have hc:=congrArg (fun a :L[X]=>a.coeff i) hp
 rw [coeff_zero,sum_coeff (z2o n) (by simp)] at hc
 simpa only [coeff_zero,map_zero] using hc
def chartFrac:F →+* E :=
 IsFractionRing.lift (K:=F) (g:=seriesIn.comp (bY false)) ((zxb Series E).comp cFm)
@[simp] theorem chartFrac_base (q:R) :
   chartFrac (algebraMap R F q)=seriesIn (bY false q) :=
  IsFractionRing.lift_algebraMap _ _
scoped instance :zZE F E :=chartFrac.toAlgebra
scoped instance :zZE R B:=Polynomial.algebra i5 aQ
abbrev seedDenoms :Submonoid R:=(i5⁰).map Polynomial.C
scoped instance :IsLocalization seedDenoms B:=Polynomial.isLocalization (i5⁰) aQ
private theorem denominators_ne_zero :seedDenoms≤R⁰:= by
 rintro _ ⟨a,ha,rfl⟩
 exact mem_nonZeroDivisors_iff_ne_zero.mpr (C_ne_zero.mpr (nonZeroDivisors.ne_zero ha))
private theorem denominators_unit (a :seedDenoms) :IsUnit (algebraMap R F a) :=
 z0j (M:=R⁰) F ⟨a,denominators_ne_zero a.property⟩
def physicalIn:B →+* F:=IsLocalization.lift denominators_unit
@[simp] theorem physicalIn_base (q:R) :
   physicalIn (algebraMap R B q)=algebraMap R F q:=IsLocalization.lift_eq _ _
scoped instance :zZE B F:=physicalIn.toAlgebra
scoped instance : @zsf R B F instAlgebraRB.toSMul instAlgebraBF.toSMul
  (show zZE R F from inferInstance).toSMul :=
 zsL (R:=R) (S:=B) (A:=F) (fun q=> by
  change algebraMap R F q=physicalIn (algebraMap R B q)
  exact (physicalIn_base q).symm)
scoped instance :z0o B F :=
 IsFractionRing.isFractionRing_of_isLocalization seedDenoms B F denominators_ne_zero
abbrev genericChart:B →+* E :=chartFrac.comp physicalIn
abbrev Zk {A:Cover} {P:L[X]} (J:LocalRoot A.f A.r P) :=
 IntermediateField.adjoin F ({seriesIn J.y} : Set E)
abbrev reference (A:Cover) :R:=C (zMG A.r)
theorem chart_reference (A:Cover) :
  bY false (reference A)=zMG (phys (C A.r)) := by
 simp only [bY,reference,coe_eval₂RingHom,eval₂_C,PowerSeries.map_C]
 congr 1
def gI {A:Cover} {P:L[X]} (J:LocalRoot A.f A.r P) :Zk J :=
  ⟨seriesIn J.y,IntermediateField.mem_adjoin_simple_self F _⟩ -
    algebraMap F (Zk J) (algebraMap R F (reference A))
def weightedLog {A:Cover} {P:L[X]} (J:LocalRoot A.f A.r P) (afu:Bool) :Series :=
  if afu then
    bY false A.g.derivative*J.logSeed - bY false (diffPoly A.g)*J.logPhys
  else bY false A.g*J.logSeed
def flowPoly (A:Cover) (afu:Bool) (q:R) :R :=
 if afu then A.g.derivative*diffPoly q - diffPoly A.g*q.derivative
 else A.g*diffPoly q
structure cxy {A:Cover} {P:L[X]} (J:LocalRoot A.f A.r P) (afu:Bool) where
 base :Derivation ℤ F F
 top:Derivation ℤ (Zk J) (Zk J)
 extends_base : ∀ z,top (algebraMap F (Zk J) z)=algebraMap F (Zk J) (base z)
 on_polynomials : ∀ q:R,base (algebraMap R F q)=algebraMap R F (flowPoly A afu q)
 log_eq : ((top (gI J)/gI J:Zk J) :E)=seriesIn (weightedLog J afu)
end
end qkjFxXb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qkjFxXb
noncomputable section
open IsDedekindDomain
open scoped WithZero
theorem cVs {M:Type} [Field M] [zZE F M] [zAa F M]
   [zw7 F M] (z :M)
   (h : ∀ (q:HeightOneSpectrum B) (w:Valuation M ℤᵐ⁰) (e :ℕ),
     Function.Surjective w→0<e →
     (∀ x,w (algebraMap F M x)=q.valuation F x^e)→w z≤1) :
   ((algebraMap F M).comp physicalIn).IsIntegralElem z := by
 let:zZE B M:=((algebraMap F M).comp physicalIn).toAlgebra
 let:zsf B F M:=zsL (R:=B) (S:=F) (A:=M) fun _=>rfl
 let:zYo B M := .trans_faithfulSMul B F M
 let N :=integralClosure B M
 let:zYo B N :=IsIntegralClosure.isTorsionFree (A:=N) B M
 let:IsDedekindDomain N :=integralClosure.isDedekindDomain B F M
 let:z0o N M:=IsIntegralClosure.isFractionRing_of_finite_extension B F M N
 have hh (Q:HeightOneSpectrum N) :Q.valuation M z≤1 := by
   let q:HeightOneSpectrum B :=
     ⟨Q.asIdeal.under B,Ideal.IsPrime.under B Q.asIdeal,Ideal.under_ne_bot B Q.ne_bot⟩
   let:Q.asIdeal.LiesOver q.asIdeal:=⟨rfl⟩
   have he :0<q.asIdeal.ramificationIdx' Q.asIdeal :=
     Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver Q.asIdeal q.ne_bot)
   exact h q (Q.valuation M) _ (Q.valuation_surjective M) he (fun x=>(q.valuation_liesOver M Q x).symm)
 obtain ⟨y,rfl⟩:=HeightOneSpectrum.mem_integers_of_valuation_le_one M z hh
 exact (y :N).property
theorem integral_le_one {D M:Type} [za6 D] [Field M] (j:D →+* M)
  (w:Valuation M ℤᵐ⁰) (hj : ∀ a,w (j a)≤1) {z :M} (hz :j.IsIntegralElem z) :
  w z≤1 := by
 let O:=w.valuationSubring
 let f :=j.codRestrict O.toSubring hj
 change (O.subtype.comp f).IsIntegralElem z at hz
 exact (Valuation.valuationSubring.integers w).isIntegral_iff_v_le_one.mp hz.of_comp
end
end qkjFxXb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qkjFxXb
noncomputable section
open Polynomial
open cu (L)
open qoGY3we (Series bY Cover LocalRoot branchPoly physDiff)
open q2TwyLa (diff diffPoly)
private theorem integral_eval {D M:Type} [za6 D] [za6 M]
   (j:D →+* M) {y :M} (hy :j.IsIntegralElem y) (f :D[X]) :
   j.IsIntegralElem (f.eval₂ j y) := by
 induction f using zCU with
 | add f g hf hg =>
   rw [eval₂_add]
   exact (RingHom.IsIntegralElem.add j hf hg)
 | monomial i a =>
   rw [eval₂_monomial]
   let:zZE D M:=j.toAlgebra
   have h:IsIntegral D y :=hy
   exact RingHom.IsIntegralElem.mul j j.isIntegralElem_map (h.pow i)
private theorem weighted_identity (A:Cover) {P:L[X]} (J:LocalRoot A.f A.r P)
   (afu:Bool) : ∃ N :R[X],
   weightedLog J afu*(J.y - bY false (reference A)) *
     A.f.derivative.eval₂ (bY false) J.y=N.eval₂ (bY false) J.y := by
 rw [chart_reference]
 let u:=J.y-PowerSeries.C (P5_7_7.phys (C A.r))
 let d:=A.f.derivative.eval₂ (bY false) J.y
 cases afu
 · refine ⟨-(C A.g*diff A.f),?_⟩
   simp only [weightedLog,Bool.false_eq_true,↓reduceIte,eval₂_neg,eval₂_mul,eval₂_C]
   calc
     _=bY false A.g*(J.logSeed*u*d) := by dsimp only [u,d]; ring
     _ = _:= by dsimp only [u,d]; rw [J.seed_eq,mul_neg]
 · refine ⟨-(C A.g.derivative*diff A.f)+C (diffPoly A.g)*physDiff A.f,?_⟩
   simp only [weightedLog,↓reduceIte,eval₂_add,eval₂_neg,eval₂_mul,eval₂_C]
   calc
     _=bY false A.g.derivative*(J.logSeed*u*d) -
         bY false (diffPoly A.g)*(J.logPhys*u*d) := by dsimp only [u,d]; ring
     _ = _:= by dsimp only [u,d]; rw [J.seed_eq,J.phys_eq]; ring
private def CJ {D:Type} [za6 D] (f :D[X]) :D :=
 f.resultant f.derivative f.natDegree (f.natDegree-1)
private theorem clear_guard {D M:Type} [za6 D] [Field M] (j:D →+* M)
    (f N :D[X]) (r :D) (y z :M) (hpos :0<f.natDegree)
    (hbu:IsUnit (j (CJ f*f.eval r))) (hy :f.eval₂ j y=0)
    (hz :z*(y - j r)*f.derivative.eval₂ j y=N.eval₂ j y) :
    ∃ n:ℕ,j.IsIntegralElem (j (CJ f*f.eval r)^n*z) := by
  let b:=CJ f*f.eval r
  let S:=Localization.Away b
  let a :=algebraMap D S
  let k :S →+* M:=IsLocalization.Away.lift b hbu
  have hk :k.comp a=j:=zz4 (IsLocalization.Away.lift_eq b hbu)
  have hka (c:D) :k (a c)=j c:=RingHom.congr_fun hk c
  let:zZE D M:=j.toAlgebra
  let:zZE S M:=k.toAlgebra
  let:SMul D S:=(show zZE D S from inferInstance).toSMul
  let:zsf D S M:=IsScalarTower.of_algebraMap_eq' hk.symm
  have unit_of_dvd {c:D} (hc:c∣b) :IsUnit (a c) :=
    isUnit_of_dvd_unit (map_dvd a hc) (IsLocalization.Away.algebraMap_isUnit b)
  have hpol:CJ f∣b:=dvd_mul_right _ _
  have href :f.eval r∣b:=dvd_mul_left _ _
  have hlc:f.leadingCoeff∣CJ f := by
    rw [CJ,resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos)]
    exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  have hc:k.IsIntegralElem (k (a f.leadingCoeff)*y) := by
    have h:=j.isIntegralElem_leadingCoeff_mul _ _ hy
    rw [← hk] at h
    exact h.of_comp
  obtain ⟨c,hc1⟩:=(unit_of_dvd (hlc.trans hpol)).exists_right_inv
  have hyi:k.IsIntegralElem y := by
    apply RingHom.IsIntegralElem.of_mul_unit (f :=k) y (k (a f.leadingCoeff)) c
    · rw [← map_mul,mul_comm c,hc1,map_one]
    · simpa only [mul_comm] using hc
  obtain ⟨_,Q,_,_,hQ⟩:=exists_mul_add_mul_eq_C_resultant f f.derivative
    (m:=f.natDegree) (n:=f.natDegree - 1) le_rfl
    (by have :=natDegree_derivative_lt hpos.ne'; omega) (Or.inl hpos.ne')
  have hd:f.derivative.eval₂ j y*Q.eval₂ j y=j (CJ f) := by
    simpa only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,hy,zero_mul,zero_add,CJ]
      using congrArg (eval₂RingHom j y) hQ
  obtain ⟨Q',hQ'⟩:=X_sub_C_dvd_sub_C_eval (p:=f) (a :=r)
  have he : -j (f.eval r)=(y - j r)*Q'.eval₂ j y := by
    simpa only [map_sub,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X,hy,zero_sub]
      using congrArg (eval₂RingHom j y) hQ'
  obtain ⟨d,hd1⟩:=(unit_of_dvd hpol).exists_right_inv
  obtain ⟨e,he1⟩:=(unit_of_dvd href).exists_right_inv
  have hd2 :j (CJ f)*k d = 1 := by
    rw [← hka,← map_mul,hd1,map_one]
  have he2 :j (f.eval r)*k e=1 := by
    rw [← hka,← map_mul,he1,map_one]
  have ev (q:D[X]) :k.IsIntegralElem (q.eval₂ j y) := by
    rw [← hk,← eval₂_map]
    exact integral_eval k hyi _
  have hprod:z=N.eval₂ j y*(-Q'.eval₂ j y*k e)*(Q.eval₂ j y*k d) := by
    have hh: (y - j r)*(-Q'.eval₂ j y*k e)=1 := by
      rw [← mul_assoc,mul_neg,← he,neg_neg,he2]
    have hh' : f.derivative.eval₂ j y*(Q.eval₂ j y*k d)=1 := by
      rw [← mul_assoc,hd,hd2]
    rw [← hz]
    calc
      _=z*((y - j r)*(-Q'.eval₂ j y*k e)) *
          (f.derivative.eval₂ j y*(Q.eval₂ j y*k d)) := by rw [hh,hh',mul_one,mul_one]
      _ = _:= by ring
  have hzi:IsIntegral S z := by
    rw [hprod]
    exact RingHom.IsIntegralElem.mul k
      (RingHom.IsIntegralElem.mul k (ev N)
        (RingHom.IsIntegralElem.mul k (RingHom.IsIntegralElem.neg k (ev Q')) k.isIntegralElem_map))
      (RingHom.IsIntegralElem.mul k (ev Q) k.isIntegralElem_map)
  obtain ⟨m,hm⟩:=hzi.exists_multiple_integral_of_isLocalization (Submonoid.powers b) z
  obtain ⟨n,hn⟩:=m.property
  refine ⟨n,?_⟩
  change j.IsIntegralElem (j (m:D)*z) at hm
  rw [← hn,map_pow] at hm
  exact hm
theorem guard_multiple (A:Cover) {P:L[X]} (J:LocalRoot A.f A.r P) (afu:Bool) :
   ∃ n:ℕ,(bY false).IsIntegralElem
     ((bY false (branchPoly A.f A.r))^n*weightedLog J afu) := by
 let j:=seriesIn.comp (bY false)
 let y :=seriesIn J.y
 let z :=seriesIn (weightedLog J afu)
 have inj:=(zxb Series E).comp cFm
 have hbu:IsUnit (j (branchPoly A.f A.r)) :=isUnit_iff_ne_zero.mpr
   ((map_ne_zero_iff j inj).mpr A.branch_ne)
 have hy :A.f.eval₂ j y=0:= by
   change A.f.eval₂ (seriesIn.comp (bY false)) (seriesIn J.y)=0
   rw [← hom_eval₂,J.root,map_zero]
 obtain ⟨N,hN⟩:=weighted_identity A J afu
 have hz :z*(y - j (reference A))*A.f.derivative.eval₂ j y=N.eval₂ j y := by
   simpa only [j,y,z,map_mul,map_sub,hom_eval₂,zQb] using congrArg seriesIn hN
 obtain ⟨n,hn⟩:=clear_guard j A.f N (reference A) y z A.positive hbu hy hz
 refine ⟨n,zjs (g:=seriesIn) (zxb Series E) ?_⟩
 change j.IsIntegralElem (seriesIn ((bY false (branchPoly A.f A.r))^n*weightedLog J afu))
 rw [map_mul,map_pow]
 exact hn
end
end qkjFxXb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qkjFxXb
noncomputable section
open Polynomial
open q2TwyLa (i5 aQ)
open qoGY3we (Series bY)
private abbrev pO:i5 →+* aQ:=algebraMap i5 aQ
private theorem base_injective :zq4 (algebraMap R B) :=
 zTo pO (zxb i5 aQ)
private theorem bWc (b:R) (hb:IsUnit b.leadingCoeff) (n:ℕ) {c:B}
  (hc: (algebraMap R B b)^n*c∈(algebraMap R B).range) :
  c∈(algebraMap R B).range := by
 obtain ⟨q,hq⟩:=hc
 have hunit :IsUnit (b^n).leadingCoeff := by rw [leadingCoeff_pow]; exact hb.pow n
 obtain ⟨a,ha⟩:=hunit.exists_left_inv
 let m:=C a*b^n
 have hm:m.Monic:=monic_C_mul_of_mul_leadingCoeff_eq_one ha
 change q.map pO=(b.map pO)^n*c at hq
 have hqm: (C a*q).map pO=m.map pO*c:= by
  simp only [m,Polynomial.map_mul,map_C,Polynomial.map_pow,hq,mul_assoc]
 refine ⟨(C a*q) /ₘ m,?_⟩
 change ((C a*q) /ₘ m).map pO=c
 rw [map_divByMonic _ hm,hqm,mul_divByMonic_cancel_left _ (hm.map _)]
private theorem unscale_lifts (b:R) (hb:IsUnit b.leadingCoeff) (n:ℕ)
  {q:R[X]} {p:B[X]}
  (h:q.map (algebraMap R B)=p.scaleRoots ((algebraMap R B b)^n)) :
  p∈lifts (algebraMap R B) := by
 apply (lifts_iff_coeff_lifts p).mpr
 intro i
 have hc:=congrArg (fun t:B[X]=>t.coeff i) h
 rw [coeff_map,coeff_scaleRoots] at hc
 refine bWc b hb (n*(p.natDegree - i)) ⟨q.coeff i,?_⟩
 rw [hc,pow_mul]
 exact mul_comm _ _
private theorem scaled_minpoly {A S K M:Type} [za6 A] [za6 S]
  [IsDomain A] [IsDomain S] [IsIntegrallyClosed A] [IsIntegrallyClosed S] [Field K] [Field M]
  [zZE A S] [zZE A K] [zZE S K] [zZE A M] [zZE S M] [zZE K M]
  [z0o A K] [z0o S K] [zsf A S K] [zsf A K M]
  [zsf S K M] [zYo S M] {d:S} {x :M}
  (hd:d≠0) (hx :IsIntegral S x) (hy :IsIntegral A (d•x)) :
  (minpoly A (d•x)).map (algebraMap A S)=(minpoly S x).scaleRoots d:= by
 have ha :minpoly K (d•x)=(minpoly A (d•x)).map (algebraMap A K) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' K hy
 have hb:minpoly K (d•x)=(minpoly S (d•x)).map (algebraMap S K) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' K (hx.smul d)
 rw [← IsIntegrallyClosed.minpoly_smul hd hx]
 apply zTo _ (zxb S K)
 rw [Polynomial.map_map,← IsScalarTower.algebraMap_eq A S K,← ha,hb]
theorem descent {b:R} (hb:IsUnit b.leadingCoeff) {z :Series} (n:ℕ)
   (hs :genericChart.IsIntegralElem (seriesIn z))
   (hr : (bY false).IsIntegralElem (bY false b^n*z)) :
   (bY false).IsIntegralElem z := by
 let:zZE B E :=genericChart.toAlgebra
 let:zZE R E :=(seriesIn.comp (bY false)).toAlgebra
 let:zsf B F E :=zsL (R:=B) (S:=F) (A:=E) fun _=>rfl
 let:SMul R F:=(show zZE R F from inferInstance).toSMul
 let:zsf R F E :=zsL (R:=R) (S:=F) (A:=E)
   fun q=>(chartFrac_base q).symm
 let:zYo B E :=
   (Module.isTorsionFree_iff_algebraMap_injective (R:=B) (A:=E)).mpr
     (chartFrac.injective.comp (zxb B F))
 let s :=seriesIn z
 let d:=algebraMap R B b^n
 have hd:d≠0:=pow_ne_zero _ (map_ne_zero_iff _ base_injective |>.mpr
   (leadingCoeff_ne_zero.mp hb.ne_zero))
 have hi:IsIntegral R (d•s) := by
   have hmap :genericChart (algebraMap R B b)=seriesIn (bY false b) := by
     simp only [zQb,physicalIn_base,chartFrac_base]
   change (seriesIn.comp (bY false)).IsIntegralElem (d•s)
   have hh:=hr.map seriesIn
   simpa only [Algebra.smul_def,show algebraMap B E=genericChart from rfl,d,s,map_pow,
     hmap,map_mul] using hh
 have hs' : IsIntegral B s :=hs
 have he :=scaled_minpoly (A:=R) (S:=B) (K:=F) (M:=E) hd hs' hi
 have hl:minpoly B s∈lifts (algebraMap R B) :=unscale_lifts b hb n he
 obtain ⟨q,hq⟩:=(mem_lifts _).mp hl
 refine ⟨q,base_injective.monic_map_iff.mpr (hq.symm ▸ minpoly.monic hs'),?_⟩
 apply zxb Series E
 rw [hom_eval₂,map_zero]
 change q.eval₂ (seriesIn.comp (bY false)) s=0
 have hcomp:genericChart.comp (algebraMap R B)=seriesIn.comp (bY false) :=
   zz4 fun x=> by simp only [zQb,physicalIn_base,chartFrac_base]
 rw [← hcomp,← eval₂_map,hq]
 exact minpoly.aeval B s
end
end qkjFxXb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qkjFxXb
noncomputable section
open Polynomial IsDedekindDomain
open P5 (K p)
open cu (L)
open q2TwyLa (i5 aQ diffPoly)
open qoGY3we (TameLog Cover LocalRoot bY branchPoly)
open scoped WithZero
open private bx0 bia from ProximityPrize.SubmissionLower.DB
def c1 :Prop :=
  ∀ (A:Cover) (P:L[X]) (J:LocalRoot A.f A.r P),
    zAa F (Zk J)∧zw7 F (Zk J) ∧
    Module.finrank F (Zk J)<p ∧ ∀ afu,Nonempty (cxy J afu)
def c2 :Prop :=
  ∀ (g:R),(g.map (algebraMap i5 aQ)).Separable →
    ∀ (D:Derivation ℤ F F),
      (∀ b:R,∃ c:R,D (algebraMap R F b)=algebraMap R F c) →
      (∃ c:R,D (algebraMap R F g)=algebraMap R F (g*c)) →
      ∀ (q:HeightOneSpectrum B),q.intValuation (algebraMap R B g)<1 →
        (∀ z,q.valuation F z≤1→q.valuation F (D z)≤1) ∧
        (∀ z,q.valuation F z<1→q.valuation F (D z)<1)
private theorem difference_ne (A:Cover) {P:L[X]} (J:LocalRoot A.f A.r P) :
  gI J≠0:= by
 intro h
 have hh:=congrArg (fun x :Zk J=>(x :E)) h
 change seriesIn J.y - chartFrac (algebraMap R F (reference A))=0 at hh
 rw [chartFrac_base,← map_sub,← map_zero seriesIn] at hh
 exact J.ref_unit.ne_zero (by simpa only [chart_reference] using (zxb _ _ hh))
private theorem branch_value (A:Cover) (q:HeightOneSpectrum B)
   (h : ¬ q.intValuation (algebraMap R B A.g)<1) :
   q.intValuation (algebraMap R B (branchPoly A.f A.r))=1 := by
 have hg:=(q.intValuation_le_one (algebraMap R B A.g)).antisymm (le_of_not_gt h)
 obtain ⟨n,b,hb⟩:=A.radical_pow
 change (algebraMap R B A.g)^n=algebraMap R B (branchPoly A.f A.r)*b at hb
 have hv :=congrArg q.intValuation hb
 rw [map_pow,hg,one_pow,map_mul] at hv
 exact (q.intValuation_le_one _).antisymm (calc
   1= _:=hv
   _≤q.intValuation (algebraMap R B (branchPoly A.f A.r))*1 :=
     mul_le_mul_of_nonneg_left (q.intValuation_le_one b) zero_le
   _ = _:=mul_one _)
private theorem flow_dvd (A:Cover) (afu:Bool) :
   ∃ c:R,flowPoly A afu A.g=A.g*c:= by
 cases afu
 · exact Exists.intro (diffPoly A.g) rfl
 · refine Exists.intro 0 ?_
   simp only [flowPoly,↓reduceIte,mul_zero]
   rw [mul_comm A.g.derivative,sub_self]
private theorem finite_one (tame :TameLog) (build:c1) (zD:c2)
    (A:Cover) {P:L[X]} (J:LocalRoot A.f A.r P) (afu:Bool) :
    (bY false).IsIntegralElem (weightedLog J afu) := by
  obtain ⟨hfin,hsep,hsmall,hflow⟩:=build A P J
  let:zAa F (Zk J) :=hfin
  let:zw7 F (Zk J) :=hsep
  let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let c:L →+* F:=(algebraMap R F).comp (C.comp zMG)
  have hc:zq4 c :=
    (zxb R F).comp (C_injective.comp PowerSeries.C_injective)
  let:CharP F p:=charP_of_injective_ringHom hc p
  obtain ⟨D⟩:=hflow afu
  obtain ⟨n,hn⟩:=guard_multiple A J afu
  let z :=D.top (gI J)/gI J
  let i:Zk J →+* E :=(Zk J).subtype
  let a :=algebraMap F (Zk J)
  let j:=a.comp (algebraMap R F)
  have hz :i z=seriesIn (weightedLog J afu) :=D.log_eq
  have hj:i.comp j=seriesIn.comp (bY false) :=
    zz4 fun b=>chartFrac_base b
  have hscale :j.IsIntegralElem (j (branchPoly A.f A.r)^n*z) := by
    apply zjs i.injective
    change (i.comp j).IsIntegralElem (i (j (branchPoly A.f A.r)^n*z))
    rw [map_mul,map_pow,hz,← zQb,hj]
    simpa only [map_mul,map_pow,zQb] using hn.map seriesIn
  have ht: (a.comp physicalIn).IsIntegralElem z := by
    apply cVs
    intro q w e hw he hres
    by_cases hq:q.intValuation (algebraMap R B A.g)<1
    · obtain ⟨d,hd⟩:=flow_dvd A afu
      have hnz : ∃ c:R,D.base (algebraMap R F A.g)=algebraMap R F (A.g*c) :=
        Exists.intro d (by rw [D.on_polynomials,hd])
      obtain ⟨hreg,htangent⟩:=zD A.g A.radical_sep D.base
        (fun b=>⟨_,D.on_polynomials b⟩) hnz q hq
      let baseD : @Derivation ℤ F F _ _ _ (Ring.toIntAlgebra F) _ _:=bx0 D.base
      let topD : @Derivation ℤ (Zk J) (Zk J) _ _ _ (Ring.toIntAlgebra (Zk J)) _ _ :=
        bx0 D.top
      have hbase (x :F) :baseD x=D.base x :=bia D.base x
      have htop (x :Zk J) :topD x=D.top x :=bia D.top x
      have hh:=tame hsmall (q.valuation F) w e baseD topD (q.valuation_surjective F) hw he hres
        (fun x=> by rw [htop,hbase]; exact D.extends_base x)
        (fun x hx=> by rw [hbase]; exact hreg x hx)
        (gI J) (difference_ne A J)
        (Or.inl fun x hx=> by rw [hbase]; exact htangent x hx)
      simpa only [htop] using hh
    · have hb:w (j (branchPoly A.f A.r))=1 := by
        rw [zQb,hres,zG3 R B F,
          q.valuation_of_algebraMap,branch_value A q hq,one_pow]
      have hle : ∀ b,w (j b)≤1 := by
        intro b
        rw [zQb,hres,zG3 R B F,q.valuation_of_algebraMap]
        exact pow_le_one₀ zero_le (q.intValuation_le_one _)
      have hv :=integral_le_one j w hle hscale
      rwa [map_mul,map_pow,hb,one_pow,one_mul] at hv
  have hs :genericChart.IsIntegralElem (i z) := by
    change (i.comp (a.comp physicalIn)).IsIntegralElem (i z)
    exact RingHom.IsIntegralElem.map ht i
  rw [hz] at hs
  exact descent A.branch_unit n hs hn
theorem of_children (build:c1) (zD:c2) :qoGY3we.c2 := by
 intro tame A P J
 exact ⟨finite_one tame build zD A J false,finite_one tame build zD A J true⟩
end
end qkjFxXb
end
end
section
section
namespace qQQM2Gb
noncomputable section
open MvPolynomial
open qFwMjQd (Chart aax)
open q9sUlTb (jac jac_map difference_row zeroAt)
open scoped Matrix
private theorem eval_congr {R:Type} [za6 R] (I:Ideal R) {u v :aax R}
  (he : ∀ j,u j ≡ v j [SMOD I]) (p:Chart R) :
  eval u p ≡ eval v p [SMOD I] := by
 change zVv I (eval u p)=zVv I (eval v p)
 have hq:zVv I ∘ u=zVv I ∘ v :=
  funext fun j=>SModEq.def.mp (he j)
 rw [map_eval,map_eval,hq]
private theorem lift {R:Type} [za6 R] {I:Ideal R} [IsAdicComplete I R]
    (f g h:Chart R) (a₀:aax R) (hJ:IsUnit (jac f g h a₀).det)
    (h₀:eval a₀ f∈I∧eval a₀ g∈I∧eval a₀ h∈I) :
    ∃ a :aax R,(∀ j,a j ≡ a₀ j [SMOD I])∧zeroAt f g h a := by
  classical
  let P:Fin 3→Chart R := ![f,g,h]
  let J:=jac f g h a₀
  let values (a :aax R) :aax R:= fun i=>eval a (P i)
  let step (a :aax R) :aax R:=J⁻¹ *ᵥ values a
  let c:ℕ→aax R:= fun n=>Nat.recOn n a₀ fun _ a=>a - step a
  have cancel (a :aax R) :J *ᵥ step a=values a := by
    change J *ᵥ (J⁻¹ *ᵥ values a)=values a
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv J hJ,Matrix.one_mulVec]
  have diff (n:ℕ) (j:Fin 3) :c (n+1) j - c n j = -(step (c n) j) := by
    change c n j - step (c n) j - c n j= _
    ring
  have step_mem (n:ℕ) (hn : ∀ i,values (c n) i∈I^(n+1)) (j:Fin 3) :
      step (c n) j∈I^(n+1) := by
    change ∑ i,J⁻¹ j i*values (c n) i∈I^(n+1)
    exact zo3 _ fun i _=>Ideal.mul_mem_left _ _ (hn i)
  have invariant (n:ℕ) :
      (∀ j,c n j ≡ a₀ j [SMOD I])∧(∀ i,values (c n) i∈I^(n+1)) := by
    induction n with
    | zero =>
      refine ⟨fun _=>rfl,fun i => ?_⟩
      obtain ⟨hf,hg,hh⟩:=h₀
      fin_cases i
      · simpa [c,values,P] using hf
      · simpa [c,values,P] using hg
      · simpa [c,values,P] using hh
    | succ n ih =>
      have delta (j:Fin 3) :c (n+1) j ≡ c n j [SMOD I] := by
        apply SModEq.sub_mem.mpr
        rw [diff,z0X]
        simpa only [pow_one] using
          zdr (Nat.le_add_left 1 n) (step_mem n ih.2 j)
      refine ⟨fun j=>(delta j).trans (ih.1 j),fun i => ?_⟩
      let k :=zVv I
      have hconst:k ∘ c n=k ∘ a₀:=funext fun j=>SModEq.def.mp (ih.1 j)
      obtain ⟨D,hD,hDq⟩ :=
        difference_row k (c (n+1)) (c n) (funext fun j=>SModEq.def.mp (delta j)) (P i)
      have hcoeff (j:Fin 3) :D j-J i j∈I:= by
        apply Ideal.Quotient.eq.mp
        change k (D j)=k (eval a₀ (pderiv j (P i)))
        rw [hDq j,hconst,pderiv_map,← map_eval]
      have hlin:eval (c n) (P i) = ∑ j,J i j*step (c n) j :=
        (congrFun (cancel (c n)) i).symm
      have herr :eval (c (n+1)) (P i) = ∑ j,(D j-J i j)*(-(step (c n) j)) := by
        calc
          _=(eval (c (n+1)) (P i)-eval (c n) (P i))+eval (c n) (P i) :=
            (sub_add_cancel _ _).symm
          _ = _:= by
            rw [hD,hlin,← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [diff]
            ring
      change eval (c (n+1)) (P i)∈I^(n+1+1)
      rw [herr,pow_succ']
      exact zo3 _ fun j _ =>
        Ideal.mul_mem_mul (hcoeff j) ((z0X _).mpr (step_mem n ih.2 j))
  have adjacent (n:ℕ) (j:Fin 3) :c (n+1) j ≡ c n j [SMOD (I^n:Ideal R)] := by
    apply SModEq.sub_mem.mpr
    rw [diff,z0X]
    exact zdr (Nat.le_succ n) (step_mem n (invariant n).2 j)
  have chain (j:Fin 3) (m n:ℕ) (hmn:m≤n) :
      c m j ≡ c n j [SMOD (I^m • ⊤ : Ideal R)] := by
    rw [← zjK,zHM,mul_one]
    induction n,hmn using Nat.le_induction with
    | base=>rfl
    | succ n hmn ih =>
      exact ih.trans (SModEq.mono (zdr hmn) (adjacent n j).symm)
  have limit (j:Fin 3) : ∃ a,∀ n,c n j ≡ a [SMOD (I^n • ⊤ : Ideal R)] :=
    IsPrecomplete.prec' (fun n=>c n j) (chain j _ _)
  choose a ha using limit
  have ha' (n:ℕ) (j:Fin 3) :c n j ≡ a j [SMOD (I^n:Ideal R)] := by
    simpa only [← zjK,zHM,mul_one] using ha j n
  have hz (i:Fin 3) :eval a (P i)=0:= by
    apply IsHausdorff.haus' (I:=I)
    intro n
    rw [← zjK,zHM,mul_one]
    exact (eval_congr (I^n) (fun j=>(ha' n j).symm) (P i)).trans
      (SModEq.zero.mpr (zdr (Nat.le_succ n) ((invariant n).2 i)))
  exact ⟨a,fun j=>(by simpa only [pow_one] using (ha' 1 j).symm :
    a j ≡ c 1 j [SMOD I]).trans ((invariant 1).1 j),hz 0,hz 1,hz 2⟩
theorem proof :q9sUlTb.c2 := by
 intro E _ f g h q hs
 let I:Ideal (zpm E) :=zye {PowerSeries.X}
 let k :zpm E →+* E :=PowerSeries.constantCoeff
 let a₀:aax (zpm E) :=zMG ∘ q
 have ha₀:k ∘ a₀=q:=funext fun j=>PowerSeries.constantCoeff_C (q j)
 have mem_I (x :zpm E) :x∈I↔k x=0:= by
   change x∈zye {PowerSeries.X} ↔ k x=0
   rw [zxV,PowerSeries.X_dvd_iff]
 have hdet:IsUnit (jac f g h a₀).det:= by
   apply PowerSeries.isUnit_iff_constantCoeff.mpr
   change IsUnit (k (jac f g h a₀).det)
   rw [k.map_det]
   change IsUnit ((Matrix.map (jac f g h a₀) k).det)
   rw [jac_map,ha₀,isUnit_iff_ne_zero]
   exact hs.2.2.2
 have mem_eval (p:Chart (zpm E)) (hp:eval q (map k p)=0) :
     eval a₀ p∈I:= by
   rw [mem_I,map_eval,ha₀]
   exact hp
 obtain ⟨a,ha,hz⟩:=lift (I:=I) f g h a₀ hdet
   ⟨mem_eval f hs.1,mem_eval g hs.2.1,mem_eval h hs.2.2.1⟩
 refine ⟨a,?_,hz⟩
 funext j
 have hj:=(mem_I _).mp (SModEq.sub_mem.mp (ha j))
 rw [map_sub,sub_eq_zero] at hj
 exact hj.trans (congrFun ha₀ j)
end
end qQQM2Gb
end
section
set_option backward.isDefEq.respectTransparency false
namespace q0wio9a
noncomputable section
open Polynomial qkjFxXb
open cu (L)
open P5 (p)
open qoGY3we (Cover LocalRoot bY physDiff)
open q2TwyLa (i5 diff diffPoly)
open q85rTDe (aNu)
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open private a5n from ProximityPrize.SubmissionLower.C
open private bx0 bia from ProximityPrize.SubmissionLower.DB
open scoped nonZeroDivisors qkjFxXb
private theorem chart_base :
  (algebraMap F E).comp (algebraMap R F)=seriesIn.comp (bY false) :=
 zz4 chartFrac_base
private theorem root_field (A:Cover) {P:L[X]} (J:LocalRoot A.f A.r P) :
   zAa F (Zk J)∧zw7 F (Zk J) ∧
     Module.finrank F (Zk J)<p:= by
 let i:=algebraMap R F
 let y :=seriesIn J.y
 let q:=A.f.map i
 have ev (g:R[X]) :
     aeval y (g.map i)=seriesIn (g.eval₂ (bY false) J.y) := by
   rw [aeval_def,eval₂_map,chart_base,← hom_eval₂]
 have hdeg:q.natDegree=A.f.natDegree :=
   natDegree_map_eq_of_injective (zxb R F) _
 have hq:q≠0:=ne_zero_of_natDegree_gt (hdeg.symm ▸ A.positive)
 have hz :aeval y q=0:= by
   change aeval y (A.f.map i)=0
   rw [ev,J.root,map_zero]
 have hd:aeval y q.derivative≠0:= by
   change aeval y (A.f.map i).derivative≠0
   rw [derivative_map,ev]
   exact (J.simple.map seriesIn).ne_zero
 have hi:IsIntegral F y :=IsAlgebraic.isIntegral ⟨q,hq,hz⟩
 have hdiv :=minpoly.dvd F y hz
 have hs :IsSeparable F y := by
   apply (separable_iff_derivative_ne_zero (minpoly.irreducible hi)).mpr
   intro h
   obtain ⟨g,hg⟩:=hdiv
   apply hd
   rw [hg,derivative_mul,h]
   simp only [map_add,map_mul,map_zero,minpoly.aeval,zero_mul,add_zero]
 refine ⟨IntermediateField.adjoin.finiteDimensional hi,?_,?_⟩
 · exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).mpr hs
 · rw [IntermediateField.adjoin.finrank hi]
   exact (natDegree_le_of_dvd hdiv hq).trans_lt (hdeg ▸ A.small)
private def seedD:Derivation ℤ R R :=
 PolynomialModule.equivPolynomialSelf.compDer
  ((PowerSeries.derivative (R:=L)).restrictScalars ℤ).mapCoeffs
private theorem seedD_apply (q:R) :seedD q=diffPoly q:= by
 ext n:1
 rw [diffPoly,sum_coeff _ (by simp)]
 rfl
private def scale {S:Type} [za6 S] [zZE ℤ S] (a :S) (d:Derivation ℤ S S) :
 Derivation ℤ S S:=a•d
private theorem scale_apply {S:Type} [za6 S] [zZE ℤ S]
 (a :S) (d:Derivation ℤ S S) (b:S) :scale a d b=a*d b:=rfl
private def flowD (A:Cover) (afu:Bool) :Derivation ℤ R R :=
 let d:Derivation ℤ R R:=(Polynomial.derivative' (R:=i5)).restrictScalars ℤ
 if afu then
  scale (S:=R) A.g.derivative seedD - scale (S:=R) (diffPoly A.g) d
 else scale (S:=R) A.g seedD
private theorem flowD_apply (A:Cover) (afu:Bool) (q:R) :
  flowD A afu q=flowPoly A afu q:= by
 cases afu <;> simp only [flowD,flowPoly,Bool.false_eq_true,↓reduceIte,Derivation.sub_apply,
  scale_apply,Derivation.restrictScalars_apply,derivative'_apply,
  seedD_apply]
private theorem flow_ref (A:Cover) (afu:Bool) :flowPoly A afu (reference A)=0:= by
 have hs :diffPoly (reference A)=0:= by
  ext n:1
  rw [diffPoly,sum_coeff _ (by simp),coeff_zero,reference,coeff_C]
  split_ifs <;> simp
 cases afu <;> simp [flowPoly,hs,reference]
private def flowPartial (A:Cover) (afu:Bool) :R[X] :=
 if afu then C A.g.derivative*diff A.f - C (diffPoly A.g)*physDiff A.f
 else C A.g*diff A.f
private theorem partial_coeff (A:Cover) (afu:Bool) (n:ℕ) :
  (flowPartial A afu).coeff n=flowPoly A afu (A.f.coeff n) := by
 have hs : (diff A.f).coeff n=diffPoly (A.f.coeff n) :=
  sum_coeff diffPoly (by simp [diffPoly]) _ _
 have ht: (physDiff A.f).coeff n=(A.f.coeff n).derivative :=
  sum_coeff derivative derivative_zero _ _
 cases afu <;> simp only [flowPartial,flowPoly,Bool.false_eq_true,↓reduceIte,
  coeff_sub,coeff_C_mul,hs,ht]
private theorem weighted_eq (A:Cover) {P:L[X]} (J:LocalRoot A.f A.r P)
   (afu:Bool) :
   weightedLog J afu*(J.y - bY false (reference A)) *
     A.f.derivative.eval₂ (bY false) J.y = -(flowPartial A afu).eval₂ (bY false) J.y := by
 rw [chart_reference]
 let u:=J.y-PowerSeries.C (P5_7_7.phys (C A.r))
 let d:=A.f.derivative.eval₂ (bY false) J.y
 cases afu
 · simp only [weightedLog,flowPartial,Bool.false_eq_true,↓reduceIte,eval₂_mul,eval₂_C]
   calc
     _=bY false A.g*(J.logSeed*u*d) := by dsimp only [u,d]; ring
     _ = _:= by dsimp only [u,d]; rw [J.seed_eq,mul_neg]
 · simp only [weightedLog,flowPartial,↓reduceIte,eval₂_sub,eval₂_mul,eval₂_C]
   calc
     _=bY false A.g.derivative*(J.logSeed*u*d) -
         bY false (diffPoly A.g)*(J.logPhys*u*d) := by dsimp only [u,d]; ring
     _ = _:= by dsimp only [u,d]; rw [J.seed_eq,J.phys_eq]; ring
private theorem build_flow (A:Cover) {P:L[X]} (J:LocalRoot A.f A.r P)
    [zw7 F (Zk J)] (afu:Bool) :Nonempty (cxy J afu) := by
  let:zk2 R F:=Algebra.FormallyEtale.of_isLocalization (Rₘ:=F) R⁰
  obtain ⟨d₀,hd₀⟩:=a5n (B:=F) (bx0 (flowD A afu))
  let d:Derivation ℤ F F:=bx0 d₀
  have hd (q:R) :d (algebraMap R F q)=algebraMap R F (flowPoly A afu q) := by
    change bx0 d₀ (algebraMap R F q)= _
    rw [bia,hd₀,bia,flowD_apply]
  let:zk2 F (Zk J) :=Algebra.FormallyEtale.of_isSeparable _ _
  obtain ⟨D₀,hD₀⟩:=a5n (B:=Zk J) (bx0 d)
  let D:Derivation ℤ (Zk J) (Zk J) :=bx0 D₀
  have hD (q:F) :D (algebraMap F (Zk J) q)=algebraMap F (Zk J) (d q) := by
    change bx0 D₀ (algebraMap F (Zk J) q)= _
    rw [bia,hD₀,bia]
  refine ⟨⟨d,D,hD,hd,?_⟩⟩
  let i:=(algebraMap F (Zk J)).comp (algebraMap R F)
  let j:Zk J →+* E :=(Zk J).subtype
  let y :Zk J:=⟨seriesIn J.y,IntermediateField.mem_adjoin_simple_self F _⟩
  have ev (q:R[X]) :
      j (q.eval₂ i y)=seriesIn (q.eval₂ (bY false) J.y) := by
    rw [hom_eval₂,show j.comp i=(algebraMap F E).comp (algebraMap R F) from rfl,
      chart_base,show j y=seriesIn J.y from rfl,← hom_eval₂]
  have hr :A.f.eval₂ i y=0 :=
    j.injective (by rw [ev,J.root,map_zero,map_zero])
  have hc:=aNu D i y A.f (flowPartial A afu) (fun n=> by
    simp only [i,zQb,hD,hd,partial_coeff])
  rw [hr,map_zero] at hc
  have hDdiff :D (gI J)=D y := by
    change D (y - i (reference A))=D y
    rw [map_sub,sub_eq_self]
    simp only [i,zQb,hD,hd,flow_ref,map_zero]
  have hu:j (gI J)=seriesIn (J.y - bY false (reference A)) := by
    change seriesIn J.y - chartFrac (algebraMap R F (reference A))= _
    rw [chartFrac_base,map_sub]
  have hnu:j (gI J)≠0:= by
    rw [hu,chart_reference]
    exact (J.ref_unit.map seriesIn).ne_zero
  have hnd:j (A.f.derivative.eval₂ i y)≠0:= by
    rw [ev]
    exact (J.simple.map seriesIn).ne_zero
  change j (D (gI J)/gI J)= _
  rw [map_div₀]
  apply (div_eq_iff hnu).mpr
  apply mul_right_cancel₀ hnd
  have hh:=congrArg j hc
  simp only [map_zero,map_add,map_mul] at hh
  calc
    _ = -j ((flowPartial A afu).eval₂ i y) := by
      rw [hDdiff,mul_comm]
      exact eq_neg_of_add_eq_zero_right hh.symm
    _=(seriesIn (weightedLog J afu)*j (gI J)) *
        j (A.f.derivative.eval₂ i y) := by
      rw [ev (flowPartial A afu),hu,ev A.f.derivative,← map_neg,← map_mul,← map_mul,
        weighted_eq A J afu]
theorem proof :qkjFxXb.c1 := by
 intro A P J
 obtain ⟨hfin,hsep,hsmall⟩:=root_field A J
 let:zw7 F (Zk J) :=hsep
 exact ⟨hfin,hsep,hsmall,build_flow A J⟩
end
end q0wio9a
end
section
set_option backward.isDefEq.respectTransparency false
namespace qAggnYd
noncomputable section
open Polynomial IsDedekindDomain
open qkjFxXb (R B F seedDenoms)
open scoped qkjFxXb
local notation "rF" => algebraMap R F
local notation "rB" => algebraMap R B
local notation "bF" => algebraMap B F
private theorem physical_closed (D:Derivation ℤ F F)
  (hR : ∀ b:R,∃ c:R,D (rF b)=rF c) (b:B) :
  ∃ c:B,D (bF b)=bF c:= by
 obtain ⟨⟨n,s⟩,hs⟩:=IsLocalization.surj seedDenoms b
 have hm:=congrArg bF hs
 simp only [map_mul,← zG3 R B F] at hm
 have hs0:rF (s :R)≠0:= by
  rw [zG3 R B F]
  exact ((z0j B s).map bF).ne_zero
 obtain ⟨dn,hdn⟩:=hR n
 obtain ⟨ds,hds⟩:=hR (s :R)
 let num :=(s :R)*dn - n*ds
 refine ⟨IsLocalization.mk' B num (s^2),?_⟩
 have hn:=congrArg bF (IsLocalization.mk'_spec B num (s^2))
 simp only [num,map_mul bF,← zG3 R B F,
  SubmonoidClass.coe_pow,map_pow,map_sub,map_mul] at hn
 rw [(eq_div_iff hs0).mpr hm,D.leibniz_div,hdn,hds,smul_eq_mul,smul_eq_mul,
  smul_eq_mul,inv_pow,mul_comm ((rF (s :R)^2)⁻¹),← div_eq_mul_inv]
 exact (div_eq_iff (pow_ne_zero 2 hs0)).mpr hn.symm
private theorem prime_closed (D:Derivation ℤ F F)
   (hB : ∀ b:B,∃ c:B,D (bF b)=bF c)
   (q:HeightOneSpectrum B) (g c:B) (hg:Squarefree g) (hq:g∈q.asIdeal)
   (hDg:D (bF g)=bF (g*c)) :
   ∀ b∈q.asIdeal,∃ d∈q.asIdeal,D (bF b)=bF d:= by
 let t:B:=Submodule.IsPrincipal.generator q.asIdeal
 have ht:zye {t} = q.asIdeal:=Ideal.span_singleton_generator _
 have htq:t∈q.asIdeal:=ht ▸ Ideal.mem_span_singleton_self _
 have hmem (b:B) :b∈q.asIdeal↔t∣b:= by rw [← ht,zxV]
 obtain ⟨k,hk⟩:=(hmem g).mp hq
 have hkq:k∉q.asIdeal:= by
   intro h
   obtain ⟨u,hu⟩:=(hmem k).mp h
   have hunit :IsUnit t:=hg t ⟨u,by rw [hk,hu,mul_assoc]⟩
   exact q.isPrime.ne_top (ht.symm.trans (Ideal.span_singleton_eq_top.mpr hunit))
 obtain ⟨dt,hdt⟩:=hB t
 obtain ⟨dk,hdk⟩:=hB k
 rw [hk,map_mul bF t k,D.leibniz,smul_eq_mul,smul_eq_mul,hdt,hdk,
   ← map_mul,← map_mul,← map_add] at hDg
 have he :=zxb B F hDg
 have hsum:t*dk+k*dt∈q.asIdeal:= by
   rw [he]
   exact q.asIdeal.mul_mem_right c (q.asIdeal.mul_mem_right k htq)
 have hdk' : k*dt∈q.asIdeal:= by
   simpa only [add_sub_cancel_left] using
     q.asIdeal.sub_mem hsum (q.asIdeal.mul_mem_right dk htq)
 have hdt' := (q.isPrime.mem_or_mem hdk').resolve_left hkq
 intro b hb
 obtain ⟨u,rfl⟩:=(hmem b).mp hb
 obtain ⟨du,hdu⟩:=hB u
 refine ⟨t*du+u*dt,q.asIdeal.add_mem (q.asIdeal.mul_mem_right du htq)
   (q.asIdeal.mul_mem_left u hdt'),?_⟩
 rw [map_mul,D.leibniz,smul_eq_mul,smul_eq_mul,hdt,hdu,map_add,map_mul,map_mul]
private theorem local_closed (D:Derivation ℤ F F) (q:HeightOneSpectrum B)
   (hB : ∀ b:B,∃ c:B,D (bF b)=bF c)
   (hI : ∀ b∈q.asIdeal,∃ c∈q.asIdeal,D (bF b)=bF c)
   (z :F) (hz :q.valuation F z≤1) :
   q.valuation F (D z)≤1 ∧
     (q.valuation F z<1→q.valuation F (D z)<1) := by
 let v :=q.valuation F
 have hle (b:B) :v (D (bF b))≤1 := by
   obtain ⟨c,hc⟩:=hB b
   rw [hc]
   exact q.valuation_le_one c
 obtain ⟨n,s,hs⟩:=q.exists_primeCompl_mul_eq_of_integer z hz
 let y :=bF (s :B)
 have hvy :v y=1 :=q.valuation_eq_one_iff_notMem.mpr s.property
 have hn:v z=v (bF n) := by
   have hv :=congrArg (fun x :F=>v x) hs
   change v (z*y)=v (bF n) at hv
   rwa [map_mul,hvy,mul_one] at hv
 have hy0:y≠0:=v.ne_zero_iff.mp (hvy.trans_ne one_ne_zero)
 have hval :v (D z)=v (y*D (bF n) - bF n*D y) := by
   rw [(eq_div_iff hy0).mpr hs,D.leibniz_div,smul_eq_mul,smul_eq_mul,smul_eq_mul,
     map_mul,map_pow,v.map_inv,hvy,inv_one,one_pow,one_mul]
 change v (D z)≤1∧(v z<1→v (D z)<1)
 constructor
 · rw [hval]
   apply v.map_sub_le
   · rw [map_mul,hvy,one_mul]
     exact hle n
   · rw [map_mul]
     exact mul_le_one' (q.valuation_le_one n) (hle s)
 · intro h
   have hnv :v (bF n)<1 :=hn ▸ h
   obtain ⟨dn,hdn,he⟩:=hI n ((q.valuation_lt_one_iff_mem n).mp hnv)
   rw [hval]
   apply v.map_sub_lt
   · rw [map_mul,hvy,one_mul,he]
     exact (q.valuation_lt_one_iff_mem dn).mpr hdn
   · rw [map_mul]
     exact (mul_le_mul_of_nonneg_left (hle s) zero_le).trans_lt (by simpa only [mul_one] using hnv)
theorem proof :qkjFxXb.c2 := by
 intro g hsep D hR hDg q hq
 have hB:=physical_closed D hR
 obtain ⟨c,hc⟩:=hDg
 have hd:D (bF (rB g))=bF (rB g*rB c) := by
  rwa [← map_mul rB,← zG3 R B F,
    ← zG3 R B F]
 have hI:=prime_closed D hB q (rB g) (rB c) hsep.squarefree
  ((q.intValuation_lt_one_iff_mem _).mp hq) hd
 exact ⟨fun z hz=>(local_closed D q hB hI z hz).1,
  fun z hz=>(local_closed D q hB hI z hz.le).2 hz⟩
end
end qAggnYd
end
end
