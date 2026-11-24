import ProximityPrize.SubmissionLower.Zgvu91a
import ProximityPrize.SubmissionLower.ZGcgEBb
import ProximityPrize.SubmissionLower.ZBcmVie
import ProximityPrize.SubmissionLower.Z4EMMWa
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import ProximityPrize.SubmissionLower.ZEdS9yd
import ProximityPrize.SubmissionLower.Zdhd3Ub
import Mathlib.NumberTheory.RamificationInertia.Valuation
set_option Elab.async false
open private sum_coeff from ProximityPrize.SubmissionLower.Z62SyBc
open _root_ renaming Algebra → zZE, Algebra.IsSeparable → zw7, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsScalarTower.algebraMap_apply → zG3, Module.IsTorsionFree → zYo, Polynomial.X → z7y, Polynomial.X_ne_zero → z05, PowerSeries.C → zMG, RingHom.comp_apply → zQb
section
namespace qVHIGFe
theorem proof :qrGSFbd.c2 :=
 qoCymac.of_children
  q5eiIAb.proof
  (qhFwyvc.of_children specialization formula)
  qvOlzpd.proof
  q6hv5Ed.proof
  qpI7nyd.proof
  qIGP9Qa.proof
end qVHIGFe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qoHmCXd
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing
open cu (L FX)
open P5_7_7 (phys)
open q2TwyLa (i5 diffPoly)
open qoGY3we (bY)
open qz2teNe
open scoped nonZeroDivisors
private theorem extendFrac {R K:Type} [CommRing R] [IsDomain R] [Field K]
    [zZE ℤ R] [zZE R K] [z0o R K] (D:Derivation ℤ R R) :
    ∃ d:Derivation ℤ K K,∀ a,d (algebraMap R K a)=algebraMap R K (D a) := by
  let f :=algebraMap R K
  let b:R →+* TrivSqZeroExt K K :=
    { toFun a :=⟨f a,f (D a)⟩
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := by intro a c; ext <;> simp
      map_mul' := by intro a c; ext <;> simp [D.leibniz,smul_eq_mul,mul_comm] }
  have hu (a :R⁰) :IsUnit (b a) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff f (zxb R K)).mpr
        (nonZeroDivisors.ne_zero a.property)))
  let g:K →+* TrivSqZeroExt K K:=IsLocalization.lift hu
  have hg (a :R) :g (f a)=b a :=IsLocalization.lift_eq hu a
  have hfst: (TrivSqZeroExt.fstHom ℤ K K).toRingHom.comp g=RingHom.id K:= by
    apply IsLocalization.ringHom_ext R⁰
    exact RingHom.ext (fun a=>congrArg TrivSqZeroExt.fst (hg a))
  have hf (a :K) : (g a).fst=a :=RingHom.congr_fun hfst a
  let d:K →+ K :=
    { toFun a :=(g a).snd
      map_zero' := by simp
      map_add' := by intro a c; simp }
  refine ⟨{ toFun:=d,map_add' := d.map_add,map_smul' := fun n a=>d.map_zsmul n a
            map_one_eq_zero' := by change (g 1).snd=0; simp
            leibniz' := fun a c=> by
              change (g (a*c)).snd=a•(g c).snd+c•(g a).snd
              rw [map_mul,TrivSqZeroExt.snd_mul,hf,hf,op_smul_eq_smul] },?_⟩
  intro a
  exact congrArg TrivSqZeroExt.snd (hg a)
local instance :zZE ℤ i5:=Ring.toIntAlgebra i5
local instance :zZE ℤ kB:=Ring.toIntAlgebra kB
local instance :Differential i5:= by
 let D:=PowerSeries.derivative (R:=L)
 exact { deriv := {
  toFun:=D
  map_add' := D.map_add
  map_smul' := fun n a=>(D.toLinearMap.toAddMonoidHom).map_zsmul n a
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz } }
private def dPoly :Derivation ℤ tu tu:= by
 let D:=Differential.mapCoeffs (A:=i5)
 exact {
  toFun:=D
  map_add' := D.map_add
  map_smul' := fun n a=>(D.toLinearMap.toAddMonoidHom).map_zsmul n a
  map_one_eq_zero' := D.map_one_eq_zero
  leibniz' := D.leibniz }
private theorem dPoly_eq (a :tu) :dPoly a=diffPoly a := by
 apply Polynomial.ext
 intro i
 rw [diffPoly,sum_coeff _ (map_zero _)]
 rfl
local instance :IsLocalRing afe :=IsLocalization.AtPrime.isLocalRing _ zeroIdeal
private theorem max_eq :
  maximalIdeal afe=Ideal.span {algebraMap tu afe z7y} := by
 rw [← IsLocalization.AtPrime.map_eq_maximalIdeal zeroIdeal afe,
  zeroIdeal,Ideal.map_span,Set.image_singleton]
instance :IsDiscreteValuationRing afe := by
 let:IsNoetherianRing afe :=IsLocalization.isNoetherianRing zeroIdeal.primeCompl _ inferInstance
 have hx :algebraMap tu afe z7y≠0 :=
   fun h=>z05 ((zxb tu kB) (by
     simp [zG3 tu afe kB,h]))
 have hn : ¬ IsField afe := by
   rw [isField_iff_maximalIdeal_eq,max_eq,Ideal.span_singleton_eq_bot]
   exact hx
 apply ((IsDiscreteValuationRing.TFAE afe hn).out 5 1).mp
 rw [max_eq]
 exact ⟨_,rfl⟩
abbrev zeroPrime :HeightOneSpectrum afe :=IsDiscreteValuationRing.maximalIdeal afe
abbrev zeroVal:=zeroPrime.valuation kB
private abbrev f :=algebraMap tu kB
private theorem val_unit (a :tu) (ha :a∈zeroIdeal.primeCompl) :
  zeroVal (f a)=1 := by
 rw [zG3 tu afe kB]
 exact (zeroPrime.valuation_eq_one_iff_notMem (K:=kB)).mpr
  (fun h=>ha ((IsLocalization.AtPrime.to_map_mem_maximal_iff afe zeroIdeal _).mp h))
theorem base_derivation :
    ∃ d:Derivation ℤ kB kB,(∀ a :tu,d (f a)=f (diffPoly a)) ∧
      ∀ z :kB,zeroVal z≤1→zeroVal (d z)≤zeroVal z := by
  obtain ⟨d,hd⟩:=extendFrac dPoly (K:=kB)
  refine ⟨d,fun a=>(hd a).trans (congrArg f (dPoly_eq a)),?_⟩
  have hπ:dPoly z7y=0:=Differential.mapCoeffs_X
  have hD (a :tu) :zeroVal (f (dPoly a))≤zeroVal (f a) := by
    suffices aux : ∀ n:ℕ,∀ a :tu,a.natDegree=n →
        zeroVal (f (dPoly a))≤zeroVal (f a) from aux _ a rfl
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a ha
      by_cases hm:a.coeff 0=0
      · obtain ⟨b,hb⟩:=X_dvd_iff.mpr hm
        by_cases hn:b=0
        · simp [hb,hn]
        · have hbn:b.natDegree<n:= by
            rw [hb,natDegree_mul z05 hn,natDegree_X] at ha
            omega
          rw [hb,dPoly.leibniz,hπ,smul_zero,add_zero,smul_eq_mul]
          simp only [map_mul f,Valuation.map_mul]
          exact mul_le_mul_of_nonneg_left (ih _ hbn b rfl) zero_le
      · rw [val_unit a (fun h=>hm (X_dvd_iff.mp (Ideal.mem_span_singleton.mp h))),
          zG3 tu afe kB]
        exact zeroPrime.valuation_le_one (K:=kB) _
  intro z hz
  obtain ⟨q,rfl⟩:=IsDiscreteValuationRing.exists_lift_of_le_one hz
  obtain ⟨a,b,hb,hq⟩:=q.property
  change (q:kB)= _ at hq
  change zeroVal (d (q:kB))≤zeroVal (q:kB)
  have hbu:=val_unit b hb
  have hDb:=(hD b).trans_eq hbu
  rw [hq,← div_eq_mul_inv,d.leibniz_div,hd,hd,smul_eq_mul,smul_eq_mul,smul_eq_mul]
  simp only [Valuation.map_mul,map_pow,map_inv₀,Valuation.map_div,hbu,
    inv_one,one_pow,one_mul,div_one]
  apply (zeroVal.map_sub _ _).trans
  simp only [Valuation.map_mul,hbu,one_mul]
  exact max_le (hD a) (mul_le_of_le_one_right' hDb)
def finiteMap:tu →+* kB:=eval₂RingHom (f.comp C) (f z7y)⁻¹
theorem finiteMap_comp:embedding.comp finiteMap=seriesIn.comp (bY false) := by
 apply Polynomial.ringHom_ext
 · intro a
   simp only [finiteMap,zQb,coe_eval₂RingHom,eval₂_C,embedding_on,bY]
 · simp only [finiteMap,zQb,coe_eval₂RingHom,eval₂_X,map_inv₀,embedding_on,
    bY,Bool.false_eq_true,↓reduceIte]
   change ((algebraMap FX Target) (phys z7y)⁻¹)⁻¹ =
    (algebraMap FX Target) (phys z7y)
   rw [map_inv₀,inv_inv]
theorem finiteMap_deriv (d:Derivation ℤ kB kB)
  (hd : ∀ a :tu,d (f a)=f (diffPoly a)) (q:tu) :
  d (finiteMap q)=finiteMap (diffPoly q) := by
 have hC (i:ℕ) :d ((f.comp C) (q.coeff i))=(f.comp C) ((diffPoly q).coeff i) := by
  rw [zQb,zQb,← dPoly_eq,hd,← dPoly_eq]
  exact congrArg f (Differential.mapCoeffs_C (q.coeff i))
 have hX:d (f z7y)=0:= by
  rw [hd,← dPoly_eq,show dPoly z7y=0 from Differential.mapCoeffs_X,map_zero]
 have h:=q85rTDe.aNu (E :=kB) d (f.comp C) (f z7y)⁻¹ q (diffPoly q) hC
 rw [d.leibniz_inv,hX,smul_zero,mul_zero,add_zero] at h
 exact h
theorem finiteMap_const (a :L) (d:Derivation ℤ kB kB)
   (hd : ∀ q:tu,d (f q)=f (diffPoly q)) :
   d (finiteMap (C (zMG a)))=0:= by
 rw [finiteMap_deriv d hd,← dPoly_eq]
 rw [show dPoly (C (zMG a))=0 by
     change Differential.mapCoeffs (C (zMG a))=0
     rw [Differential.mapCoeffs_C]
     change C (PowerSeries.derivative (zMG a))=0
     simp,map_zero]
end
end qoHmCXd
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qoHmCXd
noncomputable section
open Polynomial IsDedekindDomain IsLocalRing
open cu (L)
open P5 (K p)
open P5_7_7 (phys)
open q2TwyLa (i5 diff diffPoly)
open q85rTDe (extend_derivation aNu)
open qoGY3we
open qz2teNe
local instance :zZE ℤ kB:=Ring.toIntAlgebra kB
private theorem integral_log {R F E :Type} [CommRing R] [IsDomain R]
   [IsDiscreteValuationRing R] [Field F] [Field E] [zZE R F] [z0o R F]
   [zZE F E] [zZE R E] [IsScalarTower R F E] [Module.Finite F E]
   [zw7 F E] [CharP F p]
   (tame :TameLog) (hdeg:Module.finrank F E<p)
   (d:Derivation ℤ F F) (D:Derivation ℤ E E)
   (hD : ∀ x,D (algebraMap F E x)=algebraMap F E (d x))
   (hval : let v := (IsDiscreteValuationRing.maximalIdeal R).valuation F
           ∀ x,v x≤1→v (d x)≤v x)
   (u:E) (hu:u≠0) :IsIntegral R (D u/u) := by
 let B:=integralClosure R E
 let:IsScalarTower R B E :=IsScalarTower.of_algebraMap_eq (fun _=>rfl)
 let:zYo R E := .trans_faithfulSMul R F E
 let:IsDedekindDomain B:=IsIntegralClosure.isDedekindDomain R F E B
 let:z0o B E :=integralClosure.isFractionRing_of_finite_extension F E
 let:Algebra.IsIntegral R B:=IsIntegralClosure.isIntegral_algebra R E
 let:zYo R B:=IsIntegralClosure.isTorsionFree R E
 let v :=IsDiscreteValuationRing.maximalIdeal R
 have h (q:HeightOneSpectrum B) :q.valuation E (D u/u)≤1 := by
   let:q.asIdeal.LiesOver v.asIdeal :=
     ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)).symm⟩
   let e :=v.asIdeal.ramificationIdx' q.asIdeal
   have he :0<e :=Nat.pos_of_ne_zero
     (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver q.asIdeal v.ne_bot)
   exact tame hdeg (v.valuation F) (q.valuation E) e d D (v.valuation_surjective F)
     (q.valuation_surjective E) he (fun x=>(v.valuation_liesOver E q x).symm)
     hD (fun x hx=>(hval x hx).trans hx) u hu
     (Or.inl fun x hx=>(hval x hx.le).trans_lt hx)
 obtain ⟨b,hb⟩:=HeightOneSpectrum.mem_integers_of_valuation_le_one E (D u/u) h
 rw [← hb]
 exact b.property
private theorem root_separable {S:Type} [Field S] [zZE kB S]
  {F:kB[X]} {y :S} (hy :aeval y F=0)
  (hder :aeval y F.derivative≠0) :
  IsSeparable kB y∧(minpoly kB y).natDegree≤F.natDegree := by
 have hF:F≠0:= fun h=>hder (by simp [h])
 have hi:IsIntegral kB y :=isAlgebraic_iff_isIntegral.mp ⟨F,hF,hy⟩
 have hd:=minpoly.dvd kB y hy
 refine ⟨(separable_iff_derivative_ne_zero (minpoly.irreducible hi)).mpr ?_,
  natDegree_le_of_dvd hd hF⟩
 intro h
 obtain ⟨q,hq⟩:=hd
 apply hder
 rw [hq,derivative_mul,h,zero_mul,zero_add,map_mul,minpoly.aeval,zero_mul]
theorem proof :qz2teNe.c2 := by
 intro tame A P J
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP i5 p:=charP_of_injective_ringHom PowerSeries.C_injective p
 let:CharP kB p:=charP_of_injective_ringHom (zxb tu kB) p
 let:zZE kB Target :=embedding.toAlgebra
 let y :=seriesIn J.y
 let F:=A.f.map finiteMap
 have ev (g:tu[X]) :
     aeval y (g.map finiteMap)=seriesIn (g.eval₂ (bY false) J.y) := by
   rw [aeval_def,eval₂_map,show (algebraMap kB Target).comp finiteMap= _ from finiteMap_comp]
   exact (hom_eval₂ g (bY false) seriesIn J.y).symm
 have hs :=(J.simple.map seriesIn).ne_zero
 have hz :aeval y F=0:= by
   change aeval y (A.f.map finiteMap)=0
   rw [ev,J.root,map_zero]
 have hn:aeval y F.derivative≠0:= by
   change aeval y (A.f.map finiteMap).derivative≠0
   rwa [derivative_map,ev]
 obtain ⟨hsep,hdeg⟩:=root_separable hz hn
 let E :=IntermediateField.adjoin kB ({y} : Set Target)
 let a :E :=⟨y,IntermediateField.mem_adjoin_simple_self kB y⟩
 let i:=E.val.toRingHom
 let m:=(algebraMap kB E).comp finiteMap
 let:zw7 kB E :=
   (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
 let:Module.Finite kB E :=IntermediateField.finiteDimensional_adjoin
   (fun b hb=>(Set.mem_singleton_iff.mp hb).symm ▸ hsep.isIntegral)
 have hd:Module.finrank kB E<p :=
   (IntermediateField.adjoin.finrank hsep.isIntegral).trans_le hdeg |>.trans_lt
     ((natDegree_map_le (p:=A.f)).trans_lt A.small)
 obtain ⟨d,hcoeff,hval⟩:=base_derivation
 obtain ⟨D,hD⟩:=extend_derivation (E :=E) d
 let ref :tu:=C (zMG A.r)
 let u:=a - m ref
 have hmap :i.comp m=seriesIn.comp (bY false) :=finiteMap_comp
 have hu:i u=seriesIn (J.y-PowerSeries.C (phys (C A.r))) := by
   rw [show u=a - m ref from rfl,map_sub,← zQb,hmap,map_sub]
   congr 1
   simp only [zQb,ref,bY,coe_eval₂RingHom,eval₂_C,PowerSeries.map_C]
   rfl
 have hu' := (J.ref_unit.map seriesIn).ne_zero
 have heval (g:tu[X]) :
     i (g.eval₂ m a)=seriesIn (g.eval₂ (bY false) J.y) := by
   rw [hom_eval₂,hmap]
   exact hom_eval₂ g (bY false) seriesIn J.y |>.symm
 have hzero :A.f.eval₂ m a=0:=i.injective (by rw [heval,J.root,map_zero,map_zero])
 have hdiff :diffPoly 0=0:= by simp [diffPoly,Polynomial.sum_def]
 have hchain:=aNu D m a A.f (diff A.f) (fun j=> by
   simp only [m,zQb,hD,finiteMap_deriv d hcoeff,diff]
   rw [sum_coeff _ hdiff])
 rw [hzero,map_zero] at hchain
 have hmul :i (D a)*seriesIn (A.f.derivative.eval₂ (bY false) J.y) =
     -seriesIn ((diff A.f).eval₂ (bY false) J.y) := by
   have h:=congrArg i hchain
   rw [map_zero,map_add,map_mul,heval,heval] at h
   linear_combination -h
 have hdu:D u=D a := by
   rw [show u=a - m ref from rfl,map_sub,zQb,hD,
     finiteMap_const A.r d hcoeff,map_zero,sub_zero]
 have hlog:i (D u/u)=seriesIn J.logSeed := by
   rw [map_div₀,hdu,hu]
   apply (div_eq_iff hu').mpr
   apply mul_right_cancel₀ hs
   rw [hmul,← map_mul,← map_mul,J.seed_eq,map_neg]
 have hi: ((algebraMap kB E).comp afe.val.toRingHom).IsIntegralElem (D u/u) :=
   integral_log (R:=afe) tame (by exact hd) d D hD hval u (fun h=>hu' (hu ▸ (h ▸ map_zero i)))
 have h:=hi.map i
 rwa [hlog] at h
end
end qoHmCXd
end
