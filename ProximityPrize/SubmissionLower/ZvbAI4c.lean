import ProximityPrize.SubmissionLower.Zdj6KNe
import ProximityPrize.SubmissionLower.ZInx8Od
set_option Elab.async false
section
namespace q5eiIAb
noncomputable section
open cu (L)
open E7 (CurveField)

open q1kuFjb (integralSeries residue fWQ)
open KaehlerDifferential WithZero
open private bZj from ProximityPrize.SubmissionLower.Y
open private dW1 from ProximityPrize.SubmissionLower.BG
open private seed_derivative_mul from ProximityPrize.SubmissionLower.ZInx8Od
private abbrev Series :=LaurentSeries L
private abbrev v :Valuation Series ℤᵐ⁰:=Valued.v
private abbrev diff :Series →ₗ[L] Series :=LaurentSeries.derivative L
private theorem diff_coeff (f :Series) (i:ℤ) :
  (diff f).coeff i=(i+1)•f.coeff (i+1) := by
 simp only [diff,LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_coeff,
  Ring.choose_one_right,Nat.cast_one]
private theorem diff_zero_coeff (f :Series) : (diff f).coeff 0=f.coeff 1 := by
 simpa only [zero_add,one_smul] using diff_coeff f 0
private theorem regular_diff {f :Series} (hf :v f≤1) :v (diff f)≤1 := by
 have reg (g:Series) :v g≤1 ↔ ∀ i:ℤ,i<0→ g.coeff i=0:= by
   simpa only [neg_zero,exp_zero] using
     (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L (D:=0) (f :=g))
 apply (reg _).2
 intro i hi
 rw [diff_coeff]
 by_cases h:i+1=0
 · rw [h,zero_smul]
 · rw [(reg f).1 hf _ (by omega),smul_zero]
private theorem uniformizer_coeff {f :Series} (hf :v f=exp (-1 :ℤ)) :
   f.coeff 1≠0:= by
 intro hz
 have h:v f≤exp (-(2 :ℤ)) :=
   (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero L).2 fun i hi=> by
     by_cases he :i=1
     · rwa [he]
     · exact LaurentSeries.coeff_zero_of_lt_valuation L hf.le (by omega)
 rw [hf,exp_le_exp] at h
 omega
private theorem uniformizer_diff {f :Series} (hf :v f=exp (-1 :ℤ)) :
  v (diff f)=1 := by
 have hle :=regular_diff (hf ▸ exp_le_one_iff.mpr (by decide : (-1 :ℤ)≤0))
 refine le_antisymm hle (le_of_not_gt fun hlt => ?_)
 have hsmall:v (diff f)≤exp (-1 :ℤ) :=
  (lt_mul_exp_iff_le (y :=exp (-1 :ℤ)) exp_ne_zero).mp
    (by simpa only [← exp_add,neg_add_cancel,exp_zero] using hlt)
 exact uniformizer_coeff hf (diff_zero_coeff f ▸
  LaurentSeries.coeff_zero_of_lt_valuation L hsmall (by decide : (0:ℤ)<1))
private theorem mul_residue {f g:Series} (hf :v f≤1) (hg:v g≤1) :
  (f * g).coeff 0=f.coeff 0*g.coeff 0:= by
 let x :=integralSeries f hf
 let y :=integralSeries g hg
 exact (fWQ (x*y)).symm.trans
  ((map_mul residue x y).trans (congrArg₂ (· * ·) (fWQ x) (fWQ y)))
variable {E :Type} [Field E] [Algebra L E]
private theorem embed_smul (a :E →ₐ[L] Series) (r :L) (c:E) :
  a (r•c)=r•a c:= by
 rw [Algebra.smul_def,map_mul,a.commutes,LaurentSeries.algebraMap_apply,
  HahnSeries.C_apply,HahnSeries.single_zero_mul_eq_smul]
private theorem compare (a :E →ₐ[L] Series) (hcurve :CurveField L E) (t:E)
    (ht:diff (a t)≠0) :
    ∃ δ:Derivation L E E,∀ c,a (δ c)*diff (a t)=diff (a c) := by
  have htr :=bZj hcurve
  obtain ⟨u,_,hfin⟩:=hcurve
  let T:=IntermediateField.adjoin L ({u} : Set E)
  let:Module.Finite T E :=hfin
  have :Algebra.EssFiniteType L T:=IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton u))
  have :Algebra.EssFiniteType L E :=Algebra.EssFiniteType.comp L T E
  have hdim:=dW1 htr
  let:Algebra E Series :=a.toRingHom.toAlgebra
  let:IsScalarTower L E Series :=⟨fun r x z=> by
    change a (r•x)*z=r•(a x*z)
    rw [embed_smul,← HahnSeries.single_zero_mul_eq_smul (r :=r) (x :=a x),
      mul_assoc,HahnSeries.single_zero_mul_eq_smul]⟩
  let d:Derivation L E Series :=
    { toFun:= fun c=>diff (a c)
      map_add' := fun x y=> by simp only [map_add]
      map_smul' := fun r x=> by rw [embed_smul,map_smul,RingHom.id_apply]
      map_one_eq_zero' := by
        change diff (a 1)=0
        rw [map_one]
        change LaurentSeries.derivative L (HahnSeries.single (0:ℤ) (1 :L))=0
        rw [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_single]
        simp
      leibniz' := fun x y=> by
        change diff (a (x*y))=a x*diff (a y)+a y*diff (a x)
        rw [map_mul,seed_derivative_mul,mul_comm (diff (a x))] }
  have hnon :D L E t≠0:= fun h=>ht (by
    change d t=0
    rw [← d.liftKaehlerDifferential_comp_D,h,map_zero])
  let f :=LinearMap.toSpanSingleton E (KaehlerDifferential L E) (D L E t)
  let e :=LinearEquiv.ofBijective f
    ⟨LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton E hnon),
      exists_smul_eq_of_finrank_eq_one hdim hnon⟩
  refine ⟨e.symm.toLinearMap.compDer (D L E),fun c => ?_⟩
  have h:e.symm (D L E c)•D L E t=D L E c:=e.apply_symm_apply _
  have h' := congrArg d.liftKaehlerDifferential h
  rw [map_smul,d.liftKaehlerDifferential_comp_D,d.liftKaehlerDifferential_comp_D] at h'
  exact h'
theorem proof :qoCymac.c1 := by
 intro E _ _ w a hcurve hv
 obtain ⟨t,ht⟩:=w.normalized (exp (-1 :ℤ))
 rw [hv] at ht
 let s :=(a t).coeff 1
 have hs :s≠0:=uniformizer_coeff ht
 have hunit :=uniformizer_diff ht
 have hne :diff (a t)≠0:=v.ne_zero_iff.mp (hunit.trans_ne one_ne_zero)
 obtain ⟨δ,hδ⟩:=compare a hcurve t hne
 refine ⟨s•δ,fun c hc => ?_⟩
 rw [hv] at hc
 have hreg:=regular_diff hc
 have hδreg:v (a (δ c))≤1 := by
   have h:=congrArg v (hδ c)
   rw [map_mul,hunit,mul_one] at h
   rwa [h]
 have hcoeff :=congrArg (fun g:Series=>g.coeff 0) (hδ c)
 rw [mul_residue hδreg hunit.le,diff_zero_coeff,diff_zero_coeff] at hcoeff
 constructor
 · rw [Derivation.smul_apply,Algebra.smul_def,map_mul,w.on_constants _ hs,one_mul,hv]
   exact hδreg
 · rw [Derivation.smul_apply,embed_smul,HahnSeries.coeff_smul,smul_eq_mul,mul_comm s]
   exact hcoeff
end
end q5eiIAb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qymFiQe
noncomputable section
open Polynomial qps5rle
open P5 (p)
open cu (L)
open scoped WithZero
private theorem physical_constant (x :L) :
  algebraMap L F x=HahnSeries.C (algebraMap L SeedSeries x) := by
 rw [HahnSeries.algebraMap_apply',PowerSeries.algebraMap_apply,HahnSeries.ofPowerSeries_C]
private def seriesExpansion (x :L) :SeedSeries[X] →+* PowerSeries SeedSeries :=
 eval₂RingHom PowerSeries.C (PowerSeries.X+PowerSeries.C (algebraMap L SeedSeries x))
private theorem expand_series (x :L) :
   physExpansion x=(HahnSeries.ofPowerSeries ℤ SeedSeries).comp (seriesExpansion x) := by
 apply Polynomial.ringHom_ext
 · intro a
   simp [physExpansion,seriesExpansion,LaurentSeries.algebraMap_apply]
 · simp [physExpansion,seriesExpansion,physical_constant]
private theorem aNF (x :L) (b:SeedSeries[X]) (i:ℤ) :
  (physExpansion x b).coeff i=if i<0 then 0 else PowerSeries.coeff i.natAbs (seriesExpansion x b) := by
 rw [expand_series,RingHom.comp_apply]
 exact PowerSeries.coeff_coe (seriesExpansion x b) i
private theorem expand_zero (x :L) (b:SeedSeries[X]) :
  (physExpansion x b).coeff 0=b.eval (algebraMap L SeedSeries x) := by
 have h:PowerSeries.constantCoeff.comp (seriesExpansion x)=evalRingHom (algebraMap L SeedSeries x) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [seriesExpansion]
  · simp [seriesExpansion]
 simpa [aNF,PowerSeries.coeff_zero_eq_constantCoeff] using RingHom.congr_fun h b
private theorem expand_le (x :L) (b:SeedSeries[X]) :vPhysical (physExpansion x b)≤1 := by
 apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero SeedSeries (D:=0)).mpr
 intro i hi
 simp [aNF,hi]
private theorem expand_unit {x :L} {b:SeedSeries[X]}
  (hb:b.eval (algebraMap L SeedSeries x)≠0) :vPhysical (physExpansion x b)=1 := by
 have hc: (physExpansion x b).coeff 0≠0:= by rwa [expand_zero]
 apply le_antisymm (expand_le x b) (le_of_not_gt ?_)
 intro h
 have hn:vPhysical (physExpansion x b)≠0:= by
  intro hz
  exact hc (by simp [vPhysical.zero_iff.1 hz])
 have hlog:=(WithZero.log_lt_iff_lt_exp (a :=0) hn).mpr (by simpa only [WithZero.exp_zero] using h)
 have hsmall:=(WithZero.log_le_iff_le_exp (a := -1) hn).mp (show _≤_ by omega)
 exact hc ((LaurentSeries.valuation_le_iff_coeff_lt_eq_zero SeedSeries (D:=1)).mp hsmall 0 (by decide))
private def seedPoly (b:SeedSeries[X]) :SeedSeries[X] :=
 b.sum fun j a=>monomial j (LaurentSeries.derivative L a)
private theorem coeff_seedPoly (b:SeedSeries[X]) (j:ℕ) :
   (seedPoly b).coeff j=LaurentSeries.derivative L (b.coeff j) := by
 rw [seedPoly,coeff_sum,Polynomial.sum,Finset.sum_eq_single j,coeff_monomial]
 · simp
 · intro i _ hi
   simp [coeff_monomial,hi]
 · intro hj
   simp [notMem_support_iff.mp hj]
private theorem coeff_seedDerivative (f :SeedSeries[X][X]) (j:ℕ) :
   (seedDerivative f).coeff j=seedPoly (f.coeff j) := by
 rw [seedDerivative,coeff_sum,Polynomial.sum,Finset.sum_eq_single j,coeff_monomial]
 · simp [seedPoly]
 · intro i _ hi
   simp [coeff_monomial,hi]
 · intro hj
   simp [notMem_support_iff.mp hj]
private theorem derive_C {D:Derivation ℤ F F} (hD:coefficientwise D) (a :SeedSeries) :
  D (algebraMap SeedSeries F a)=algebraMap SeedSeries F (LaurentSeries.derivative L a) := by
 apply HahnSeries.ext
 funext i
 rw [hD,LaurentSeries.algebraMap_apply,LaurentSeries.algebraMap_apply,HahnSeries.C_apply,HahnSeries.C_apply]
 by_cases hi:i=0 <;> simp [hi]
theorem derive_seed {D:Derivation ℤ F F} (hD:coefficientwise D) :D seed = 1 := by
 rw [seed,derive_C hD,LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_single]
 simp [HahnSeries.C_apply,LaurentSeries.algebraMap_apply]
private theorem derive_physical {D:Derivation ℤ F F} (hD:coefficientwise D) (x :L) :
   D (HahnSeries.single 1 1+algebraMap L F x)=0:= by
 have hτ:D (HahnSeries.single 1 1)=0:= by
   apply HahnSeries.ext
   funext i
   rw [hD,HahnSeries.coeff_zero]
   by_cases hi:i=1
   · rw [hi,HahnSeries.coeff_single_same]
     change LaurentSeries.derivative L (HahnSeries.single 0 1)=0
     rw [LaurentSeries.derivative_apply,LaurentSeries.hasseDeriv_single]
     simp
   · simp [HahnSeries.coeff_single_of_ne hi]
 rw [map_add,hτ,zero_add,physical_constant,← LaurentSeries.algebraMap_apply,derive_C hD]
 have h:LaurentSeries.derivative L (algebraMap L SeedSeries x)=0:= by
   rw [LaurentSeries.algebraMap_apply,HahnSeries.C_apply,LaurentSeries.derivative_apply,
     LaurentSeries.hasseDeriv_single]
   simp
 rw [h,map_zero]
theorem derive_coeff {D:Derivation ℤ F F} (hD:coefficientwise D)
  (x :L) (f :SeedSeries[X][X]) (i:ℕ) :
  D (physExpansion x (f.coeff i))=physExpansion x ((seedDerivative f).coeff i) := by
 rw [coeff_seedDerivative]
 unfold physExpansion
 simp only [coe_eval₂RingHom]
 rw [aNu D _ _ _ (seedPoly (f.coeff i)),derive_physical hD,mul_zero,add_zero]
 intro j
 rw [coeff_seedPoly,derive_C hD]
private theorem rootIntegral (g:F[X]) (hcoeff : ∀ i,vPhysical (g.coeff i)≤1)
   (hunit :vPhysical g.leadingCoeff=1) (w:Roots) (hw:aeval (point w) g=0) :
   IsIntegral IntegerRing (point w) := by
 have hne :g.leadingCoeff≠0:= fun hz=> by simp [hz] at hunit
 let q:=C g.leadingCoeff⁻¹*g
 have hq:q.Monic:=monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hne)
 have hqa :aeval (point w) q=0:= by simp [q,hw]
 let j:=algebraMap IntegerRing F
 have hmem:q∈(mapRingHom j).range :=(Polynomial.mem_map_range j).mpr (fun i=> by
   have hc:vPhysical (q.coeff i)≤1 := by
     simpa only [q,coeff_C_mul,map_mul,map_inv₀,hunit,inv_one,one_mul] using hcoeff i
   exact ⟨⟨q.coeff i,hc⟩,rfl⟩)
 obtain ⟨r,hr⟩:=hmem
 change r.map j=q at hr
 have hj:Function.Injective j:=Subtype.val_injective
 have hrm:r.Monic:=hj.monic_map_iff.mpr (hr.symm ▸ hq)
 refine ⟨r,hrm,?_⟩
 change (r.eval₂ (algebraMap IntegerRing (Simple w)) (point w))=0
 rw [show algebraMap IntegerRing (Simple w)=(algebraMap F (Simple w)).comp j from rfl,
   ← eval₂_map,hr]
 exact hqa
private theorem expand_injective (x :L) :Function.Injective (physExpansion x) := by
 let j:=algebraMap SeedSeries[X] F
 have hj:Function.Injective j:=Polynomial.algebraMap_hahnSeries_injective ℤ
 have hm:physExpansion x=j.comp (taylorAlgHom (algebraMap L SeedSeries x)).toRingHom:= by
   apply Polynomial.ringHom_ext
   · intro a
     simp [j,physExpansion,LaurentSeries.algebraMap_apply]
   · simp [j,physExpansion,physical_constant,taylor_X]
 rw [hm]
 exact hj.comp (taylor_injective _)
private theorem expanded_separable (x :L) (f :SeedSeries[X][X])
    (hpos :0<f.natDegree) (hdis :f.discr≠0) : (f.map (physExpansion x)).Separable := by
  let g:=f.map (physExpansion x)
  have hg:g.natDegree=f.natDegree :=natDegree_map_eq_of_injective (expand_injective x) _
  have hpos' : 0<g.natDegree :=hg ▸ hpos
  let r :=g.resultant g.derivative g.natDegree (g.natDegree - 1)
  have hr :r≠0:= by
    unfold r g
    rw [derivative_map,hg,resultant_map_map,resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos)]
    exact (map_ne_zero_iff _ (expand_injective x)).2
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        (leadingCoeff_ne_zero.mpr (fun h=> by simp [h] at hpos))) hdis)
  obtain ⟨a,b,_,_,hab⟩:=exists_mul_add_mul_eq_C_resultant g g.derivative le_rfl
    (natDegree_derivative_le g) (Or.inl hpos'.ne')
  refine ⟨C r⁻¹*a,C r⁻¹*b,?_⟩
  rw [mul_assoc,mul_assoc,← mul_add,mul_comm a g,mul_comm b g.derivative,
    hab,← C_mul,inv_mul_cancel₀ hr,C_1]
theorem root_data (x :L) (f :SeedSeries[X][X]) (hp:0<f.natDegree)
   (hdeg:f.natDegree<p) (hl:leadAt x f≠0) (hdisc:f.discr≠0)
   (w:Roots) (hw:evalRoot x f w=0) :
   IsSeparable F w∧Module.finrank F (Simple w)<p ∧
     IsIntegral IntegerRing (point w)∧evalRoot x f.derivative w≠0:= by
 let g:=f.map (physExpansion x)
 have hg:g.natDegree=f.natDegree :=natDegree_map_eq_of_injective (expand_injective x) _
 have hn:g≠0:= fun h=>hp.ne' (by simpa [h] using hg.symm)
 have hroot :aeval w g=0:= by simpa only [g,aeval_def,eval₂_map,evalRoot] using hw
 have hm:=minpoly.dvd F w hroot
 have hs :=expanded_separable x f hp hdisc
 refine ⟨hs.of_dvd hm,?_,?_,?_⟩
 · rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral w)]
   exact (natDegree_le_of_dvd hm hn).trans_lt (hg.symm ▸ hdeg)
 · refine rootIntegral g (fun i=> by simpa only [g,coeff_map] using expand_le x (f.coeff i)) ?_ w ?_
   · dsimp only [g]
     rw [leadingCoeff_map_of_injective (expand_injective x)]
     exact expand_unit hl
   · apply (Simple w).val.injective
     change (Simple w).val (aeval (point w) g)=(Simple w).val 0
     rw [← aeval_algHom_apply (Simple w).val,map_zero]
     exact hroot
 · simpa only [g,derivative_map,aeval_def,eval₂_map,evalRoot] using hs.aeval_derivative_ne_zero hroot
end
end qymFiQe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qymFiQe
noncomputable section
open Polynomial qps5rle
open P5 (p)
open scoped WithZero
def c1 :Prop := ∀ (D:Derivation ℤ F F),coefficientwise D →
  ∀ w:Roots,IsSeparable F w → ∀ a :Simple w,
    ∃ c:Fin p→smallConstants D w,a=btY D w c
def c2 :Prop := ∀ (D:Derivation ℤ F F),coefficientwise D →
  ∀ w:Roots,IsSeparable F w→Module.finrank F (Simple w)<p →
    ∀ V:ValuationSubring (Simple w),
      (∀ a :IntegerRing,algebraMap IntegerRing (Simple w) a∈V) →
      ∀ c:Fin p→smallConstants D w,btY D w c∈V →
        ∀ i:Fin p,(c i:Simple w)∈V
private theorem seed_integral:seed∈IntegerRing:= by
 apply (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero SeedSeries (D:=0)).mpr
 intro i hi
 have hn:i≠0:=ne_of_lt hi
 simp [seed,LaurentSeries.algebraMap_apply,HahnSeries.C_apply,hn]
private theorem integral_derivative (span:c1) (coeffs :c2)
  (D:Derivation ℤ F F) (hD:coefficientwise D) (w:Roots)
  (hs :IsSeparable F w) (hd:Module.finrank F (Simple w)<p)
  (D' : Derivation ℤ (Simple w) (Simple w))
  (he : ∀ a,D' (algebraMap F (Simple w) a)=algebraMap F (Simple w) (D a))
  (a :Simple w) (ha :IsIntegral IntegerRing a) :IsIntegral IntegerRing (D' a) := by
 obtain ⟨c,hc⟩:=span D hD w hs a
 have hseed :D' (algebraMap F (Simple w) seed)=1 := by rw [he,derive_seed hD,map_one]
 apply integralOfValuations w
 intro V hV
 have haV:=integral_mem V hV ha
 have hcoeff :=coeffs D hD w hs hd V hV c (hc ▸ haV)
 have hz :algebraMap F (Simple w) seed∈V:=hV ⟨seed,seed_integral⟩
 rw [hc,btY,map_sum]
 apply V.toSubring.sum_mem
 intro i _
 rw [D'.leibniz,D'.leibniz_pow,hseed,killConstants D w D' he (c i)]
 simp only [smul_eq_mul,nsmul_eq_mul,mul_zero,mul_one,add_zero]
 exact V.toSubring.mul_mem (hcoeff i)
  (V.toSubring.mul_mem (natCast_mem V.toSubring _) (V.toSubring.pow_mem hz _))
theorem of_children (span:c1) (coeffs :c2) :qps5rle.c3:= by
 intro x f hp hd hl hdisc w hw
 obtain ⟨hs,hdim,hi,hn⟩:=root_data x f hp hd hl hdisc w hw
 obtain ⟨D,hD⟩:=base_derivation
 obtain ⟨D',hD'⟩:=extendSimple D w hs
 let e :SeedSeries[X] →+* Simple w:=(algebraMap F (Simple w)).comp (physExpansion x)
 let j:Simple w →+* Roots :=(Simple w).val.toRingHom
 let ev (q:SeedSeries[X][X]) :=q.eval₂ e (point w)
 have hmap (q:SeedSeries[X][X]) :j (ev q)=evalRoot x q w:= by
   exact hom_eval₂ q e j (point w)
 have hroot :ev f=0:=j.injective (by rw [hmap,hw,map_zero])
 have hsep:ev f.derivative≠0:= fun h=>hn (by rw [← hmap,h,map_zero])
 have hchain:ev (seedDerivative f)+ev f.derivative*D' (point w)=0:= by
   have h:=aNu D' e (point w) f (seedDerivative f) (fun i=> by
     simp only [e,RingHom.comp_apply,hD',derive_coeff hD])
   change D' (ev f)=ev (seedDerivative f)+ev f.derivative*D' (point w) at h
   simpa only [hroot,map_zero] using h.symm
 have hquot:D' (point w) = -(ev (seedDerivative f)/ev f.derivative) := by
   rw [← neg_div,eq_div_iff hsep,mul_comm]
   exact eq_neg_of_add_eq_zero_right hchain
 have hI:=integral_derivative span coeffs D hD w hs hdim D' hD' (point w) hi
 rw [hquot] at hI
 have hJ:IsIntegral IntegerRing (j (-(ev (seedDerivative f)/ev f.derivative))) :=
   hI.algebraMap
 simpa only [map_neg,map_div₀,hmap] using hJ
end
end qymFiQe
end
