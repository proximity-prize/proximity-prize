import Mathlib.RingTheory.Ideal.Norm.RelNorm
import ProximityPrize.SubmissionLower.Zpj8DDa
set_option Elab.async false
open _root_ renaming Algebra.norm → zXP, Function.Surjective → zpX, Ideal.span_singleton_le_iff_mem → zvl, IsScalarTower.algebraMap_apply → zG3
namespace qXARP7c
noncomputable section
open Finset IsDedekindDomain WithZero
open scoped WithZero
open E7 (KB)
open private cu7 from ProximityPrize.SubmissionLower.A2
variable {H J:Type} [Field H] [Field J] [Algebra H J]
variable (v :Valuation H ℤᵐ⁰)
local notation "O" => v.valuationSubring
local notation "N" => integralClosure O J
private theorem nontrivial_val {D:Type} [Field D] (u:Valuation D ℤᵐ⁰)
   (hu:zpX u) :u.IsNontrivial:= by
 obtain ⟨a,ha⟩:=hu (exp (-1 :ℤ))
 refine (u.isNontrivial_iff_exists_lt_one).mpr ⟨a,u.ne_zero_iff.mp ?_,?_⟩
 · rw [ha]; exact exp_ne_zero
 · rw [ha,← exp_zero,exp_lt_exp]; decide
private def RG (u:Valuation J ℤᵐ⁰) (h : ∀ x :O,u (algebraMap O J x)≤1) :
  N →+* u.valuationSubring := by
 let j:O →+* u.valuationSubring :=
  (algebraMap O J).codRestrict u.valuationSubring.toSubring h
 let:Algebra O u.valuationSubring :=j.toAlgebra
 let:IsScalarTower O u.valuationSubring J:=IsScalarTower.of_algebraMap_eq fun _=>rfl
 exact (algebraMap N J).codRestrict u.valuationSubring.toSubring fun b =>
  (Valuation.integer.integers u).isIntegral_iff_v_le_one.mp (IsIntegral.tower_top b.property)
private def center [IsDedekindDomain N] (u:Valuation J ℤᵐ⁰)
  (h : ∀ x :O,u (algebraMap O J x)≤1) {π:O}
  (hπ: (π:H)≠0) (hπu:u (algebraMap O J π)<1) :HeightOneSpectrum N := by
 let p:=(IsLocalRing.maximalIdeal u.valuationSubring).comap (RG v u h)
 have hprime : (IsLocalRing.maximalIdeal u.valuationSubring).IsPrime :=inferInstance
 refine ⟨p,hprime.comap _,?_⟩
 intro hp
 have hm:algebraMap O N π∈p:=u.mem_maximalIdeal_iff.mpr (by
  change u (algebraMap N J (algebraMap O N π))<1
  rwa [← zG3 O N J])
 rw [hp,Ideal.mem_bot] at hm
 apply hπ
 apply (algebraMap H J).injective
 change algebraMap H J (algebraMap O H π)=algebraMap H J 0
 rw [← zG3 O H J,zG3 O N J,hm,
  map_zero,map_zero]
private theorem center_mem [IsDedekindDomain N] (u:Valuation J ℤᵐ⁰)
  (h : ∀ x :O,u (algebraMap O J x)≤1) {π:O}
  (hπ: (π:H)≠0) (hπu:u (algebraMap O J π)<1) (a :N) :
  a∈(center v u h hπ hπu).asIdeal↔u (algebraMap N J a)<1 := by
 change RG v u h a∈IsLocalRing.maximalIdeal u.valuationSubring↔_
 exact u.mem_maximalIdeal_iff (a :=RG v u h a)
private theorem center_val [IsDedekindDomain N] [IsFractionRing N J] (u:Valuation J ℤᵐ⁰)
   (hu:zpX u) (h : ∀ x :O,u (algebraMap O J x)≤1) {π:O}
   (hπ: (π:H)≠0) (hπu:u (algebraMap O J π)<1) :
   (center v u h hπ hπu).valuation J=u:= by
 let P:=center v u h hπ hπu
 have hle : (P.valuation J).valuationSubring≤u.valuationSubring := by
   intro x hx
   obtain ⟨a,d,he⟩:=P.exists_primeCompl_mul_eq_of_integer x hx
   have hd:u (algebraMap N J d)=1 :=le_antisymm (RG v u h d).property
     (le_of_not_gt fun hg=>d.property ((center_mem v u h hπ hπu d).mpr hg))
   change u x≤1
   have he' := congrArg (fun z :J=>u z) he
   rw [map_mul,hd,mul_one] at he'
   exact he'.le.trans (RG v u h a).property
 exact cu7 (P.valuation_surjective J) hu <|
   (Valuation.isEquiv_iff_valuationSubring _ _).mpr (ValuationSubring.eq_of_le_of_ne_top _ hle
     (fun he=>((u.valuationSubring_eq_top_iff).mp he) (nontrivial_val u hu)))
theorem integral_norm_order [Module.Finite H J] [Algebra.IsSeparable H J]
    (hv :zpX v) {ι:Type*} (s :Finset ι)
    (u:ι→Valuation J ℤᵐ⁰) (e :ι→ℕ)
    (hu : ∀ i∈s,zpX (u i))
    (he : ∀ i∈s,0<e i)
    (hbase : ∀ i∈s,∀ x :H,u i (algebraMap H J x)=v x^e i)
    (hinj:Set.InjOn u s) (b:J) (hb:b≠0) (hbI:IsIntegral O b) :
    ∑ i∈s,KB (u i) b≤KB v (zXP H b) := by
  classical
  let:v.IsNontrivial:=nontrivial_val v hv
  let:v.IsRankOneDiscrete :=Valuation.IsRankOneDiscrete.mk' v
  let:IsDedekindDomain N :=integralClosure.isDedekindDomain O H J
  let:IsFractionRing N J:=IsIntegralClosure.isFractionRing_of_finite_extension O H J N
  let:Module.Finite O N :=IsIntegralClosure.finite O H J N
  let:Module.IsTorsionFree O N :=IsIntegralClosure.isTorsionFree O J
  let π:=(Classical.choice (inferInstance :Nonempty (Valuation.Uniformizer v)))
  have hπ:v (π.1 :H)=exp (-1 :ℤ) := by
    rw [π.2.val,Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hv]
    rfl
  let p:=IsLocalRing.maximalIdeal O
  have hO (i:s) (x :O) :u i (algebraMap O J x)≤1 := by
    rw [zG3 O H J,hbase i i.property]
    exact pow_le_one₀ zero_le x.property
  have huπ (i:s) :u i (algebraMap O J π.1)<1 := by
    rw [zG3 O H J,hbase i i.property,show algebraMap O H π.1=π.1.val from rfl,
      hπ,← exp_nsmul,← exp_zero,exp_lt_exp]
    simpa using he i i.property
  let P (i:s) :HeightOneSpectrum N :=center v (u i) (hO i) π.ne_zero (huπ i)
  have hpv (i:s) : (P i).valuation J=u i :=
    center_val v _ (hu i i.property) (hO i) π.ne_zero (huπ i)
  let d (i:s) :=KB (u i) b
  let y :N :=⟨b,hbI⟩
  have hy (i:s) :y∈(P i).asIdeal^d i:= by
    rw [← (P i).intValuation_le_pow_iff_mem,← (P i).valuation_of_algebraMap (K:=J),hpv]
    change u i b≤exp (-(d i:ℤ))
    have hlog:log (u i b)≤0:= by
      rw [← log_one]
      exact (log_le_log ((u i).ne_zero_iff.mpr hb) one_ne_zero).2
        (RG v (u i) (hO i) y).property
    rw [← exp_log ((u i).ne_zero_iff.mpr hb),exp_le_exp]
    dsimp [d,KB]
    omega
  have hprod:Ideal.span {y} ≤ ∏ i:s,(P i).asIdeal^d i:= by
    rw [← HeightOneSpectrum.inf_pow_eq_prod _ _ _ (fun i _ j _ hij=> by
      intro hP
      exact hij (Subtype.ext (hinj i.property j.property
        ((hpv i).symm.trans ((congrArg (fun x :HeightOneSpectrum N=>x.valuation J) hP).trans (hpv j))))))]
    apply Finset.le_inf
    exact fun i _=>(zvl _).mpr (hy i)
  have hnorm (i:s) :Ideal.relNorm O (P i).asIdeal≤p:= by
    refine (Ideal.relNorm_le_comap O _).trans ?_
    intro a ha
    have haa :=(center_mem v (u i) (hO i) π.ne_zero (huπ i) (algebraMap O N a)).mp ha
    rw [← zG3 O N J,zG3 O H J,
      hbase i i.property] at haa
    exact v.mem_maximalIdeal_iff.mpr (lt_of_not_ge fun h=>(not_le_of_gt haa) (one_le_pow₀ h))
  have hN :=Ideal.relNorm_mono O hprod
  rw [Ideal.relNorm_singleton,map_prod] at hN
  have hN' : Ideal.span {Algebra.intNorm O N y} ≤ p ^ ∑ i:s,d i:= by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact hN.trans (Finset.prod_le_prod fun i _=> by rw [map_pow]; gcongr; exact hnorm i)
  change _≤(IsLocalRing.maximalIdeal O)^_ at hN'
  rw [π.2.is_generator,Ideal.span_singleton_pow] at hN'
  obtain ⟨t,ht⟩:=Ideal.mem_span_singleton.mp
    ((zvl _).mp hN')
  have hval :=congrArg (fun c:O=>v (algebraMap O H c)) ht
  rw [Algebra.algebraMap_intNorm (L:=J),map_mul,map_pow,map_mul,map_pow] at hval
  change v (zXP H b)=v (π.1 :H)^(∑ i:s,d i)*v (t:H) at hval
  have hle :v (zXP H b)≤exp (-((∑ i:s,d i:ℕ) :ℤ)) := by
    rw [hval,hπ,← exp_nsmul]
    have hmul (a :ℤᵐ⁰) :a*v (t:H)≤a := by
      simpa only [mul_one] using (mul_le_mul' (le_refl a) t.property)
    simpa using hmul (exp ((∑ i:s,d i)•(-1 :ℤ)))
  have hlog:=(log_le_iff_le_exp (v.ne_zero_iff.mpr (Algebra.norm_ne_zero_iff.mpr hb))).mpr hle
  rw [← Finset.sum_attach s]
  change (∑ i:s,d i)≤(-log (v (zXP H b))).toNat
  omega
end
end qXARP7c
