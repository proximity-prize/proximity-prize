import Mathlib.RingTheory.LaurentSeries
import ProximityPrize.SubmissionLower.ZzQsYjc
import ProximityPrize.SubmissionLower.Z3EWiUc
import ProximityPrize.SubmissionLower.ZFFuWqa
import ProximityPrize.SubmissionLower.ZGlW6Oc
import ProximityPrize.SubmissionLower.ZgdIx1d
set_option Elab.async false
open _root_ renaming PowerSeries → zpm, PowerSeries.X → zWv, PowerSeries.constantCoeff → zbO, PowerSeries.ext → zub
set_option autoImplicit true
section
namespace quwKLBd
noncomputable section
open PowerSeries
variable {k A:Type} [Field k] [CommRing A] [IsDomain A]
 (c:k →+* A) (r :A →+* k) (hr : ∀ b,r (c b)=b)
 (π:A) (hp:π≠0) (hrπ:r π=0)
 (hd : ∀ a,π∣a - c (r a))
private def tail (a :A) :A:=(hd a).choose
omit [IsDomain A] in
private theorem mul_tail (a :A) :π*tail c r π hd a=a - c (r a) :=
 (hd a).choose_spec.symm
private def shift:A →+ A where
 toFun:=tail c r π hd
 map_zero' := by
   apply mul_left_cancel₀ hp
   rw [mul_tail,map_zero,map_zero,sub_zero,mul_zero]
 map_add' a b:= by
   apply mul_left_cancel₀ hp
   rw [mul_tail,mul_add,mul_tail,mul_tail,map_add r,map_add c]
   ring
include hrπ in
private theorem shift_mul (a :A) :shift c r π hp hd (π*a)=a := by
 apply mul_left_cancel₀ hp
 change π*tail c r π hd (π*a)= _
 rw [mul_tail,map_mul,hrπ,zero_mul,map_zero,sub_zero]
include hr in
private theorem shift_const_mul (b:k) (a :A) :
   shift c r π hp hd (c b*a)=c b*shift c r π hp hd a := by
 apply mul_left_cancel₀ hp
 change π*tail c r π hd (c b*a)=π*(c b*tail c r π hd a)
 rw [mul_tail,map_mul r,hr,map_mul c,mul_left_comm,mul_tail,mul_sub]
private def digits :ℕ→A →+ k
 | 0=>r.toAddMonoidHom
 | n+1=>(digits n).comp (shift c r π hp hd)
private def expansions :A →+ zpm k where
 toFun a :=PowerSeries.mk fun n=>digits c r π hp hd n a
 map_zero' := zub fun n=> by rw [coeff_mk,map_zero,map_zero]
 map_add' a b:=zub fun n=> by rw [coeff_mk,map_add,map_add,coeff_mk,coeff_mk]
local notation "F" => expansions c r π hp hd
private theorem coeff_expansions (n:ℕ) (a :A) :
   coeff n (F a)=digits c r π hp hd n a :=
 coeff_mk n (fun m=>digits c r π hp hd m a)
private theorem res_expansions (a :A) :constantCoeff (F a)=r a := by
 rw [← coeff_zero_eq_constantCoeff_apply,coeff_expansions]
 rfl
private theorem coeff_succ_expansions (n:ℕ) (a :A) :
   coeff (n+1) (F a)=coeff n (F (shift c r π hp hd a)) := by
 rw [coeff_expansions,coeff_expansions]
 rfl
include hrπ in
private theorem expansions_mul_pi (a :A) :F (π*a)=zWv*F a := by
 apply zub
 intro n
 cases n with
 | zero=>rw [coeff_zero_X_mul,coeff_zero_eq_constantCoeff_apply,res_expansions,map_mul,
     hrπ,zero_mul]
 | succ n=>rw [coeff_succ_expansions,shift_mul _ _ _ _ hrπ,coeff_succ_X_mul]
include hr in
private theorem coeff_const_mul (b:k) (n:ℕ) (a :A) :
   coeff n (F (c b*a))=b*coeff n (F a) := by
 induction n generalizing a with
 | zero=>simp only [coeff_zero_eq_constantCoeff_apply,res_expansions,map_mul,hr]
 | succ n ih=>rw [coeff_succ_expansions,coeff_succ_expansions,shift_const_mul _ _ hr,ih]
include hr in
private theorem expansions_const_mul (b:k) (a :A) :F (c b*a)=C b*F a :=
 zub fun n=>(coeff_const_mul c r hr π hp hd b n a).trans (coeff_C_mul n (F a) b).symm
include hr in
private theorem expansions_const (b:k) :F (c b)=C b:= by
 have hz :shift c r π hp hd (c b)=0:= by
   apply mul_left_cancel₀ hp
   change π*tail c r π hd (c b)=π*0
   rw [mul_tail,hr,sub_self,mul_zero]
 apply zub
 intro n
 cases n with
 | zero=>rw [coeff_zero_C,coeff_zero_eq_constantCoeff_apply,res_expansions,hr]
 | succ n=>rw [coeff_succ_expansions,hz,map_zero,map_zero,coeff_succ_C]
private theorem decompose (a :A) :a=π*shift c r π hp hd a+c (r a) := by
 change a=π*tail c r π hd a+c (r a)
 rw [mul_tail,sub_add_cancel]
include hr hrπ in
private theorem expansions_mul (a b:A) :F (a*b)=F a*F b:= by
 have hstep (x y :A) :F (x*y) =
     zWv*F (shift c r π hp hd x*y)+C (r x)*F y := by
   conv_lhs=>rw [decompose c r π hp hd x,add_mul,mul_assoc]
   rw [map_add,expansions_mul_pi _ _ _ _ hrπ,expansions_const_mul _ _ hr]
 have hsingle (x :A) :F x=zWv*F (shift c r π hp hd x)+C (r x) := by
   conv_lhs=>rw [decompose c r π hp hd x]
   rw [map_add,expansions_mul_pi _ _ _ _ hrπ,expansions_const _ _ hr]
 apply zub
 intro n
 induction n generalizing a b with
 | zero=>simp only [coeff_zero_eq_constantCoeff_apply,map_mul,res_expansions]
 | succ n ih =>
   rw [hstep,hsingle a,add_mul,mul_assoc]
   simp only [map_add,coeff_succ_X_mul,ih]
include hr hp hrπ hd in
theorem exists_expansion :
   ∃ f :A →+* zpm k,
     (∀ b,f (c b)=C b)∧(∀ a,constantCoeff (f a)=r a)∧f π=PowerSeries.X:= by
 let f :A →+* zpm k :=
   { F with
     map_one' := by
       change F 1=1
       rw [← c.map_one,expansions_const _ _ hr,map_one]
     map_mul' := expansions_mul c r hr π hp hrπ hd }
 refine ⟨f,expansions_const c r hr π hp hd,res_expansions c r π hp hd,?_⟩
 change F π=zWv
 have h1 :F 1=1 :=f.map_one
 simpa only [mul_one,h1] using expansions_mul_pi c r π hp hrπ hd 1
end
end quwKLBd
end
set_option backward.isDefEq.respectTransparency false
namespace quwKLBd
noncomputable section
open E7 (CurvePlace)
open scoped WithZero
open WithZero
open private fWV fWT from ProximityPrize.SubmissionLower.ZFFuWqa
variable {k E :Type} [Field k] [IsAlgClosed k] [Field E] [Algebra k E]
 (w:CurvePlace k E)
local notation "V" => w.value.valuationSubring
private theorem small {z :ℤᵐ⁰} (hz :z<1) :z≤exp (-1 :ℤ) := by
 apply (lt_mul_exp_iff_le (y :=exp (-1 :ℤ)) exp_ne_zero).mp
 simpa only [← exp_add,neg_add_cancel,exp_zero] using hz
omit [IsAlgClosed k] in
private theorem const_le (b:k) :w.value (algebraMap k E b)≤1 := by
 by_cases hb:b=0
 · simp [hb]
 · exact (w.on_constants b hb).le
private def constants :k →+* V :=
 (algebraMap k E).codRestrict w.value.valuationSubring.toSubring (const_le w)
private theorem res_surjective (π:V) (hπ:w.value (π:E)=exp (-1 :ℤ))
   {u:E} (hu:IsTranscendenceBasis k (fun _:Unit=>u)) :
   Function.Surjective ((IsLocalRing.residue V).comp (constants w)) := by
 let res :=IsLocalRing.residue V
 let c:=constants w
 let:Algebra k (IsLocalRing.ResidueField V) :=(res.comp c).toAlgebra
 have hne : (π:E)≠0:=w.value.ne_zero_iff.mp (hπ ▸ exp_ne_zero)
 have hzero :res π=0:=(IsLocalRing.residue_eq_zero_iff _).mpr
   (w.value.mem_maximalIdeal_iff.mpr (hπ ▸ (exp_lt_one_iff.mpr (by decide : (-1 :ℤ)<0))))
 intro x
 obtain ⟨a,rfl⟩:=IsLocalRing.residue_surjective (R:=V) x
 obtain ⟨b,hb⟩:=fWT (fWV (RingHom.id E) V c
   (fun _=>rfl) hu hne π rfl hzero (a :E) a rfl)
 exact ⟨b,hb.symm⟩
private theorem exists_integral_expansion {u:E}
   (hu:IsTranscendenceBasis k (fun _:Unit=>u)) :
   ∃ f :V →+* zpm k,
     (∀ b,f (constants w b)=PowerSeries.C b) ∧
     (∀ a,zbO (f a)=0↔w.value (a :E)<1) ∧
     (∀ a,(Valued.v :Valuation (LaurentSeries k) ℤᵐ⁰) (f a :LaurentSeries k)=w.value (a :E)) := by
 obtain ⟨p,hp⟩:=w.normalized (exp (-1 :ℤ))
 let π:V:=⟨p,by
   change w.value p≤1
   rw [hp]
   exact exp_le_one_iff.mpr (by decide)⟩
 have hπ:w.value (π:E)=exp (-1 :ℤ) :=hp
 have hπ' : (π:E)≠0:=w.value.ne_zero_iff.mp (hπ ▸ exp_ne_zero)
 let res :=IsLocalRing.residue V
 let c:=constants w
 let e :=RingEquiv.ofBijective (res.comp c) ⟨(res.comp c).injective,res_surjective w π hπ hu⟩
 let r :V →+* k :=e.symm.toRingHom.comp res
 have hrc (b:k) :r (c b)=b:=e.symm_apply_apply b
 have hr (a :V) :r a=0↔w.value (a :E)<1 :=
   (map_eq_zero_iff _ e.symm.injective).trans ((IsLocalRing.residue_eq_zero_iff _).trans
     w.value.mem_maximalIdeal_iff)
 have hrπ:r π=0:=(hr π).mpr (hπ ▸ exp_lt_one_iff.mpr (by decide : (-1 :ℤ)<0))
 have hd (a :V) :π∣a - c (r a) := by
   let b:=a - c (r a)
   have hb:w.value (b:E)<1 :=(hr b).mp (by simp only [b,map_sub,hrc,sub_self])
   let q:V:=⟨(b:E)/(π:E),by
     change w.value ((b:E)/(π:E))≤1
     rw [map_div₀,hπ,div_le_one₀ WithZero.exp_pos]
     exact small hb⟩
   exact ⟨q,Subtype.ext (by
     change (b:E)=(π:E)*((b:E)/(π:E))
     rw [mul_comm,div_mul_cancel₀ _ hπ'])⟩
 obtain ⟨f,hf,hfr,hfp⟩:=exists_expansion c r hrc π
   (fun h=>hπ' (congrArg Subtype.val h)) hrπ hd
 have hker (a :V) :zbO (f a)=0↔w.value (a :E)<1 := by
   rw [hfr,hr]
 refine ⟨f,hf,hker,?_⟩
 let l:=HahnSeries.ofPowerSeries ℤ k
 let v :=(Valued.v :Valuation (LaurentSeries k) ℤᵐ⁰)
 have hunit (a :V) (ha :w.value (a :E)=1) :v (l (f a))=1 := by
   have hcc:zbO (f a)≠0:= fun hn=>((hker a).mp hn).ne ha
   apply le_antisymm ((LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨f a,rfl⟩)
   apply le_of_not_gt
   intro hlt
   have hzero :=(LaurentSeries.intValuation_le_iff_coeff_lt_eq_zero k (d:=1) (f a)).mp
     (small hlt) 0 (by decide)
   exact hcc (by simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero)
 intro a
 by_cases ha :a=0
 · simp [ha]
 have hz :w.value (a :E)≠0:=w.value.ne_zero_iff.mpr (fun h=>ha (Subtype.ext h))
 have hn:0 ≤ -log (w.value (a :E)) :=
   neg_nonneg.mpr (log_le_iff_le_exp hz |>.mpr (by simpa only [exp_zero] using (show w.value (a :E)≤1 from a.property)))
 obtain ⟨n,hn⟩:=Int.eq_ofNat_of_zero_le hn
 have hval :w.value (a :E)=exp (-(n:ℤ)) := by
   rw [← hn,neg_neg,exp_log hz]
 have hpow:w.value ((π:E)^n)=exp (-(n:ℤ)) := by
   rw [map_pow,hπ,← exp_nsmul,nsmul_eq_mul,mul_neg,mul_one]
 let q:E :=(a :E)/(π:E)^n
 have hq:w.value q=1 := by
   rw [show q= _ from rfl,map_div₀,hval,hpow,div_self exp_ne_zero]
 let b:V:=⟨q,hq.le⟩
 have he :a=π^n*b:=Subtype.ext (by
   change (a :E)=(π:E)^n*((a :E)/(π:E)^n)
   rw [mul_comm,div_mul_cancel₀ _ (pow_ne_zero _ hπ')])
 change v (l (f a))=w.value (a :E)
 rw [hval,he,map_mul,map_pow,hfp,map_mul,map_pow,map_mul,hunit b hq,mul_one]
 exact LaurentSeries.valuation_X_pow k n
theorem exists_laurent {u:E} (hu:IsTranscendenceBasis k (fun _:Unit=>u)) :
   ∃ (f :V →+* zpm k) (g:E →ₐ[k] LaurentSeries k),
     (∀ a,(f a :LaurentSeries k)=g (a :E)) ∧
     (∀ b,f (constants w b)=PowerSeries.C b) ∧
     (∀ a,zbO (f a)=0↔w.value (a :E)<1) ∧
     (∀ a,(Valued.v :Valuation (LaurentSeries k) ℤᵐ⁰) (g a)=w.value a) := by
 obtain ⟨f,hf,hker,hv⟩:=exists_integral_expansion w hu
 let l:=(HahnSeries.ofPowerSeries ℤ k).comp f
 have hl:Function.Injective l:= by
   apply (injective_iff_map_eq_zero' _).mpr
   intro a
   constructor
   · intro ha
     apply Subtype.ext
     have hval :=(hv a).symm
     change w.value (a :E)=(Valued.v :Valuation (LaurentSeries k) ℤᵐ⁰) (l a) at hval
     rw [ha,map_zero] at hval
     exact w.value.zero_iff.mp hval
   · rintro rfl
     exact l.map_zero
 let g:E →+* LaurentSeries k :=IsFractionRing.lift hl
 have hg (a :V) :g (a :E)=l a :=
   IsFractionRing.lift_algebraMap hl a
 have hconst (b:k) :g (algebraMap k E b)=algebraMap k (LaurentSeries k) b:= by
   rw [← show (constants w b:E)=algebraMap k E b from rfl,hg]
   change ((f (constants w b) :zpm k) :LaurentSeries k)= _
   rw [hf,PowerSeries.coe_C,LaurentSeries.algebraMap_apply]
 refine ⟨f,⟨g,hconst⟩,fun a=>(hg a).symm,hf,hker,?_⟩
 intro a
 obtain ⟨b,c,_,rfl⟩:=IsFractionRing.div_surjective V a
 change (Valued.v :Valuation (LaurentSeries k) ℤᵐ⁰) (g ((b:E)/(c:E))) =
   w.value ((b:E)/(c:E))
 rw [map_div₀,map_div₀,map_div₀,hg,hg]
 simp only [l,RingHom.comp_apply,hv]
end
end quwKLBd
