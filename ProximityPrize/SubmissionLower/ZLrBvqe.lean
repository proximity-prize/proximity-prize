import ProximityPrize.SubmissionLower.Zeo5Ibd
import ProximityPrize.SubmissionLower.ZYcqQEc
import ProximityPrize.SubmissionLower.ZqYLuMe
set_option Elab.async false
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace qMskYpa
noncomputable section
open Polynomial KaehlerDifferential TensorProduct
open scoped TensorProduct nonZeroDivisors
open cu (L)
open P5 (K p)
open qNu3xvc
open qypA4Sc (ajm)
open private avoid from ProximityPrize.SubmissionLower.ZYcqQEc
open private coeff_injective fXW ordinate_degree from ProximityPrize.SubmissionLower.Zeo5Ibd
open private separable_of_small_root from ProximityPrize.SubmissionLower.Z3R7Dac
variable {E :Type} [Field E] [Algebra L E]
local instance (A:Equation E) :Algebra (RatFunc E) (EC A) :=
 (IsFractionRing.lift (K:=RatFunc E) (coeff_injective A)).toAlgebra
local instance (A:Equation E) :IsScalarTower E[X] (RatFunc E) (EC A) :=
 IsScalarTower.of_algebraMap_eq fun q=>(fXW A q).symm
local instance (A:Equation E) :IsScalarTower E (RatFunc E) (EC A) :=
 IsScalarTower.of_algebraMap_eq fun c=> by
  change seed A c=algebraMap (RatFunc E) (EC A) (RatFunc.C c)
  rw [← RatFunc.algebraMap_C,fXW]
  rfl
omit [Algebra L E] in
private theorem physical_transcendental (A:Equation E) :Transcendental E (amm A) := by
 apply transcendental_iff_injective.mpr
 have h: (aeval (amm A) :E[X] →ₐ[E] EC A).toRingHom=ajm A:= by
   apply Polynomial.ringHom_ext
   · intro c
     simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,aeval_C]
     rfl
   · simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,aeval_X]
     rfl
 change Function.Injective ((aeval (amm A) :E[X] →ₐ[E] EC A).toRingHom)
 rw [h]
 exact coeff_injective A
private theorem physical_separable (A:Equation E) (hp:A.d<p)
  [Module.Finite (RatFunc E) (EC A)]
  (hr :Module.finrank (RatFunc E) (EC A)≤A.d) :
  Algebra.IsSeparable (RatFunc E) (EC A) := by
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
 let:CharP (RatFunc E) p:=charP_of_injective_ringHom (RatFunc.C:E →+* RatFunc E).injective p
 refine ⟨fun z=>separable_of_small_root (minpoly.ne_zero (IsIntegral.of_finite (RatFunc E) z))
  ((minpoly.natDegree_le z).trans_lt (hr.trans_lt hp)) (minpoly.aeval _ _)⟩
private theorem differential (A:Equation E) (hp:A.d<p)
  [Module.Finite (RatFunc E) (EC A)]
  (hr :Module.finrank (RatFunc E) (EC A)≤A.d) :
  ∃ e :Ω[EC A⁄E] ≃ₗ[EC A] EC A,e (D E _ (amm A))=1 := by
 let F:=EC A
 let:Algebra.FormallyEtale (RatFunc E) F :=
  (Algebra.FormallyEtale.iff_isSeparable (RatFunc E) F).mpr (physical_separable A hp hr)
 let:Algebra.FormallyEtale E[X] (RatFunc E) :=
  Algebra.FormallyEtale.of_isLocalization E[X]⁰
 let:Algebra.FormallyEtale E[X] F:=Algebra.FormallyEtale.comp E[X] (RatFunc E) F
 let e :=tensorKaehlerEquivOfFormallyEtale E E[X] F
 let f :=AlgebraTensorModule.congr (LinearEquiv.refl F F) (polynomialEquiv E)
 refine ⟨e.symm.trans (f.trans (AlgebraTensorModule.rid E[X] F F)),?_⟩
 change (AlgebraTensorModule.rid E[X] F F) (f (e.symm (D E F
  (algebraMap E[X] F Polynomial.X))))=1
 rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
 dsimp only [f]
 rw [AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,polynomialEquiv_D,derivative_X,
  AlgebraTensorModule.rid_tmul,Algebra.smul_def,map_one,one_mul]
theorem separating:qTFhFCb.c1 := by
  intro E _ _ A hp H
  let F:=EC A
  let X₀:=amm A
  let U (a :L) :=constant A a*X₀+H
  obtain ⟨hfin,hr⟩:=ordinate_degree A
  let:=hfin
  obtain ⟨δ,hδ⟩:=differential A hp hr
  have hU (a :L) :δ (D E F (U a))=constant A a+δ (D E F H) := by
    have hc:D E F (constant A a)=0:=(D E F).map_algebraMap _
    simp only [U,map_add,Derivation.leibniz,hc,smul_zero,add_zero,map_smul,
      show δ (D E F X₀)=1 from hδ,smul_eq_mul,mul_one]
  let k :=algebraicClosure E F
  have hbad: ({a :L | U a∈k} : Set L).Subsingleton := by
    intro a ha b hb
    by_contra h
    have hc:constant A a - constant A b≠0 :=
      sub_ne_zero.mpr (((seed A).comp (algebraMap L E)).injective.ne h)
    have hmem (a :L) :constant A a∈k :=k.algebraMap_mem _
    have hz :=k.div_mem (k.sub_mem ha hb) (k.sub_mem (hmem a) (hmem b))
    change (U a-U b)/(constant A a - constant A b)∈k at hz
    rw [show U a-U b=X₀*(constant A a - constant A b) by dsimp [U]; ring,
      mul_div_cancel_right₀ _ hc] at hz
    exact physical_transcendental A (mem_algebraicClosure_iff.mp hz)
  have hbad' : ({a :L | δ (D E F (U a))=0} : Set L).Subsingleton := by
    intro a ha b hb
    change δ (D E F (U a))=0 at ha
    change δ (D E F (U b))=0 at hb
    rw [hU] at ha hb
    exact ((seed A).comp (algebraMap L E)).injective (add_right_cancel (ha.trans hb.symm))
  obtain ⟨a,ha,ha'⟩:=avoid (fun _:Unit => {a | U a∈k}) (fun _=>hbad) _ hbad'.finite
  have htr :Transcendental E (U a) := fun h=>ha' () (mem_algebraicClosure_iff.mpr h)
  let B:=IntermediateField.adjoin E {U a}
  have hB:Module.Finite B F:=FunctionField.finiteDimensional_of_adjoin_transcendental htr
  let:=hB
  have hsep:Algebra.IsSeparable B F:= by
    let f :=KaehlerDifferential.map E B F F
    have hsur :=KaehlerDifferential.map_surjective E B F
    have hzero :f (D E F (U a))=0:= by
      rw [KaehlerDifferential.map_D]
      exact (D B F).map_algebraMap ⟨U a,IntermediateField.mem_adjoin_simple_self E _⟩
    let:Algebra.FormallyUnramified B F:=⟨(subsingleton_iff_forall_eq 0).mpr fun z=> by
      obtain ⟨q,rfl⟩:=hsur z
      have he :q=(δ q/δ (D E F (U a)))•D E F (U a) := by
        apply δ.injective
        rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ ha]
      change f q=0
      rw [he,map_smul,hzero,smul_zero]⟩
    exact Algebra.FormallyUnramified.isSeparable B F
  let e :=RatFunc.algEquivOfTranscendental (U a) htr
  let m:=(B.val.comp e.toAlgHom).toRingHom
  let:Algebra (RatFunc E) F:=m.toAlgebra
  refine ⟨a,m,fun c=>(B.val.comp e.toAlgHom).commutes c,?_,?_,?_⟩
  · exact RatFunc.algEquivOfTranscendental_X (U a) htr
  · refine ((Module.finBasis B F).mapCoeffs e.symm.toRingEquiv ?_).finiteDimensional_of_finite
    intro c z
    rw [Algebra.smul_def,Algebra.smul_def]
    change (e (e.symm c) :F)*z=(c:F)*z
    rw [e.apply_symm_apply]
  · exact Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F)
      (RingHom.ext fun c=> by
        change (e (e.symm c) :F)=c.val
        rw [e.apply_symm_apply])
end
end qMskYpa
end
section
set_option backward.isDefEq.respectTransparency false
namespace qO4AyGb
noncomputable section
open Polynomial qrKC9pb
open cu (L)
open private avoid a1v from ProximityPrize.SubmissionLower.ZYcqQEc
open scoped WithZero
variable {J:Input} {r :Bool}
private abbrev O (v :GraphPrime J r) :=v.val.valuationSubring
private abbrev res (v :GraphPrime J r) :=IsLocalRing.residue (O v)
private def constIn (v :GraphPrime J r) :L →+* O v :=
 (constMap J).codRestrict (O v).toSubring fun c=> by
   change v.val (constMap J c)≤1
   obtain rfl | hc:=eq_or_ne c 0
   · simp
   · exact (v.constants _ hc).le
private abbrev resConst (v :GraphPrime J r) :=(res v).comp (constIn v)
private theorem residue_zero (v :GraphPrime J r) (t:O v) :
   res v t=0↔v.val (t:EC J)<1 :=
 (IsLocalRing.residue_eq_zero_iff t).trans (v.val.mem_maximalIdeal_iff (a :=t))
private theorem res_mem (v :GraphPrime J r) (t:O v) :
  res v t∈(resConst v).fieldRange↔ResidueConstant J v.val (t:EC J) := by
 rw [RingHom.mem_fieldRange]
 change (∃ c,res v (constIn v c)=res v t)↔_
 apply exists_congr
 intro c
 change _↔v.val ((t - constIn v c:O v) :EC J)<1
 rw [← residue_zero,map_sub,sub_eq_zero,eq_comm]
private def gaugeIn (v :GraphPrime J r) (τ:L) :O v :=
 let y :O v :=⟨jU J r,v.regular 2⟩
 if r then y+constIn v τ else 1+constIn v τ*y
private theorem gaugeIn_val (v :GraphPrime J r) (τ:L) :
  (gaugeIn v τ:EC J) =
    if r then jU J true+constant J τ else gauge J τ:= by
 cases r <;> rfl
private theorem res_gaugeIn (v :GraphPrime J r) (τ:L) :
  let y :=res v (⟨jU J r,v.regular 2⟩:O v)
  res v (gaugeIn v τ)=if r then y+resConst v τ else 1+resConst v τ*y := by
 cases r <;> simp [gaugeIn]
private theorem bad_gauge (v :GraphPrime J r) :
   ({τ:L | res v (gaugeIn v τ)=0} : Set L).Subsingleton := by
 let y :=res v (⟨jU J r,v.regular 2⟩:O v)
 let e :=resConst v
 intro a ha b hb
 change res v (gaugeIn v a)=0 at ha
 change res v (gaugeIn v b)=0 at hb
 rw [res_gaugeIn] at ha hb
 apply e.injective
 cases r
 · change 1+e a*y=0 at ha
   change 1+e b*y=0 at hb
   have hy :y≠0:= by
     intro h
     simp [h] at ha
   exact mul_right_cancel₀ hy (add_left_cancel (ha.trans hb.symm))
 · exact add_left_cancel (ha.trans hb.symm)
private theorem bad_zero_gauge (J:Input) :
  ({τ:L | gauge J τ=0} : Set L).Subsingleton := by
 intro a ha b hb
 change 1+constMap J a*jU J false=0 at ha
 change 1+constMap J b*jU J false=0 at hb
 exact (constMap J).injective
  (mul_right_cancel₀ (ordinate_false_ne_zero J) (add_left_cancel (ha.trans hb.symm)))
private theorem varying (v :GraphPrime J r) {a x :L} (h:Over J v a x) :
   ¬ ResidueConstant J v.val (jU J r) ∨ ¬ ResidueConstant J v.val (jet J r) := by
 obtain ⟨i,hi⟩:=v.curve
 fin_cases i
 · exact (hi ⟨x,h.2⟩).elim
 · exact (hi ⟨a,h.1⟩).elim
 · exact Or.inl hi
 · exact Or.inr hi
private theorem gauged_coords (v :GraphPrime J r) (τ:L) (hg:gauge J τ≠0)
    (hG:res v (gaugeIn v τ)≠0)
    (hn : ¬ ResidueConstant J v.val (jU J r) ∨ ¬ ResidueConstant J v.val (jet J r)) :
    (v.val (polar J false/gauge J τ^(J.l-2))=v.val (polar J r)) ∧
    ∃ u j:O v,(u:EC J)=jU J false/gauge J τ ∧
      (j:EC J)=jet J false/gauge J τ^2 ∧
      (res v u∉(resConst v).fieldRange∨res v j∉(resConst v).fieldRange) := by
  let G:=gaugeIn v τ
  have hv :v.val (G:EC J)=1 :=
    le_antisymm G.property (le_of_not_gt fun h=>hG ((residue_zero v G).2 h))
  have hg' : (G:EC J)≠0:=v.val.ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  let I:O v :=⟨(G:EC J)⁻¹,by
    change v.val ((G:EC J)⁻¹)≤1
    rw [map_inv₀,hv,inv_one]⟩
  have hGI:G* I=1 :=Subtype.ext (mul_inv_cancel₀ hg')
  let y₀:O v :=⟨jU J r,v.regular 2⟩
  let j₀:O v :=⟨jet J r,v.regular 3⟩
  let ρ:=res v
  let k :=(resConst v).fieldRange
  let a :=resConst v τ
  have ha :a∈k :=(resConst v).mem_fieldRange_self τ
  have hI:ρ I*ρ G=1 := by rw [mul_comm,← map_mul,hGI,map_one]
  have hYJ:ρ y₀∉k∨ρ j₀∉k := by
    simpa only [k,ρ,res_mem,y₀,j₀] using hn
  have hv' := hv
  rw [gaugeIn_val] at hv'
  cases r
  · change v.val (gauge J τ)=1 at hv'
    refine ⟨by rw [map_div₀,map_pow,hv',one_pow,div_one],y₀*I,j₀*I^2,rfl,?_,?_⟩
    · change jet J false*((G:EC J)⁻¹)^2= _
      rw [gaugeIn_val]
      simp [div_eq_mul_inv,inv_pow]
    · by_contra! h
      simp only [map_mul,map_pow] at h
      have hG' : ρ G=1+a*ρ y₀:=res_gaugeIn v τ
      have hu: (ρ y₀*ρ I)*ρ G=ρ y₀:= by rw [mul_assoc,hI,mul_one]
      have he :ρ y₀*(1-a*(ρ y₀*ρ I))=ρ y₀*ρ I:= by
        rw [hG'] at hu
        linear_combination -hu
      have hc:1-a*(ρ y₀*ρ I)≠0:= by
        intro hz
        rw [hz,mul_zero] at he
        simp [← he] at hz
      have hy :ρ y₀∈k :=(eq_div_iff hc).2 he ▸
        k.div_mem h.1 (k.sub_mem k.one_mem (k.mul_mem ha h.1))
      have hkG:ρ G∈k :=hG'.symm ▸ k.add_mem k.one_mem (k.mul_mem ha hy)
      have hj: (ρ j₀*ρ I^2)*ρ G^2=ρ j₀:= by rw [mul_assoc,← mul_pow,hI,one_pow,mul_one]
      exact (hYJ.resolve_left (not_not_intro hy)) (hj ▸ k.mul_mem h.2 (k.pow_mem hkG _))
  · let q:=jU J true
    let d:=gauge J τ
    have hq:q≠0:=inv_ne_zero (ordinate_false_ne_zero J)
    have hdq:d*q=q+constant J τ:=gauge_mul_reciprocal J τ
    change v.val (q+constant J τ)=1 at hv'
    obtain ⟨hp,hj⟩:=a7C J
    change polar J true = -(q^(J.l-2)*polar J false) at hp
    change jet J true = -(q^2*jet J false) at hj
    have hpol:polar J false/d^(J.l-2) =
        -(polar J true/(q+constant J τ)^(J.l-2)) := by
      rw [hp,neg_div,neg_neg,← hdq,mul_pow]
      field_simp [show d≠0 from hg,hq]
    refine ⟨by rw [hpol,v.val.map_neg,map_div₀,map_pow,hv',one_pow,div_one],
      I,-j₀*I^2,?_,?_,?_⟩
    · change (q+constant J τ)⁻¹=jU J false/d
      rw [← hdq,mul_inv_rev,show q⁻¹=jU J false from inv_inv _,div_eq_mul_inv]
    · change -jet J true*((q+constant J τ)⁻¹)^2=jet J false/d^2
      rw [hj,neg_neg,← hdq,inv_pow,mul_pow]
      field_simp [show d≠0 from hg,hq]
    · by_contra! h
      simp only [map_mul,map_neg,map_pow] at h
      have hG' : ρ G=ρ y₀+a :=res_gaugeIn v τ
      have he :ρ G=(ρ I)⁻¹:=(eq_div_iff (show ρ I≠0 from
        fun hz=> by rw [hz,zero_mul] at hI; exact zero_ne_one hI)).2
        (by rw [mul_comm,hI]) |>.trans (one_div _)
      have hkG:ρ G∈k :=he.symm ▸ k.inv_mem h.1
      have hy :ρ y₀∈k :=(show ρ G-a=ρ y₀ by rw [hG',add_sub_cancel_right]) ▸
        k.sub_mem hkG ha
      have hJ: (-ρ j₀*ρ I^2)*ρ G^2 = -ρ j₀:= by
        rw [mul_assoc,← mul_pow,hI,one_pow,mul_one]
      exact (hYJ.resolve_left (not_not_intro hy))
        (neg_neg (ρ j₀) ▸ k.neg_mem (hJ ▸ k.mul_mem h.2 (k.pow_mem hkG _)))
private theorem fresh (v :GraphPrime J r) (t:O v) (ht:res v t∉(resConst v).fieldRange)
  (g:L[X]) (hg:g≠0) :
  v.val (g.eval₂ (constMap J) (t:EC J))=1 := by
 let z :=g.eval₂ (constIn v) t
 have hz : (z :EC J)=g.eval₂ (constMap J) (t:EC J) :=
  Polynomial.hom_eval₂ g (constIn v) (O v).subtype t
 rw [← hz]
 refine le_antisymm z.property (le_of_not_gt fun h=>ht ?_)
 let:Algebra L (IsLocalRing.ResidueField (O v)) :=(resConst v).toAlgebra
 have ha :IsAlgebraic L (res v t) :=⟨g,hg,by
  change g.eval₂ (resConst v) (res v t)=0
  rw [← hom_eval₂]
  exact (residue_zero v z).2 h⟩
 obtain ⟨c,hc⟩:=minpoly.mem_range_of_degree_eq_one L (res v t)
  (IsAlgClosed.degree_eq_one_of_irreducible L (minpoly.irreducible (isAlgebraic_iff_isIntegral.mp ha)))
 exact RingHom.mem_fieldRange.mpr ⟨c,hc⟩
theorem exists_pencil (J:Input) (ι:Type) [Fintype ι] (a x :ι→L) (r :ι→Bool)
   (D : ∀ i,GraphPrime J (r i)) (h : ∀ i,Over J (D i) (a i) (x i)) :
   ∃ τ b:L,gauge J τ≠0 ∧ ∀ i,
     (D i).val (jU J false/gauge J τ)≤1 ∧
     (D i).val (polar J false/gauge J τ^(J.l-2))=(D i).val (polar J (r i)) ∧
     ∀ g:L[X],g≠0→(D i).val (g.eval₂ (constMap J) (qW J τ b))=1 := by
 classical
 obtain ⟨τ,hτ,hG⟩:=avoid (fun i => {τ | res (D i) (gaugeIn (D i) τ)=0})
   (fun i=>bad_gauge (D i)) _ (bad_zero_gauge J).finite
 have hg:gauge J τ≠0:=hτ
 have hcoord (i:ι) :=gauged_coords (D i) τ hg (hG i) (varying (D i) (h i))
 choose u j hu hj hn using fun i=>(hcoord i).2
 obtain ⟨b,-,hb⟩:=avoid
   (fun i => {b | resConst (D i) b*res (D i) (u i)+res (D i) (j i) ∈
     (resConst (D i)).fieldRange})
   (fun i=>a1v _ _ _ (hn i)) ∅ Set.finite_empty
 refine ⟨τ,b,hg,fun i=>⟨hu i ▸ (u i).property,(hcoord i).1,fun g hgn => ?_⟩⟩
 let t:=constIn (D i) b*u i+j i
 have ht: (t:EC J)=qW J τ b:= by
   change constant J b*(u i:EC J)+(j i:EC J)= _
   rw [hu,hj]
   rfl
 rw [← ht]
 refine fresh (D i) t (fun h=>hb i ?_) g hgn
 change resConst (D i) b*res (D i) (u i)+res (D i) (j i) ∈
   (resConst (D i)).fieldRange
 simpa only [t,map_add,map_mul,RingHom.comp_apply] using h
end
end qO4AyGb
end
