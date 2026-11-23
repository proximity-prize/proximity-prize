import ProximityPrize.SubmissionLower.Z0zgXCc
import ProximityPrize.SubmissionLower.ZQ2Yete
import ProximityPrize.SubmissionLower.ZWvyx4b
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qyUzJvd
noncomputable section
open Polynomial
open P5 (K)
open cu (L FX jz)
open P5_7_7 (phys embed)
open qGnV2ac (Sections)
open qrKC9pb
open private fiber fiber_deriv regular_fiber from ProximityPrize.SubmissionLower.ZWvyx4b
open private derivative_reverse coeff_X_derivative from ProximityPrize.SubmissionLower.Z0zgXCc
private theorem no_common_root {E :Type*} [Field E] {f :E[X]} {y :E}
  (hc:IsCoprime f f.derivative) (hy :f.eval y=0) :f.derivative.eval y≠0:= by
 obtain ⟨a,b,hab⟩:=hc
 intro h
 have e :=congrArg (evalRingHom y) hab
 simp only [map_add,map_mul,map_one,coe_evalRingHom,hy,h,mul_zero,add_zero,
  zero_ne_one] at e
private theorem no_common_reverse_root {E :Type*} [Field E] {f :E[X]} {y :E}
  (hd:0<f.natDegree) (hc:IsCoprime f f.derivative) (hy :f.reverse.eval y=0) :
  f.reverse.derivative.eval y≠0:= by
 have hf :f≠0:=ne_zero_of_natDegree_gt hd
 have hy₀:y≠0:= by
  rintro rfl
  rw [← coeff_zero_eq_eval_zero,coeff_zero_reverse] at hy
  exact (leadingCoeff_ne_zero.mpr hf) hy
 let G:=C (f.natDegree :E)*f-Polynomial.X*f.derivative
 have hg:G.natDegree≤f.natDegree - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  change (C (f.natDegree :E)*f-Polynomial.X*f.derivative).coeff i=0
  rw [coeff_sub,coeff_C_mul,coeff_X_derivative]
  rcases lt_or_eq_of_le (show f.natDegree≤ i by omega) with hi' | hi'
  · rw [coeff_eq_zero_of_natDegree_lt hi',mul_zero,zero_mul,sub_self]
  · rw [hi',mul_comm,sub_self]
 have hroot :f.eval y⁻¹=0:= by
  let:=invertibleOfNonzero (inv_ne_zero hy₀)
  exact (eval₂_reverse_eq_zero_iff (RingHom.id E) y⁻¹ f).mp (by simpa only [invOf_eq_inv,inv_inv,eval₂_id] using hy)
 intro h
 rw [derivative_reverse f hd] at h
 let:=invertibleOfNonzero (inv_ne_zero hy₀)
 have hG:=(eval₂_reflect_eq_zero_iff (RingHom.id E) y⁻¹ (f.natDegree-1) G hg).mp
  (by simpa only [invOf_eq_inv,inv_inv,eval₂_id] using h)
 have hz :=no_common_root hc hroot
 simp only [G,eval₂_id,eval_sub,eval_mul,eval_C,eval_X,hroot,mul_zero,zero_sub,
  neg_eq_zero] at hG
 exact (mul_ne_zero (inv_ne_zero hy₀) hz) hG
variable {J:Input} {r :Bool} (D:GraphPrime J r)
private abbrev Residue :=IsLocalRing.ResidueField D.val.valuationSubring
private def reduced:Chart J r →+* Residue D :=
 (IsLocalRing.residue _).comp ((algebraMap (Chart J r) (EC J)).codRestrict
   D.val.valuationSubring.toSubring (chart_regular D))
private theorem reduced_eq_zero (a :Chart J r) :
  reduced D a=0↔D.val (a :EC J)<1 := by
 rw [reduced,RingHom.comp_apply,IsLocalRing.residue_eq_zero_iff,D.val.mem_maximalIdeal_iff]
 rfl
private theorem physical_injective (h : ¬ ResidueConstant J D.val (amm J)) :
    Function.Injective ((reduced D).comp (evalPhysical J r)) := by
  let e :=(reduced D).comp (evalPhysical J r)
  apply (injective_iff_map_eq_zero e).mpr
  intro q hq
  by_contra hne
  rw [(IsAlgClosed.splits q).eq_prod_roots,map_mul,map_multiset_prod] at hq
  rcases mul_eq_zero.mp hq with hc | hp
  · have hC:e (C q.leadingCoeff)=reduced D (algebraMap L _ q.leadingCoeff) := by
      simp only [e,RingHom.comp_apply,evalPhysical,coe_eval₂RingHom,eval₂_C]
    rw [hC,reduced_eq_zero] at hc
    exact (D.constants _ (leadingCoeff_ne_zero.mpr hne) ▸ hc).false
  · obtain ⟨g,hg,hzero⟩:=Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hp)
    obtain ⟨a,_,rfl⟩:=Multiset.mem_map.mp hg
    have he :e (Polynomial.X - C a)=reduced D (physDiff J r a) := by
      simp only [e,RingHom.comp_apply,map_sub,evalPhysical,coe_eval₂RingHom,eval₂_X,
        eval₂_C,physDiff]
    rw [he,reduced_eq_zero] at hzero
    exact h ⟨a,hzero⟩
private theorem fiber_map (z :K) (F:P5_7_7.Dg) :
  fiber F z=F.map ((evalRingHom (jz z)).comp (mapRingHom phys)) := by
 ext i
 simp only [fiber,embed,coe_mapRingHom,coeff_map,RingHom.comp_apply,phys]
theorem physical_constant (S:Sections J.F) (γ:K) (hγ:γ∈S.CF)
    (hz :D.val (seed J - constant J (algebraMap K L (S.seed γ)))<1)
    (hp:D.val (polar J r)<1) :ResidueConstant J D.val (amm J) := by
  by_contra h
  let z :=S.seed γ
  let φ:FX →+* Residue D:=IsFractionRing.lift (physical_injective D h)
  let e :=(evalRingHom (jz z)).comp (mapRingHom phys)
  have hφ (q:L[X]) :φ (phys q)=reduced D (evalPhysical J r q) :=
    IsFractionRing.lift_algebraMap (physical_injective D h) q
  have h₁: (reduced D).comp (evalSeed J r)=φ.comp e := by
    apply Polynomial.ringHom_ext
    · intro q
      simpa only [RingHom.comp_apply,evalSeed,coe_eval₂RingHom,eval₂_C,e,
        coe_mapRingHom,map_C,coe_evalRingHom,eval_C] using (hφ q).symm
    · have he :=(reduced_eq_zero D (seedDiff J r (algebraMap K L z))).mpr hz
      rw [seedDiff,map_sub,sub_eq_zero] at he
      change reduced D (evalSeed J r Polynomial.X)=φ (e Polynomial.X)
      have hX:e Polynomial.X=jz z := by simp [e]
      rw [evalSeed,coe_eval₂RingHom,eval₂_X,hX,← show phys (C (algebraMap K L z))=jz z from rfl,
        hφ,evalPhysical,coe_eval₂RingHom,eval₂_C]
      exact he
  let y :=reduced D (coord J r 2)
  have h₂ (G:P5_7_7.Dg) :reduced D (evalChart J r G)=((fiber G z).map φ).eval y := by
    rw [evalChart,coe_eval₂RingHom,hom_eval₂,h₁,fiber_map,map_map,← eval₂_eq_eval_map]
  have hA:=h₂ (chartEq J r)
  have hB:=h₂ (chartEq J r).derivative
  have he₁:evalChart J r (chartEq J r)=0 :=
    Subtype.ext ((coe_evalChart J r _).trans (chart_root J r))
  have he₂:=(reduced_eq_zero D (sep J r)).mpr ((coe_sep J r).symm ▸ hp)
  rw [he₁,map_zero,eq_comm] at hA
  rw [← show sep J r=evalChart J r (chartEq J r).derivative from rfl,he₂,eq_comm] at hB
  obtain ⟨hd,hc⟩:=(regular_fiber J.Ca.jU J.Ca.two_le J.Ca.tame z).mp
    (S.regular_ordinate γ hγ)
  let f :=(fiber J.F z).map φ
  have hC:IsCoprime f f.derivative := by
    change IsCoprime ((fiber J.F z).map φ) (((fiber J.F z).map φ).derivative)
    rw [derivative_map]
    exact hc.map (mapRingHom φ)
  have hf :f.natDegree=J.l:=(natDegree_map_eq_of_injective φ.injective _).trans hd
  have heq : (fiber (chartEq J r) z).map φ=if r then f.reverse else f := by
    cases r
    · rfl
    · change (fiber J.F.reverse z).map φ=f.reverse
      have hmap (G:P5_7_7.Dg) : (fiber G z).map φ=G.map (φ.comp e) := by
        rw [fiber_map,map_map]
      calc
        (fiber J.F.reverse z).map φ=(J.F.map (φ.comp e)).reflect J.l:= by
          rw [hmap,reverse,J.Ca.jU,reflect_map]
        _=f.reverse := by rw [← hmap,← hf]; rfl
  rw [fiber_deriv,← derivative_map,heq] at hB
  rw [heq] at hA
  cases r
  · exact no_common_root hC hA hB
  · exact no_common_reverse_root (hf.symm ▸ (by have :=J.Ca.two_le; omega)) hC hA hB
end
end qyUzJvd
