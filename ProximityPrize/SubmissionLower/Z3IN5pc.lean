import ProximityPrize.SubmissionLower.ZN2gA7a
import ProximityPrize.SubmissionLower.Zk6yNvb
set_option Elab.async false
set_option autoImplicit true
section
namespace qTFhFCb
noncomputable section
open cu (L)
open qNu3xvc (Equation EC jU jet)
open P5_7_1_7_4_3_4 (gauge)
variable {E :Type} [Field E] [Algebra L E]
def pencilOrd (A:Equation E) (l:L) :EC A :=
 jU A false/gauge A l
def pencilJet (A:Equation E) (l:L) :EC A :=
 jet A false/gauge A l^2
end
end qTFhFCb
end
section
set_option backward.isDefEq.respectTransparency false
namespace qTFhFCb
noncomputable section
open Polynomial qNu3xvc
open qypA4Sc (ajm)
open P5_7_1_7_4_3_4 (gauge)
open cu (L)
open P5 (K p)
open private chart_root from ProximityPrize.SubmissionLower.Z5cOcra
open private other other_degree reflect_partials from ProximityPrize.SubmissionLower.ZN2gA7a
variable {E :Type} [Field E]
private theorem coeff_phys (f :E[X][X]) (i:ℕ) :
   (physicalDerivative f).coeff i=(f.coeff i).derivative := by
 classical
 rw [physicalDerivative,coeff_sum,sum_def]
 simp only [coeff_monomial,Finset.sum_ite_eq']
 split_ifs with h
 · rfl
 · rw [notMem_support_iff.mp h,derivative_zero]
private theorem eval_false (A:Equation E) (f :E[X][X]) :
  KM A false f=a7W A f := by
 change f.eval₂ ((a7W A).comp C) (a7W A Polynomial.X)= _
 rw [← hom_eval₂,eval₂_C_X]
private theorem eval_ne (A:Equation E) (f :E[X][X]) (hf :f≠0)
  (hd:f.natDegree<A.d) :KM A false f≠0:= by
 rw [eval_false]
 intro h
 have hz :AdjoinRoot.mk A.f f=0 :=
  IsFractionRing.injective (AdjoinRoot A.f) (EC A) (by simpa [a7W] using h)
 exact (not_le_of_gt hd) (natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp hz) hf)
theorem chart_transition [Algebra L E] (A:Equation E) (hd:2≤A.d) (ht:A.d<p) :
    polar A false≠0 ∧
      ∀ l:L,gauge A l≠0 →
      let g:=jU A true+constant A l
      g≠0 →
        pencilOrd A l=g⁻¹ ∧
        pencilJet A l = -jet A true/g^2 ∧
        polar A false/gauge A l^(A.d-2) = -(polar A true/g^(A.d-2)) := by
  let _:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
  let _:CharP E p:=charP_of_injective_ringHom (algebraMap L E).injective p
  let _:CharP E[X] p:=inferInstance
  let m:=A.d-1
  have hm:m+1=A.d:=Nat.sub_add_cancel A.positive
  have hn: (A.d:E[X])≠0:= fun h =>
    (not_le_of_gt ht) (Nat.le_of_dvd A.positive ((CharP.cast_eq_zero_iff _ p _).mp h))
  have hdf :A.f.derivative≠0:= by
    intro h
    have hc:=congrArg (fun f :E[X][X]=>f.coeff m) h
    rw [coeff_derivative,hm,← leadingCoeff,coeff_zero] at hc
    apply mul_ne_zero (leadingCoeff_ne_zero.mpr A.irreducible.ne_zero) hn
    simpa only [← hm,Nat.cast_add,Nat.cast_one] using hc
  have hfd:A.f.derivative.natDegree≤ m:=natDegree_derivative_le _
  have q2 :polar A false≠0:=eval_ne A _ hdf (hfd.trans_lt (by omega))
  let y :=jU A false
  let z :=jU A true
  have hz :z=y⁻¹:=rfl
  have hy :y≠0:= by
    have h:=eval_ne A (Polynomial.X:E[X][X]) Polynomial.X_ne_zero (by rw [natDegree_X]; omega)
    simpa only [KM,coe_eval₂RingHom,eval₂_X] using h
  have q3:z≠0:=hz ▸ inv_ne_zero hy
  have hyz :y*z=1 :=hz ▸ mul_inv_cancel₀ hy
  let _:=invertibleOfNonzero hy
  have q0 (f :E[X][X]) (n:ℕ) (hf :f.natDegree≤n) :
      KM A true (f.reflect n)=KM A false f*z^n:= by
    have h:=eval₂_reflect_mul_pow (ajm A) y n f hf
    rw [invOf_eq_inv,← hz] at h
    have he :KM A true (f.reflect n)*y^n=KM A false f :=h
    calc
      _=KM A false f/y^n:=(eq_div_iff (pow_ne_zero _ hy)).mpr he
      _ = _:= by rw [div_eq_mul_inv,← inv_pow,← hz]
  have hroot :KM A false A.f=0:=chart_root A hd false
  have hOther :KM A false (other A.d A.f) = -(y*polar A false) := by
    have hX:KM A false Polynomial.X=y :=eval₂_X _ _
    simp [other,hroot,hX,polar,chartEq]
  have hP:polar A true = -(z^(A.d-2)*polar A false) := by
    have h:=(reflect_partials A.f m hm.symm).1
    change KM A true A.f.reverse.derivative= _
    rw [← h,q0 _ _ (other_degree A.f m hm.ge),hm,hOther,neg_mul]
    congr 1
    have he :y*z^m=z^(A.d-2) := by
      rw [show m=(A.d-2)+1 by omega,pow_succ',← mul_assoc,hyz,one_mul]
    rw [mul_comm y,mul_assoc,he,mul_comm]
  have hpd (f :E[X][X]) : (physicalDerivative f).natDegree≤f.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_phys,coeff_eq_zero_of_natDegree_lt hi,derivative_zero]
  have hR:physicalDerivative A.f.reverse=(physicalDerivative A.f).reflect A.d:= by
    ext i
    rw [coeff_phys,coeff_reverse,coeff_reflect,coeff_phys]
  have hQ:KM A true (physicalDerivative A.f.reverse) =
      KM A false (physicalDerivative A.f)*z^A.d:= by
    rw [hR,q0 _ _ (hpd A.f)]
  have hJ:jet A true = -(z^2*jet A false) := by
    change -(KM A true (physicalDerivative A.f.reverse))/polar A true =
      -(z^2*(-(KM A false (physicalDerivative A.f))/polar A false))
    rw [hQ,hP,show z^A.d=z^(A.d-2)*z^2 by rw [← pow_add,Nat.sub_add_cancel hd]]
    field_simp [q2,q3]
  refine ⟨q2,fun l hg hG => ?_⟩
  change z+constant A l≠0 at hG
  have q1 :gauge A l*z=z+constant A l:= by
    change (1+constant A l*y)*z= _
    rw [add_mul,one_mul,mul_assoc,hyz,mul_one]
  constructor
  · change y/gauge A l=(z+constant A l)⁻¹
    rw [← one_div]
    apply (div_eq_div_iff hg hG).mpr
    rw [← q1,mul_left_comm,hyz,mul_one,one_mul]
  constructor
  · change jet A false/gauge A l^2 = -jet A true/(z+constant A l)^2
    rw [hJ,neg_neg,← q1,mul_pow]
    field_simp [hg,q3]
  · change polar A false/gauge A l^(A.d-2) = -(polar A true/(z+constant A l)^(A.d-2))
    rw [hP,neg_div,neg_neg,← q1,mul_pow]
    field_simp [hg,q3]
end
end qTFhFCb
end
