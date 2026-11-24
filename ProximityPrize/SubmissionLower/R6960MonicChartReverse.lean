import ProximityPrize.SubmissionLower.R6960DifferentialPoles
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Taylor

set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 2400000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial

section Euler

variable {R : Type*} [CommRing R]

private theorem coeff_mul_X_derivative (f : (Polynomial R)) (i : ℕ) :
    (Polynomial.X*f.derivative).coeff i=f.coeff i*(i:R) := by
  cases i with
  | zero => simp
  | succ i => rw [coeff_X_mul,coeff_derivative,Nat.cast_succ]

/-- Euler's identity for the reversed homogeneous equation, with
declared degree preserved through differentiation. -/
theorem reflect_derivative (f : (Polynomial R)) (e : ℕ) (he : 0<e) (bound : f.natDegree≤e) :
    Polynomial.X*(f.reflect e).derivative =
      C (e:R)*f.reflect e-f.derivative.reflect (e-1) := by
  ext i
  rw [coeff_mul_X_derivative,coeff_sub,coeff_C_mul,coeff_reflect,coeff_reflect,
    coeff_derivative]
  by_cases fit : i<e
  · have b₁ : i≤e := fit.le
    have b₂ : i≤e-1 := by omega
    rw [revAt_le b₁,revAt_le b₂]
    have eq : e-1-i+1=e-i := by omega
    rw [eq]
    have scalar : (((e-1-i : ℕ) : R) + 1) = ((e-i : ℕ):R) := by
      simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun n : ℕ => (n:R)) eq
    rw [scalar,Nat.cast_sub b₁]
    ring
  · have ld : e ≤ i := Nat.le_of_not_gt fit
    rw [revAt_eq_self_of_lt (show e - 1 < i from by omega),
      coeff_eq_zero_of_natDegree_lt (bound.trans_lt (by omega : e < i+1)),zero_mul,sub_zero]
    rcases eq_or_lt_of_le ld with rfl | lt
    · ring
    · rw [revAt_eq_self_of_lt lt,coeff_eq_zero_of_natDegree_lt (bound.trans_lt lt),mul_zero,zero_mul]

end Euler

section Basic

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The monic polynomial for the reciprocal ordinate on a chart at c. -/
def equation (f : (Polynomial A)) (c : A) (u : Aˣ) : (Polynomial A) :=
  C ((↑u⁻¹ : A))*(f.taylor c).reverse

theorem equation_degree (f : (Polynomial A)) (c : A) (u : Aˣ) (hu : f.eval c=(u:A)) :
    (equation f c u).natDegree=f.natDegree := by
  have nn : (f.taylor c).coeff 0≠0 := by rw [taylor_coeff_zero,hu]; exact u.ne_zero
  rw [equation,natDegree_C_mul (Units.ne_zero _),reverse_natDegree,
    natTrailingDegree_eq_zero.mpr (Or.inr nn),Nat.sub_zero,natDegree_taylor]

theorem equation_monic (f : (Polynomial A)) (c : A) (u : Aˣ) (hu : f.eval c=(u:A)) :
    (equation f c u).Monic := by
  have nn : (f.taylor c).coeff 0≠0 := by rw [taylor_coeff_zero,hu]; exact u.ne_zero
  unfold Monic equation
  rw [leadingCoeff_mul,leadingCoeff_C,reverse_leadingCoeff,trailingCoeff_eq_coeff_zero nn,
    taylor_coeff_zero,hu,Units.inv_mul]

theorem equation_coeff_zero (f : (Polynomial A)) (c : A) (u : Aˣ) :
    (equation f c u).coeff 0=(↑u⁻¹:A)*f.leadingCoeff := by
  rw [equation,coeff_C_mul,coeff_zero_reverse,leadingCoeff_taylor]

end Basic

section Evaluation

variable {A E : Type*} [CommRing A] [IsDomain A] [Field E]

private theorem taylor_root_eval (i : A→+*E) (f : (Polynomial A)) (c : A) (α : E) :
    (f.taylor c).eval₂ i (α-i c)=f.eval₂ i α := by
  rw [taylor_apply,eval₂_comp,eval₂_add,eval₂_X,eval₂_C,sub_add_cancel]

private theorem derivative_taylor (f : (Polynomial A)) (c : A) :
    (f.taylor c).derivative=f.derivative.taylor c := by
  simp [taylor_apply,derivative_comp]

theorem sub_ne_at_root (i : A→+*E) {f : (Polynomial A)} {c : A} {u : Aˣ}
    (hu : f.eval c=(u:A)) {α : E} (root : f.eval₂ i α=0) : α-i c≠0 := by
  intro h
  have e : α=i c := sub_eq_zero.mp h
  rw [e,eval₂_at_apply,hu] at root
  exact (u.isUnit.map i).ne_zero root

theorem equation_root (i : A→+*E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) {α : E} (root : f.eval₂ i α=0) :
    (equation f c u).eval₂ i (α-i c)⁻¹=0 := by
  let w := α-i c
  have wn : w≠0 := sub_ne_at_root i hu root
  letI : Invertible w := invertibleOfNonzero wn
  have eq : (f.taylor c).eval₂ i w=0 := (taylor_root_eval i f c α).trans root
  have go := (eval₂_reverse_eq_zero_iff i w (f.taylor c)).mpr eq
  rw [invOf_eq_inv] at go
  rw [equation,eval₂_mul,eval₂_C,go,mul_zero]

/-- The derivative at the reciprocal root is obtained by homogeneous
differentiation of the same chart polynomial. -/
theorem equation_derivative (i : A→+*E) (f : (Polynomial A)) (c : A) (u : Aˣ)
    (hu : f.eval c=(u:A)) (degree : 2≤f.natDegree)
    {α : E} (root : f.eval₂ i α=0) :
    f.derivative.eval₂ i α*((α-i c)⁻¹)^(f.natDegree-2)=
      -(i (u:A))*((equation f c u).derivative.eval₂ i (α-i c)⁻¹) := by
  let w := α-i c
  let β := w⁻¹
  let p := f.taylor c
  let e := f.natDegree
  have wn : w≠0 := sub_ne_at_root i hu root
  have bne : β≠0 := inv_ne_zero wn
  letI : Invertible w := invertibleOfNonzero wn
  have rdegree : p.natDegree=e := natDegree_taylor f c
  have reverse_eq : p.reflect e=p.reverse := by rw [reverse,rdegree]
  have hroot := (eval₂_reverse_eq_zero_iff i w p).mpr ((taylor_root_eval i f c α).trans root)
  rw [invOf_eq_inv] at hroot
  have hroot' : p.reverse.eval₂ i β=0 := hroot
  have exp := reflect_derivative p e (by omega) rdegree.le
  have hom := congrArg (eval₂RingHom i β) exp
  simp only [map_mul,map_sub,coe_eval₂RingHom,eval₂_X,eval₂_C,reverse_eq,hroot',mul_zero,zero_sub] at hom
  have reverse_d : (p.derivative.reflect (e-1)).eval₂ i β * w^(e-1)=f.derivative.eval₂ i α := by
    have h := eval₂_reflect_mul_pow i w (e-1) p.derivative
      ((natDegree_derivative_le p).trans_eq (by rw [rdegree]))
    rw [invOf_eq_inv,derivative_taylor,taylor_root_eval] at h
    simpa only [β,p,derivative_taylor] using h
  have evalD : (p.reverse.derivative).eval₂ i β =
      -(f.derivative.eval₂ i α*β^(e-2)) := by
    have step : (p.derivative.reflect (e-1)).eval₂ i β=f.derivative.eval₂ i α*β^(e-1) := by
      apply mul_right_cancel₀ (pow_ne_zero _ wn)
      rw [reverse_d,mul_assoc,← mul_pow,inv_mul_cancel₀ wn,one_pow,mul_one]
    apply mul_left_cancel₀ bne
    rw [hom,step,show e-1=(e-2)+1 by omega,pow_succ]
    ring
  change f.derivative.eval₂ i α*β^(e-2)=-i (u:A)*(equation f c u).derivative.eval₂ i β
  rw [equation,derivative_C_mul,eval₂_mul,eval₂_C,show (f.taylor c).reverse=p.reverse from rfl,
    evalD]
  have cancel : i (u:A)*i ((↑u⁻¹:A))=1 := by rw [← map_mul,Units.mul_inv,map_one]
  calc
    _ = (i (u:A)*i ((↑u⁻¹:A)))*(f.derivative.eval₂ i α*β^(e-2)) := by rw [cancel,one_mul]
    _ = _ := by ring

#print axioms reflect_derivative
#print axioms equation_derivative
end Evaluation
end
end Lower6960.MonicChart
