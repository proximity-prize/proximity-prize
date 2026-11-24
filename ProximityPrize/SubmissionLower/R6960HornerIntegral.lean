import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Valuation.LocalSubring

set_option Elab.async false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency.types false

namespace Lower6960.Horner
noncomputable section
open Polynomial
open scoped Polynomial BigOperators

variable {A E : Type*} [CommRing A] [Field E]

/-- The Horner term at cut `d` is `Y` times the polynomial tail starting
at the coefficient of `Y^d`. For a degree-`e` equation, cut `e-i+1`
has the form `a_e Y^i + … + a_(e-i+1) Y`. -/
def hornerPolynomial (p : (Polynomial A)) (d : ℕ) : (Polynomial A) := Polynomial.X * (p /ₘ (Polynomial.X ^ d))

def horner (ι : A →+* E) (p : (Polynomial A)) (d : ℕ) (y : E) : E :=
  (hornerPolynomial p d).eval₂ ι y

theorem horner_eq (ι : A →+* E) (p : (Polynomial A)) (d : ℕ) (y : E) :
    horner ι p d y=y*(p /ₘ (Polynomial.X ^ d)).eval₂ ι y := by
  rw [horner,hornerPolynomial,eval₂_mul,eval₂_X]

private theorem remainder_degree [Nontrivial A] (p : (Polynomial A)) {d : ℕ} (pos : 0<d) :
    (p %ₘ (Polynomial.X ^ d)).natDegree<d := by
  have nz : (Polynomial.X : (Polynomial A))^d≠1 := by
    intro h
    have deg := congrArg natDegree h
    rw [natDegree_X_pow,natDegree_one] at deg
    omega
  simpa only [natDegree_X_pow] using natDegree_modByMonic_lt p (monic_X_pow d) nz

private theorem backward_eval (ι : A →+* E) (p : (Polynomial A)) {d : ℕ} (pos : 0<d) (y : E)
    (yn : y≠0) (root : p.eval₂ ι y=0) :
    horner ι p d y=-((p %ₘ (Polynomial.X ^ d)).reflect (d-1)).eval₂ ι y⁻¹ := by
  let : Nontrivial A := ι.domain_nontrivial
  let r := p %ₘ (Polynomial.X ^ d)
  let q := p /ₘ (Polynomial.X ^ d)
  have qr : r.eval₂ ι y + y^d*q.eval₂ ι y=0 := by
    have h := congrArg (fun f : (Polynomial A)=>f.eval₂ ι y) (modByMonic_add_div p (Polynomial.X ^ d))
    rw [eval₂_add,eval₂_mul,eval₂_X_pow,root] at h
    exact h
  let : Invertible y := invertibleOfNonzero yn
  have rd : r.natDegree≤d-1 := by
    change (p %ₘ (Polynomial.X ^ d)).natDegree≤d-1
    have lt := remainder_degree p pos
    omega
  have ref := eval₂_reflect_mul_pow ι y (d-1) r rd
  rw [invOf_eq_inv] at ref
  have split : y^d=y^(d-1)*y := by
    rw [←pow_succ,Nat.sub_add_cancel pos]
  apply mul_right_cancel₀ (pow_ne_zero (d-1) yn)
  calc
    horner ι p d y*y^(d-1)=y^d*q.eval₂ ι y := by
      rw [horner_eq,split]
      change y*q.eval₂ ι y*y^(d-1)=_
      ring
    _ = -r.eval₂ ι y := by linear_combination qr
    _ = -((r.reflect (d-1)).eval₂ ι y⁻¹)*y^(d-1) := by rw [neg_mul,ref]

private theorem eval_in_valuation (V : ValuationSubring E) (ι : A →+* E)
    (coeffs : ∀ a,ι a∈V) {y : E} (hy : y∈V) (p : (Polynomial A)) : p.eval₂ ι y∈V := by
  rw [eval₂_eq_sum]
  exact V.toSubring.sum_mem fun i _=>V.toSubring.mul_mem (coeffs (p.coeff i)) (V.toSubring.pow_mem hy i)

/-- A Horner term is integral even when the root itself is nonintegral.
In each valuation ring containing the base, either the forward tail or
the reversed remainder is a polynomial in an integral coordinate. -/
theorem horner_integral [Algebra A E] (p : (Polynomial A)) {d : ℕ} (pos : 0<d) (y : E)
    (root : p.eval₂ (algebraMap A E) y=0) :
    IsIntegral A (horner (algebraMap A E) p d y) := by
  change horner (algebraMap A E) p d y∈(integralClosure A E).toSubring
  rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R:=(integralClosure A E).toSubring),Subring.mem_iInf]
  rintro ⟨V,contains⟩
  have coeffs (a : A) : algebraMap A E a∈V := contains (show IsIntegral A (algebraMap A E a) from isIntegral_algebraMap)
  by_cases yn : y=0
  · simp only [horner_eq,yn,zero_mul]
    exact V.zero_mem
  rcases V.mem_or_inv_mem y with hy|hy
  · exact eval_in_valuation V (algebraMap A E) coeffs hy _
  · rw [backward_eval (algebraMap A E) p pos y yn root]
    exact V.toSubring.neg_mem (eval_in_valuation V (algebraMap A E) coeffs hy _)

theorem coeff_tail [Nontrivial A] (p : (Polynomial A)) {d : ℕ} (pos : 0<d) (j : ℕ) :
    (p /ₘ (Polynomial.X ^ d)).coeff j=p.coeff (d+j) := by
  have rzero : (p %ₘ (Polynomial.X ^ d)).coeff (d+j)=0 :=
    coeff_eq_zero_of_natDegree_lt ((remainder_degree p pos).trans_le (Nat.le_add_right _ _))
  have eq := congrArg (fun f : (Polynomial A)=>f.coeff (d+j)) (modByMonic_add_div p (Polynomial.X ^ d))
  rw [coeff_add,rzero,zero_add,Nat.add_comm d j,coeff_X_pow_mul] at eq
  simpa only [Nat.add_comm j d] using eq

#print axioms horner_integral
#print axioms coeff_tail
end
end Lower6960.Horner
