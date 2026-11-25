import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic

set_option Elab.async false

namespace Research6966.AffineODE

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Numerators of the linear and constant terms after clearing the n-th
derivative of a solution of A*y' = B*y + C by A^n. -/
def pair (δ : R → R) (A B C : R) : ℕ → R × R
  | 0 => (1, 0)
  | n + 1 =>
    let (l, m) := pair δ A B C n
    (A * δ l - n * δ A * l + B * l, A * δ m - n * δ A * m + C * l)

private theorem clear_power (D : S →+ S) (one : D 1 = 0)
    (mul : ∀ a b, D (a*b) = D a*b + a*D b) (a : S) (n : ℕ) :
    a * D (a^n) = n * a^n * D a := by
  induction n with
  | zero => simp [one]
  | succ n ih =>
    rw [pow_succ, mul, Nat.cast_succ]; linear_combination a * ih

/-- Specializing the two seed coefficients commutes with abscissa
differentiation. No nonzero initial value or separant at a code node is needed. -/
theorem cleared_derivatives (δ : R → R) (D : S →+ S) (f : R →+* S)
    (one : D 1 = 0) (mul : ∀ a b, D (a*b) = D a*b + a*D b)
    (coeff : ∀ a, D (f a) = f (δ a)) (A B C : R) (y : S)
    (ode : f A * D y = f B * y + f C) (n : ℕ) :
    f A ^ n * D^[n] y = f (pair δ A B C n).1 * y + f (pair δ A B C n).2 := by
  induction n with
  | zero => simp [pair]
  | succ n ih =>
    have diff := congrArg D ih
    simp only [mul, map_add, coeff] at diff
    rw [Function.iterate_succ_apply', pow_succ, pair]
    simp only [map_add, map_sub, map_mul, map_natCast]
    have power := clear_power D one mul (f A) n
    rw [coeff] at power
    linear_combination f A * diff + f (pair δ A B C n).1 * ode
      - (D^[n] y) * power - (n:S) * f (δ A) * ih

open MvPolynomial in
theorem degree_bounds {σ k : Type*} [Field k] (δ : MvPolynomial σ k → MvPolynomial σ k)
    (keeps : ∀ p, (δ p).totalDegree ≤ p.totalDegree) (A B C : MvPolynomial σ k)
    (u : ℕ) (ha : A.totalDegree ≤ u) (hb : B.totalDegree ≤ u) (hc : C.totalDegree ≤ u) (n : ℕ) :
    (pair δ A B C n).1.totalDegree ≤ n*u ∧ (pair δ A B C n).2.totalDegree ≤ n*u := by
  induction n with
  | zero => simp [pair]
  | succ n ih =>
    have step (X Y : MvPolynomial σ k) (hx : X.totalDegree ≤ n*u)
        (hy : Y.totalDegree ≤ n*u) (T : MvPolynomial σ k) (ht : T.totalDegree ≤ u) :
        (A*δ X - n*δ A*X + T*Y).totalDegree ≤ (n+1)*u := by
      apply (totalDegree_add _ _).trans; apply max_le
      · apply (totalDegree_sub _ _).trans; apply max_le
        · apply (totalDegree_mul _ _).trans;rw [Nat.succ_mul];have := keeps X;omega
        · apply (totalDegree_mul _ _).trans
          have hnum : ((n : MvPolynomial σ k) * δ A).totalDegree ≤ u := by
            apply (totalDegree_mul _ _).trans
            have hz : (n : MvPolynomial σ k).totalDegree=0 := by
              rw [← map_natCast (MvPolynomial.C : k →+* MvPolynomial σ k), totalDegree_C]
            have := keeps A
            omega
          rw [Nat.succ_mul];omega
      · apply (totalDegree_mul _ _).trans;rw [Nat.succ_mul];omega
    exact ⟨step _ _ ih.1 ih.1 B hb,step _ _ ih.2 ih.1 C hc⟩

#print axioms cleared_derivatives
#print axioms degree_bounds

/-- Put every Taylor coefficient over the same denominator. The weights are
the scalar evaluation weights at a physical coordinate. -/
def response (d : ℕ) (weights : ℕ → R) (A : R) (p : ℕ → R) : R :=
  ∑ i ∈ Finset.range (d+1), weights i * A^(d-i) * p i

theorem common_denominator (A : R) (f : R →+* S) (y : S)
    (l m : ℕ → R) (v : ℕ → S) (d : ℕ) (weights : ℕ → R)
    (entry : ∀ i ≤ d, f A^i * v i = f (l i)*y + f (m i)) :
    f A^d * (∑ i ∈ Finset.range (d+1), f (weights i)*v i) =
        f (response d weights A l)*y + f (response d weights A m) := by
  simp only [response,map_sum,map_mul,map_pow,Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have le : i≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  conv_lhs => rw [←Nat.sub_add_cancel le,pow_add]
  linear_combination f (weights i)*f A^(d-i)*entry i le

open MvPolynomial in
theorem response_degree {σ k : Type*} [Field k] (A : MvPolynomial σ k) (u d : ℕ)
    (weights p : ℕ → MvPolynomial σ k) (hA : A.totalDegree≤u)
    (hw : ∀ i : ℕ, (weights i).totalDegree = 0) (hp : ∀ i : ℕ, (p i).totalDegree ≤ i * u) :
    (response d weights A p).totalDegree ≤ d * u := by
  unfold response
  apply Finset.sum_induction _ (fun q:MvPolynomial σ k=>q.totalDegree≤d*u)
  · exact fun v w hv hw'=>(totalDegree_add _ _).trans (max_le hv hw')
  · simp
  · intro i hi
    have le : i≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    apply (totalDegree_mul _ _).trans
    have lhs: (weights i * A^(d-i)).totalDegree≤(d-i)*u := by
      apply (totalDegree_mul _ _).trans
      rw [hw,zero_add]
      exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hA)
    exact (Nat.add_le_add lhs (hp i)).trans_eq (by rw [←Nat.add_mul,Nat.sub_add_cancel le])

open Polynomial in
theorem evaluation_from_derivatives {k : Type*} [Field k] (p : k[X]) (x t : k)
    (d : ℕ) (deg : p.natDegree≤d) (fac : ∀ i ≤ d, (i.factorial : k)≠0) :
    p.eval t = ∑ i ∈ Finset.range (d+1), ((t-x)^i / (i.factorial:k)) *
      (derivative^[i] p).eval x := by
  calc
    _ = (taylor x p).eval (t-x) := (taylor_eval_sub x p t).symm
    _ = _ := by
      rw [(taylor x p).eval_eq_sum_range' (n:=d+1) (by rw [natDegree_taylor]; omega) (t-x)]
      apply Finset.sum_congr rfl
      intro i hi
      have le:=Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have h := congrFun (factorial_smul_hasseDeriv (R:=k) i) p
      change i.factorial • (hasseDeriv i p) = derivative^[i] p at h
      rw [taylor_coeff,←h, show (i.factorial • (hasseDeriv i p)).eval x =
        i.factorial • (hasseDeriv i p).eval x from map_nsmul (evalRingHom x) _ _,nsmul_eq_mul]
      field_simp [fac i le]

#print axioms common_denominator
#print axioms response_degree
#print axioms evaluation_from_derivatives

end Research6966.AffineODE
