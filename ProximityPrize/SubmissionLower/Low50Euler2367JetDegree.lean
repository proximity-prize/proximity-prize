import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic

open scoped BigOperators Polynomial
open Polynomial

namespace EulerJetDegree

variable {R : Type*} [CommRing R]

def signedChoose (D i k : ℕ) : R :=
  ∑ r ∈ Finset.range (i + 1),
    (-1 : R) ^ r * (D-r).choose (i-r) * k.choose r

theorem signedChoose_step (D i k : ℕ) :
    signedChoose (R := R) D (i+1) (k+1) =
      signedChoose D (i+1) k - signedChoose (D-1) i k := by
  unfold signedChoose
  simp only [Finset.sum_range_succ' _ (i+1), pow_zero, Nat.sub_zero,
    Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
  have h : (∑ r ∈ Finset.range (i+1),
      (-1 : R) ^ (r+1) * (D-(r+1)).choose ((i+1)-(r+1)) * (k+1).choose (r+1)) =
      (∑ r ∈ Finset.range (i+1),
        (-1 : R) ^ (r+1) * (D-(r+1)).choose ((i+1)-(r+1)) * k.choose (r+1)) -
      ∑ r ∈ Finset.range (i+1), (-1 : R) ^ r * (D-1-r).choose (i-r) * k.choose r := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [Nat.choose_succ_succ, Nat.cast_add, pow_succ,
      show D - (r+1) = D-1-r by omega,
      show i+1-(r+1)=i-r by omega]
    ring
  rw [h]
  ring

theorem signedChoose_eq {D i k : ℕ} (h : k ≤ D) :
    signedChoose (R := R) D i k = ((D-k).choose i : R) := by
  induction k generalizing D i with
  | zero =>
    unfold signedChoose
    rw [Finset.sum_eq_single 0]
    · simp
    · intro r hr hne
      simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hne)]
    · simp
  | succ k ih =>
    cases i with
    | zero => simp [signedChoose]
    | succ i =>
      rw [signedChoose_step, ih (by omega : k ≤ D), ih (by omega : k ≤ D-1)]
      rw [show D-k = (D-(k+1))+1 by omega,
        show D-1-k = D-(k+1) by omega, Nat.choose_succ_succ, Nat.cast_add]
      ring

/-- Euler-adjusted Hasse jet, using physical degree cap `D`. -/
noncomputable def euler (D i : ℕ) (f : R[X]) : R[X] :=
  ∑ r ∈ Finset.range (i+1),
    C ((-1 : R) ^ r * (D-r).choose (i-r)) * (X^r * hasseDeriv r f)

theorem coeff_euler {D i k : ℕ} (f : R[X]) (hk : k ≤ D) :
    (euler D i f).coeff k = ((D-k).choose i : R) * f.coeff k := by
  rw [← signedChoose_eq hk]
  unfold euler signedChoose
  rw [Polynomial.finsetSum_coeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hr : r ≤ k
  · simp [hr, hasseDeriv_coeff, Nat.sub_add_cancel hr, mul_assoc]
  · simp [hr, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hr)]

theorem natDegree_euler_le (D i : ℕ) (f : R[X]) : (euler D i f).natDegree ≤ f.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  unfold euler
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro r _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hr : r ≤ k
  · simp [hr, hasseDeriv_coeff, Nat.sub_add_cancel hr, coeff_eq_zero_of_natDegree_lt hk]
  · simp [hr]

theorem natDegree_euler_le_sub {D i : ℕ} {f : R[X]} (hf : f.natDegree ≤ D) :
    (euler D i f).natDegree ≤ D-i := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases hD : k ≤ D
  · rw [coeff_euler f hD]
    simp [Nat.choose_eq_zero_of_lt (by omega : D-k < i)]
  · exact coeff_eq_zero_of_natDegree_lt
      ((natDegree_euler_le D i f).trans_lt (hf.trans_lt (Nat.lt_of_not_ge hD)))

theorem natDegree_euler_lineCoeff_le {A D i : ℕ} (hi : i ≤ 3) (hiD : i ≤ D)
    (hDA : D ≤ A) {S U : R[X]} (hS : S.natDegree ≤ D) (hU : U.natDegree ≤ A+3)
    (j : ℕ) :
    (((C (euler D i S) + C (euler D i U) * X) : (R[X])[X]).coeff j).natDegree ≤
      D-i + (A+6-D) * j := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
  by_cases h0 : j = 0
  · simpa [h0] using natDegree_euler_le_sub (i := i) hS
  · by_cases h1 : j = 1
    · have h := (natDegree_euler_le D i U).trans hU
      subst j
      simp only [one_ne_zero, ite_false, ite_true, zero_add, mul_one]
      omega
    · simp [h0, h1]

private def Bounded (W b : ℕ) (Q : (R[X])[X]) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + W*j

private theorem bounded_mul {W a b : ℕ} {F G : (R[X])[X]}
    (hF : Bounded W a F) (hG : Bounded W b G) : Bounded W (a+b) (F*G) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  refine natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega

theorem bounded_const {W b : ℕ} {f : R[X]} (h : f.natDegree ≤ b) :
    Bounded W b (C f) := by
  intro j
  by_cases h0 : j = 0
  · simpa [h0] using h
  · simp [Polynomial.coeff_C, h0]

private theorem bounded_pow {W b : ℕ} {f : (R[X])[X]}
    (h : Bounded W b f) (n : ℕ) : Bounded W (b*n) (f^n) := by
  induction n with
  | zero => simp only [pow_zero, mul_zero]; exact bounded_const (by simp)
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact bounded_mul ih h

private theorem bounded_prod {I : Type*} (ids : Finset I) {W : ℕ}
    (f : I → (R[X])[X]) (b : I → ℕ) (h : ∀ i ∈ ids, Bounded W (b i) (f i)) :
    Bounded W (∑ i ∈ ids, b i) (∏ i ∈ ids, f i) := by
  classical
  induction ids using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact bounded_const (by simp)
  | insert i ids hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact bounded_mul (h i (Finset.mem_insert_self _ _))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- The Euler-adjusted locator pencil after the common denominator has been cleared. -/
noncomputable def eulerLine (D : ℕ) (P : MvPolynomial (Fin 4) (R[X])) (S U : R[X]) : (R[X])[X] :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => C (euler D i.val S) + C (euler D i.val U) * X) P

theorem natDegree_eulerLine_coeff_le {A D T : ℕ} (hD : 3 ≤ D) (hDA : D ≤ A)
    (P : MvPolynomial (Fin 4) (R[X])) {S U : R[X]}
    (hS : S.natDegree ≤ D) (hU : U.natDegree ≤ A+3)
    (hp : ∀ m ∈ P.support,
      (P.coeff m).natDegree + m.sum (fun i a => (D-i.val)*a) ≤ T) (j : ℕ) :
    ((eulerLine D P S U).coeff j).natDegree ≤ T + (A+6-D)*j := by
  let b (i : Fin 4) := D-i.val
  let F (i : Fin 4) : (R[X])[X] := C (euler D i.val S) + C (euler D i.val U)*X
  have hF (i : Fin 4) : Bounded (A+6-D) (b i) (F i) := by
    intro k
    have hi : i.val ≤ 3 := Nat.le_of_lt_succ i.isLt
    exact natDegree_euler_lineCoeff_le hi (hi.trans hD) hDA hS hU k
  unfold eulerLine
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := bounded_mul (bounded_const (W:=A+6-D) (f:=P.coeff m) le_rfl)
    (bounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => bounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hp m hm) _)

theorem natDegree_coeff_le_of_XPow_mul [IsDomain R] {J T W j : ℕ}
    (P : (R[X])[X])
    (h : (((C ((X : R[X])^J))*P).coeff j).natDegree ≤ T+J+W*j) :
    (P.coeff j).natDegree ≤ T+W*j := by
  rw [Polynomial.coeff_C_mul] at h
  by_cases hn : P.coeff j = 0
  · simp [hn]
  · rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hn, natDegree_X_pow] at h
    omega

#print axioms natDegree_euler_le_sub
#print axioms natDegree_euler_lineCoeff_le
#print axioms natDegree_eulerLine_coeff_le
#print axioms natDegree_coeff_le_of_XPow_mul

end EulerJetDegree
