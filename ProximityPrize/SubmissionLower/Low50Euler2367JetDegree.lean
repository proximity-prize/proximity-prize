import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Cutter53AnchorLocal -- serialize candidate build

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

private def Bounded (W b : ℕ) (Q : (R[X])[X]) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + W*j

end EulerJetDegree
