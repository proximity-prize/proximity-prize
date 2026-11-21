import Mathlib.Algebra.Polynomial.HasseDeriv
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Global.Multiplicity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option Elab.async false

namespace Low48EulerJets
noncomputable section
open Polynomial
open scoped Polynomial

variable {K : Type*} [CommRing K]

def euler (S : K[X]) : K[X] := X * S.derivative

def dropLeading (D : ℕ) (S : K[X]) : K[X] := euler S - C (D : K) * S

private theorem coeff_euler (S : K[X]) (n : ℕ) :
    (euler S).coeff n = S.coeff n * (n : K) := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_X_mul, coeff_derivative]; simp

theorem dropLeading_degree {D : ℕ} (h : 0 < D) (S : K[X]) (hS : S.natDegree ≤ D) :
    (dropLeading D S).natDegree ≤ D-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [dropLeading, coeff_sub, coeff_euler, coeff_C_mul]
  by_cases eq : n=D
  · rw [eq, mul_comm,sub_self]
  · rw [coeff_eq_zero_of_natDegree_lt (show S.natDegree < n by omega)]
    simp

def reduced (D : ℕ) (S : K[X]) : ℕ → K[X]
  | 0 => S
  | i+1 => dropLeading (D-i) (reduced D S i)

theorem reduced_degree {D i : ℕ} (S : K[X]) (hS : S.natDegree ≤ D) (hi : i ≤ D) :
    (reduced D S i).natDegree ≤ D-i := by
  induction i with
  | zero => simpa [reduced] using hS
  | succ i ih =>
    have step := dropLeading_degree (show 0 < D-i by omega) (reduced D S i) (ih (by omega))
    simpa [reduced,Nat.sub_sub] using step

def scaled (i : ℕ) (S : K[X]) : K[X] := X^i * hasseDeriv i S

private theorem coeff_scaled (i : ℕ) (S : K[X]) (n : ℕ) :
    (scaled i S).coeff n = (n.choose i : K) * S.coeff n := by
  by_cases h : i ≤ n
  · rw [scaled, coeff_X_pow_mul', ite_eq_left h, hasseDeriv_coeff, Nat.sub_add_cancel h]
  · have hlt : n < i := by omega
    simp [scaled, coeff_X_pow_mul', h, Nat.choose_eq_zero_of_lt hlt]

theorem euler_scaled (i : ℕ) (S : K[X]) : euler (scaled i S) =
    C (i : K) * scaled i S + C (i+1 : K) * scaled (i+1) S := by
  ext n
  simp only [coeff_euler,coeff_add,coeff_C_mul,coeff_scaled]
  have hn : n.choose i*n = i*(n.choose i)+(i+1)*(n.choose (i+1)) := by
    by_cases h : i ≤ n
    · rw [mul_comm (i+1), Nat.choose_succ_right_eq, mul_comm i,
        ← Nat.mul_add, Nat.add_sub_of_le h]
    · rw [Nat.choose_eq_zero_of_lt (by omega : n < i),
        Nat.choose_eq_zero_of_lt (by omega : n < i+1)]
      simp
  have hh : (n.choose i : K)*(n : K) =
      (i : K)*(n.choose i : K)+(i+1 : K)*(n.choose (i+1) : K) := by
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      using congrArg (fun n : ℕ => (n : K)) hn
  linear_combination S.coeff n * hh

private theorem euler_add (F G : K[X]) : euler (F+G) = euler F+euler G := by
  simp [euler,mul_add]

private theorem euler_sub (F G : K[X]) : euler (F-G) = euler F-euler G := by
  simp [euler,mul_sub]

private theorem euler_C_mul (a : K) (S : K[X]) :
    euler (C a*S) = C a*euler S := by
  simp [euler,mul_left_comm]

@[simp] theorem scaled_zero (S : K[X]) : scaled 0 S = S := by simp [scaled]

private theorem euler_self (S : K[X]) : euler S = scaled 1 S := by
  simpa using euler_scaled 0 S

theorem reduced_one (D : ℕ) (S : K[X]) :
    reduced D S 1 = scaled 1 S - C (D : K)*S := by
  simp only [reduced, dropLeading, Nat.sub_zero, euler_self]

theorem reduced_two {D : ℕ} (hd : 1 ≤ D) (S : K[X]) :
    reduced D S 2 = C 2 * scaled 2 S -
      C (2*((D : K)-1)) * scaled 1 S + C ((D : K)*((D : K)-1)) * S := by
  rw [show reduced D S 2 = dropLeading (D-1) (reduced D S 1) from rfl, reduced_one]
  simp only [dropLeading, euler_sub, euler_C_mul, euler_scaled, euler_self S]
  simp only [Nat.cast_one, map_one, Nat.cast_sub hd, map_sub, map_mul, map_ofNat, map_add]
  ring

theorem reduced_three {D : ℕ} (hd : 2 ≤ D) (S : K[X]) :
    reduced D S 3 = C 6 * scaled 3 S -
      C (6*((D : K)-2)) * scaled 2 S +
      C (3*((D : K)-1)*((D : K)-2)) * scaled 1 S -
      C ((D : K)*((D : K)-1)*((D : K)-2)) * S := by
  rw [show reduced D S 3 = dropLeading (D-2) (reduced D S 2) from rfl, reduced_two (by omega)]
  simp only [dropLeading, euler_add, euler_sub, euler_C_mul, euler_scaled, euler_self S]
  simp only [Nat.cast_ofNat, C_1, Nat.cast_sub hd, map_sub, map_mul, map_ofNat, map_add]
  simp only [Nat.cast_one, C_1]
  ring

theorem product_degree {D : ℕ} (hD : 3 ≤ D) (S : K[X]) (hS : S.natDegree ≤ D)
    (x a b c f : ℕ) :
    (X^x * S^a * (reduced D S 1)^b * (reduced D S 2)^c * (reduced D S 3)^f).natDegree ≤
       x+a*D+b*(D-1)+c*(D-2)+f*(D-3) := by
  apply natDegree_mul_le_of_le _ (natDegree_pow_le_of_le f (reduced_degree S hS hD))
  apply natDegree_mul_le_of_le _ (natDegree_pow_le_of_le c (reduced_degree S hS (by omega : 2≤D)))
  apply natDegree_mul_le_of_le _ (natDegree_pow_le_of_le b (reduced_degree S hS (by omega : 1≤D)))
  exact natDegree_mul_le_of_le (natDegree_X_pow_le _) (natDegree_pow_le_of_le a hS)

open PolynomialDifferential ReedSolomon.HiddenDerivative

def scaledVar (i : Fin 4) : DifferentialPolynomial K 3 :=
  MvPolynomial.X none ^ i.val * MvPolynomial.X (some i)

def first (D : ℕ) : DifferentialPolynomial K 3 :=
  scaledVar 1 - MvPolynomial.C (D : K) * scaledVar 0

def second (D : ℕ) : DifferentialPolynomial K 3 :=
  MvPolynomial.C (2 : K) * scaledVar 2 -
    MvPolynomial.C (2 * ((D : K) - 1)) * scaledVar 1 +
    MvPolynomial.C ((D : K) * ((D : K) - 1)) * scaledVar 0

def third (D : ℕ) : DifferentialPolynomial K 3 :=
  MvPolynomial.C (6 : K) * scaledVar 3 -
    MvPolynomial.C (6 * ((D : K) - 2)) * scaledVar 2 +
    MvPolynomial.C (3 * ((D : K) - 1) * ((D : K) - 2)) * scaledVar 1 -
    MvPolynomial.C ((D : K) * ((D : K) - 1) * ((D : K) - 2)) * scaledVar 0

def column (D x a b c f : ℕ) : DifferentialPolynomial K 3 :=
  MvPolynomial.X none ^ x * scaledVar 0 ^ a *
    first D ^ b * second D ^ c * third D ^ f

private theorem specialize_scaledVar (S : K[X]) (i : Fin 4) :
    differentialSpecializationHom S (scaledVar i) = scaled i S := by
  simp [scaledVar, scaled, differentialSpecializationHom]

theorem column_degree {D : ℕ} (hD : 3 ≤ D) (S : K[X]) (hS : S.natDegree ≤ D)
    (x a b c f : ℕ) :
    (differentialSpecialization (column D x a b c f) S).natDegree ≤
      x+a*D+b*(D-1)+c*(D-2)+f*(D-3) := by
  have hC (z : K) : differentialSpecializationHom (d := 3) S (MvPolynomial.C z) = C z :=
    differentialSpecialization_C z S
  have hX : differentialSpecializationHom (d := 3) S (MvPolynomial.X none) = X :=
    differentialSpecialization_x S
  have h0 : differentialSpecializationHom S (scaledVar 0) = S :=
    (specialize_scaledVar S 0).trans (scaled_zero S)
  have hi1 : (1 : Fin 4).val = 1 := rfl
  have hi2 : (2 : Fin 4).val = 2 := rfl
  have hi3 : (3 : Fin 4).val = 3 := rfl
  have h1 : differentialSpecializationHom S (first D) = reduced D S 1 := by
    rw [first, reduced_one]
    simp only [map_sub, map_mul, hC, h0, specialize_scaledVar, hi1]
  have h2 : differentialSpecializationHom S (second D) = reduced D S 2 := by
    rw [second, reduced_two (show 1 ≤ D by omega)]
    simp only [map_add, map_sub, map_mul, hC, h0, specialize_scaledVar, hi1, hi2]
  have h3 : differentialSpecializationHom S (third D) = reduced D S 3 := by
    rw [third, reduced_three (show 2 ≤ D by omega)]
    simp only [map_add, map_sub, map_mul, hC, h0, specialize_scaledVar, hi1, hi2, hi3]
  unfold differentialSpecialization column
  simp only [map_mul, map_pow, hX, h0, h1, h2, h3]
  exact product_degree hD S hS x a b c f

theorem contact_zero {ι : Type*} [IsDomain K] {m A d : ℕ}
    (points received : ι → K) (indices : Finset ι) {Q : DifferentialPolynomial K d}
    (P : K[X]) (hdegree : (differentialSpecialization Q P).natDegree < m * A)
    (hconstraints : ∀ i ∈ indices, SatisfiesLocalConstraints m (points i) (received i) Q)
    (hpoints : Set.InjOn points (indices : Set ι)) (hcard : A ≤ indices.card)
    (hagreements : ∀ i ∈ indices, P.eval (points i) = received i) :
    differentialSpecialization Q P = 0 :=
  eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn points indices m A hpoints hcard
    (fun i hi => X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P (points i) (received i)
      (hagreements i hi) (hconstraints i hi)) hdegree

#print axioms product_degree
#print axioms column_degree
#print axioms contact_zero

end
end Low48EulerJets
