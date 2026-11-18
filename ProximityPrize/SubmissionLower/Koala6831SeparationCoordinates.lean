import ProximityPrize.SubmissionLower.Koala6831CoefficientSystem
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace ProximityPrize.SubmissionLower.Koala6831Separation

open Polynomial
open Koala6831CoefficientSystem (coefficientPolynomial)
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def regroup : (MvPolynomial (Fin 2) K)[X] →+* MvPolynomial (Fin 2) K[X] :=
  Polynomial.eval₂RingHom (MvPolynomial.map Polynomial.C) (MvPolynomial.C Polynomial.X)

@[simp] theorem regroup_C (P : MvPolynomial (Fin 2) K) :
    regroup (Polynomial.C P) = MvPolynomial.map Polynomial.C P := by simp [regroup]

@[simp] theorem regroup_X :
    regroup (Polynomial.X : (MvPolynomial (Fin 2) K)[X]) = MvPolynomial.C Polynomial.X := by
  simp [regroup]

theorem coeff_regroup_eq (P : (MvPolynomial (Fin 2) K)[X]) (m : Fin 2 →₀ ℕ) (cap : ℕ)
    (hP : P.natDegree ≤ cap) :
    (regroup P).coeff m = coefficientPolynomial P m cap := by
  change (P.eval₂ (MvPolynomial.map Polynomial.C) (MvPolynomial.C Polynomial.X)).coeff m = _
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hP), MvPolynomial.coeff_sum]
  unfold coefficientPolynomial
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_pow, mul_comm (MvPolynomial.map Polynomial.C (P.coeff i)), MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, mul_comm, Polynomial.C_mul_X_pow_eq_monomial]

private theorem coeff_coefficientPolynomial (P : (MvPolynomial (Fin 2) K)[X])
    (m : Fin 2 →₀ ℕ) (cap i : ℕ) (hP : P.natDegree ≤ cap) :
    (coefficientPolynomial P m cap).coeff i = (P.coeff i).coeff m := by
  unfold coefficientPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  by_cases hi : i ≤ cap
  · simp [hi]
  · have hzero : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (hP.trans_lt (Nat.lt_of_not_ge hi))
    simp [hi, hzero]

theorem regroup_injective : Function.Injective (regroup (K := K)) := by
  intro P Q h
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  have he := congrArg (fun f : MvPolynomial (Fin 2) K[X] ↦ (f.coeff m).coeff i) h
  have hP : P.natDegree ≤ max P.natDegree Q.natDegree := le_max_left _ _
  have hQ : Q.natDegree ≤ max P.natDegree Q.natDegree := le_max_right _ _
  simpa only [coeff_regroup_eq P m _ hP, coeff_regroup_eq Q m _ hQ,
    coeff_coefficientPolynomial P m _ i hP, coeff_coefficientPolynomial Q m _ i hQ] using he

theorem regroup_surjective : Function.Surjective (regroup (K := K)) := by
  have hconst : regroup.comp (Polynomial.mapRingHom (MvPolynomial.C :
      K →+* MvPolynomial (Fin 2) K)) = MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  intro P
  induction P using MvPolynomial.induction_on with
  | C t =>
      exact ⟨t.map MvPolynomial.C, DFunLike.congr_fun hconst t⟩
  | add P Q hP hQ =>
      obtain ⟨p, rfl⟩ := hP
      obtain ⟨q, rfl⟩ := hQ
      exact ⟨p + q, map_add _ _ _⟩
  | mul_X P i hP =>
      obtain ⟨p, rfl⟩ := hP
      refine ⟨p * Polynomial.C (MvPolynomial.X i), ?_⟩
      rw [map_mul, regroup_C, MvPolynomial.map_X]

theorem primitive_regroup (beta first second : (MvPolynomial (Fin 2) K)[X])
    (h : ∀ D, D ∣ beta → D ∣ first → D ∣ second → IsUnit D) :
    ∀ D, D ∣ regroup beta → D ∣ regroup first → D ∣ regroup second → IsUnit D := by
  intro D hβ h₁ h₂
  obtain ⟨d, rfl⟩ := regroup_surjective D
  have lift (x : (MvPolynomial (Fin 2) K)[X]) (hx : regroup d ∣ regroup x) : d ∣ x := by
    obtain ⟨q, hq⟩ := hx
    obtain ⟨p, rfl⟩ := regroup_surjective q
    exact ⟨p, regroup_injective (hq.trans (map_mul _ _ _).symm)⟩
  exact (h d (lift _ hβ) (lift _ h₁) (lift _ h₂)).map regroup

theorem map_eval_regroup (P : (MvPolynomial (Fin 2) K)[X]) (x : K) :
    MvPolynomial.map (Polynomial.evalRingHom x) (regroup P) = P.eval (MvPolynomial.C x) := by
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_map, coeff_regroup_eq P m P.natDegree le_rfl]
  exact Koala6831CoefficientSystem.eval_coefficientPolynomial P m P.natDegree x le_rfl

end ProximityPrize.SubmissionLower.Koala6831Separation
