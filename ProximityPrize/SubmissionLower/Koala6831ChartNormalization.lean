import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace ProximityPrize.SubmissionLower.Koala6831ChartNormalization

open Polynomial
open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {K : Type*} [Field K]

private theorem coeff_mul_of_lower_vanish {f g : Polynomial K} {n : ℕ}
    (hlower : ∀ k < n, f.coeff k = 0) : (f * g).coeff n = f.coeff n * g.coeff 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (n, 0)
  · intro ij hij hne
    have hsum := Finset.mem_antidiagonal.mp hij
    have hlt : ij.1 < n := by
      by_contra hn
      exact hne (Prod.ext (by omega) (by omega))
    rw [hlower _ hlt, zero_mul]
  · simp

private theorem map_taylor_eval (f : Polynomial (Polynomial K)) (x z : K) :
    (taylor (C x) f).map (evalRingHom z) = taylor x (f.map (evalRingHom z)) := by
  simp only [taylor_apply, map_comp, Polynomial.map_add, Polynomial.map_X,
    Polynomial.map_C, coe_evalRingHom, eval_C]

private theorem taylor_coeff_natDegree_le (f : Polynomial (Polynomial K)) (x : K)
    (k bound : ℕ) (hbound : ∀ j, (f.coeff j).natDegree ≤ bound) :
    ((taylor (C x) f).coeff k).natDegree ≤ bound := by
  rw [taylor_coeff, eval_eq_sum]
  unfold Polynomial.sum
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  change (((hasseDeriv k f).coeff j) * (C x)^j).natDegree ≤ bound
  rw [hasseDeriv_coeff]
  have hchoose : ((j + k).choose k : Polynomial K) = C (((j + k).choose k : ℕ) : K) := by
    simp
  have hpower : (C x)^j = C (x^j) := (map_pow Polynomial.C x j).symm
  rw [hchoose, hpower]
  apply (Polynomial.natDegree_mul_C_le _ _).trans
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hbound _)

theorem exists_node_tests (denominator numerator : Polynomial (Polynomial K))
    (hnonzero : denominator ≠ 0) (denominatorDegree numeratorDegree : ℕ)
    (hdenDegree : ∀ j, (denominator.coeff j).natDegree ≤ denominatorDegree)
    (hnumDegree : ∀ j, (numerator.coeff j).natDegree ≤ numeratorDegree) :
    ∃ denominatorAt numeratorAt : K → Polynomial K,
      (∀ x, denominatorAt x ≠ 0) ∧
      (∀ x, (denominatorAt x).natDegree ≤ denominatorDegree) ∧
      (∀ x, (numeratorAt x).natDegree ≤ numeratorDegree) ∧
      ∀ (x seed : K) (selected : Polynomial K),
        denominator.map (evalRingHom seed) * selected = numerator.map (evalRingHom seed) →
        (denominatorAt x).eval seed * selected.eval x = (numeratorAt x).eval seed := by
  classical
  have hexists (x : K) : ∃ k, (taylor (C x) denominator).coeff k ≠ 0 := by
    have ht : taylor (C x) denominator ≠ 0 :=
      fun h => hnonzero ((taylor_eq_zero (C x) denominator).mp h)
    obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr ht
    exact ⟨k, Polynomial.mem_support_iff.mp hk⟩
  let order (x : K) := Nat.find (hexists x)
  refine ⟨fun x => (taylor (C x) denominator).coeff (order x),
    fun x => (taylor (C x) numerator).coeff (order x),
    fun x => Nat.find_spec (hexists x),
    fun x => taylor_coeff_natDegree_le denominator x (order x) _ hdenDegree,
    fun x => taylor_coeff_natDegree_le numerator x (order x) _ hnumDegree, ?_⟩
  intro x seed selected hEq
  have hlower (k : ℕ) (hk : k < order x) :
      (taylor x (denominator.map (evalRingHom seed))).coeff k = 0 := by
    have hz : (taylor (C x) denominator).coeff k = 0 := by
      by_contra hne
      exact Nat.find_min (hexists x) hk hne
    rw [← map_taylor_eval, coeff_map, hz, map_zero]
  have heq := congrArg (fun f => (taylor x f).coeff (order x)) hEq
  rw [taylor_mul, coeff_mul_of_lower_vanish hlower, taylor_coeff_zero,
    ← map_taylor_eval denominator x seed, ← map_taylor_eval numerator x seed,
    coeff_map, coeff_map] at heq
  exact heq

end

end ProximityPrize.SubmissionLower.Koala6831ChartNormalization
