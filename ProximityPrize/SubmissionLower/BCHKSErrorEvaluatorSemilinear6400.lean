import ProximityPrize.SubmissionLower.BCHKSPrimitiveTripleBicomponent6400
import ProximityPrize.SubmissionLower.BCHKSReedSolomonCofactor6400

/-!
# Error evaluators for the surviving score-64 semilinear branch

Interpolate the received word on the full evaluation domain.  Its difference
from a decoded owner polynomial vanishes at every genuine agreement, so the
agreement locator factors out and leaves an error evaluator `D` of degree
strictly below the number of genuine errors.  The evaluator is nonzero at
every error coordinate.

Combining this factorization with the normalized primitive-triple relation
shows that the error locator outside the fixed coordinate defect divides

`A * D + B * sigma(D)`.

This is the polynomial, multiplicity-free key equation needed before cyclic
Frobenius elimination can be applied to the remaining bicomponent branch.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSErrorEvaluatorSemilinear6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

private theorem evaluator_degree_lt_error_count
    (e d r : ℕ) (he : e ≤ 262144)
    (hdegree : (262144 - e) + d = r) (hr : r < 262144) :
    d < e := by
  omega

/-- The unique degree-below-domain-size interpolation polynomial of one
received affine word. -/
noncomputable def score6400ReceivedInterpolator
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) : IRSProfile.Field[X] :=
  Lagrange.interpolate Finset.univ
    (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
    (fun i ↦ f₀ i + z * f₁ i)

@[simp]
theorem score6400ReceivedInterpolator_eval
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (i : IRSProfile.Index) :
    (score6400ReceivedInterpolator f₀ f₁ z).eval
        (IRSProfile.domain i) = f₀ i + z * f₁ i := by
  exact Lagrange.eval_interpolate_at_node
    (fun i ↦ f₀ i + z * f₁ i)
    IRSProfile.domain.injective.injOn (Finset.mem_univ i)

theorem score6400ReceivedInterpolator_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) :
    (score6400ReceivedInterpolator f₀ f₁ z).natDegree < 262144 := by
  let W := score6400ReceivedInterpolator f₀ f₁ z
  have hcard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hdegree : W.degree <
      (Fintype.card IRSProfile.Index : WithBot ℕ) := by
    change
      (Lagrange.interpolate Finset.univ
        (fun i : IRSProfile.Index ↦ IRSProfile.domain i)
        (fun i ↦ f₀ i + z * f₁ i)).degree <
          (Fintype.card IRSProfile.Index : WithBot ℕ)
    simpa only [Finset.card_univ] using
      (Lagrange.degree_interpolate_lt
        (s := Finset.univ)
        (v := fun i : IRSProfile.Index ↦ IRSProfile.domain i)
        (fun i ↦ f₀ i + z * f₁ i)
        IRSProfile.domain.injective.injOn)
  change W.natDegree < 262144
  by_cases hW : W = 0
  · rw [hW, Polynomial.natDegree_zero]
    norm_num
  · rw [Polynomial.natDegree_lt_iff_degree_lt hW]
    rw [hcard] at hdegree
    exact hdegree

theorem score6400_received_sub_owner_natDegree_lt
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (hPdegree : P.natDegree ≤ 131071) :
    (score6400ReceivedInterpolator f₀ f₁ z - P).natDegree < 262144 := by
  apply (Polynomial.natDegree_sub_le _ _).trans_lt
  apply max_lt
  · exact score6400ReceivedInterpolator_natDegree_lt f₀ f₁ z
  · exact hPdegree.trans_lt (by norm_num)

theorem score6400_received_sub_owner_ne_zero
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (E : Finset IRSProfile.Index)
    (hEdef : E = Finset.univ.filter (fun i ↦
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0))
    (hEnonempty : E.Nonempty) :
    score6400ReceivedInterpolator f₀ f₁ z - P ≠ 0 := by
  classical
  obtain ⟨i, hiE⟩ := hEnonempty
  have hiError :
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0 := by
    rw [hEdef] at hiE
    exact (Finset.mem_filter.mp hiE).2
  intro hzero
  apply hiError
  have heval := congrArg
    (fun R : IRSProfile.Field[X] ↦ R.eval (IRSProfile.domain i)) hzero
  simpa only [Polynomial.eval_sub, score6400ReceivedInterpolator_eval,
    Polynomial.eval_zero] using heval

theorem score6400_received_sub_owner_eval_eq_zero_of_not_mem_error
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (E : Finset IRSProfile.Index)
    (hEdef : E = Finset.univ.filter (fun i ↦
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0))
    (i : IRSProfile.Index) (hiE : i ∉ E) :
    (score6400ReceivedInterpolator f₀ f₁ z - P).eval
        (IRSProfile.domain i) = 0 := by
  classical
  have hiE' := hiE
  rw [hEdef] at hiE'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    not_ne_iff] at hiE'
  simpa only [Polynomial.eval_sub, score6400ReceivedInterpolator_eval]
    using hiE'

theorem score6400_errorEvaluator_natDegree_lt
    (E : Finset IRSProfile.Index) (D R : IRSProfile.Field[X])
    (hdegree :
      ((Finset.univ : Finset IRSProfile.Index) \ E).card +
        D.natDegree = R.natDegree)
    (hRdegree : R.natDegree < 262144) :
    D.natDegree < E.card := by
  have hIndexCard : Fintype.card IRSProfile.Index = 262144 := by
    norm_num [IRSProfile.Index]
  have hEcard : E.card ≤ 262144 := by
    calc
      E.card ≤ Fintype.card IRSProfile.Index := by
        simpa only [Finset.card_univ] using Finset.card_le_univ E
      _ = 262144 := hIndexCard
  have hcomplement :
      ((Finset.univ : Finset IRSProfile.Index) \ E).card =
        262144 - E.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hIndexCard]
  have hdegree' :
      (262144 - E.card) + D.natDegree = R.natDegree := by
    simpa only [hcomplement] using hdegree
  exact evaluator_degree_lt_error_count E.card D.natDegree R.natDegree
    hEcard hdegree' hRdegree

theorem score6400_errorEvaluator_eval_ne_zero
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (E : Finset IRSProfile.Index) (D : IRSProfile.Field[X])
    (hEdef : E = Finset.univ.filter (fun i ↦
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0))
    (hfactor :
      outsideAgreementLocator IRSProfile.domain Finset.univ E * D =
        score6400ReceivedInterpolator f₀ f₁ z - P) :
    ∀ i ∈ E, D.eval (IRSProfile.domain i) ≠ 0 := by
  classical
  intro i hiE hDeval
  have hiError :
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0 := by
    have hiE' := hiE
    rw [hEdef] at hiE'
    exact (Finset.mem_filter.mp hiE').2
  apply hiError
  have heval := congrArg
    (fun R : IRSProfile.Field[X] ↦ R.eval (IRSProfile.domain i)) hfactor
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub,
    score6400ReceivedInterpolator_eval, hDeval, mul_zero] using heval.symm

/-- Factoring all actual agreement roots leaves an evaluator of degree below
the actual error count, nonvanishing at every error coordinate. -/
theorem exists_score6400_errorEvaluator
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (E : Finset IRSProfile.Index)
    (hPdegree : P.natDegree ≤ 131071)
    (hEdef : E = Finset.univ.filter (fun i ↦
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0))
    (hEnonempty : E.Nonempty) :
    ∃ D : IRSProfile.Field[X],
      outsideAgreementLocator IRSProfile.domain Finset.univ E * D =
          score6400ReceivedInterpolator f₀ f₁ z - P ∧
      D ≠ 0 ∧
      D.natDegree < E.card ∧
      ∀ i ∈ E, D.eval (IRSProfile.domain i) ≠ 0 := by
  classical
  have hdiffNe := score6400_received_sub_owner_ne_zero
    f₀ f₁ z P E hEdef hEnonempty
  have hzero : ∀ i ∈ (Finset.univ : Finset IRSProfile.Index),
      i ∉ E →
        (score6400ReceivedInterpolator f₀ f₁ z - P).eval
          (IRSProfile.domain i) = 0 := by
    intro i _hi hiE
    exact score6400_received_sub_owner_eval_eq_zero_of_not_mem_error
      f₀ f₁ z P E hEdef i hiE
  obtain ⟨D, hfactor, hDne, hdegree⟩ :=
    exists_outsideAgreementCofactor IRSProfile.domain
      (Finset.univ : Finset IRSProfile.Index) E
      (score6400ReceivedInterpolator f₀ f₁ z - P) hdiffNe hzero
  have hdiffDegree := score6400_received_sub_owner_natDegree_lt
    f₀ f₁ z P hPdegree
  have hDdegree := score6400_errorEvaluator_natDegree_lt E D
    (score6400ReceivedInterpolator f₀ f₁ z - P) hdegree hdiffDegree
  have hDnonzero := score6400_errorEvaluator_eval_ne_zero
    f₀ f₁ z P E D hEdef hfactor
  exact ⟨D, hfactor, hDne, hDdegree, hDnonzero⟩

/-- The normalized coordinate relation descends through the agreement
locator: every genuine error outside `Fixed` is a root of the semilinear
evaluator polynomial. -/
theorem semilinear_errorEvaluator_locator_dvd
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (E Fixed : Finset IRSProfile.Index)
    (A B D : IRSProfile.Field[X])
    (hEdef : E = Finset.univ.filter (fun i ↦
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0))
    (hfactor :
      outsideAgreementLocator IRSProfile.domain Finset.univ E * D =
        score6400ReceivedInterpolator f₀ f₁ z - P)
    (hrelation : ∀ i, i ∉ Fixed →
      A.eval (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        B.eval (IRSProfile.domain i) *
            (koalaSexticFrobenius (f₀ i + z * f₁ i) -
              (P.map koalaSexticFrobenius.toRingHom).eval
                (IRSProfile.domain i)) = 0) :
    outsideAgreementLocator IRSProfile.domain E Fixed ∣
      A * D + B * D.map koalaSexticFrobenius.toRingHom := by
  classical
  let L := outsideAgreementLocator IRSProfile.domain
    (Finset.univ : Finset IRSProfile.Index) E
  apply outsideAgreementLocator_dvd
  intro i hiE hiFixed
  have hiError :
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0 := by
    have hiE' := hiE
    rw [hEdef] at hiE'
    exact (Finset.mem_filter.mp hiE').2
  have hfactorEval := congrArg
    (fun R : IRSProfile.Field[X] ↦ R.eval (IRSProfile.domain i)) hfactor
  have herror :
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) =
        L.eval (IRSProfile.domain i) * D.eval (IRSProfile.domain i) := by
    simpa only [L, Polynomial.eval_mul, Polynomial.eval_sub,
      score6400ReceivedInterpolator_eval] using hfactorEval.symm
  have hLmap : L.map koalaSexticFrobenius.toRingHom = L := by
    simpa only [L] using outsideAgreementLocator_map IRSProfile.domain
      koalaSexticFrobenius koalaSexticFrobenius_fixed_domain
      (Finset.univ : Finset IRSProfile.Index) E
  have hLfixed :
      koalaSexticFrobenius (L.eval (IRSProfile.domain i)) =
        L.eval (IRSProfile.domain i) := by
    rw [← polynomial_map_eval_of_fixed_locator koalaSexticFrobenius L
      (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i), hLmap]
  have hDmap :
      (D.map koalaSexticFrobenius.toRingHom).eval
          (IRSProfile.domain i) =
        koalaSexticFrobenius (D.eval (IRSProfile.domain i)) :=
    polynomial_map_eval_of_fixed_locator koalaSexticFrobenius D
      (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i)
  have hsecond :
      koalaSexticFrobenius (f₀ i + z * f₁ i) -
          (P.map koalaSexticFrobenius.toRingHom).eval
            (IRSProfile.domain i) =
        L.eval (IRSProfile.domain i) *
          (D.map koalaSexticFrobenius.toRingHom).eval
            (IRSProfile.domain i) := by
    rw [polynomial_map_eval_of_fixed_locator koalaSexticFrobenius P
      (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i)]
    rw [← map_sub, herror, map_mul, hLfixed, ← hDmap]
  have hrel := hrelation i hiFixed
  rw [herror, hsecond] at hrel
  have hLne : L.eval (IRSProfile.domain i) ≠ 0 := by
    simpa only [L] using outsideAgreementLocator_eval_ne_zero_of_mem
      IRSProfile.domain (Finset.univ : Finset IRSProfile.Index) E hiE
  have hproduct :
      L.eval (IRSProfile.domain i) *
          (A * D + B * D.map koalaSexticFrobenius.toRingHom).eval
            (IRSProfile.domain i) = 0 := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul]
    linear_combination hrel
  exact (mul_eq_zero.mp hproduct).resolve_left hLne

/-- Complete per-owner evaluator package for the surviving branch. -/
theorem exists_score6400_semilinear_errorEvaluator
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (P : IRSProfile.Field[X])
    (E Fixed : Finset IRSProfile.Index)
    (A B : IRSProfile.Field[X])
    (hPdegree : P.natDegree ≤ 131071)
    (hEdef : E = Finset.univ.filter (fun i ↦
      (f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i) ≠ 0))
    (hElower : 76771 ≤ E.card)
    (hrelation : ∀ i, i ∉ Fixed →
      A.eval (IRSProfile.domain i) *
            ((f₀ i + z * f₁ i) - P.eval (IRSProfile.domain i)) +
        B.eval (IRSProfile.domain i) *
            (koalaSexticFrobenius (f₀ i + z * f₁ i) -
              (P.map koalaSexticFrobenius.toRingHom).eval
                (IRSProfile.domain i)) = 0) :
    ∃ D : IRSProfile.Field[X],
      outsideAgreementLocator IRSProfile.domain Finset.univ E * D =
          score6400ReceivedInterpolator f₀ f₁ z - P ∧
      D ≠ 0 ∧
      D.natDegree < E.card ∧
      (∀ i ∈ E, D.eval (IRSProfile.domain i) ≠ 0) ∧
      outsideAgreementLocator IRSProfile.domain E Fixed ∣
        A * D + B * D.map koalaSexticFrobenius.toRingHom := by
  have hEnonempty : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨D, hfactor, hDne, hDdegree, hDnonzero⟩ :=
    exists_score6400_errorEvaluator f₀ f₁ z P E
      hPdegree hEdef hEnonempty
  exact ⟨D, hfactor, hDne, hDdegree, hDnonzero,
    semilinear_errorEvaluator_locator_dvd f₀ f₁ z P E Fixed A B D
      hEdef hfactor hrelation⟩

/-- The semilinear evaluator divisor has at least `54283` distinct domain
roots once the checked bicomponent fixed-set cap is used. -/
theorem score6400_errorOutsideFixed_card_lower
    (E Fixed : Finset IRSProfile.Index)
    (hElower : 76771 ≤ E.card) (hFixed : Fixed.card ≤ 22488) :
    54283 ≤ (E \ Fixed).card := by
  have hsplit := Finset.card_sdiff_add_card_inter E Fixed
  have hinter : (E ∩ Fixed).card ≤ Fixed.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

end BCHKSErrorEvaluatorSemilinear6400
end ProximityPrize.SubmissionLower
