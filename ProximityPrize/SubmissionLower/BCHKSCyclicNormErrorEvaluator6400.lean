import ProximityPrize.SubmissionLower.BCHKSErrorEvaluatorSemilinear6400

/-!
# Cyclic Frobenius elimination for the score-64 error evaluator

The production coefficient field has degree six over KoalaBear.  Following
the semilinear evaluator equation around its six Frobenius conjugates makes
the unknown error evaluator cancel.  Consequently every genuine error
outside the fixed-coordinate defect is a root of

`Norm₆(A) - Norm₆(B)`.

This file verifies the order-six field identity, the scalar cyclic
cancellation, its polynomial specialization, and the resulting root-count
dichotomy.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSCyclicNormErrorEvaluator6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSErrorEvaluatorSemilinear6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

local instance : CharP IRSProfile.Field 2130706433 :=
  koalaSexticChar

local instance : Fact (Nat.Prime 2130706433) :=
  koalaPrimeFact

/-- The characteristic Frobenius has order dividing six on the production
sextic field. -/
theorem koalaSexticFrobenius_six_apply
    (x : IRSProfile.Field) :
    (koalaSexticFrobenius^[6]) x = x := by
  have hiterate :
      (koalaSexticFrobenius^[6]) x = x ^ 2130706433 ^ 6 := by
    simpa only [koalaSexticFrobenius, coe_frobeniusEquiv] using
      (iterate_frobenius (R := IRSProfile.Field) 2130706433 6 x)
  rw [hiterate]
  have hcard : Fintype.card IRSProfile.Field = 2130706433 ^ 6 := by
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]
  rw [← hcard]
  exact FiniteField.pow_card x

private def cyclicProductSix {F : Type*} (sigma : F → F) (x : F) [Mul F] : F :=
  x * sigma x * sigma (sigma x) * sigma (sigma (sigma x)) *
    sigma (sigma (sigma (sigma x))) *
      sigma (sigma (sigma (sigma (sigma x))))

private theorem cyclicProductSix_eq_of_semilinear
    {F : Type*} [Field F] (sigma : F ≃+* F)
    (hcycle : ∀ x, sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (a b d : F) (hd : d ≠ 0)
    (h : a * d + b * sigma d = 0) :
    cyclicProductSix sigma a = cyclicProductSix sigma b := by
  have h0 : a * d = -(b * sigma d) := by
    linear_combination h
  have h1 := congrArg sigma h0
  simp only [map_mul, map_neg] at h1
  have h2 := congrArg sigma h1
  simp only [map_mul, map_neg] at h2
  have h3 := congrArg sigma h2
  simp only [map_mul, map_neg] at h3
  have h4 := congrArg sigma h3
  simp only [map_mul, map_neg] at h4
  have h5 := congrArg sigma h4
  simp only [map_mul, map_neg] at h5
  have hd1 : sigma d ≠ 0 := by simpa using hd
  have hd2 : sigma (sigma d) ≠ 0 := by simpa using hd1
  have hd3 : sigma (sigma (sigma d)) ≠ 0 := by simpa using hd2
  have hd4 : sigma (sigma (sigma (sigma d))) ≠ 0 := by simpa using hd3
  have hd5 : sigma (sigma (sigma (sigma (sigma d)))) ≠ 0 := by
    simpa using hd4
  have hdprod : cyclicProductSix sigma d ≠ 0 := by
    dsimp only [cyclicProductSix]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero hd hd1) hd2) hd3) hd4) hd5
  apply mul_right_cancel₀ hdprod
  dsimp only [cyclicProductSix]
  calc
    (a * sigma a * sigma (sigma a) * sigma (sigma (sigma a)) *
          sigma (sigma (sigma (sigma a))) *
            sigma (sigma (sigma (sigma (sigma a))))) *
        (d * sigma d * sigma (sigma d) * sigma (sigma (sigma d)) *
          sigma (sigma (sigma (sigma d))) *
            sigma (sigma (sigma (sigma (sigma d))))) =
      (a * d) * (sigma a * sigma d) *
        (sigma (sigma a) * sigma (sigma d)) *
        (sigma (sigma (sigma a)) * sigma (sigma (sigma d))) *
        (sigma (sigma (sigma (sigma a))) *
          sigma (sigma (sigma (sigma d)))) *
        (sigma (sigma (sigma (sigma (sigma a)))) *
          sigma (sigma (sigma (sigma (sigma d))))) := by ring
    _ = (-(b * sigma d)) *
        (-(sigma b * sigma (sigma d))) *
        (-(sigma (sigma b) * sigma (sigma (sigma d)))) *
        (-(sigma (sigma (sigma b)) *
          sigma (sigma (sigma (sigma d))))) *
        (-(sigma (sigma (sigma (sigma b))) *
          sigma (sigma (sigma (sigma (sigma d)))))) *
        (-(sigma (sigma (sigma (sigma (sigma b)))) * d)) := by
      rw [h0, h1, h2, h3, h4, h5, hcycle d]
    _ = (b * sigma b * sigma (sigma b) * sigma (sigma (sigma b)) *
          sigma (sigma (sigma (sigma b))) *
            sigma (sigma (sigma (sigma (sigma b))))) *
        (d * sigma d * sigma (sigma d) * sigma (sigma (sigma d)) *
          sigma (sigma (sigma (sigma d))) *
            sigma (sigma (sigma (sigma (sigma d))))) := by ring

noncomputable def koalaFrobeniusConjugate :
    ℕ → IRSProfile.Field[X] → IRSProfile.Field[X]
  | 0, P => P
  | n + 1, P =>
      (koalaFrobeniusConjugate n P).map
        koalaSexticFrobenius.toRingHom

noncomputable def koalaCyclicNormSix (P : IRSProfile.Field[X]) :
    IRSProfile.Field[X] :=
  koalaFrobeniusConjugate 0 P *
    koalaFrobeniusConjugate 1 P *
    koalaFrobeniusConjugate 2 P *
    koalaFrobeniusConjugate 3 P *
    koalaFrobeniusConjugate 4 P *
    koalaFrobeniusConjugate 5 P

theorem koalaFrobeniusConjugate_eval_of_fixed
    (P : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hx : koalaSexticFrobenius x = x) (n : ℕ) :
    (koalaFrobeniusConjugate n P).eval x =
      (koalaSexticFrobenius^[n]) (P.eval x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate,
        polynomial_map_eval_of_fixed_locator
          koalaSexticFrobenius _ x hx,
        ih, Function.iterate_succ_apply']

theorem koalaCyclicNormSix_eval_of_fixed
    (P : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hx : koalaSexticFrobenius x = x) :
    (koalaCyclicNormSix P).eval x =
      cyclicProductSix koalaSexticFrobenius (P.eval x) := by
  simp only [koalaCyclicNormSix, Polynomial.eval_mul,
    koalaFrobeniusConjugate_eval_of_fixed P x hx]
  simp only [Function.iterate_zero_apply, Function.iterate_succ_apply']
  rfl

theorem koalaCyclicNormSix_eval_eq_of_semilinear
    (A B D : IRSProfile.Field[X]) (x : IRSProfile.Field)
    (hx : koalaSexticFrobenius x = x)
    (hD : D.eval x ≠ 0)
    (hsemilinear :
      (A * D + B * D.map koalaSexticFrobenius.toRingHom).eval x = 0) :
    (koalaCyclicNormSix A).eval x =
      (koalaCyclicNormSix B).eval x := by
  have hscalar :
      A.eval x * D.eval x +
        B.eval x * koalaSexticFrobenius (D.eval x) = 0 := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      polynomial_map_eval_of_fixed_locator
        koalaSexticFrobenius D x hx] at hsemilinear
    exact hsemilinear
  rw [koalaCyclicNormSix_eval_of_fixed A x hx,
    koalaCyclicNormSix_eval_of_fixed B x hx]
  apply cyclicProductSix_eq_of_semilinear koalaSexticFrobenius
    (fun y => ?_) (A.eval x) (B.eval x) (D.eval x) hD hscalar
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    using koalaSexticFrobenius_six_apply y

theorem koalaCyclicNormSix_locator_dvd
    (E Fixed : Finset IRSProfile.Index)
    (A B D : IRSProfile.Field[X])
    (hDnonzero : ∀ i ∈ E, D.eval (IRSProfile.domain i) ≠ 0)
    (hsemilinear :
      outsideAgreementLocator IRSProfile.domain E Fixed ∣
        A * D + B * D.map koalaSexticFrobenius.toRingHom) :
    outsideAgreementLocator IRSProfile.domain E Fixed ∣
      koalaCyclicNormSix A - koalaCyclicNormSix B := by
  classical
  obtain ⟨Cof, hfactor⟩ := hsemilinear
  apply outsideAgreementLocator_dvd
  intro i hiE hiFixed
  have hilocator :
      (outsideAgreementLocator IRSProfile.domain E Fixed).eval
          (IRSProfile.domain i) = 0 := by
    apply Lagrange.eval_nodal_at_node
    exact Finset.mem_sdiff.mpr ⟨hiE, hiFixed⟩
  have hsemieval :
      (A * D + B * D.map koalaSexticFrobenius.toRingHom).eval
          (IRSProfile.domain i) = 0 := by
    rw [hfactor, Polynomial.eval_mul, hilocator, zero_mul]
  have hnorm := koalaCyclicNormSix_eval_eq_of_semilinear A B D
    (IRSProfile.domain i) (koalaSexticFrobenius_fixed_domain i)
    (hDnonzero i hiE) hsemieval
  rw [Polynomial.eval_sub, hnorm, sub_self]

theorem koalaFrobeniusConjugate_ne_zero
    (P : IRSProfile.Field[X]) (hP : P ≠ 0) (n : ℕ) :
    koalaFrobeniusConjugate n P ≠ 0 := by
  induction n with
  | zero => exact hP
  | succ n ih =>
      rw [koalaFrobeniusConjugate]
      exact Polynomial.map_ne_zero ih

theorem koalaFrobeniusConjugate_natDegree
    (P : IRSProfile.Field[X]) (n : ℕ) :
    (koalaFrobeniusConjugate n P).natDegree = P.natDegree := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [koalaFrobeniusConjugate, Polynomial.natDegree_map, ih]

theorem koalaCyclicNormSix_ne_zero
    (P : IRSProfile.Field[X]) (hP : P ≠ 0) :
    koalaCyclicNormSix P ≠ 0 := by
  dsimp only [koalaCyclicNormSix]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero
      (koalaFrobeniusConjugate_ne_zero P hP 0)
      (koalaFrobeniusConjugate_ne_zero P hP 1))
    (koalaFrobeniusConjugate_ne_zero P hP 2))
    (koalaFrobeniusConjugate_ne_zero P hP 3))
    (koalaFrobeniusConjugate_ne_zero P hP 4))
    (koalaFrobeniusConjugate_ne_zero P hP 5)

theorem koalaCyclicNormSix_natDegree
    (P : IRSProfile.Field[X]) (hP : P ≠ 0) :
    (koalaCyclicNormSix P).natDegree = 6 * P.natDegree := by
  rw [koalaCyclicNormSix,
    Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (koalaFrobeniusConjugate_ne_zero P hP 0)
        (koalaFrobeniusConjugate_ne_zero P hP 1))
        (koalaFrobeniusConjugate_ne_zero P hP 2))
        (koalaFrobeniusConjugate_ne_zero P hP 3))
        (koalaFrobeniusConjugate_ne_zero P hP 4))
      (koalaFrobeniusConjugate_ne_zero P hP 5),
    Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (koalaFrobeniusConjugate_ne_zero P hP 0)
        (koalaFrobeniusConjugate_ne_zero P hP 1))
        (koalaFrobeniusConjugate_ne_zero P hP 2))
        (koalaFrobeniusConjugate_ne_zero P hP 3))
      (koalaFrobeniusConjugate_ne_zero P hP 4),
    Polynomial.natDegree_mul
      (mul_ne_zero (mul_ne_zero
        (koalaFrobeniusConjugate_ne_zero P hP 0)
        (koalaFrobeniusConjugate_ne_zero P hP 1))
        (koalaFrobeniusConjugate_ne_zero P hP 2))
      (koalaFrobeniusConjugate_ne_zero P hP 3),
    Polynomial.natDegree_mul
      (mul_ne_zero
        (koalaFrobeniusConjugate_ne_zero P hP 0)
        (koalaFrobeniusConjugate_ne_zero P hP 1))
      (koalaFrobeniusConjugate_ne_zero P hP 2),
    Polynomial.natDegree_mul
      (koalaFrobeniusConjugate_ne_zero P hP 0)
      (koalaFrobeniusConjugate_ne_zero P hP 1)]
  simp only [koalaFrobeniusConjugate_natDegree]
  omega

theorem koalaCyclicNormSix_sub_natDegree_le
    (A B : IRSProfile.Field[X]) (hA : A ≠ 0) (hB : B ≠ 0) :
    (koalaCyclicNormSix A - koalaCyclicNormSix B).natDegree ≤
      6 * max A.natDegree B.natDegree := by
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  rw [koalaCyclicNormSix_natDegree A hA,
    koalaCyclicNormSix_natDegree B hB]
  omega

theorem score6400_koalaCyclicNormSix_dichotomy
    (E Fixed : Finset IRSProfile.Index)
    (A B D : IRSProfile.Field[X])
    (hElower : 76771 ≤ E.card)
    (hFixed : Fixed.card ≤ 22488)
    (hDnonzero : ∀ i ∈ E, D.eval (IRSProfile.domain i) ≠ 0)
    (hsemilinear :
      outsideAgreementLocator IRSProfile.domain E Fixed ∣
        A * D + B * D.map koalaSexticFrobenius.toRingHom) :
    koalaCyclicNormSix A = koalaCyclicNormSix B ∨
      54283 ≤
        (koalaCyclicNormSix A - koalaCyclicNormSix B).natDegree := by
  have hdiv := koalaCyclicNormSix_locator_dvd E Fixed A B D
    hDnonzero hsemilinear
  by_cases hzero :
      koalaCyclicNormSix A - koalaCyclicNormSix B = 0
  · exact Or.inl (sub_eq_zero.mp hzero)
  · right
    calc
      54283 ≤ (E \ Fixed).card :=
        score6400_errorOutsideFixed_card_lower E Fixed hElower hFixed
      _ = (outsideAgreementLocator IRSProfile.domain E Fixed).natDegree := by
        rw [outsideAgreementLocator_natDegree]
      _ ≤ (koalaCyclicNormSix A - koalaCyclicNormSix B).natDegree :=
        Polynomial.natDegree_le_of_dvd hdiv hzero

end BCHKSCyclicNormErrorEvaluator6400
end ProximityPrize.SubmissionLower
