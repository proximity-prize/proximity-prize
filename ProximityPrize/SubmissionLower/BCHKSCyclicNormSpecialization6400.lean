import ProximityPrize.SubmissionLower.BCHKSCyclicNormErrorEvaluator6400

/-!
# Specialization splits for the score-64 cyclic norm

The cyclic norm obstruction has two useful consequences before any global
Hilbert--90 argument is attempted.

* If the ordinary bivariate quotient lane has larger locator degree than the
  Frobenius lane, every specialization with equal cyclic norms is a zero of
  the ordinary leading challenge coefficient.  Thus this part of an owner
  family costs only one Cramer challenge-degree budget.
* If both specialized lanes have degree at most `d`, an error locator with
  more than `6*d` roots forces the two cyclic norms to be equal.  At the
  production caps this eliminates the nonzero-norm branch whenever the
  common locator factor has degree at least `11632` and the ordinary quotient
  direction is no larger than the Frobenius direction.

These are genuine complementary subcase closures.  They deliberately do not
claim that the remaining norm-zero, varying-gauge family is already aligned.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSCyclicNormSpecialization6400

open Polynomial
open Polynomial.Bivariate
open ProximityPrize.Benchmark
open BCHKSErrorEvaluatorSemilinear6400
open BCHKSCyclicNormErrorEvaluator6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- Every coefficient of a nonzero factor inherits a uniform challenge-degree
cap from the product. -/
theorem quotient_coeff_natDegree_le
    (P H Q : IRSProfile.Field[X][X]) (S n : Nat)
    (hfactor : P = H * Q) (hH : H ≠ 0) (hQ : Q ≠ 0)
    (hcoeff : ∀ j, (P.coeff j).natDegree ≤ S) :
    (Q.coeff n).natDegree ≤ S := by
  have hPdegree : degreeX P ≤ S :=
    degreeX_le_of_coeff_natDegree_le P S hcoeff
  have hmul : degreeX (H * Q) = degreeX H + degreeX Q :=
    Polynomial.Bivariate.degreeX_mul H Q hH hQ
  have hQdegree : degreeX Q ≤ S := by
    rw [hfactor, hmul] at hPdegree
    omega
  exact (Polynomial.Bivariate.coeff_natDegree_le_degreeX Q n).trans
    hQdegree

/-- If specialization preserves the leading coefficient of the larger lane,
equal cyclic norms would force an impossible specialized degree equality. -/
theorem leadingCoeff_eval_eq_zero_of_cyclicNorm_eq_of_natDegree_lt
    (A B : IRSProfile.Field[X][X]) (z : IRSProfile.Field)
    (hdegree : B.natDegree < A.natDegree)
    (hnorm :
      koalaCyclicNormSix (A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix (B.map (Polynomial.evalRingHom z))) :
    A.leadingCoeff.eval z = 0 := by
  by_contra hlead
  let Az : IRSProfile.Field[X] :=
    A.map (Polynomial.evalRingHom z)
  let Bz : IRSProfile.Field[X] :=
    B.map (Polynomial.evalRingHom z)
  have hlead' :
      Polynomial.evalRingHom z A.leadingCoeff ≠ 0 := by
    change A.leadingCoeff.eval z ≠ 0
    exact hlead
  have hAzDegree : Az.natDegree = A.natDegree := by
    exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero
      (Polynomial.evalRingHom z) hlead'
  have hAz : Az ≠ 0 := by
    intro hzero
    have hzeroDegree : Az.natDegree = 0 := by simp only [hzero, natDegree_zero]
    have hApositive : 0 < A.natDegree := by omega
    omega
  have hnorm' : koalaCyclicNormSix Az = koalaCyclicNormSix Bz := by
    simpa only [Az, Bz] using hnorm
  have hNormAz : koalaCyclicNormSix Az ≠ 0 :=
    koalaCyclicNormSix_ne_zero Az hAz
  have hNormBz : koalaCyclicNormSix Bz ≠ 0 := by
    rw [← hnorm']
    exact hNormAz
  have hBz : Bz ≠ 0 := by
    intro hzero
    apply hNormBz
    simp only [hzero, koalaCyclicNormSix, koalaFrobeniusConjugate,
      Polynomial.map_zero, zero_mul]
  have hnormDegree := congrArg Polynomial.natDegree hnorm'
  rw [koalaCyclicNormSix_natDegree Az hAz,
    koalaCyclicNormSix_natDegree Bz hBz, hAzDegree] at hnormDegree
  have hBzDegree : Bz.natDegree ≤ B.natDegree :=
    Polynomial.natDegree_map_le
  omega

/-- Consequently, the equal-norm specializations of an asymmetric bivariate
pair are all roots of one nonzero challenge polynomial. -/
theorem cyclicNormEqual_filter_card_le_of_natDegree_lt
    (A B : IRSProfile.Field[X][X]) (T : Finset IRSProfile.Field) (S : Nat)
    (hA : A ≠ 0) (hdegree : B.natDegree < A.natDegree)
    (hchallenge : A.leadingCoeff.natDegree ≤ S) :
    (T.filter (fun z ↦
      koalaCyclicNormSix (A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix (B.map (Polynomial.evalRingHom z)))).card ≤ S := by
  classical
  let zeroSet := T.filter (fun z ↦
    koalaCyclicNormSix (A.map (Polynomial.evalRingHom z)) =
      koalaCyclicNormSix (B.map (Polynomial.evalRingHom z)))
  have hlead : A.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hA
  have hsubset : zeroSet ⊆ A.leadingCoeff.roots.toFinset := by
    intro z hz
    have hzNorm := (Finset.mem_filter.mp hz).2
    have hzRoot :=
      leadingCoeff_eval_eq_zero_of_cyclicNorm_eq_of_natDegree_lt
        A B z hdegree hzNorm
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hlead]
    exact hzRoot
  change zeroSet.card ≤ S
  calc
    zeroSet.card ≤ A.leadingCoeff.roots.toFinset.card :=
      Finset.card_le_card hsubset
    _ ≤ A.leadingCoeff.roots.card := Multiset.toFinset_card_le _
    _ ≤ A.leadingCoeff.natDegree := Polynomial.card_roots' _
    _ ≤ S := hchallenge

/-- The preceding result as the exact degree-or-small-exception dichotomy
used by the production rank-one branch. -/
theorem cyclicNormEqual_degree_or_card_le
    (A B : IRSProfile.Field[X][X]) (T : Finset IRSProfile.Field) (S : Nat)
    (hA : A ≠ 0) (hchallenge : A.leadingCoeff.natDegree ≤ S) :
    A.natDegree ≤ B.natDegree ∨
      (T.filter (fun z ↦
        koalaCyclicNormSix (A.map (Polynomial.evalRingHom z)) =
          koalaCyclicNormSix (B.map (Polynomial.evalRingHom z)))).card ≤ S := by
  by_cases hdegree : A.natDegree ≤ B.natDegree
  · exact Or.inl hdegree
  · exact Or.inr (cyclicNormEqual_filter_card_le_of_natDegree_lt
      A B T S hA (Nat.lt_of_not_ge hdegree) hchallenge)

/-- The cyclic norm has degree at most six times the input degree, including
the zero-polynomial case. -/
theorem koalaCyclicNormSix_natDegree_le (P : IRSProfile.Field[X]) :
    (koalaCyclicNormSix P).natDegree ≤ 6 * P.natDegree := by
  by_cases hP : P = 0
  · simp [hP, koalaCyclicNormSix, koalaFrobeniusConjugate]
  · exact (koalaCyclicNormSix_natDegree P hP).le

/-- More locator roots than the maximum norm-difference degree force the
norm obstruction to vanish identically. -/
theorem koalaCyclicNormSix_eq_of_locator_card_gt_six_mul
    (E Fixed : Finset IRSProfile.Index)
    (A B D : IRSProfile.Field[X]) (d : Nat)
    (hAdegree : A.natDegree ≤ d) (hBdegree : B.natDegree ≤ d)
    (hDnonzero : ∀ i, i ∈ E → D.eval (IRSProfile.domain i) ≠ 0)
    (hsemilinear :
      outsideAgreementLocator IRSProfile.domain E Fixed ∣
        A * D + B * D.map koalaSexticFrobenius.toRingHom)
    (hroom : 6 * d < (E \ Fixed).card) :
    koalaCyclicNormSix A = koalaCyclicNormSix B := by
  have hdiv := koalaCyclicNormSix_locator_dvd E Fixed A B D
    hDnonzero hsemilinear
  by_contra hnorm
  have hdiff : koalaCyclicNormSix A - koalaCyclicNormSix B ≠ 0 := by
    simpa only [sub_ne_zero] using hnorm
  have hlower :
      (E \ Fixed).card ≤
        (koalaCyclicNormSix A - koalaCyclicNormSix B).natDegree := by
    rw [← outsideAgreementLocator_natDegree IRSProfile.domain E Fixed]
    exact Polynomial.natDegree_le_of_dvd hdiv hdiff
  have hupper :
      (koalaCyclicNormSix A - koalaCyclicNormSix B).natDegree ≤
        6 * d := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    apply max_le
    · exact (koalaCyclicNormSix_natDegree_le A).trans
        (Nat.mul_le_mul_left 6 hAdegree)
    · exact (koalaCyclicNormSix_natDegree_le B).trans
        (Nat.mul_le_mul_left 6 hBdegree)
  omega

/-- Exact production arithmetic for the low-direction, large-common-factor
subcase.  It rules out a nonzero cyclic norm obstruction without replacing
the still-open varying-gauge norm-zero branch. -/
theorem score6400_cyclicNorm_eq_of_largeFixedFactor
    (E Fixed : Finset IRSProfile.Index)
    (A B D : IRSProfile.Field[X]) (h d : Nat)
    (hElower : 76771 ≤ E.card)
    (hFixed : Fixed.card ≤ h)
    (hlarge : 11632 ≤ h)
    (hdegreeBudget : h + d ≤ 22488)
    (hAdegree : A.natDegree ≤ d) (hBdegree : B.natDegree ≤ d)
    (hDnonzero : ∀ i, i ∈ E → D.eval (IRSProfile.domain i) ≠ 0)
    (hsemilinear :
      outsideAgreementLocator IRSProfile.domain E Fixed ∣
        A * D + B * D.map koalaSexticFrobenius.toRingHom) :
    koalaCyclicNormSix A = koalaCyclicNormSix B := by
  have hsplit := Finset.card_sdiff_add_card_inter E Fixed
  have hinter : (E ∩ Fixed).card ≤ Fixed.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hroom : 6 * d < (E \ Fixed).card := by
    omega
  exact koalaCyclicNormSix_eq_of_locator_card_gt_six_mul
    E Fixed A B D d hAdegree hBdegree hDnonzero hsemilinear hroom

theorem score6400_largeFactor_norm_room_exact :
    6 * (22488 - 11632) < 76771 - 11632 := by
  norm_num

end BCHKSCyclicNormSpecialization6400
end ProximityPrize.SubmissionLower
