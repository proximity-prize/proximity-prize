import ProximityPrize.SubmissionLower.BCHKSCyclicNormSpecialization6400

/-!
# Production rank-one cyclic-norm split

This module connects the abstract specialization lemmas to the actual
score-64 primitive quotient triple.

For an asymmetric quotient direction, norm-zero owners are charged to the
leading challenge coefficient of the ordinary lane.  For a common factor of
locator degree at least `11632` and a direction no larger than the Frobenius
lane, every retained shell owner is forced into the norm-zero branch.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneNormSplit6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSErrorEvaluatorSemilinear6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSCyclicNormSpecialization6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

private abbrev CramerChallengeCap : Nat := 76779 * 2130706433

/-- In the production quotient, an ordinary direction strictly larger than
the Frobenius direction has at most one Cramer budget of norm-zero owners. -/
theorem score6400_rankOne_normEqual_filter_card_le_of_degree_gt
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B : IRSProfile.Field[X][X])
    (T : Finset IRSProfile.Field)
    (hqdegree : ∀ n, (q n).natDegree ≤ CramerChallengeCap)
    (hHpositive : 0 < H.natDegree)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A)
    (hA : A ≠ 0)
    (hdegree : B.natDegree < A.natDegree) :
    (T.filter (fun z ↦
      koalaCyclicNormSix (A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix (B.map (Polynomial.evalRingHom z)))).card ≤
      CramerChallengeCap := by
  have hH : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHpositive
    simp at hHpositive
  have hchallenge : A.leadingCoeff.natDegree ≤ CramerChallengeCap := by
    simpa only [Polynomial.leadingCoeff] using
      (quotient_coeff_natDegree_le
        (score6400PolynomialLocatorRelationPair q).1.1 H A
        CramerChallengeCap A.natDegree hAfactor hH hA
        (fun n ↦
          score6400PolynomialLocatorRelationPair_fst_coeff_natDegree_le
            q CramerChallengeCap n hqdegree))
  exact cyclicNormEqual_filter_card_le_of_natDegree_lt
    A B T CramerChallengeCap hA hdegree hchallenge

/-- Production degree accounting for the Frobenius quotient lane. -/
theorem score6400_frobeniusQuotient_degree_add_factor_le
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H B : IRSProfile.Field[X][X])
    (hH : H ≠ 0) (hB : B ≠ 0)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B) :
    H.natDegree + B.natDegree ≤ 22488 := by
  have hBraw :
      (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0 := by
    rw [hBfactor]
    exact mul_ne_zero hH hB
  have hBrawDegree :
      (score6400PolynomialLocatorRelationPair q).2.1.natDegree <
        locatorFrobeniusRows6400 := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hBraw]
    exact Polynomial.mem_degreeLT.mp
      (score6400PolynomialLocatorRelationPair q).2.2
  have hfactorDegree := congrArg Polynomial.natDegree hBfactor
  rw [Polynomial.natDegree_mul hH hB] at hfactorDegree
  norm_num [locatorFrobeniusRows6400] at hBrawDegree
  omega

/-- If the selected common factor is large and the primitive ordinary lane
is no larger than the primitive Frobenius lane, every retained shell owner
has equal specialized cyclic norms.  Thus the nonzero-norm branch is closed
in this exact production range. -/
theorem score6400_rankOne_specializedNorm_eq_of_largeFactor
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (T : Finset IRSProfile.Field)
    (hHpositive : 0 < H.natDegree)
    (hHlarge : 11632 ≤ H.natDegree)
    (hB : B ≠ 0)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B)
    (hAdegree : A.natDegree ≤ B.natDegree)
    (hFixed : Fixed.card ≤ H.natDegree)
    (hrelations :
      ∀ z ∈ T,
        ∀ Agree : Finset IRSProfile.Index, ∀ P : IRSProfile.Field[X],
          185364 ≤ Agree.card →
          P.natDegree ≤ 131071 →
          (∀ i ∈ Agree,
            P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) →
          ∀ i, i ∉ Fixed →
            (A.map (Polynomial.evalRingHom z)).eval
                  (IRSProfile.domain i) *
                ((f₀ i + z * f₁ i) -
                  P.eval (IRSProfile.domain i)) +
              (B.map (Polynomial.evalRingHom z)).eval
                  (IRSProfile.domain i) *
                (koalaSexticFrobenius (f₀ i + z * f₁ i) -
                  (P.map koalaSexticFrobenius.toRingHom).eval
                    (IRSProfile.domain i)) = 0)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∀ z ∈ T,
      koalaCyclicNormSix (A.map (Polynomial.evalRingHom z)) =
        koalaCyclicNormSix (B.map (Polynomial.evalRingHom z)) := by
  have hH : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHpositive
    simp at hHpositive
  have hdegreeBudget : H.natDegree + B.natDegree ≤ 22488 :=
    score6400_frobeniusQuotient_degree_add_factor_le
      q H B hH hB hBfactor
  intro z hz
  obtain ⟨Agree, P, E, hAgreeCard, hPdegree, hagree,
      _hunexplained, hEdef, hElower, _hEupper⟩ :=
    exists_score6400_large_error_witness
      f₀ f₁ z (hbad z hz) (hnotOld z hz)
  let Az : IRSProfile.Field[X] :=
    A.map (Polynomial.evalRingHom z)
  let Bz : IRSProfile.Field[X] :=
    B.map (Polynomial.evalRingHom z)
  obtain ⟨D, _hfactor, _hD, _hDdegree, hDnonzero, hsemilinear⟩ :=
    exists_score6400_semilinear_errorEvaluator
      f₀ f₁ z P E Fixed Az Bz hPdegree hEdef hElower
        (hrelations z hz Agree P hAgreeCard hPdegree hagree)
  have hAzdegree : Az.natDegree ≤ B.natDegree :=
    Polynomial.natDegree_map_le.trans hAdegree
  have hBzdegree : Bz.natDegree ≤ B.natDegree :=
    Polynomial.natDegree_map_le
  exact score6400_cyclicNorm_eq_of_largeFixedFactor
    E Fixed Az Bz D H.natDegree B.natDegree
      hElower hFixed hHlarge hdegreeBudget hAzdegree hBzdegree
      hDnonzero hsemilinear

theorem score6400_rankOne_normExceptional_budget_lt_ownerFloor :
    CramerChallengeCap < ownerFloor := by
  norm_num [CramerChallengeCap, ownerFloor]

end BCHKSRankOneNormSplit6400
end ProximityPrize.SubmissionLower
