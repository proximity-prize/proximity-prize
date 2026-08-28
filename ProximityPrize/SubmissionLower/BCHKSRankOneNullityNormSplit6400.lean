import ProximityPrize.SubmissionLower.BCHKSRankOneBicomponentDegree6400
import ProximityPrize.SubmissionLower.BCHKSRankOneNormSplit6400

/-!
# Nullity closes the common-factor gap in the cyclic-norm branch

The original production argument forces cyclic-norm equality when the common
factor has degree at least `11632`.  The nullity rebate

```text
deg_X B' <= 22489 - L
```

forces the same conclusion in the complementary factor range once
`L >= 11633`.  Thus, for a low ordinary direction, factor size no longer
restricts the cyclic-norm conclusion in that nullity range.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneNullityNormSplit6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSErrorEvaluatorSemilinear6400
open BCHKSCyclicNormErrorEvaluator6400
open BCHKSCyclicNormSpecialization6400
open BCHKSRankOneNormSplit6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- Production semilinear relations force cyclic-norm equality whenever an
explicit degree budget fits inside the error roots outside the fixed set. -/
theorem score6400_rankOne_specializedNorm_eq_of_degreeRoom
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (A B : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (T : Finset IRSProfile.Field)
    (h d : Nat)
    (hFixed : Fixed.card ≤ h)
    (hroom : 6 * d < 76771 - h)
    (hAdegree : A.natDegree ≤ d)
    (hBdegree : B.natDegree ≤ d)
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
  have hAzdegree : Az.natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hAdegree
  have hBzdegree : Bz.natDegree ≤ d :=
    Polynomial.natDegree_map_le.trans hBdegree
  have hsplit := Finset.card_sdiff_add_card_inter E Fixed
  have hinter : (E ∩ Fixed).card ≤ Fixed.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hrootRoom : 6 * d < (E \ Fixed).card := by
    omega
  exact koalaCyclicNormSix_eq_of_locator_card_gt_six_mul
    E Fixed Az Bz D d hAzdegree hBzdegree
      hDnonzero hsemilinear hrootRoom

/-- At nullity at least `11633`, the old large-factor range and the new
dimension-degree range cover every possible positive common-factor degree. -/
theorem score6400_rankOne_specializedNorm_eq_of_nullity
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B : IRSProfile.Field[X][X])
    (Fixed : Finset IRSProfile.Index)
    (T : Finset IRSProfile.Field)
    (L : Nat)
    (hLlarge : 11633 ≤ L)
    (hHpositive : 0 < H.natDegree)
    (hB : B ≠ 0)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B)
    (hBnullity :
      B.natDegree ≤ locatorFrobeniusRows6400 - L)
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
  by_cases hHlarge : 11632 ≤ H.natDegree
  · exact score6400_rankOne_specializedNorm_eq_of_largeFactor
      f₀ f₁ q H A B Fixed T hHpositive hHlarge hB hBfactor
        hAdegree hFixed hrelations hbad hnotOld
  · have hHsmall : H.natDegree ≤ 11631 := by omega
    have hBdegree : B.natDegree ≤ 22489 - L := by
      simpa only [locatorFrobeniusRows6400] using hBnullity
    have hAdegree' : A.natDegree ≤ 22489 - L :=
      hAdegree.trans hBdegree
    have hroom :
        6 * (22489 - L) < 76771 - H.natDegree := by
      omega
    exact score6400_rankOne_specializedNorm_eq_of_degreeRoom
      f₀ f₁ A B Fixed T H.natDegree (22489 - L)
        hFixed hroom hAdegree' hBdegree hrelations hbad hnotOld

theorem score6400_nullity_factor_ranges_cover :
    ∀ L h : Nat, 11633 ≤ L → 0 < h → h ≤ 22488 →
      11632 ≤ h ∨ 6 * (22489 - L) < 76771 - h := by
  intro L h hL hpos hcap
  omega

end BCHKSRankOneNullityNormSplit6400
end ProximityPrize.SubmissionLower
