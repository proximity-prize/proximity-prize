import ProximityPrize.SubmissionLower.BCHKSBoundedCramerFamilyData6400
import ProximityPrize.SubmissionLower.BCHKSIntegralKernelPair6400
import ProximityPrize.SubmissionLower.BCHKSMultiplierFamilyAbstract6400

/-! # A multiplier for one selected rank-one Cramer pair -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneCramerMultiplierFamily6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSRationalPairKernelTransport6400

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Every selected Cramer pair in a rational-rank-one kernel is a polynomial
multiple of a fixed nonzero coprime primitive direction. -/
theorem exists_score6400_selectedCramer_multiplier
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (data : Score6400BoundedCramerFamilyData f₀ f₁ L)
    (q₀ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B : IRSProfile.Field[X][X])
    (hq₀ : q₀ ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (hH : H ≠ 0) (hB : B ≠ 0)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q₀).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q₀).2.1 = H * B)
    (hcoprime : IsCoprime
      (A.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X])))
      (B.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X]))))
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0)
    (j : SelectedColumnComplement data.cols) :
    ∃ multiplier : (FractionRing IRSProfile.Field[X])[X],
      (score6400SelectedLocatorCramerOrdinary f₀ f₁
          data.rows data.cols data.hcols j).map
            (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X])) =
        multiplier * A.map (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X])) ∧
      (score6400SelectedLocatorCramerFrobenius f₀ f₁
          data.rows data.cols data.hcols j).map
            (algebraMap IRSProfile.Field[X]
              (FractionRing IRSProfile.Field[X])) =
        multiplier * B.map (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X])) := by
  let K := FractionRing IRSProfile.Field[X]
  let iota : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let Am : K[X] := A.map iota
  let Bm : K[X] := B.map iota
  let Hm : K[X] := H.map iota
  let qj := score6400SelectedLocatorCramerVector f₀ f₁
    data.rows data.cols data.hcols j
  let hj : qj ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin := by
    simpa only [qj] using data.kernel j
  let pivot := score6400IntegralKernelPair f₀ f₁ q₀ hq₀
  let selected := score6400IntegralKernelPair f₀ f₁ qj hj
  have hiota : Function.Injective iota :=
    IsFractionRing.injective IRSProfile.Field[X] K
  have hHm : Hm ≠ 0 := by
    intro hzero
    apply hH
    apply Polynomial.map_injective iota hiota
    simpa only [Hm, Polynomial.map_zero] using hzero
  have hBm : Bm ≠ 0 := by
    intro hzero
    apply hB
    apply Polynomial.map_injective iota hiota
    simpa only [Bm, Polynomial.map_zero] using hzero
  have hpivotA : pivot.1.1.1 = Hm * Am := by
    calc
      pivot.1.1.1 =
          (score6400PolynomialLocatorRelationPair q₀).1.1.map iota := by
            simpa only [pivot, K, iota] using
              score6400IntegralKernelPair_fst f₀ f₁ q₀ hq₀
      _ = (H * A).map iota := congrArg (Polynomial.map iota) hAfactor
      _ = Hm * Am := by simp only [Polynomial.map_mul, Hm, Am]
  have hpivotB : pivot.1.2.1 = Hm * Bm := by
    calc
      pivot.1.2.1 =
          (score6400PolynomialLocatorRelationPair q₀).2.1.map iota := by
            simpa only [pivot, K, iota] using
              score6400IntegralKernelPair_snd f₀ f₁ q₀ hq₀
      _ = (H * B).map iota := congrArg (Polynomial.map iota) hBfactor
      _ = Hm * Bm := by simp only [Polynomial.map_mul, Hm, Bm]
  have hselectedA : selected.1.1.1 =
      (score6400SelectedLocatorCramerOrdinary f₀ f₁
        data.rows data.cols data.hcols j).map iota := by
    simpa only [selected, qj, hj, K, iota,
      score6400SelectedLocatorCramerOrdinary] using
      score6400IntegralKernelPair_fst f₀ f₁ qj hj
  have hselectedB : selected.1.2.1 =
      (score6400SelectedLocatorCramerFrobenius f₀ f₁
        data.rows data.cols data.hcols j).map iota := by
    simpa only [selected, qj, hj, K, iota,
      score6400SelectedLocatorCramerFrobenius] using
      score6400IntegralKernelPair_snd f₀ f₁ qj hj
  have hdet := hrankOne pivot selected
  have hcross : (Hm * Am) *
        (score6400SelectedLocatorCramerFrobenius f₀ f₁
          data.rows data.cols data.hcols j).map iota =
      (Hm * Bm) *
        (score6400SelectedLocatorCramerOrdinary f₀ f₁
          data.rows data.cols data.hcols j).map iota := by
    have hzero := polynomialPair_cross_eq_of_det_eq_zero
      pivot.1 selected.1 hdet
    rw [hpivotA, hpivotB, hselectedA, hselectedB] at hzero
    exact hzero
  simpa only [K, iota, Am, Bm] using
    exists_multiplier_of_factored_coprime_cross
      Hm Am Bm
      ((score6400SelectedLocatorCramerOrdinary f₀ f₁
        data.rows data.cols data.hcols j).map iota)
      ((score6400SelectedLocatorCramerFrobenius f₀ f₁
        data.rows data.cols data.hcols j).map iota)
      hHm hBm (by simpa only [Am, Bm, K, iota] using hcoprime) hcross

end BCHKSRankOneCramerMultiplierFamily6400
end ProximityPrize.SubmissionLower
