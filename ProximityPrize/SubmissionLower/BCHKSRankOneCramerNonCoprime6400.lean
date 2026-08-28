import ProximityPrize.SubmissionLower.BCHKSPolynomialPairRankOneAbstract6400
import ProximityPrize.SubmissionLower.BCHKSRationalPairKernelTransport6400

/-!
# Selecting a non-coprime production Cramer relation

This is the linear-algebra half of the rank-one common-factor construction.
Resultant descent and primitive gcd extraction are intentionally left to the
next module so Lean need not retain both large proof contexts at once.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneCramerNonCoprime6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSRationalPairKernelTransport6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- A rank-one rational locator kernel of nullity at least two contains a
bounded integral Cramer vector whose two polynomial lanes are non-coprime
after injection into the challenge fraction field. -/
theorem exists_score6400_rankOne_Cramer_nonCoprimePair
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L)
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0) :
    ∃ q : Score6400LocatorMinorIndex → IRSProfile.Field[X],
      q ∈ LinearMap.ker
          (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
      (∀ n, (q n).natDegree ≤ 76779 * 2130706433) ∧
      ¬ IsCoprime
        ((score6400PolynomialLocatorRelationPair q).1.1.map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])))
        ((score6400PolynomialLocatorRelationPair q).2.1.map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))) ∧
      ((score6400PolynomialLocatorRelationPair q).1.1 ≠ 0 ∨
        (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0) := by
  classical
  let K := FractionRing IRSProfile.Field[X]
  let ι : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let M := score6400LocatorPolynomialMatrix f₀ f₁
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  let W := LinearMap.ker (M.map ι).mulVecLin
  let V := W.comap e.toLinearMap
  obtain ⟨r, rows, cols, _hrows, hcols, hrank, hcomplement, hminor,
      hpolynomialKer, hdegree, hspan⟩ :=
    exists_score6400_spanning_bounded_locatorCramerFamily
      f₀ f₁ L hkernelRank
  let coordinateFamily : SelectedColumnComplement cols →
      Score6400LocatorMinorIndex → K :=
    mappedSelectedPolynomialCramerKernelVector ι M rows cols hcols
  let A := score6400SelectedLocatorCramerOrdinary
    f₀ f₁ rows cols hcols
  let B := score6400SelectedLocatorCramerFrobenius
    f₀ f₁ rows cols hcols
  have hA : ∀ j, A j ∈ Polynomial.degreeLT IRSProfile.Field[X]
      locatorOrdinaryRows6400 :=
    score6400SelectedLocatorCramerOrdinary_mem_degreeLT
      f₀ f₁ rows cols hcols
  have hB : ∀ j, B j ∈ Polynomial.degreeLT IRSProfile.Field[X]
      locatorFrobeniusRows6400 :=
    score6400SelectedLocatorCramerFrobenius_mem_degreeLT
      f₀ f₁ rows cols hcols
  let pairFamily : SelectedColumnComplement cols →
      PolynomialPairSpace K locatorOrdinaryRows6400
        locatorFrobeniusRows6400 :=
    locatorPairFamilyFraction
      locatorOrdinaryRows6400 locatorFrobeniusRows6400 A B hA hB
  have hfamily : ∀ j, pairFamily j = e.symm (coordinateFamily j) := by
    intro j
    simpa only [pairFamily, A, B, coordinateFamily, K, ι, M,
      locatorPairFamilyFraction,
      score6400SelectedLocatorCramerOrdinary,
      score6400SelectedLocatorCramerFrobenius,
      score6400SelectedLocatorCramerVector,
      mappedSelectedPolynomialCramerKernelVector, e] using
        score6400_locatorFractionRelationPair_eq_coordinatePair
          (score6400SelectedLocatorCramerVector
            f₀ f₁ rows cols hcols j)
  have hpairLI : LinearIndependent K pairFamily := by
    simpa only [K, pairFamily, A, B] using
      linearIndependent_score6400SelectedLocatorCramerFractionPairs
        f₀ f₁ rows cols hcols hminor
  have hcoordinateMem : ∀ j, coordinateFamily j ∈ W := by
    intro j
    change coordinateFamily j ∈ LinearMap.ker (M.map ι).mulVecLin
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self j)
  let coordinateKernelFamily : SelectedColumnComplement cols → W :=
    fun j ↦ ⟨coordinateFamily j, hcoordinateMem j⟩
  let kernelPairFamily : SelectedColumnComplement cols → V :=
    fun j ↦ submoduleToComapEquiv e W (coordinateKernelFamily j)
  have hkernelPairCoe : ∀ j,
      (kernelPairFamily j).1 = e.symm (coordinateFamily j) := by
    intro j
    have hcoe := submoduleToComapEquiv_apply_coe
      e W (coordinateKernelFamily j)
    simpa only [kernelPairFamily, coordinateKernelFamily] using hcoe
  have hpairKernel : ∀ j,
      pairFamily j = (kernelPairFamily j).1 := by
    intro j
    exact (hfamily j).trans (hkernelPairCoe j).symm
  have hpairDet : ∀ i j,
      polynomialPairDet (pairFamily i) (pairFamily j) = 0 := by
    intro i j
    have hdet := hrankOne (kernelPairFamily i) (kernelPairFamily j)
    simpa only [hpairKernel i, hpairKernel j] using hdet
  have hJcard : Fintype.card (SelectedColumnComplement cols) = L := by
    rw [← Nat.card_eq_fintype_card]
    exact hcomplement
  obtain ⟨j, hnotCoprime⟩ :=
    exists_nonCoprime_member_of_linearIndependent_pairDet_eq_zero
      pairFamily hpairLI (by rw [hJcard]; exact hLtwo) hpairDet
  have hnotCoprimeMap :
      ¬ IsCoprime ((A j).map ι) ((B j).map ι) := by
    simpa only [pairFamily, locatorPairFamilyFraction,
      locatorFractionDegreeLT] using hnotCoprime
  have hmapPairNe : (A j).map ι ≠ 0 ∨ (B j).map ι ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hpairLI.ne_zero j
    apply Prod.ext
    · apply Subtype.ext
      change (A j).map
        (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X])) = 0
      simpa only [ι, K] using hzero.1
    · apply Subtype.ext
      change (B j).map
        (algebraMap IRSProfile.Field[X]
          (FractionRing IRSProfile.Field[X])) = 0
      simpa only [ι, K] using hzero.2
  have hpairNe : A j ≠ 0 ∨ B j ≠ 0 :=
    hmapPairNe.imp
      (fun hmap hzero ↦ hmap (by simp only [hzero, Polynomial.map_zero]))
      (fun hmap hzero ↦ hmap (by simp only [hzero, Polynomial.map_zero]))
  let q := score6400SelectedLocatorCramerVector
    f₀ f₁ rows cols hcols j
  have hrmax : r ≤ 76779 := by
    have hcardN : Fintype.card Score6400LocatorMinorIndex = 76781 := by
      norm_num [Score6400LocatorMinorIndex, locatorOrdinaryRows6400,
        locatorFrobeniusRows6400]
    rw [hcardN] at hrank
    omega
  have hqdegree : ∀ n, (q n).natDegree ≤ 76779 * 2130706433 := by
    intro n
    exact (hdegree j n).trans (Nat.mul_le_mul_right 2130706433 hrmax)
  refine ⟨q, ?_, hqdegree, ?_, ?_⟩
  · simpa only [q, score6400SelectedLocatorCramerVector] using
      hpolynomialKer j
  · simpa only [q, A, B, K, ι,
      score6400SelectedLocatorCramerOrdinary,
      score6400SelectedLocatorCramerFrobenius] using hnotCoprimeMap
  · simpa only [q, A, B, score6400SelectedLocatorCramerOrdinary,
      score6400SelectedLocatorCramerFrobenius] using hpairNe

end BCHKSRankOneCramerNonCoprime6400
end ProximityPrize.SubmissionLower
