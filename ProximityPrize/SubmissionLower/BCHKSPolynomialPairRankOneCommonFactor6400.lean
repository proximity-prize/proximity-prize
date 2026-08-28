import ProximityPrize.SubmissionLower.BCHKSCommonFactorDescent6400
import ProximityPrize.SubmissionLower.BCHKSRankOneCramerNonCoprime6400

/-!
# Primitive common factors in the production rank-one Cramer family

The memory-heavy Cramer-family selection is compiled separately in
`BCHKSRankOneCramerNonCoprime6400`.  This module performs only the resultant
descent and integral primitive-gcd extraction.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark
open BCHKSTwoAxisResultant6400
open BCHKSCommonFactorDescent6400
open BCHKSRankOneCramerNonCoprime6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- In every production rational-rank-one locator kernel of nullity at least
two, one selected integral Cramer relation has a primitive full common
locator factor.  Its chosen integral quotient lanes are coprime over the
challenge fraction field, and the relation retains the sharp Cramer
coefficient bound needed by the global affine interpolation. -/
theorem exists_score6400_rankOne_Cramer_coprimeQuotient
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
      ∃ H A' B' : IRSProfile.Field[X][X],
        q ∈ LinearMap.ker
            (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
        (∀ n, (q n).natDegree ≤ 76779 * 2130706433) ∧
        H.IsPrimitive ∧ 0 < H.natDegree ∧
        (score6400PolynomialLocatorRelationPair q).1.1 = H * A' ∧
        (score6400PolynomialLocatorRelationPair q).2.1 = H * B' ∧
        IsCoprime
          (A'.map (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])))
          (B'.map (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))) ∧
        ((score6400PolynomialLocatorRelationPair q).1.1 ≠ 0 ∨
          (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0) ∧
        H.natDegree ≤ homogeneousLocatorCap := by
  classical
  obtain ⟨q, hqker, hqdegree, hnotCoprimeMap, hpairNe⟩ :=
    exists_score6400_rankOne_Cramer_nonCoprimePair
      f₀ f₁ L hkernelRank hLtwo hrankOne
  let K := FractionRing IRSProfile.Field[X]
  let iota : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let A := (score6400PolynomialLocatorRelationPair q).1.1
  let B := (score6400PolynomialLocatorRelationPair q).2.1
  have hiota : Function.Injective iota :=
    IsFractionRing.injective IRSProfile.Field[X] K
  have hmapPairNe : A.map iota ≠ 0 ∨ B.map iota ≠ 0 := by
    rcases hpairNe with hAne | hBne
    · left
      intro hzero
      apply hAne
      apply Polynomial.map_injective iota hiota
      simpa only [Polynomial.map_zero] using hzero
    · right
      intro hzero
      apply hBne
      apply Polynomial.map_injective iota hiota
      simpa only [Polynomial.map_zero] using hzero
  have hnotCoprime : ¬ IsCoprime (A.map iota) (B.map iota) := by
    simpa only [A, B, K, iota] using hnotCoprimeMap
  have hresultantMap :
      Polynomial.resultant (A.map iota) (B.map iota) = 0 :=
    Polynomial.resultant_eq_zero_iff.mpr ⟨hmapPairNe, hnotCoprime⟩
  have hAdegree : (A.map iota).natDegree = A.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hiota A
  have hBdegree : (B.map iota).natDegree = B.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hiota B
  have hresultantFixed :
      Polynomial.resultant (A.map iota) (B.map iota)
        A.natDegree B.natDegree = 0 := by
    simpa only [hAdegree, hBdegree] using hresultantMap
  have hresultant : Polynomial.resultant A B = 0 := by
    apply hiota
    rw [← Polynomial.resultant_map_map]
    simpa only [map_zero] using hresultantFixed
  obtain ⟨H, A', B', hHprimitive, hHpositive, hAfactor, hBfactor,
      hcoprime⟩ :=
    exists_integralPrimitiveGCD_of_resultant_eq_zero_of_pair_ne_zero
      A B (by simpa only [A, B] using hpairNe) hresultant
  have hHdivA : H ∣ A := ⟨A', hAfactor⟩
  have hHdivB : H ∣ B := ⟨B', hBfactor⟩
  have hHcap : H.natDegree ≤ homogeneousLocatorCap := by
    rcases hpairNe with hAne | hBne
    · have hAdegreeLt : A.natDegree < locatorOrdinaryRows6400 := by
        rw [Polynomial.natDegree_lt_iff_degree_lt (by
          simpa only [A] using hAne)]
        exact Polynomial.mem_degreeLT.mp
          (score6400PolynomialLocatorRelationPair q).1.2
      have hle := Polynomial.natDegree_le_of_dvd hHdivA
        (by simpa only [A] using hAne)
      norm_num [locatorOrdinaryRows6400, homogeneousLocatorCap]
        at hAdegreeLt ⊢
      omega
    · have hBdegreeLt : B.natDegree < locatorFrobeniusRows6400 := by
        rw [Polynomial.natDegree_lt_iff_degree_lt (by
          simpa only [B] using hBne)]
        exact Polynomial.mem_degreeLT.mp
          (score6400PolynomialLocatorRelationPair q).2.2
      have hle := Polynomial.natDegree_le_of_dvd hHdivB
        (by simpa only [B] using hBne)
      norm_num [locatorFrobeniusRows6400, homogeneousLocatorCap]
        at hBdegreeLt ⊢
      omega
  refine ⟨q, H, A', B', hqker, hqdegree, hHprimitive, hHpositive,
    ?_, ?_, ?_, ?_, hHcap⟩
  · simpa only [A] using hAfactor
  · simpa only [B] using hBfactor
  · simpa only [K, iota] using hcoprime
  · exact hpairNe

/-- Compatibility endpoint retaining only divisibility by the selected
primitive common factor. -/
theorem exists_score6400_rankOne_Cramer_commonFactor
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
      ∃ H : IRSProfile.Field[X][X],
        q ∈ LinearMap.ker
            (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
        (∀ n, (q n).natDegree ≤ 76779 * 2130706433) ∧
        H.IsPrimitive ∧ 0 < H.natDegree ∧
        H ∣ (score6400PolynomialLocatorRelationPair q).1.1 ∧
        H ∣ (score6400PolynomialLocatorRelationPair q).2.1 ∧
        ((score6400PolynomialLocatorRelationPair q).1.1 ≠ 0 ∨
          (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0) ∧
        H.natDegree ≤ homogeneousLocatorCap := by
  obtain ⟨q, H, A', B', hqker, hqdegree, hHprimitive, hHpositive,
      hAfactor, hBfactor, _hcoprime, hpairNe, hHcap⟩ :=
    exists_score6400_rankOne_Cramer_coprimeQuotient
      f₀ f₁ L hkernelRank hLtwo hrankOne
  exact ⟨q, H, hqker, hqdegree, hHprimitive, hHpositive,
    ⟨A', hAfactor⟩, ⟨B', hBfactor⟩, hpairNe, hHcap⟩

end ProximityPrize.SubmissionLower
