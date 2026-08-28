import ProximityPrize.SubmissionLower.BCHKSRationalPairKernelTransport6400
import ProximityPrize.SubmissionLower.BCHKSRankOneDimensionDegree6400

/-!
# Production dimension--degree descent for the score-64 rank-one kernel

The rational polynomial-pair kernel is linearly equivalent to the original
coordinate kernel.  A polynomial kernel vector therefore supplies a member
of the rational pair kernel after coefficientwise injection into the
challenge fraction field.

For the fixed coprime primitive quotient direction `(A',B')`, rational rank
one makes every kernel pair a polynomial multiple of that direction.  The
abstract multiplier-window theorem then gives the sharp unequal-box bound

```text
deg_X B' <= 22489 - L.
```
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneDegreeProduction6400

open Polynomial
open ProximityPrize.Benchmark
open BCHKSRankOneDimensionDegree6400
open BCHKSRationalPairKernelTransport6400

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

/-- Production nullity rebate for the primitive Frobenius direction. -/
theorem score6400_primitiveFrobenius_natDegree_le_sub_nullity
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B : IRSProfile.Field[X][X])
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hq : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (hH : H ≠ 0) (hB : B ≠ 0)
    (hAfactor :
      (score6400PolynomialLocatorRelationPair q).1.1 = H * A)
    (hBfactor :
      (score6400PolynomialLocatorRelationPair q).2.1 = H * B)
    (hcoprime : IsCoprime
      (A.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X])))
      (B.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X]))))
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0) :
    B.natDegree ≤ locatorFrobeniusRows6400 - L := by
  let K := FractionRing IRSProfile.Field[X]
  let iota : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let M := score6400LocatorPolynomialMatrix f₀ f₁
  let e := polynomialPairCoordinateEquiv K
    locatorOrdinaryRows6400 locatorFrobeniusRows6400
  let W := LinearMap.ker (M.map iota).mulVecLin
  let V := W.comap e.toLinearMap
  let Am : K[X] := A.map iota
  let Bm : K[X] := B.map iota
  let Hm : K[X] := H.map iota
  have hiota : Function.Injective iota :=
    IsFractionRing.injective IRSProfile.Field[X] K
  have hBm : Bm ≠ 0 := by
    intro hzero
    apply hB
    apply Polynomial.map_injective iota hiota
    simpa only [Bm, Polynomial.map_zero] using hzero
  have hHm : Hm ≠ 0 := by
    intro hzero
    apply hH
    apply Polynomial.map_injective iota hiota
    simpa only [Hm, Polynomial.map_zero] using hzero
  have hqMap :
      (iota ∘ q) ∈ W := by
    change (iota ∘ q) ∈ LinearMap.ker
      ((score6400LocatorPolynomialMatrix f₀ f₁).map iota).mulVecLin
    exact ringHom_comp_mem_ker_map_mulVec iota
      (score6400LocatorPolynomialMatrix f₀ f₁) q hq
  let coordinatePivot : W := ⟨iota ∘ q, hqMap⟩
  let pivot : V := submoduleToComapEquiv e W coordinatePivot
  have hpivotCoe' : pivot.1 = e.symm coordinatePivot.1 := by
    simpa only [pivot] using
      submoduleToComapEquiv_apply_coe e W coordinatePivot
  have hpivotCoe : pivot.1 = e.symm (iota ∘ q) := by
    simpa only [coordinatePivot] using hpivotCoe'
  have hrelation :
      (locatorFractionDegreeLT locatorOrdinaryRows6400
          (score6400PolynomialLocatorRelationPair q).1.1
          (score6400PolynomialLocatorRelationPair q).1.2,
        locatorFractionDegreeLT locatorFrobeniusRows6400
          (score6400PolynomialLocatorRelationPair q).2.1
          (score6400PolynomialLocatorRelationPair q).2.2) = pivot.1 := by
    have hcoordinate :=
      score6400_locatorFractionRelationPair_eq_coordinatePair q
    change
      (locatorFractionDegreeLT locatorOrdinaryRows6400
          (score6400PolynomialLocatorRelationPair q).1.1
          (score6400PolynomialLocatorRelationPair q).1.2,
        locatorFractionDegreeLT locatorFrobeniusRows6400
          (score6400PolynomialLocatorRelationPair q).2.1
          (score6400PolynomialLocatorRelationPair q).2.2) =
        e.symm (iota ∘ q) at hcoordinate
    exact hcoordinate.trans hpivotCoe.symm
  have hpivotRawA :
      pivot.1.1.1 =
        (score6400PolynomialLocatorRelationPair q).1.1.map iota := by
    have hcomponent := congrArg
      (fun p : PolynomialPairSpace K locatorOrdinaryRows6400
        locatorFrobeniusRows6400 ↦ p.1.1) hrelation
    simpa only [locatorFractionDegreeLT] using hcomponent.symm
  have hpivotRawB :
      pivot.1.2.1 =
        (score6400PolynomialLocatorRelationPair q).2.1.map iota := by
    have hcomponent := congrArg
      (fun p : PolynomialPairSpace K locatorOrdinaryRows6400
        locatorFrobeniusRows6400 ↦ p.2.1) hrelation
    simpa only [locatorFractionDegreeLT] using hcomponent.symm
  have hpivotA : pivot.1.1.1 = Hm * Am := by
    calc
      pivot.1.1.1 =
          (score6400PolynomialLocatorRelationPair q).1.1.map iota :=
        hpivotRawA
      _ = (H * A).map iota :=
        congrArg (Polynomial.map iota) hAfactor
      _ = Hm * Am := by
        simp only [Polynomial.map_mul, Hm, Am]
  have hpivotB : pivot.1.2.1 = Hm * Bm := by
    calc
      pivot.1.2.1 =
          (score6400PolynomialLocatorRelationPair q).2.1.map iota :=
        hpivotRawB
      _ = (H * B).map iota :=
        congrArg (Polynomial.map iota) hBfactor
      _ = Hm * Bm := by
        simp only [Polynomial.map_mul, Hm, Bm]
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
  have hBdegree : B.natDegree < locatorFrobeniusRows6400 := by
    have hdegrees := congrArg Polynomial.natDegree hBfactor
    rw [Polynomial.natDegree_mul hH hB] at hdegrees
    omega
  have hBmdegree : Bm.natDegree < locatorFrobeniusRows6400 := by
    rw [Polynomial.natDegree_map_eq_of_injective hiota B]
    exact hBdegree
  have hVrank : Module.finrank K V = L := by
    have hWrank : Module.finrank K W = L := by
      change Module.finrank K W = L at hkernelRank
      exact hkernelRank
    exact (submoduleToComapEquiv e W).finrank_eq.symm.trans hWrank
  have hdegreeMap :=
    secondDirection_natDegree_le_sub_finrank_of_factored_pivot
      V pivot Hm Am Bm hHm hBm
        (by simpa only [Am, Bm, iota] using hcoprime)
        hBmdegree hpivotA hpivotB (fun v ↦ hrankOne v pivot)
  rw [hVrank, Polynomial.natDegree_map_eq_of_injective hiota B] at hdegreeMap
  exact hdegreeMap

end BCHKSRankOneDegreeProduction6400
end ProximityPrize.SubmissionLower
