import ProximityPrize.SubmissionLower.BCHKSPolynomialPairRankOneCommonFactor6400
import ProximityPrize.SubmissionLower.BCHKSLocatorPolynomialPairToCodeOwner6400

/-!
# Production fibres for rank-one common locator factors

This module connects the selected common factor to both specialization axes.
Owner fibres use the decoded-polynomial identity.  Coordinate fibres use the
polynomial-valued source relation before challenge specialization.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open Polynomial.Bivariate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open ProximityPrize.Benchmark
open BCHKSExactSparsification6400
open BCHKSTwoAxisResultant6400
open BCHKSCommonFactorDescent6400

/-- Swapping and then specializing the new outer variable is the same as
evaluating the original locator variable at the corresponding constant. -/
theorem bivariate_swap_map_eval_eq_eval_C
    {F : Type} [Field F] (Q : F[X][X]) (x : F) :
    (swap Q).map (Polynomial.evalRingHom x) =
      Q.eval (Polynomial.C x) := by
  rw [← Polynomial.Bivariate.evalX_eq_map]
  exact (Polynomial.Bivariate.evalY_eq_evalX_swap x Q).symm

/-- A coefficientwise challenge-degree cap bounds the bivariate challenge
degree. -/
theorem degreeX_le_of_coeff_natDegree_le
    {F : Type} [Field F] (Q : F[X][X]) (S : Nat)
    (hcoeff : ∀ n, (Q.coeff n).natDegree ≤ S) :
    degreeX Q ≤ S := by
  unfold degreeX
  exact Finset.sup_le fun n _hn ↦ hcoeff n

/-- A common factor of the two polynomial multiplier lanes divides the
global affine lane at every source-coordinate fibre. -/
theorem score6400_commonFactor_coordinate_fiber
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H : IRSProfile.Field[X][X])
    (hHA : H ∣ (score6400PolynomialLocatorRelationPair q).1.1)
    (hHB : H ∣ (score6400PolynomialLocatorRelationPair q).2.1)
    (i : IRSProfile.Index) :
    (swap H).map (Polynomial.evalRingHom (IRSProfile.domain i)) ∣
      (swap (score6400PolynomialLocatorPairToCode f₀ f₁ q)).map
        (Polynomial.evalRingHom (IRSProfile.domain i)) := by
  rw [bivariate_swap_map_eval_eq_eval_C,
    bivariate_swap_map_eval_eq_eval_C,
    score6400PolynomialLocatorPairToCode_eval_coordinate,
    score6400PolynomialPairRelationWord, polynomialBilinearWord]
  have hAeval :
      H.eval (Polynomial.C (IRSProfile.domain i)) ∣
        (score6400PolynomialLocatorRelationPair q).1.1.eval
          (Polynomial.C (IRSProfile.domain i)) := by
    simpa using map_dvd
      (Polynomial.evalRingHom (Polynomial.C (IRSProfile.domain i))) hHA
  have hBeval :
      H.eval (Polynomial.C (IRSProfile.domain i)) ∣
        (score6400PolynomialLocatorRelationPair q).2.1.eval
          (Polynomial.C (IRSProfile.domain i)) := by
    simpa using map_dvd
      (Polynomial.evalRingHom (Polynomial.C (IRSProfile.domain i))) hHB
  rcases hAeval with ⟨A', hA'⟩
  rcases hBeval with ⟨B', hB'⟩
  refine ⟨A' * score6400ReceivedPolynomial f₀ f₁ i +
    B' * score6400FrobeniusReceivedPolynomial f₀ f₁ i, ?_⟩
  rw [hA', hB']
  ring

/-- A common factor of the global multiplier lanes divides the affine lane
at every owner carrying a score-64 agreement witness. -/
theorem score6400_commonFactor_owner_fiber
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hqker : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (H : IRSProfile.Field[X][X])
    (hHA : H ∣ (score6400PolynomialLocatorRelationPair q).1.1)
    (hHB : H ∣ (score6400PolynomialLocatorRelationPair q).2.1)
    (z : IRSProfile.Field)
    (A : Finset IRSProfile.Index) (P : IRSProfile.Field[X])
    (hAcard : 185364 ≤ A.card)
    (hPdegree : P.natDegree ≤ 131071)
    (hagree : ∀ i ∈ A,
      P.eval (IRSProfile.domain i) = f₀ i + z * f₁ i) :
    H.map (Polynomial.evalRingHom z) ∣
      (score6400PolynomialLocatorPairToCode f₀ f₁ q).map
        (Polynomial.evalRingHom z) := by
  rw [score6400PolynomialLocatorPairToCode_map_eval_eq_owner_mapped
    f₀ f₁ q hqker z A P hAcard hPdegree hagree]
  have hAmapRaw := map_dvd
    (Polynomial.mapRingHom (Polynomial.evalRingHom z)) hHA
  have hBmapRaw := map_dvd
    (Polynomial.mapRingHom (Polynomial.evalRingHom z)) hHB
  have hAmap : H.map (Polynomial.evalRingHom z) ∣
      (score6400PolynomialLocatorRelationPair q).1.1.map
        (Polynomial.evalRingHom z) := by
    simpa using hAmapRaw
  have hBmap : H.map (Polynomial.evalRingHom z) ∣
      (score6400PolynomialLocatorRelationPair q).2.1.map
        (Polynomial.evalRingHom z) := by
    simpa using hBmapRaw
  rcases hAmap with ⟨A', hA'⟩
  rcases hBmap with ⟨B', hB'⟩
  refine ⟨A' * P + B' * P.map koalaSexticFrobenius.toRingHom, ?_⟩
  rw [hA', hB']
  ring

/-- Every retained bad owner supplies the owner fibre required by the
two-axis resultant theorem. -/
theorem score6400_commonFactor_retained_owner_fiber
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (q : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (hqker : q ∈ LinearMap.ker
      (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin)
    (H : IRSProfile.Field[X][X])
    (hHA : H ∣ (score6400PolynomialLocatorRelationPair q).1.1)
    (hHB : H ∣ (score6400PolynomialLocatorRelationPair q).2.1)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    H.map (Polynomial.evalRingHom z) ∣
      (score6400PolynomialLocatorPairToCode f₀ f₁ q).map
        (Polynomial.evalRingHom z) := by
  obtain ⟨A, P, _E, hAcard, hPdegree, hagree, _hunexplained,
      _hE, _hEcard, _hEupper⟩ :=
    exists_score6400_large_error_witness f₀ f₁ z hbad hnotOld
  exact score6400_commonFactor_owner_fiber
    f₀ f₁ q hqker H hHA hHB z A P hAcard hPdegree hagree

/-- Production instantiation of the complementary-resultant argument for
every rational-rank-one nullity `L ≥ 2`.  It returns a positive locator
factor common to the selected homogeneous factor and its global affine lane.
-/
theorem exists_score6400_rankOne_twoAxis_commonFactor
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L)
    (hrankOne : ∀ u v : score6400LocatorRationalPairKernel f₀ f₁,
      polynomialPairDet u.1 v.1 = 0)
    (T : Finset IRSProfile.Field)
    (hTcard : ownerFloor ≤ T.card)
    (hbad : ∀ z ∈ T,
      MCABad IRSProfile.baseCode f₀ f₁ 185364 z)
    (hnotOld : ∀ z ∈ T,
      ¬ MCABad IRSProfile.baseCode f₀ f₁ 185374 z) :
    ∃ q : Score6400LocatorMinorIndex → IRSProfile.Field[X],
      ∃ H D : IRSProfile.Field[X][X],
        q ∈ LinearMap.ker
            (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin ∧
        (∀ n, (q n).natDegree ≤ 76779 * 2130706433) ∧
        H.IsPrimitive ∧ 0 < H.natDegree ∧
        H ∣ (score6400PolynomialLocatorRelationPair q).1.1 ∧
        H ∣ (score6400PolynomialLocatorRelationPair q).2.1 ∧
        ((score6400PolynomialLocatorRelationPair q).1.1 ≠ 0 ∨
          (score6400PolynomialLocatorRelationPair q).2.1 ≠ 0) ∧
        H.natDegree ≤ homogeneousLocatorCap ∧
        D.IsPrimitive ∧ 0 < D.natDegree ∧ D ∣ H ∧
        D ∣ score6400PolynomialLocatorPairToCode f₀ f₁ q := by
  classical
  obtain ⟨q, H, hqker, hqdegree, hHprimitive, hHpositive,
      hHdivA, hHdivB, hpairNe, hHcap⟩ :=
    exists_score6400_rankOne_Cramer_commonFactor
      f₀ f₁ L hkernelRank hLtwo hrankOne
  let C := score6400PolynomialLocatorPairToCode f₀ f₁ q
  have hfield :
      76779 * 2130706433 + 2130706433 <
        Fintype.card IRSProfile.Field := by
    rw [CompPoly.Extension.Ext.card_ext]
    norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]
  have hCYlt : C.natDegree < 185363 := by
    exact score6400PolynomialLocatorPairToCode_natDegree_lt
      f₀ f₁ q hqker (76779 * 2130706433) hqdegree hfield
  have hCY : C.natDegree ≤ affineLocatorCap := by
    norm_num [affineLocatorCap] at hCYlt ⊢
    omega
  have hCX : degreeX C ≤ affineChallengeCap := by
    apply degreeX_le_of_coeff_natDegree_le
    intro n
    have hcoeff := score6400PolynomialLocatorPairToCode_coeff_natDegree_le
      f₀ f₁ q (76779 * 2130706433) hqdegree n
    have hcoeffC : (C.coeff n).natDegree ≤
        76779 * 2130706433 + 2130706433 := by
      simpa only [C] using hcoeff
    norm_num [affineChallengeCap] at hcoeffC ⊢
    omega
  have hCoords : coordinateCount ≤
      (Finset.univ : Finset IRSProfile.Index).card := by
    norm_num [coordinateCount, IRSProfile.Index]
  have hownerFiber : ∀ z ∈ T,
      H.map (Polynomial.evalRingHom ((Function.Embedding.refl _ ) z)) ∣
        C.map (Polynomial.evalRingHom ((Function.Embedding.refl _) z)) := by
    intro z hz
    exact score6400_commonFactor_retained_owner_fiber
      f₀ f₁ q hqker H hHdivA hHdivB z
        (hbad z hz) (hnotOld z hz)
  have hcoordFiber : ∀ i ∈ (Finset.univ : Finset IRSProfile.Index),
      (swap H).map (Polynomial.evalRingHom (IRSProfile.domain i)) ∣
        (swap C).map (Polynomial.evalRingHom (IRSProfile.domain i)) := by
    intro i _hi
    exact score6400_commonFactor_coordinate_fiber
      f₀ f₁ q H hHdivA hHdivB i
  obtain ⟨D, hDprimitive, hDpositive, hDdivH, hDdivC⟩ :=
    production_exists_positiveLocatorCommonFactor
      H C T (Function.Embedding.refl IRSProfile.Field)
      (Finset.univ : Finset IRSProfile.Index) IRSProfile.domain
      H.natDegree (degreeX H)
      hHprimitive rfl rfl hHpositive hHcap hCY hCX hTcard hCoords
      hownerFiber hcoordFiber
  exact ⟨q, H, D, hqker, hqdegree, hHprimitive, hHpositive,
    hHdivA, hHdivB, hpairNe, hHcap, hDprimitive, hDpositive, hDdivH,
    by simpa only [C] using hDdivC⟩

end ProximityPrize.SubmissionLower
