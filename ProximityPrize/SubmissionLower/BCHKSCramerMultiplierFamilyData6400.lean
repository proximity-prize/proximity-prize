import ProximityPrize.SubmissionLower.BCHKSRankOneSelectedCramerMultiplier6400

/-! # Compact data for the selected Cramer multiplier family -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRankOneCramerMultiplierFamily6400

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure Score6400CramerMultiplierFamilyData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (selection : Score6400BoundedCramerFamilyData f₀ f₁ L)
    (A B : IRSProfile.Field[X][X]) where
  multipliers : SelectedColumnComplement selection.cols →
    (FractionRing IRSProfile.Field[X])[X]
  firstFactor : ∀ j,
    (score6400SelectedLocatorCramerOrdinary f₀ f₁ selection.rows
        selection.cols selection.hcols j).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])) =
      multipliers j * A.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X]))
  secondFactor : ∀ j,
    (score6400SelectedLocatorCramerFrobenius f₀ f₁ selection.rows
        selection.cols selection.hcols j).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])) =
      multipliers j * B.map (algebraMap IRSProfile.Field[X]
        (FractionRing IRSProfile.Field[X]))
  linearIndependent : LinearIndependent
    (FractionRing IRSProfile.Field[X]) multipliers
  degree : ∀ j, (multipliers j).natDegree <
    locatorFrobeniusRows6400 - B.natDegree

/-- Pointwise existence of the common multipliers, together with a nonzero
primitive Frobenius lane, upgrades to an independent bounded multiplier
family. -/
theorem exists_score6400_CramerMultiplierFamilyData_of_pointwise
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (selection : Score6400BoundedCramerFamilyData f₀ f₁ L)
    (A B : IRSProfile.Field[X][X]) (hB : B ≠ 0)
    (hexists : ∀ j : SelectedColumnComplement selection.cols,
      ∃ multiplier : (FractionRing IRSProfile.Field[X])[X],
        (score6400SelectedLocatorCramerOrdinary f₀ f₁ selection.rows
            selection.cols selection.hcols j).map
              (algebraMap IRSProfile.Field[X]
                (FractionRing IRSProfile.Field[X])) =
          multiplier * A.map (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])) ∧
        (score6400SelectedLocatorCramerFrobenius f₀ f₁ selection.rows
            selection.cols selection.hcols j).map
              (algebraMap IRSProfile.Field[X]
                (FractionRing IRSProfile.Field[X])) =
          multiplier * B.map (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))) :
    Nonempty (Score6400CramerMultiplierFamilyData
      f₀ f₁ L selection A B) := by
  classical
  let K := FractionRing IRSProfile.Field[X]
  let iota : IRSProfile.Field[X] →+* K :=
    algebraMap IRSProfile.Field[X] K
  let Am : K[X] := A.map iota
  let Bm : K[X] := B.map iota
  let multipliers : SelectedColumnComplement selection.cols → K[X] :=
    fun j ↦ Classical.choose (hexists j)
  have hfirst : ∀ j,
      (score6400SelectedLocatorCramerOrdinary f₀ f₁ selection.rows
        selection.cols selection.hcols j).map iota =
          multipliers j * Am := by
    intro j
    exact (Classical.choose_spec (hexists j)).1
  have hsecond : ∀ j,
      (score6400SelectedLocatorCramerFrobenius f₀ f₁ selection.rows
        selection.cols selection.hcols j).map iota =
          multipliers j * Bm := by
    intro j
    exact (Classical.choose_spec (hexists j)).2
  have hpairFirst : ∀ j,
      (score6400SelectedLocatorFractionPair f₀ f₁ selection.rows
        selection.cols selection.hcols j).1.1 =
          multipliers j * Am := by
    intro j
    rw [score6400SelectedLocatorFractionPair_fst]
    exact hfirst j
  have hpairSecond : ∀ j,
      (score6400SelectedLocatorFractionPair f₀ f₁ selection.rows
        selection.cols selection.hcols j).2.1 =
          multipliers j * Bm := by
    intro j
    rw [score6400SelectedLocatorFractionPair_snd]
    exact hsecond j
  have hLI : LinearIndependent K multipliers :=
    linearIndependent_multipliers_of_pair_factors
      (score6400SelectedLocatorFractionPair f₀ f₁ selection.rows
        selection.cols selection.hcols)
      multipliers Am Bm selection.pairLI hpairFirst hpairSecond
  have hiota : Function.Injective iota :=
    IsFractionRing.injective IRSProfile.Field[X] K
  have hBm : Bm ≠ 0 := by
    intro hzero
    apply hB
    apply Polynomial.map_injective iota hiota
    simpa only [Bm, Polynomial.map_zero] using hzero
  have hdegree : ∀ j, (multipliers j).natDegree <
      locatorFrobeniusRows6400 - B.natDegree := by
    intro j
    let RawB := score6400SelectedLocatorCramerFrobenius f₀ f₁
      selection.rows selection.cols selection.hcols j
    have hM : multipliers j ≠ 0 := hLI.ne_zero j
    have hRawMap : RawB.map iota = multipliers j * Bm := by
      simpa only [RawB] using hsecond j
    have hRawMapNe : RawB.map iota ≠ 0 := by
      rw [hRawMap]
      exact mul_ne_zero hM hBm
    have hRawNe : RawB ≠ 0 := by
      intro hzero
      apply hRawMapNe
      rw [hzero, Polynomial.map_zero]
    have hRawDegree : (RawB.map iota).natDegree <
        locatorFrobeniusRows6400 := by
      rw [Polynomial.natDegree_map_eq_of_injective hiota]
      rw [Polynomial.natDegree_lt_iff_degree_lt hRawNe]
      exact Polynomial.mem_degreeLT.mp
        (score6400SelectedLocatorCramerFrobenius_mem_degreeLT
          f₀ f₁ selection.rows selection.cols selection.hcols j)
    have hdegree' := multiplier_natDegree_lt_sub_of_factor
      (multipliers j) Bm (RawB.map iota) locatorFrobeniusRows6400
      hM hBm hRawMap hRawDegree
    rw [Polynomial.natDegree_map_eq_of_injective hiota B] at hdegree'
    exact hdegree'
  refine ⟨{
    multipliers := multipliers
    firstFactor := ?_
    secondFactor := ?_
    linearIndependent := ?_
    degree := hdegree }⟩
  · simpa only [K, iota, Am] using hfirst
  · simpa only [K, iota, Bm] using hsecond
  · simpa only [K] using hLI

/-- Production constructor: select the bounded Cramer basis and obtain its
independent family of primitive-direction multipliers. -/
theorem exists_score6400_rankOne_Cramer_multiplierFamily
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (q₀ : Score6400LocatorMinorIndex → IRSProfile.Field[X])
    (H A B : IRSProfile.Field[X][X])
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L)
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
      polynomialPairDet u.1 v.1 = 0) :
    ∃ selection : Score6400BoundedCramerFamilyData f₀ f₁ L,
      Nonempty (Score6400CramerMultiplierFamilyData
        f₀ f₁ L selection A B) := by
  obtain ⟨selection⟩ := exists_score6400_boundedCramerFamilyData
    f₀ f₁ L hkernelRank hLtwo
  refine ⟨selection, exists_score6400_CramerMultiplierFamilyData_of_pointwise
    f₀ f₁ L selection A B hB ?_⟩
  intro j
  exact exists_score6400_selectedCramer_multiplier
    f₀ f₁ L selection q₀ H A B hq₀ hH hB hAfactor hBfactor
    hcoprime hrankOne j

end BCHKSRankOneCramerMultiplierFamily6400
end ProximityPrize.SubmissionLower
