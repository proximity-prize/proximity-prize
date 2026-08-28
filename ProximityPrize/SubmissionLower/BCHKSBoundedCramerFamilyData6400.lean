import ProximityPrize.SubmissionLower.BCHKSLocatorCramerRankTwoAssembly6400

/-! # Compact data for the bounded score-64 Cramer family -/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The fraction-field pair attached to one selected integral Cramer vector. -/
noncomputable def score6400SelectedLocatorFractionPair
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : Nat} (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    PolynomialPairSpace (FractionRing IRSProfile.Field[X])
      locatorOrdinaryRows6400 locatorFrobeniusRows6400 :=
  locatorPairFamilyFraction locatorOrdinaryRows6400
    locatorFrobeniusRows6400
    (score6400SelectedLocatorCramerOrdinary f₀ f₁ rows cols hcols)
    (score6400SelectedLocatorCramerFrobenius f₀ f₁ rows cols hcols)
    (score6400SelectedLocatorCramerOrdinary_mem_degreeLT
      f₀ f₁ rows cols hcols)
    (score6400SelectedLocatorCramerFrobenius_mem_degreeLT
      f₀ f₁ rows cols hcols) j

@[simp]
theorem score6400SelectedLocatorFractionPair_fst
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : Nat} (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    (score6400SelectedLocatorFractionPair
      f₀ f₁ rows cols hcols j).1.1 =
      (score6400SelectedLocatorCramerOrdinary
        f₀ f₁ rows cols hcols j).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])) := rfl

@[simp]
theorem score6400SelectedLocatorFractionPair_snd
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    {r : Nat} (rows cols : Fin r → Score6400LocatorMinorIndex)
    (hcols : Function.Injective cols)
    (j : SelectedColumnComplement cols) :
    (score6400SelectedLocatorFractionPair
      f₀ f₁ rows cols hcols j).2.1 =
      (score6400SelectedLocatorCramerFrobenius
        f₀ f₁ rows cols hcols j).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X])) := rfl

/-- All selection facts needed downstream, hidden behind named Cramer-vector
and pair interfaces so the production index type is elaborated only once. -/
structure Score6400BoundedCramerFamilyData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat) where
  r : Nat
  rows : Fin r → Score6400LocatorMinorIndex
  cols : Fin r → Score6400LocatorMinorIndex
  hcols : Function.Injective cols
  rank_eq : r + L = Fintype.card Score6400LocatorMinorIndex
  card_eq : Nat.card (SelectedColumnComplement cols) = L
  r_le : r ≤ 76779
  kernel : ∀ j,
    score6400SelectedLocatorCramerVector f₀ f₁ rows cols hcols j ∈
      LinearMap.ker (score6400LocatorPolynomialMatrix f₀ f₁).mulVecLin
  degree : ∀ (j : SelectedColumnComplement cols)
      (n : Score6400LocatorMinorIndex),
    (score6400SelectedLocatorCramerVector
      f₀ f₁ rows cols hcols j n).natDegree ≤
        76779 * 2130706433
  pairLI : LinearIndependent (FractionRing IRSProfile.Field[X])
    (score6400SelectedLocatorFractionPair f₀ f₁ rows cols hcols)

/-- Select the compact bounded family from a rational kernel of nullity at
least two. -/
theorem exists_score6400_boundedCramerFamilyData
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L) :
    Nonempty (Score6400BoundedCramerFamilyData f₀ f₁ L) := by
  classical
  obtain ⟨r, rows, cols, _hrows, hcols, hrank, hcomplement, hminor,
      hkernel, hdegree, _hspan⟩ :=
    exists_score6400_spanning_bounded_locatorCramerFamily
      f₀ f₁ L hkernelRank
  have hcardN : Fintype.card Score6400LocatorMinorIndex = 76781 := by
    norm_num [Score6400LocatorMinorIndex, locatorOrdinaryRows6400,
      locatorFrobeniusRows6400]
  have hrle : r ≤ 76779 := by
    rw [hcardN] at hrank
    omega
  refine ⟨{
    r := r
    rows := rows
    cols := cols
    hcols := hcols
    rank_eq := hrank
    card_eq := hcomplement
    r_le := hrle
    kernel := ?_
    degree := ?_
    pairLI := ?_ }⟩
  · intro j
    simpa only [score6400SelectedLocatorCramerVector] using hkernel j
  · intro j n
    have hj := hdegree j n
    simpa only [score6400SelectedLocatorCramerVector] using
      hj.trans (Nat.mul_le_mul_right 2130706433 hrle)
  · unfold score6400SelectedLocatorFractionPair
    exact linearIndependent_score6400SelectedLocatorCramerFractionPairs
      f₀ f₁ rows cols hcols hminor

end ProximityPrize.SubmissionLower
