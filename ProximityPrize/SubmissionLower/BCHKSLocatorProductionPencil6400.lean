import ProximityPrize.SubmissionLower.BCHKSLocatorSyndrome6400

/-!
# Production two-Frobenius locator pencil

This module reindexes a selected `76781`-by-`76781` transpose of the direct
syndrome-Hankel stack into the two column blocks used by the checked
Kronecker-separation theorem.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark
open BCHKSExactSparsification6400

@[simp]
theorem locator_koalaSexticFrobenius_apply (x : IRSProfile.Field) :
    koalaSexticFrobenius x = x ^ 2130706433 := by
  rw [koalaSexticFrobenius, frobeniusEquiv_def]

abbrev Score6400LocatorMinorIndex :=
  Fin locatorOrdinaryRows6400 ⊕ Fin locatorFrobeniusRows6400

/-- Reindex the selected ordinary and Frobenius equations by the locator
coefficient coordinates. -/
noncomputable def score6400LocatorCoefficientEquiv :
    Score6400LocatorMinorIndex ≃ Fin (76780 + 1) :=
  finSumFinEquiv.trans (finCongr (by
    norm_num [locatorOrdinaryRows6400, locatorFrobeniusRows6400]))

/-- One coefficient matrix part of the transposed selected stack.  Ordinary
equations occupy the left columns and first-Frobenius equations the right
columns. -/
noncomputable def score6400LocatorStackPart
    (f : IRSProfile.Index → IRSProfile.Field) :
    Matrix Score6400LocatorMinorIndex Score6400LocatorMinorIndex
      IRSProfile.Field
  | coefficient, Sum.inl row =>
      rsSyndromeMoment IRSProfile.domain f
        (row.1 + (score6400LocatorCoefficientEquiv coefficient).1)
  | coefficient, Sum.inr row =>
      koalaSexticFrobenius
        (rsSyndromeMoment IRSProfile.domain f
          (row.1 + (score6400LocatorCoefficientEquiv coefficient).1))

theorem score6400LocatorStack_specialize_ordinary
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (coefficient : Score6400LocatorMinorIndex)
    (row : Fin locatorOrdinaryRows6400) :
    twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433) coefficient (Sum.inl row) =
      rsSyndromeMoment IRSProfile.domain (fun i => f₀ i + z * f₁ i)
        (row.1 + (score6400LocatorCoefficientEquiv coefficient).1) := by
  rw [rsSyndromeMoment_affine]
  rfl

theorem score6400LocatorStack_specialize_frobenius
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field) (coefficient : Score6400LocatorMinorIndex)
    (row : Fin locatorFrobeniusRows6400) :
    twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433) coefficient (Sum.inr row) =
      koalaSexticFrobenius
        (rsSyndromeMoment IRSProfile.domain (fun i => f₀ i + z * f₁ i)
          (row.1 + (score6400LocatorCoefficientEquiv coefficient).1)) := by
  rw [rsSyndromeMoment_affine, map_add, map_mul,
    locator_koalaSexticFrobenius_apply]
  rfl

/-- A nonzero Frobenius-fixed locator in the direct Hankel kernel gives a
transpose kernel for the selected square two-block stack. -/
theorem score6400_locatorStack_transpose_ker_ne_bot_of_fixed_hankel_locator
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (locator : Fin (76780 + 1) → IRSProfile.Field)
    (hlocatorNe : locator ≠ 0)
    (hlocatorFixed : ∀ j,
      koalaSexticFrobenius (locator j) = locator j)
    (hlocatorMem : locator ∈ LinearMap.ker
      (rsSyndromeHankel IRSProfile.domain
        (fun i => f₀ i + z * f₁ i)
        locatorOrdinaryRows6400 76780).mulVecLin) :
    LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).transpose.mulVecLin ≠ ⊥ := by
  classical
  let locator' : Score6400LocatorMinorIndex → IRSProfile.Field :=
    fun j => locator (score6400LocatorCoefficientEquiv j)
  have hlocator'Ne : locator' ≠ 0 := by
    intro hzero
    apply hlocatorNe
    funext j
    obtain ⟨i, rfl⟩ := score6400LocatorCoefficientEquiv.surjective j
    exact congrFun hzero i
  have hordinary := hlocatorMem
  rw [LinearMap.mem_ker] at hordinary
  have hlocator'Ker : locator' ∈ LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).transpose.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext equation
    rcases equation with row | row
    · simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, Pi.zero_apply]
      calc
        (∑ coefficient : Score6400LocatorMinorIndex,
            twoBlockSpecialization
                (score6400LocatorStackPart f₀)
                (score6400LocatorStackPart f₁)
                z (z ^ 2130706433) coefficient (Sum.inl row) *
              locator' coefficient) =
            ∑ j : Fin (76780 + 1),
              rsSyndromeMoment IRSProfile.domain
                  (fun i => f₀ i + z * f₁ i) (row.1 + j.1) * locator j := by
          apply Fintype.sum_equiv score6400LocatorCoefficientEquiv
          intro coefficient
          rw [score6400LocatorStack_specialize_ordinary]
        _ = 0 := by
          have hrow := congrFun hordinary row
          simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
            rsSyndromeHankel, Pi.zero_apply] using hrow
    · simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, Pi.zero_apply]
      let ordinaryRow : Fin locatorOrdinaryRows6400 :=
        ⟨row.1, by
          exact Nat.lt_trans row.2 (by
            norm_num [locatorOrdinaryRows6400,
              locatorFrobeniusRows6400])⟩
      have hrow := congrFun hordinary ordinaryRow
      have hrow' : ∑ j : Fin (76780 + 1),
          rsSyndromeMoment IRSProfile.domain
              (fun i => f₀ i + z * f₁ i) (row.1 + j.1) * locator j = 0 := by
        simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
          rsSyndromeHankel, Pi.zero_apply, ordinaryRow] using hrow
      calc
        (∑ coefficient : Score6400LocatorMinorIndex,
            twoBlockSpecialization
                (score6400LocatorStackPart f₀)
                (score6400LocatorStackPart f₁)
                z (z ^ 2130706433) coefficient (Sum.inr row) *
              locator' coefficient) =
            ∑ j : Fin (76780 + 1),
              koalaSexticFrobenius
                (rsSyndromeMoment IRSProfile.domain
                    (fun i => f₀ i + z * f₁ i) (row.1 + j.1) * locator j) := by
          apply Fintype.sum_equiv score6400LocatorCoefficientEquiv
          intro coefficient
          rw [score6400LocatorStack_specialize_frobenius, map_mul,
            hlocatorFixed]
        _ = koalaSexticFrobenius
            (∑ j : Fin (76780 + 1),
              rsSyndromeMoment IRSProfile.domain
                  (fun i => f₀ i + z * f₁ i) (row.1 + j.1) * locator j) := by
          rw [map_sum]
        _ = 0 := by rw [hrow', map_zero]
  intro hbot
  apply hlocator'Ne
  have : locator' ∈ (⊥ : Submodule IRSProfile.Field
      (Score6400LocatorMinorIndex → IRSProfile.Field)) := by
    rw [← hbot]
    exact hlocator'Ker
  simpa using this

/-- Every concrete score-64 bad slope makes the same selected square
ordinary/Frobenius stack singular. -/
theorem score6400_locatorStack_transpose_ker_ne_bot_of_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (z : IRSProfile.Field)
    (hbad : MCABad IRSProfile.baseCode f₀ f₁ 185364 z) :
    LinearMap.ker
      (twoBlockSpecialization
        (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
        z (z ^ 2130706433)).transpose.mulVecLin ≠ ⊥ := by
  obtain ⟨locator, hlocatorNe, hlocatorFixed, hlocatorMem⟩ :=
    exists_score6400_fixed_locator_of_mcaBad f₀ f₁ z hbad
  exact score6400_locatorStack_transpose_ker_ne_bot_of_fixed_hankel_locator
    f₀ f₁ z locator hlocatorNe hlocatorFixed hlocatorMem

/-- If more score-64 bad slopes exist than the diagonal degree budget, then
the selected two-parameter locator minor vanishes identically.  This is the
exact cheap/structural dichotomy boundary for the direct-locator route. -/
theorem score6400_locatorBivariate_det_eq_zero_of_many_mcaBad
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field)
    (T : Finset IRSProfile.Field)
    (hcard : locatorDiagonalDegree6400 < T.card)
    (hbad : ∀ z ∈ T, MCABad IRSProfile.baseCode f₀ f₁ 185364 z) :
    (twoBlockBivariatePencil
      (score6400LocatorStackPart f₀)
      (score6400LocatorStackPart f₁)).det = 0 := by
  apply twoBlockBivariate_det_eq_zero_of_many_frobenius_transpose_kernels
    T 2130706433 (score6400LocatorStackPart f₀)
      (score6400LocatorStackPart f₁)
  · norm_num
  · simp only [Fintype.card_fin]
    norm_num [locatorOrdinaryRows6400]
  · simpa only [Fintype.card_fin, locatorDiagonalDegree6400] using hcard
  · intro z hz
    exact score6400_locatorStack_transpose_ker_ne_bot_of_mcaBad
      f₀ f₁ z (hbad z hz)

end ProximityPrize.SubmissionLower
