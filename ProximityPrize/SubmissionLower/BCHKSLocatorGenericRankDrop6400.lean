import ProximityPrize.SubmissionLower.BCHKSLocatorRelationReverse6400
import ProximityPrize.SubmissionLower.BCHKSBoundedCramerFamilyData6400

/-!
# A fixed generic minor detects every local locator rank drop

Choose a maximal minor of the production locator matrix over the rational
function field.  Its determinant is a single nonzero challenge polynomial.
Whenever specialization increases the locator-kernel nullity above the
generic value, that fixed determinant must vanish.  Its degree is at most one
production Cramer budget.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial
open ProximityPrize.Benchmark

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A single nonzero polynomial of degree at most `76779*p` contains every
challenge where the specialized locator kernel has nullity larger than its
generic nullity `L`. -/
theorem exists_score6400_genericPivot_rankDropPolynomial
    (f₀ f₁ : IRSProfile.Index → IRSProfile.Field) (L : Nat)
    (hkernelRank : Module.finrank
      (FractionRing IRSProfile.Field[X])
      (LinearMap.ker
        ((score6400LocatorPolynomialMatrix f₀ f₁).map
          (algebraMap IRSProfile.Field[X]
            (FractionRing IRSProfile.Field[X]))).mulVecLin) = L)
    (hLtwo : 2 ≤ L) :
    ∃ Δ : IRSProfile.Field[X],
      Δ ≠ 0 ∧
      Δ.natDegree ≤ 76779 * 2130706433 ∧
      ∀ z : IRSProfile.Field,
        L < Module.finrank IRSProfile.Field
          (LinearMap.ker
            (twoBlockSpecialization
              (score6400LocatorStackPart f₀)
              (score6400LocatorStackPart f₁)
              z (z ^ 2130706433)).mulVecLin) →
        Δ.eval z = 0 := by
  classical
  obtain ⟨r, rows, cols, _hrows, hcols, hrank, hcomplement,
      hdet, _hkernel, _hdegree, _hspan⟩ :=
    exists_score6400_spanning_bounded_locatorCramerFamily
      f₀ f₁ L hkernelRank
  let M := score6400LocatorPolynomialMatrix f₀ f₁
  let Δ : IRSProfile.Field[X] :=
    (selectedPolynomialPivotBlock M rows cols).det
  have hΔne : Δ ≠ 0 := by
    intro hzero
    apply hdet
    simp only [Δ, M, hzero, map_zero]
  have hcard : Fintype.card Score6400LocatorMinorIndex = 76781 := by
    norm_num [Score6400LocatorMinorIndex, locatorOrdinaryRows6400,
      locatorFrobeniusRows6400]
  have hrle : r ≤ 76779 := by
    rw [hcard] at hrank
    omega
  have hΔdegreeRaw : Δ.natDegree ≤ r * 2130706433 := by
    change (selectedPolynomialPivotBlock M rows cols).det.natDegree ≤
      r * 2130706433
    have hbound := polynomialMatrix_det_natDegree_le_card_mul
      (selectedPolynomialPivotBlock M rows cols) 2130706433 (by
        intro i j
        change (score6400LocatorPolynomialMatrix f₀ f₁
          (rows i) (cols j)).natDegree ≤ 2130706433
        exact score6400LocatorPolynomialMatrix_entry_natDegree_le
          f₀ f₁ (rows i) (cols j))
    simpa only [Fintype.card_fin] using hbound
  have hΔdegree : Δ.natDegree ≤ 76779 * 2130706433 :=
    hΔdegreeRaw.trans (Nat.mul_le_mul_right 2130706433 hrle)
  refine ⟨Δ, hΔne, hΔdegree, ?_⟩
  intro z hlocal
  by_contra hΔeval
  have hdetEval :
      (Polynomial.evalRingHom z)
        (selectedPolynomialPivotBlock M rows cols).det ≠ 0 := by
    change (selectedPolynomialPivotBlock M rows cols).det.eval z ≠ 0
    simpa only [Δ] using hΔeval
  have htop := finrank_selectedRows_ker_eq_card_complement
    (Polynomial.evalRingHom z) M rows cols hcols hdetEval
  have htopL : Module.finrank IRSProfile.Field
      (LinearMap.ker
        ((((M.submatrix rows (Equiv.refl Score6400LocatorMinorIndex)).map
          (Polynomial.evalRingHom z))).mulVecLin)) = L := by
    simpa only [hcomplement] using htop
  have hfullLe := fullMatrix_ker_le_selectedRows_ker
    (Polynomial.evalRingHom z) M rows
  have hfinrankLe := Submodule.finrank_mono hfullLe
  have hfullCap : Module.finrank IRSProfile.Field
      (LinearMap.ker
        ((M.map (Polynomial.evalRingHom z)).mulVecLin)) ≤ L := by
    rw [htopL] at hfinrankLe
    exact hfinrankLe
  have hlocal' : L < Module.finrank IRSProfile.Field
      (LinearMap.ker
        ((M.map (Polynomial.evalRingHom z)).mulVecLin)) := by
    have hmap : M.map (Polynomial.evalRingHom z) =
        twoBlockSpecialization
          (score6400LocatorStackPart f₀) (score6400LocatorStackPart f₁)
          z (z ^ 2130706433) := by
      exact score6400LocatorPolynomialMatrix_map_eval f₀ f₁ z
    rw [hmap]
    exact hlocal
  omega

end ProximityPrize.SubmissionLower
