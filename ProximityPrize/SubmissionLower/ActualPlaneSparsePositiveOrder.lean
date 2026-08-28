import ProximityPrize.SubmissionLower.ActualPlanePositiveOrder
import ProximityPrize.SubmissionLower.ActualPlaneSparseCoordinateCaps

/-!
# Positive plane order with a sparse first-orientation gate

For the preferred outer variable we use the Newton-trapezoid resultant
bound.  If that variable has degree zero, the existing two-variable swap is
forced; in that branch the vanished inner degree deletes one rectangular
resultant term, so only the opposite cross product is needed.
-/

namespace ProximityPrize.SubmissionLower.ActualPlaneSparsePositiveOrder

open ActualCurveCoordinateField TrivariateRationalCollection
open ActualPlaneCoordinateKernel ActualPlaneCoordinateCaps
open ActualPlanePositiveOrder ActualPlaneSparseCoordinateCaps

noncomputable section

variable (K : Type) [Field K]

theorem swapped_planeMap_degreeX_le_outer_natDegree
    (order : Fin 3 ≃ Fin 3) (F : Original K) :
    Polynomial.Bivariate.degreeX (planeMap K (swapOtherOrder order) F) ≤
      (planeMap K order F).natDegree := by
  have hrename :
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
        (rationalMap K order F)).degreeOf 1 =
          (rationalMap K order F).degreeOf 0 := by
    simpa only [Equiv.swap_apply_left] using
      (MvPolynomial.degreeOf_rename_of_injective
        (p := rationalMap K order F) (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2))
  change Polynomial.Bivariate.degreeX
      (bivariateEquiv (RatFunc K) (rationalMap K (swapOtherOrder order) F)) ≤
    (bivariateEquiv (RatFunc K) (rationalMap K order F)).natDegree
  rw [rationalMap_swapOtherOrder]
  change Polynomial.Bivariate.degreeX
      (bivariateEquiv (RatFunc K)
        (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (rationalMap K order F))) ≤ _
  calc
    _ ≤ (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
        (rationalMap K order F)).degreeOf 1 :=
      bivariateEquiv_degreeX_le (RatFunc K) _
    _ = (rationalMap K order F).degreeOf 0 := hrename
    _ = _ := (bivariateEquiv_natDegree (RatFunc K) (rationalMap K order F)).symm

/-- A preferred sparse orientation, with a rectangular fallback only when
the preferred outer degree vanishes. -/
theorem exists_positive_sparse_characteristic_order
    (order : Fin 3 ≃ Fin 3)
    (P : Ideal (Original K)) [P.IsPrime] (G H : Original K) (p : ℕ)
    (hG : Irreducible G) (hmem : G ∈ P)
    (ht : Transcendental K (coordinate K P (order 0)))
    (h1 : G.degreeOf (order 1) < p) (h2 : G.degreeOf (order 2) < p)
    (NG MH LG LH NZ : ℕ)
    (hNG : G.degreeOf (order 1) ≤ NG)
    (hMH : H.degreeOf (order 1) ≤ MH)
    (hNZ : G.degreeOf (order 2) ≤ NZ)
    (hNGjoint : NG ≤ LG) (hMHjoint : MH ≤ LH)
    (hGcap : ∀ d ∈ G.support, d (order 1) + d (order 2) ≤ LG)
    (hHcap : ∀ d ∈ H.support, d (order 1) + d (order 2) ≤ LH)
    (hsparse : MH * LG + NG * LH < p + NG * MH)
    (hswap : NZ * MH < p) :
    ∃ order' : Fin 3 ≃ Fin 3,
      order' 0 = order 0 ∧
      originalMixedDegree K order' G H = originalMixedDegree K order G H ∧
      0 < (planeMap K order' G).natDegree ∧
      (planeMap K order' G).natDegree < p ∧
      (Polynomial.resultant (planeMap K order' G) (planeMap K order' H)).natDegree < p := by
  have hirr := rationalMap_irreducible_of_component K order P G hG hmem ht
  have hpositive := positive_degree_of_irreducible (rationalMap K order G) hirr
  by_cases houter : 0 < (rationalMap K order G).degreeOf 0
  · have hpos : 0 < (planeMap K order G).natDegree := by
      change 0 < (bivariateEquiv (RatFunc K) (rationalMap K order G)).natDegree
      rw [bivariateEquiv_natDegree]
      exact houter
    have hplaneG : (planeMap K order G).natDegree ≤ NG :=
      (planeMap_natDegree_le K order G).trans hNG
    have hplaneH : (planeMap K order H).natDegree ≤ MH :=
      (planeMap_natDegree_le K order H).trans hMH
    have hres := planeMap_resultant_natDegree_lt_of_sparse_caps K order G H
      NG MH LG LH p hplaneG hplaneH hNGjoint hMHjoint
      (rationalMap_support_pair_cap K order G LG hGcap)
      (rationalMap_support_pair_cap K order H LH hHcap) hsparse
    exact ⟨order, rfl, rfl, hpos,
      (planeMap_natDegree_le K order G).trans_lt h1, hres⟩
  · have hzero : (planeMap K order G).natDegree = 0 := by
      change (bivariateEquiv (RatFunc K) (rationalMap K order G)).natDegree = 0
      rw [bivariateEquiv_natDegree]
      exact Nat.eq_zero_of_not_pos houter
    have hinnerZero :
        Polynomial.Bivariate.degreeX (planeMap K (swapOtherOrder order) G) = 0 :=
      Nat.eq_zero_of_le_zero ((swapped_planeMap_degreeX_le_outer_natDegree K order G).trans_eq hzero)
    have hsecond : 0 < (rationalMap K order G).degreeOf 1 := by
      rcases hpositive with hfirst | hsecond
      · exact (houter hfirst).elim
      · exact hsecond
    have hpos : 0 < (planeMap K (swapOtherOrder order) G).natDegree := by
      rwa [swapped_outer_degree]
    have hres :
        (Polynomial.resultant (planeMap K (swapOtherOrder order) G)
          (planeMap K (swapOtherOrder order) H)).natDegree < p := by
      have hstd := bivariate_resultant_natDegree_le
        (planeMap K (swapOtherOrder order) G)
        (planeMap K (swapOtherOrder order) H)
        (planeMap K (swapOtherOrder order) G).natDegree
        (planeMap K (swapOtherOrder order) H).natDegree
      have hgOuter : (planeMap K (swapOtherOrder order) G).natDegree ≤ NZ :=
        (planeMap_natDegree_le K (swapOtherOrder order) G).trans (by
          simpa only [swapOtherOrder_one] using hNZ)
      have hhInner :
          Polynomial.Bivariate.degreeX (planeMap K (swapOtherOrder order) H) ≤ MH :=
        (planeMap_degreeX_le K (swapOtherOrder order) H).trans (by
          simpa only [swapOtherOrder_two] using hMH)
      calc
        _ ≤ (planeMap K (swapOtherOrder order) H).natDegree *
              Polynomial.Bivariate.degreeX (planeMap K (swapOtherOrder order) G) +
            (planeMap K (swapOtherOrder order) G).natDegree *
              Polynomial.Bivariate.degreeX (planeMap K (swapOtherOrder order) H) := hstd
        _ = (planeMap K (swapOtherOrder order) G).natDegree *
              Polynomial.Bivariate.degreeX (planeMap K (swapOtherOrder order) H) := by
            simp [hinnerZero]
        _ ≤ NZ * MH := Nat.mul_le_mul hgOuter hhInner
        _ < p := hswap
    exact ⟨swapOtherOrder order, swapOtherOrder_zero order,
      originalMixedDegree_swap K order G H, hpos,
      (planeMap_natDegree_le K (swapOtherOrder order) G).trans_lt (by
        simpa only [swapOtherOrder_one] using h2), hres⟩

end


#print axioms swapped_planeMap_degreeX_le_outer_natDegree
#print axioms exists_positive_sparse_characteristic_order

end ProximityPrize.SubmissionLower.ActualPlaneSparsePositiveOrder
