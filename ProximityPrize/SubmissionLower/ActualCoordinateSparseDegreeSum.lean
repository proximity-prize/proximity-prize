import ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum
import ProximityPrize.SubmissionLower.ActualCurveSparseProjectionBounds

/-!
# Coordinate degree sums with a sparse middle projection

Only coordinate `1` (the contact slope/base coordinate) uses the sparse
`0+2` Newton support.  Coordinates `0` and `2` retain the established
rectangular characteristic gates.
-/

namespace ProximityPrize.SubmissionLower.ActualCoordinateSparseDegreeSum

open ActualCurveCoordinateField ActualCurveRationalProjection
  TrivariateRationalCollection ActualCurveZeroCount ActualPlanePositiveOrder
  ActualCurveProjectionBounds ActualCurveSparseProjectionBounds
  ActualCoordinateDegreeSum

noncomputable section

variable (K : Type) [Field K]

section Family

variable {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]

theorem sum_actualCoordinateDegree_le_original_sparse
    (order : Fin 3 ≃ Fin 3) (hinj : Function.Injective P)
    (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hHmem : ∀ i, H ∈ P i)
    (hproper : ¬ G ∣ H)
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
    (∑ i, actualCoordinateDegree K (P i) (order 0)) ≤
      originalMixedDegree K order G H := by
  classical
  let s : Set I := {i | Transcendental K (coordinate K (P i) (order 0))}
  let D : s → ℕ := fun i =>
    letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
      rationalBaseAlgebra K (P i) (order 0) i.2
    Module.finrank (RatFunc K) (CoordinateField K (P i))
  have hinj' : Function.Injective (fun i : s => P i) := by
    intro i j h
    apply Subtype.ext
    exact hinj h
  have hbound : (∑ i : s, D i) ≤ originalMixedDegree K order G H := by
    have h := original_finite_separable_sum_finrank_bound_sparse K order
      (fun i : s => P i) (fun i => i.2) hinj' p G H hG
      (fun i => hGmem i) (fun i => hHmem i) hproper h1 h2
      NG MH LG LH NZ hNG hMH hNZ hNGjoint hMHjoint hGcap hHcap hsparse hswap
    exact h.2
  calc
    _ = ∑ i : s, D i := by
      apply Finset.sum_congr_set s (fun i => actualCoordinateDegree K (P i) (order 0)) D
      · intro i hi
        exact actualCoordinateDegree_of_transcendental K (P i) (order 0) hi
      · intro i hi
        change ¬ Transcendental K (coordinate K (P i) (order 0)) at hi
        exact dif_neg hi
    _ ≤ _ := hbound

end Family

section Single

theorem finiteSeparable_at_of_original_gate
    (P : Ideal (Original K)) [P.IsPrime] (i : Fin 3)
    (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P) (hproper : ¬ G ∣ H)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed : coordinateMixedDegree K G H i < p)
    (hi : Transcendental K (coordinate K P i)) :
    letI : Algebra (RatFunc K) (CoordinateField K P) := rationalBaseAlgebra K P i hi
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  have hbase : order 0 = i := Equiv.swap_apply_left _ _
  have ht : Transcendental K (coordinate K P (order 0)) := by
    simpa only [hbase] using hi
  have hresult :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P (order 0) ht
      FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
        Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order 0) ht
    have h := original_finite_separable_finrank_bound K order P ht p G H
      hG hGmem hHmem hproper (hdegree (order 1)) (hdegree (order 2)) (by
        simpa only [coordinateMixedDegree] using hmixed)
    exact ⟨h.1, h.2.1⟩
  have halg := rationalBaseAlgebra_congr K P (order 0) i hbase ht hi
  cases hbase
  exact hresult

theorem projectionsFiniteSeparable_of_middle_sparse_gates
    (P : Ideal (Original K)) [P.IsPrime] (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P) (hproper : ¬ G ∣ H)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree K G H 0 < p)
    (hmixed2 : coordinateMixedDegree K G H 2 < p)
    (NG MH LG LH NZ : ℕ)
    (hNG : G.degreeOf 0 ≤ NG) (hMH : H.degreeOf 0 ≤ MH)
    (hNZ : G.degreeOf 2 ≤ NZ)
    (hNGjoint : NG ≤ LG) (hMHjoint : MH ≤ LH)
    (hGcap : ∀ d ∈ G.support, d 0 + d 2 ≤ LG)
    (hHcap : ∀ d ∈ H.support, d 0 + d 2 ≤ LH)
    (hsparse : MH * LG + NG * LH < p + NG * MH)
    (hswap : NZ * MH < p) :
    ProjectionsFiniteSeparable K P := by
  intro i hi
  fin_cases i
  · exact finiteSeparable_at_of_original_gate K P 0 p G H hG hGmem hHmem hproper
      hdegree hmixed0 hi
  · let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
    have ht : Transcendental K (coordinate K P (order 0)) := by
      simpa [order] using hi
    have h := original_finite_separable_finrank_bound_sparse K order P ht p G H
      hG hGmem hHmem hproper (hdegree 0) (hdegree 2)
      NG MH LG LH NZ hNG hMH hNZ hNGjoint hMHjoint
      (by simpa [order, Equiv.swap_apply_def] using hGcap)
      (by simpa [order, Equiv.swap_apply_def] using hHcap) hsparse hswap
    exact ⟨h.1, h.2.1⟩
  · exact finiteSeparable_at_of_original_gate K P 2 p G H hG hGmem hHmem hproper
      hdegree hmixed2 hi

end Single

end


#print axioms sum_actualCoordinateDegree_le_original_sparse
#print axioms finiteSeparable_at_of_original_gate
#print axioms projectionsFiniteSeparable_of_middle_sparse_gates

end ProximityPrize.SubmissionLower.ActualCoordinateSparseDegreeSum

