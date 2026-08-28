import ProximityPrize.SubmissionLower.ActualCurveProjectionBounds
import ProximityPrize.SubmissionLower.ActualPlaneSparsePositiveOrder

/-!
# Actual curve projection bounds with one sparse plane gate

The finrank bound remains the established rectangular mixed degree.  Only the
characteristic proof for the resultant is sharpened, so all downstream point
counts retain their previous budgets.
-/

namespace ProximityPrize.SubmissionLower.ActualCurveSparseProjectionBounds

open ActualCurveCoordinateField ActualCurveRationalProjection
  ActualCurveProjectionBounds TrivariateRationalCollection
  ActualPlaneCoordinateDegree
open ActualPlanePositiveOrder ActualPlaneSparsePositiveOrder
open ActualPlaneCoordinateKernel

noncomputable section

variable (K : Type) [Field K]

private def sparseSingleSummary (P : Ideal (Original K)) [P.IsPrime]
    (A : Algebra (RatFunc K) (CoordinateField K P)) (B : ℕ) : Prop :=
  letI := A
  FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
    Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
    Module.finrank (RatFunc K) (CoordinateField K P) ≤ B

private def sparseFamilySummary {I : Type} [Fintype I]
    (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (A : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i))) (B : ℕ) : Prop :=
  letI := A
  (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
    Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
    (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤ B

section Single

variable (order : Fin 3 ≃ Fin 3) (P : Ideal (Original K)) [P.IsPrime]
variable (ht : Transcendental K (coordinate K P (order 0)))

theorem original_finite_separable_finrank_bound_sparse
    (p : ℕ) [CharP K p] (G H : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hHmem : H ∈ P) (hproper : ¬ G ∣ H)
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
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order 0) ht
    FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
      Module.finrank (RatFunc K) (CoordinateField K P) ≤
        originalMixedDegree K order G H := by
  obtain ⟨order', hbase, hbudget, hpos, houter, hres⟩ :=
    exists_positive_sparse_characteristic_order K order P G H p hG hGmem ht h1 h2
      NG MH LG LH NZ hNG hMH hNZ hNGjoint hMHjoint hGcap hHcap hsparse hswap
  have ht' : Transcendental K (coordinate K P (order' 0)) := by
    simpa only [hbase] using ht
  have hresult :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P (order' 0) ht'
      FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
        Algebra.IsSeparable (RatFunc K) (CoordinateField K P) ∧
        Module.finrank (RatFunc K) (CoordinateField K P) ≤
          originalMixedDegree K order' G H := by
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (order' 0) ht'
    obtain ⟨hfd, hsep, hbound⟩ := actual_finite_separable_finrank_bound
      K order' P ht' p G H hG hGmem hHmem hproper hpos houter hres
    exact ⟨hfd, hsep, hbound.trans (plane_budget_le_original K order' G H)⟩
  change sparseSingleSummary K P (rationalBaseAlgebra K P (order' 0) ht')
    (originalMixedDegree K order' G H) at hresult
  rw [rationalBaseAlgebra_congr K P (order' 0) (order 0) hbase ht' ht, hbudget] at hresult
  exact hresult

end Single

section Family

variable (order : Fin 3 ≃ Fin 3) {I : Type} [Fintype I]
variable (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]

theorem original_finite_separable_sum_finrank_bound_sparse
    (ht : ∀ i, Transcendental K (coordinate K (P i) (order 0)))
    (hinj : Function.Injective P) (p : ℕ) [CharP K p] (G H : Original K)
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
    letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
      fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)
    (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
      Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
      (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
        originalMixedDegree K order G H := by
  classical
  by_cases hI : Nonempty I
  · let i₀ : I := Classical.choice hI
    obtain ⟨order', hbase, hbudget, hpos, houter, hres⟩ :=
      exists_positive_sparse_characteristic_order K order (P i₀) G H p
        hG (hGmem i₀) (ht i₀) h1 h2 NG MH LG LH NZ
        hNG hMH hNZ hNGjoint hMHjoint hGcap hHcap hsparse hswap
    have ht' : ∀ i, Transcendental K (coordinate K (P i) (order' 0)) := by
      intro i
      simpa only [hbase] using ht i
    have hresult :
        letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
          fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
        (∀ i, FiniteDimensional (RatFunc K) (CoordinateField K (P i)) ∧
          Algebra.IsSeparable (RatFunc K) (CoordinateField K (P i))) ∧
          (∑ i, Module.finrank (RatFunc K) (CoordinateField K (P i))) ≤
            originalMixedDegree K order' G H := by
      letI : ∀ i, Algebra (RatFunc K) (CoordinateField K (P i)) :=
        fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)
      obtain ⟨hfields, hbound⟩ := actual_finite_separable_sum_finrank_bound
        K order' P ht' hinj p G H hG hGmem hHmem hproper hpos houter hres
      exact ⟨hfields, hbound.trans (plane_budget_le_original K order' G H)⟩
    have halg : (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i)) =
        (fun i => rationalBaseAlgebra K (P i) (order 0) (ht i)) := by
      funext i
      exact rationalBaseAlgebra_congr K (P i) (order' 0) (order 0)
        hbase (ht' i) (ht i)
    change sparseFamilySummary K P
      (fun i => rationalBaseAlgebra K (P i) (order' 0) (ht' i))
      (originalMixedDegree K order' G H) at hresult
    rw [halg, hbudget] at hresult
    exact hresult
  · letI : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    constructor
    · intro i
      exact isEmptyElim i
    · simp

end Family

end

#print axioms original_finite_separable_finrank_bound_sparse
#print axioms original_finite_separable_sum_finrank_bound_sparse

end ProximityPrize.SubmissionLower.ActualCurveSparseProjectionBounds
