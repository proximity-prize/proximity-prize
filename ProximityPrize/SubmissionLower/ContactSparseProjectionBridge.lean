import ProximityPrize.SubmissionLower.ContactSparseResultant
import ProximityPrize.SubmissionLower.ActualCoordinateDegreeSum

/-!
# Sparse base-R projection bridge

The Y- and Z-base coordinate projections retain the old rectangle gates.
The R-base projection uses the joint Y+Z support and the sparse resultant,
with an actual zero-Y outer-degree fallback to the Z-outer chart.  Final
coordinate-degree budgets remain the original rectangular mixed degrees.
-/

namespace ProximityPrize.SubmissionLower.ContactSparseProjectionBridge

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ActualCurveProjectionBounds ActualCoordinateDegreeSum ActualPlanePositiveOrder
open ContactSparseResultant TrivariateRationalCollection

noncomputable section

variable (K : Type) [Field K]

/-- Finite/separable projection property with only the base-R gate replaced
by the sparse joint-support certificate. -/
theorem projectionsFiniteSeparable_of_sparse_rBase_gates
    (P : Ideal (Original K)) [P.IsPrime] (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P) (hproper : ¬ G ∣ T)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree K G T 0 < p)
    (hmixed2 : coordinateMixedDegree K G T 2 < p)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap K rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap K rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t)
    (hgy : gy < p) (hg : g < p) (hprod : g * ty < p)
    (hsparse : gy * t + ty * g - gy * ty < p) :
    ProjectionsFiniteSeparable K P := by
  intro i hi
  fin_cases i
  · let order : Fin 3 ≃ Fin 3 := Equiv.refl (Fin 3)
    have ht : Transcendental K (coordinate K P (order 0)) := by simpa [order] using hi
    have hm : originalMixedDegree K order G T < p := by
      simpa [order, coordinateMixedDegree_zero, originalMixedDegree] using hmixed0
    have hr := original_finite_separable_finrank_bound K order P ht p G T
      hG hGmem hTmem hproper (hdegree (order 1)) (hdegree (order 2)) hm
    have halg : rationalBaseAlgebra K P (order 0) ht =
        rationalBaseAlgebra K P 0 hi := by
      apply rationalBaseAlgebra_congr K P
      simp [order]
    rw [halg] at hr
    exact ⟨hr.1, hr.2.1⟩
  · have ht : Transcendental K (coordinate K P (rBaseYOuterOrder 0)) := by
      simpa using hi
    have hr := original_finite_separable_finrank_bound_rBase_sparse K P ht p G T
      hG hGmem hTmem hproper gy ty g t hGY hTY hGtotalY hTtotalY hGtotalZ
      hyg hyt hgy hg hprod hsparse
    have halg : rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht =
        rationalBaseAlgebra K P 1 hi := by
      apply rationalBaseAlgebra_congr K P
      simp
    rw [halg] at hr
    exact ⟨hr.1, hr.2.1⟩
  · let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
    have ht : Transcendental K (coordinate K P (order 0)) := by simpa [order] using hi
    have hm : originalMixedDegree K order G T < p := by
      simpa [order, coordinateMixedDegree_two, originalMixedDegree,
        Equiv.swap_apply_def, Nat.add_comm, Nat.mul_comm] using hmixed2
    have hr := original_finite_separable_finrank_bound K order P ht p G T
      hG hGmem hTmem hproper (hdegree (order 1)) (hdegree (order 2)) hm
    have halg : rationalBaseAlgebra K P (order 0) ht =
        rationalBaseAlgebra K P 2 hi := by
      apply rationalBaseAlgebra_congr K P
      simp [order]
    rw [halg] at hr
    exact ⟨hr.1, hr.2.1⟩

/-- Summed actual base-R coordinate degrees consume the old rectangular
mixed budget, even though separability is certified by the sparse bound. -/
theorem sum_actualCoordinateDegree_rBase_le_sparse
    {I : Type} [Fintype I] (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P) (p : ℕ) [CharP K p] (G T : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i) (hTmem : ∀ i, T ∈ P i)
    (hproper : ¬ G ∣ T)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap K rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap K rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t)
    (hgy : gy < p) (hg : g < p) (hprod : g * ty < p)
    (hsparse : gy * t + ty * g - gy * ty < p) :
    (∑ i, actualCoordinateDegree K (P i) 1) ≤ coordinateMixedDegree K G T 1 := by
  classical
  let sI : Set I := {i | Transcendental K (coordinate K (P i) 1)}
  have htrans (i : sI) : Transcendental K (coordinate K (P i) 1) := by
    have hi := i.property
    change Transcendental K (coordinate K (P i) 1) at hi
    exact hi
  let D : sI → ℕ := fun i =>
    letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
      rationalBaseAlgebra K (P i) (rBaseYOuterOrder 0) (by simpa using htrans i)
    Module.finrank (RatFunc K) (CoordinateField K (P i))
  have hinj' : Function.Injective (fun i : sI => P i) := by
    intro i j h
    apply Subtype.ext
    exact hinj h
  have hbound : (∑ i : sI, D i) ≤ originalMixedDegree K rBaseYOuterOrder G T := by
    have hr := original_finite_separable_sum_finrank_bound_rBase_sparse K
      (fun i : sI => P i) (fun i => by simpa using htrans i) hinj' p G T hG
      (fun i => hGmem i) (fun i => hTmem i) hproper gy ty g t hGY hTY
      hGtotalY hTtotalY hGtotalZ hyg hyt hgy hg hprod hsparse
    exact hr.2
  calc
    (∑ i, actualCoordinateDegree K (P i) 1) = ∑ i : sI, D i := by
      apply Finset.sum_congr_set sI (fun i => actualCoordinateDegree K (P i) 1) D
      · intro i hi
        exact actualCoordinateDegree_of_transcendental K (P i) 1 hi
      · intro i hi
        change ¬ Transcendental K (coordinate K (P i) 1) at hi
        exact dif_neg hi
    _ ≤ originalMixedDegree K rBaseYOuterOrder G T := hbound
    _ = coordinateMixedDegree K G T 1 := by
      simp [coordinateMixedDegree, rBaseYOuterOrder]

end

end ProximityPrize.SubmissionLower.ContactSparseProjectionBridge

#print axioms ProximityPrize.SubmissionLower.ContactSparseProjectionBridge.projectionsFiniteSeparable_of_sparse_rBase_gates
#print axioms ProximityPrize.SubmissionLower.ContactSparseProjectionBridge.sum_actualCoordinateDegree_rBase_le_sparse

