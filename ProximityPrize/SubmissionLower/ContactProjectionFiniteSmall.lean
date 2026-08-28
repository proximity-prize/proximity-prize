import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ActualCurveZeroCountSmall
import ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeDegree
import ProximityPrize.SubmissionLower.ActualPlaneCharacteristicFreeFamilyDegree
import ProximityPrize.SubmissionLower.ContactSparseProjectionBridge

/-!
# Small characteristic-free projection data for contact components

The Y- and Z-base projections retain their established strict
characteristic certificates.  The sparse base-R projection is allowed
up to (but not including) twice the characteristic and uses the new full
corank theorem instead of a separability argument.
-/

namespace ProximityPrize.SubmissionLower.ContactProjectionFiniteSmall

open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
  ActualCurveProjectionBounds ActualCoordinateDegreeSum
  ActualPlanePositiveOrder ActualPlaneCoordinateDegree
  ActualPlaneCoordinateKernel
  ActualPlaneCharacteristicFreeFamilyDegree
  ActualPlaneCharacteristicFreeDegree
  ContactSparseResultant ContactSparseProjectionBridge
  TrivariateRationalCollection

noncomputable section

variable (K : Type) [Field K]

private def projectionSummary
    (P : Ideal (Original K)) [P.IsPrime]
    (A : Algebra (RatFunc K) (CoordinateField K P)) (p : ℕ) : Prop :=
  letI := A
  FiniteDimensional (RatFunc K) (CoordinateField K P) ∧
    Module.finrank (RatFunc K) (CoordinateField K P) < 2 * p

private def separableSummary
    (P : Ideal (Original K)) [P.IsPrime]
    (A : Algebra (RatFunc K) (CoordinateField K P)) : Prop :=
  letI := A
  Algebra.IsSeparable (RatFunc K) (CoordinateField K P)

/-- Every actual component projection is finite and has full degree below
`2p`; only the base-R arm may be inseparable. -/
theorem projectionsFiniteSmall_of_sparse_rBase_gates
    (P : Ideal (Original K)) [P.IsPrime]
    (p : ℕ) [CharP K p] (hp : p.Prime)
    (G T : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P)
    (hproper : ¬ G ∣ T)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree K G T 0 < p)
    (hmixed2 : coordinateMixedDegree K G T 2 < p)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap K rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap K rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t)
    (hsparse : gy * t + ty * g - gy * ty < 2 * p)
    (hcollapsed : g * ty < 2 * p) :
    ActualCurveZeroCountSmall.ProjectionsFiniteSmall K P p := by
  intro i hi
  fin_cases i
  · let order : Fin 3 ≃ Fin 3 := Equiv.refl (Fin 3)
    have ht : Transcendental K (coordinate K P (order 0)) := by
      simpa [order] using hi
    have hm : originalMixedDegree K order G T < p := by
      simpa [order, coordinateMixedDegree_zero, originalMixedDegree] using hmixed0
    have hr := original_finite_separable_finrank_bound K order P ht p G T
      hG hGmem hTmem hproper (hdegree (order 1)) (hdegree (order 2)) hm
    have halg : rationalBaseAlgebra K P (order 0) ht =
        rationalBaseAlgebra K P 0 hi := by
      apply rationalBaseAlgebra_congr K P
      simp [order]
    have result : projectionSummary K P
        (rationalBaseAlgebra K P (order 0) ht) p :=
      ⟨hr.1, hr.2.2.trans_lt (hm.trans (by omega))⟩
    rw [halg] at result
    exact result

  · have ht : Transcendental K
        (coordinate K P (rBaseYOuterOrder 0)) := by simpa using hi
    letI : Algebra (RatFunc K) (CoordinateField K P) :=
      rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht
    by_cases hy : 0 < (planeMap K rBaseYOuterOrder G).natDegree
    · have hr := actual_finite_finrank_le_resultant_natDegree
        K rBaseYOuterOrder P ht G T hG hGmem hTmem hproper hy
      have hres := planeMap_sparse_resultant_le_caps K rBaseYOuterOrder G T
        gy ty g t hGtotalY hTtotalY hGY hTY hyg hyt
      have hsmall : Module.finrank (RatFunc K) (CoordinateField K P) < 2 * p :=
        (Nat.le_trans hr.2 hres).trans_lt hsparse
      have halg : rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht =
          rationalBaseAlgebra K P 1 hi := by
        apply rationalBaseAlgebra_congr K P
        simp
      have result : projectionSummary K P
          (rationalBaseAlgebra K P (rBaseYOuterOrder 0) ht) p := ⟨hr.1, hsmall⟩
      rw [halg] at result
      exact result
    · have hy0 : (planeMap K rBaseYOuterOrder G).natDegree = 0 :=
        Nat.eq_zero_of_not_pos hy
      obtain ⟨order', hor, hbase, hpos⟩ :=
        exists_positive_outer_order K rBaseYOuterOrder P G hG hGmem ht
      have hzorder : order' = rBaseZOuterOrder := by
        rcases hor with h | h
        · subst order'
          exact (hy hpos).elim
        · exact h
      subst order'
      have htZ : Transcendental K
          (coordinate K P (rBaseZOuterOrder 0)) := by simpa using ht
      have hr := actual_finite_finrank_le_resultant_natDegree
        K rBaseZOuterOrder P htZ G T hG hGmem hTmem hproper hpos
      have hres := planeMap_zOuter_resultant_le_of_yOuter_zero
        K G T g ty hy0 hGtotalZ hTY
      have hsmallZ :
          letI : Algebra (RatFunc K) (CoordinateField K P) :=
            rationalBaseAlgebra K P (rBaseZOuterOrder 0) htZ
          Module.finrank (RatFunc K) (CoordinateField K P) < 2 * p :=
        (Nat.le_trans hr.2 hres).trans_lt hcollapsed
      have halgZ : rationalBaseAlgebra K P (rBaseZOuterOrder 0) htZ =
          rationalBaseAlgebra K P 1 hi := by
        apply rationalBaseAlgebra_congr K P
        simp
      have result : projectionSummary K P
          (rationalBaseAlgebra K P (rBaseZOuterOrder 0) htZ) p :=
        ⟨hr.1, hsmallZ⟩
      rw [halgZ] at result
      exact result
  · let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
    have ht : Transcendental K (coordinate K P (order 0)) := by
      simpa [order] using hi
    have hm : originalMixedDegree K order G T < p := by
      simpa [order, coordinateMixedDegree_two, originalMixedDegree,
        Equiv.swap_apply_def, Nat.add_comm, Nat.mul_comm] using hmixed2
    have hr := original_finite_separable_finrank_bound K order P ht p G T
      hG hGmem hTmem hproper (hdegree (order 1)) (hdegree (order 2)) hm
    have halg : rationalBaseAlgebra K P (order 0) ht =
        rationalBaseAlgebra K P 2 hi := by
      apply rationalBaseAlgebra_congr K P
      simp [order]
    have result : projectionSummary K P
        (rationalBaseAlgebra K P (order 0) ht) p :=
      ⟨hr.1, hr.2.2.trans_lt (hm.trans (by omega))⟩
    rw [halg] at result
    exact result

/-- The complete base-R degree sum consumes the established rectangular
mixed-degree budget without a separability or characteristic-size hypothesis.
The sparse caps are retained because the companion projection theorem uses
the same interface. -/
theorem sum_actualCoordinateDegree_rBase_le_mixed_charfree
    {I : Type} [Fintype I]
    (P : I → Ideal (Original K)) [∀ i, (P i).IsPrime]
    (hinj : Function.Injective P)
    (G T : Original K)
    (hG : Irreducible G) (hGmem : ∀ i, G ∈ P i)
    (hTmem : ∀ i, T ∈ P i) (hproper : ¬ G ∣ T)
    (gy ty g t : ℕ)
    (hGY : G.degreeOf 0 ≤ gy) (hTY : T.degreeOf 0 ≤ ty)
    (hGtotalY : (rationalMap K rBaseYOuterOrder G).totalDegree ≤ g)
    (hTtotalY : (rationalMap K rBaseYOuterOrder T).totalDegree ≤ t)
    (hGtotalZ : (rationalMap K rBaseZOuterOrder G).totalDegree ≤ g)
    (hyg : gy ≤ g) (hyt : ty ≤ t) :
    (∑ i, actualCoordinateDegree K (P i) 1) ≤
      coordinateMixedDegree K G T 1 := by
  classical
  let sI : Set I := {i | Transcendental K (coordinate K (P i) 1)}
  have htrans (i : sI) : Transcendental K (coordinate K (P i) 1) := i.property
  let D : sI → ℕ := fun i ↦
    letI : Algebra (RatFunc K) (CoordinateField K (P i)) :=
      rationalBaseAlgebra K (P i) (rBaseYOuterOrder 0) (by simpa using htrans i)
    Module.finrank (RatFunc K) (CoordinateField K (P i))
  have hinj' : Function.Injective (fun i : sI ↦ P i) := by
    intro i j h
    apply Subtype.ext
    exact hinj h
  have hbound : (∑ i : sI, D i) ≤
      originalMixedDegree K rBaseYOuterOrder G T := by
    by_cases hI : Nonempty sI
    · let i₀ : sI := Classical.choice hI
      by_cases hy : 0 < (planeMap K rBaseYOuterOrder G).natDegree
      · have hr := actual_sum_finrank_le_resultant_natDegree K
          rBaseYOuterOrder (fun i : sI ↦ P i)
          (fun i ↦ by simpa using htrans i) hinj'
          G T hG (fun i ↦ hGmem i) (fun i ↦ hTmem i) hproper hy
        exact hr.trans ((bivariate_resultant_natDegree_le
          (planeMap K rBaseYOuterOrder G) (planeMap K rBaseYOuterOrder T)
          (planeMap K rBaseYOuterOrder G).natDegree
          (planeMap K rBaseYOuterOrder T).natDegree).trans
            (plane_budget_le_original K rBaseYOuterOrder G T))
      · have hy0 : (planeMap K rBaseYOuterOrder G).natDegree = 0 :=
          Nat.eq_zero_of_not_pos hy
        obtain ⟨order', hor, hbase, hpos⟩ := exists_positive_outer_order
          K rBaseYOuterOrder (P i₀) G hG (hGmem i₀)
            (by simpa using htrans i₀)
        have hzorder : order' = rBaseZOuterOrder := by
          rcases hor with h | h
          · subst order'
            exact (hy hpos).elim
          · exact h
        subst order'
        have htZ : ∀ i : sI,
            Transcendental K (coordinate K (P i) (rBaseZOuterOrder 0)) := by
          intro i
          simpa using htrans i
        have hr := actual_sum_finrank_le_resultant_natDegree K
          rBaseZOuterOrder (fun i : sI ↦ P i) htZ hinj'
          G T hG (fun i ↦ hGmem i) (fun i ↦ hTmem i) hproper hpos
        have halg :
            (fun i : sI ↦ rationalBaseAlgebra K (P i)
              (rBaseZOuterOrder 0) (htZ i)) =
            (fun i : sI ↦ rationalBaseAlgebra K (P i)
              (rBaseYOuterOrder 0) (by simpa using htrans i)) := by
          funext i
          apply rationalBaseAlgebra_congr K (P i)
          simp
        rw [halg] at hr
        have hb := (bivariate_resultant_natDegree_le
          (planeMap K rBaseZOuterOrder G) (planeMap K rBaseZOuterOrder T)
          (planeMap K rBaseZOuterOrder G).natDegree
          (planeMap K rBaseZOuterOrder T).natDegree).trans
            (plane_budget_le_original K rBaseZOuterOrder G T)
        simpa [D, rBaseZOuterOrder, originalMixedDegree_swap] using hr.trans hb
    · letI : IsEmpty sI := ⟨fun i ↦ hI ⟨i⟩⟩
      simp
  calc
    (∑ i, actualCoordinateDegree K (P i) 1) = ∑ i : sI, D i := by
      apply Finset.sum_congr_set sI
        (fun i ↦ actualCoordinateDegree K (P i) 1) D
      · intro i hi
        exact actualCoordinateDegree_of_transcendental K (P i) 1 hi
      · intro i hi
        change ¬ Transcendental K (coordinate K (P i) 1) at hi
        exact dif_neg hi
    _ ≤ originalMixedDegree K rBaseYOuterOrder G T := hbound
    _ = coordinateMixedDegree K G T 1 := by
      simp [coordinateMixedDegree, rBaseYOuterOrder]

variable [IsAlgClosed K]

/-- If the base-R projection is not separable, one of the other two
coordinates must be transcendental.  Otherwise both are base scalars,
the two-generator theorem collapses the R-rational extension to degree
one, and degree one is separable. -/
theorem left_or_right_transcendental_of_r_not_separable
    (P : Ideal (Original K)) [P.IsPrime]
    (hR : Transcendental K (coordinate K P 1))
    (hnotsep :
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P 1 hR
      ¬ Algebra.IsSeparable (RatFunc K) (CoordinateField K P)) :
    Transcendental K (coordinate K P 0) ∨
      Transcendental K (coordinate K P 2) := by
  by_contra hnone
  push_neg at hnone
  have h0alg : IsAlgebraic K (coordinate K P 0) := not_not.mp hnone.1
  have h2alg : IsAlgebraic K (coordinate K P 2) := not_not.mp hnone.2
  obtain ⟨a0, ha0⟩ := coordinate_eq_scalar_of_isAlgebraic K P 0 h0alg
  obtain ⟨a2, ha2⟩ := coordinate_eq_scalar_of_isAlgebraic K P 2 h2alg
  letI : Algebra (RatFunc K) (CoordinateField K P) :=
    rationalBaseAlgebra K P 1 hR
  letI : IsScalarTower K (RatFunc K) (CoordinateField K P) :=
    rationalBaseScalarTower K P 1 hR
  have hgen : IntermediateField.adjoin (RatFunc K)
      ({coordinate K P 0, coordinate K P 2} : Set (CoordinateField K P)) = ⊤ :=
    adjoin_two_coordinates_over_ratFunc_eq_top K P 1 0 2 hR (by decide)
  have hbot : IntermediateField.adjoin (RatFunc K)
      ({coordinate K P 0, coordinate K P 2} : Set (CoordinateField K P)) = ⊥ := by
    rw [IntermediateField.adjoin_eq_bot_iff]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx0 | hx2
    · subst x
      rw [← ha0]
      exact IntermediateField.mem_bot.mpr
        ⟨algebraMap K (RatFunc K) a0,
          (IsScalarTower.algebraMap_apply K (RatFunc K)
            (CoordinateField K P) a0).symm⟩
    · rw [Set.mem_singleton_iff] at hx2
      subst x
      rw [← ha2]
      exact IntermediateField.mem_bot.mpr
        ⟨algebraMap K (RatFunc K) a2,
          (IsScalarTower.algebraMap_apply K (RatFunc K)
            (CoordinateField K P) a2).symm⟩
  have hfinrank : Module.finrank (RatFunc K) (CoordinateField K P) = 1 := by
    rw [← IntermediateField.finrank_top', ← hgen, hbot,
      IntermediateField.finrank_bot]
  have hproduct := Field.finSepDegree_mul_finInsepDegree
    (RatFunc K) (CoordinateField K P)
  rw [hfinrank] at hproduct
  have hsepPos : 0 < Field.finSepDegree (RatFunc K) (CoordinateField K P) := by
    by_contra h
    have hz := Nat.eq_zero_of_not_pos h
    rw [hz, zero_mul] at hproduct
    omega
  have hinsepLe : Field.finInsepDegree (RatFunc K) (CoordinateField K P) ≤ 1 := by
    have h := Nat.le_mul_of_pos_left
      (Field.finInsepDegree (RatFunc K) (CoordinateField K P)) hsepPos
    rwa [hproduct] at h
  have hinsep : Field.finInsepDegree (RatFunc K) (CoordinateField K P) = 1 := by
    have hne : Field.finInsepDegree (RatFunc K) (CoordinateField K P) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hproduct
      omega
    omega
  exact hnotsep
    (SmallInseparableProjection.isSeparable_iff_finInsepDegree_eq_one.mpr hinsep)

/-- Every non-point component has a separable transcendental coordinate
available for the fixed normalization, even when its R projection is the
small purely inseparable arm. -/
theorem exists_separable_separator
    (P : Ideal (Original K)) [P.IsPrime]
    (hnonpoint : ∀ v : Fin 3 → K,
      P ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (p : ℕ) [CharP K p]
    (G T : Original K)
    (hG : Irreducible G) (hGmem : G ∈ P) (hTmem : T ∈ P)
    (hproper : ¬ G ∣ T)
    (hdegree : ∀ j : Fin 3, G.degreeOf j < p)
    (hmixed0 : coordinateMixedDegree K G T 0 < p)
    (hmixed2 : coordinateMixedDegree K G T 2 < p) :
    ∃ (i : Fin 3) (hi : Transcendental K (coordinate K P i)),
      letI : Algebra (RatFunc K) (CoordinateField K P) :=
        rationalBaseAlgebra K P i hi
      Algebra.IsSeparable (RatFunc K) (CoordinateField K P) := by
  have safe0 (h0 : Transcendental K (coordinate K P 0)) :
      separableSummary K P (rationalBaseAlgebra K P 0 h0) := by
    let order : Fin 3 ≃ Fin 3 := Equiv.refl (Fin 3)
    have ht : Transcendental K (coordinate K P (order 0)) := by
      simpa [order] using h0
    have hm : originalMixedDegree K order G T < p := by
      simpa [order, coordinateMixedDegree_zero, originalMixedDegree] using hmixed0
    have hr := original_finite_separable_finrank_bound K order P ht p G T
      hG hGmem hTmem hproper (hdegree (order 1)) (hdegree (order 2)) hm
    have halg : rationalBaseAlgebra K P (order 0) ht =
        rationalBaseAlgebra K P 0 h0 := by
      apply rationalBaseAlgebra_congr K P
      simp [order]
    have result : separableSummary K P
        (rationalBaseAlgebra K P (order 0) ht) := hr.2.1
    rw [halg] at result
    exact result
  have safe2 (h2 : Transcendental K (coordinate K P 2)) :
      separableSummary K P (rationalBaseAlgebra K P 2 h2) := by
    let order : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
    have ht : Transcendental K (coordinate K P (order 0)) := by
      simpa [order] using h2
    have hm : originalMixedDegree K order G T < p := by
      simpa [order, coordinateMixedDegree_two, originalMixedDegree,
        Equiv.swap_apply_def, Nat.add_comm, Nat.mul_comm] using hmixed2
    have hr := original_finite_separable_finrank_bound K order P ht p G T
      hG hGmem hTmem hproper (hdegree (order 1)) (hdegree (order 2)) hm
    have halg : rationalBaseAlgebra K P (order 0) ht =
        rationalBaseAlgebra K P 2 h2 := by
      apply rationalBaseAlgebra_congr K P
      simp [order]
    have result : separableSummary K P
        (rationalBaseAlgebra K P (order 0) ht) := hr.2.1
    rw [halg] at result
    exact result
  obtain ⟨i, hi⟩ := exists_transcendental_coordinate_of_ne_point_kernel
    K P hnonpoint
  fin_cases i
  · exact ⟨0, hi, safe0 hi⟩
  · by_cases hsep :
        letI : Algebra (RatFunc K) (CoordinateField K P) :=
          rationalBaseAlgebra K P 1 hi
        Algebra.IsSeparable (RatFunc K) (CoordinateField K P)
    · exact ⟨1, hi, hsep⟩
    · rcases left_or_right_transcendental_of_r_not_separable K P hi hsep with h0 | h2
      · exact ⟨0, h0, safe0 h0⟩
      · exact ⟨2, h2, safe2 h2⟩
  · exact ⟨2, hi, safe2 hi⟩

end

end ProximityPrize.SubmissionLower.ContactProjectionFiniteSmall

#print axioms ProximityPrize.SubmissionLower.ContactProjectionFiniteSmall.projectionsFiniteSmall_of_sparse_rBase_gates
