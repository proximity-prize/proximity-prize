import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

noncomputable section

set_option autoImplicit false

variable {K E Γ₀ : Type*} [Field K] [Field E] [Algebra K E]
  [LinearOrderedCommMonoidWithZero Γ₀]

private theorem valuation_scalar_mul_le (v : Valuation E Γ₀) [v.IsTrivialOn K]
    (y : E) (a : K) :
    v (algebraMap K E a * y) ≤ v y := by
  rw [map_mul]
  calc
    v (algebraMap K E a) * v y ≤ 1 * v y :=
      mul_le_mul_of_nonneg_right
        (Valuation.IsTrivialOn.valuation_algebraMap_le_one v a) zero_le
    _ = v y := one_mul _

theorem affineProjection_valuation_le (v : Valuation E Γ₀) [v.IsTrivialOn K]
    (z₀ y : E) (a : K) :
    v (z₀ + algebraMap K E a * y) ≤ max (v z₀) (v y) :=
  (v.map_add _ _).trans (max_le_max le_rfl (valuation_scalar_mul_le v y a))

theorem affineProjection_valuation_bad_subsingleton (v : Valuation E Γ₀) [v.IsTrivialOn K]
    (z₀ y : E) :
    {a : K | v (z₀ + algebraMap K E a * y) < max (v z₀) (v y)}.Subsingleton := by
  intro a ha b hb
  change v (z₀ + algebraMap K E a * y) < max (v z₀) (v y) at ha
  change v (z₀ + algebraMap K E b * y) < max (v z₀) (v y) at hb
  by_contra hab
  by_cases hy : v y < v z₀
  · rw [max_eq_left hy.le] at ha
    have hsmall := v.map_sub_lt ha ((valuation_scalar_mul_le v y a).trans_lt hy)
    rw [add_sub_cancel_right] at hsmall
    exact lt_irrefl _ hsmall
  · rw [max_eq_right (le_of_not_gt hy)] at ha hb
    have hsmall := v.map_sub_lt ha hb
    rw [show (z₀ + algebraMap K E a * y) - (z₀ + algebraMap K E b * y) =
        algebraMap K E (a - b) * y by rw [map_sub]; ring] at hsmall
    have hunit : v (algebraMap K E (a - b)) = 1 :=
      Valuation.IsTrivialOn.eq_one (a - b) (sub_ne_zero.mpr hab)
    rw [map_mul, hunit, one_mul] at hsmall
    exact lt_irrefl _ hsmall

theorem affineProjection_valuation_eq (v : Valuation E Γ₀) [v.IsTrivialOn K]
    (z₀ y : E) (a : K)
    (h : ¬ v (z₀ + algebraMap K E a * y) < max (v z₀) (v y)) :
    v (z₀ + algebraMap K E a * y) = max (v z₀) (v y) :=
  le_antisymm (affineProjection_valuation_le v z₀ y a) (le_of_not_gt h)

private theorem poleOrder_le_of_valuation_le (v : Valuation E (WithZero (Multiplicative ℤ)))
    {x y : E} (h : v x ≤ v y) :
    RCN187.poleOrder v x ≤ RCN187.poleOrder v y := by
  unfold RCN187.poleOrder
  by_cases hx : v x = 0
  · simp only [hx, WithZero.log_zero, max_self]
    exact le_max_left _ _
  · have hy : v y ≠ 0 := ne_of_gt ((lt_of_le_of_ne zero_le (Ne.symm hx)).trans_le h)
    exact max_le_max le_rfl ((WithZero.log_le_log hx hy).mpr h)

theorem affineProjection_poleOrder_eq
    (v : Valuation E (WithZero (Multiplicative ℤ))) [v.IsTrivialOn K]
    (z₀ y : E) (a : K)
    (h : ¬ v (z₀ + algebraMap K E a * y) < max (v z₀) (v y)) :
    RCN187.poleOrder v (z₀ + algebraMap K E a * y) =
      max (RCN187.poleOrder v z₀) (RCN187.poleOrder v y) := by
  have hv := affineProjection_valuation_eq v z₀ y a h
  rcases le_total (v z₀) (v y) with hle | hle
  · rw [max_eq_right hle] at hv
    rw [max_eq_right (poleOrder_le_of_valuation_le v hle)]
    exact congrArg (fun w : WithZero (Multiplicative ℤ) => max 0 w.log) hv
  · rw [max_eq_left hle] at hv
    rw [max_eq_left (poleOrder_le_of_valuation_le v hle)]
    exact congrArg (fun w : WithZero (Multiplicative ℤ) => max 0 w.log) hv

theorem exists_avoiding_finite_subsingleton_parameters {ι A : Type*}
    [Finite ι] [Infinite A] (bad : ι → Set A) (hbad : ∀ i, (bad i).Subsingleton) :
    ∃ a : A, ∀ i, a ∉ bad i := by
  classical
  have hfin : (⋃ i, bad i).Finite := Set.finite_iUnion (fun i => (hbad i).finite)
  obtain ⟨a, ha⟩ := hfin.exists_notMem
  exact ⟨a, fun i hi => ha (Set.mem_iUnion.mpr ⟨i, hi⟩)⟩

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
