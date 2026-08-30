import ProximityPrize.SubmissionLower.ContactFlagExactSeparableProjection

namespace ProximityPrize.SubmissionLower.ContactFlagGlobalPoleProjection

open scoped Classical WithZero
open IsDedekindDomain
open ContactLocalPoleBound
open CoordinateBoxZeroCount
open ContactRegularComponentCover
open ContactFlagAffineFamilyDegree
open ContactFlagExactSeparableProjection
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ArbitraryRationalProjection

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000

theorem poleOrder_eq_max_of_valuation_eq_max
    {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x y z : L)
    (h : v x = max (v y) (v z)) :
    poleOrder v x = max (poleOrder v y) (poleOrder v z) := by
  unfold poleOrder
  rw [h]
  by_cases hy : v y = 0
  · rw [hy]
    simp
  by_cases hz : v z = 0
  · rw [hz]
    simp
  rcases le_total (v y) (v z) with hyz | hzy
  · rw [max_eq_right hyz]
    rw [max_eq_right
      (max_le_max_left 0 ((WithZero.log_le_log hy hz).2 hyz))]
  · rw [max_eq_left hzy]
    rw [max_eq_left
      (max_le_max_left 0 ((WithZero.log_le_log hz hy).2 hzy))]

theorem valuation_le_one_of_poleOrder_eq_zero
    {L : Type*} [Field L]
    (v : Valuation L (WithZero (Multiplicative ℤ))) (x : L)
    (h : poleOrder v x = 0) :
    v x ≤ 1 := by
  by_cases hx : v x = 0
  · simp [hx]
  by_contra hnot
  have hlt : (1 : WithZero (Multiplicative ℤ)) < v x :=
    lt_of_not_ge hnot
  have hlog : 0 < (v x).log := by
    simpa only [WithZero.log_one] using
      ((WithZero.log_lt_log one_ne_zero hx).2 hlt)
  unfold poleOrder at h
  rw [max_eq_right hlog.le] at h
  omega

section RegularComponents

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega]
variable {G T H : MvPolynomial (Fin 3) Omega}
variable
    {hseparator : ∀ C : RegularComponent Omega G T H,
      Transcendental Omega (coordinate Omega C.1 2)}
    {hproj : ∀ C : RegularComponent Omega G T H,
      ProjectionsFiniteSeparable Omega C.1}

end RegularComponents

end

end ProximityPrize.SubmissionLower.ContactFlagGlobalPoleProjection
