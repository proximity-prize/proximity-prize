import ProximityPrize.SubmissionLower.Gate61Fin
import ProximityPrize.SubmissionLower.Gate63Gt0
import ProximityPrize.SubmissionLower.Gate63Gt1
import ProximityPrize.SubmissionLower.Gate63Gt2
import ProximityPrize.SubmissionLower.Gate63Gt3
import ProximityPrize.SubmissionLower.Gate63Gt4
import ProximityPrize.SubmissionLower.Gate63Gt5
import ProximityPrize.SubmissionLower.Gate63Gt6
import ProximityPrize.SubmissionLower.Gate63Gt7
import ProximityPrize.SubmissionLower.Gate63Gt8
import ProximityPrize.SubmissionLower.Gate63Gt9
import ProximityPrize.SubmissionLower.Gate63Gt10
import ProximityPrize.SubmissionLower.Gate63Gt11

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
set_option Elab.async false

namespace Gate61Fin
open Gate61Cell
open K1_13 (Shape shape)
theorem allOne0 (id t : ℕ) (hid : id < 17) (ht : t < 15) : one id t = true := by
  interval_cases id
  · interval_cases t
    · rfl
    · rfl
    · exact c_0_2
    · exact c_0_3
    · exact c_0_4
    · exact c_0_5
    · exact c_0_6
    · exact c_0_7
    · exact c_0_8
    · exact c_0_9
    · exact c_0_10
    · exact c_0_11
    · exact c_0_12
    · exact c_0_13
    · exact c_0_14
  · interval_cases t
    · rfl
    · rfl
    · exact c_1_2
    · exact c_1_3
    · exact c_1_4
    · exact c_1_5
    · exact c_1_6
    · exact c_1_7
    · exact c_1_8
    · exact c_1_9
    · exact c_1_10
    · exact c_1_11
    · exact c_1_12
    · exact c_1_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact c_2_2
    · exact c_2_3
    · exact c_2_4
    · exact c_2_5
    · exact c_2_6
    · exact c_2_7
    · exact c_2_8
    · exact c_2_9
    · exact c_2_10
    · exact c_2_11
    · exact c_2_12
    · exact c_2_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact c_3_2
    · exact c_3_3
    · exact c_3_4
    · exact c_3_5
    · exact c_3_6
    · exact c_3_7
    · exact c_3_8
    · exact c_3_9
    · exact c_3_10
    · exact c_3_11
    · exact c_3_12
    · exact c_3_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · exact c_4_2
    · exact c_4_3
    · exact c_4_4
    · exact c_4_5
    · exact c_4_6
    · exact c_4_7
    · exact c_4_8
    · exact c_4_9
    · exact c_4_10
    · exact c_4_11
    · exact c_4_12
    · exact c_4_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact c_5_3
    · exact c_5_4
    · exact c_5_5
    · exact c_5_6
    · exact c_5_7
    · exact c_5_8
    · exact c_5_9
    · exact c_5_10
    · exact c_5_11
    · exact c_5_12
    · exact c_5_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · exact c_6_3
    · exact c_6_4
    · exact c_6_5
    · exact c_6_6
    · exact c_6_7
    · exact c_6_8
    · exact c_6_9
    · exact c_6_10
    · exact c_6_11
    · exact c_6_12
    · exact c_6_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_7_4
    · exact c_7_5
    · exact c_7_6
    · exact c_7_7
    · exact c_7_8
    · exact c_7_9
    · exact c_7_10
    · exact c_7_11
    · exact c_7_12
    · exact c_7_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_8_5
    · exact c_8_6
    · exact c_8_7
    · exact c_8_8
    · exact c_8_9
    · exact c_8_10
    · exact c_8_11
    · exact c_8_12
    · exact c_8_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_9_7
    · exact c_9_8
    · exact c_9_9
    · exact c_9_10
    · exact c_9_11
    · exact c_9_12
    · exact c_9_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_10_10
    · exact c_10_11
    · exact c_10_12
    · exact c_10_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_12_5
    · exact c_12_6
    · exact c_12_7
    · exact c_12_8
    · exact c_12_9
    · exact c_12_10
    · exact c_12_11
    · exact c_12_12
    · exact c_12_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_13_6
    · exact c_13_7
    · exact c_13_8
    · exact c_13_9
    · exact c_13_10
    · exact c_13_11
    · exact c_13_12
    · exact c_13_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_14_7
    · exact c_14_8
    · exact c_14_9
    · exact c_14_10
    · exact c_14_11
    · exact c_14_12
    · exact c_14_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_15_10
    · exact c_15_11
    · exact c_15_12
    · exact c_15_13
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

theorem allOne : ∀ id, id < 17 → ∀ t, t < 15 → one id t = true := fun id hid t ht => allOne0 id t hid ht

theorem gated_ok {id : ℕ} {x : Shape} (h : Low6960Gate.Gated id x) (hv : valid x = true) : shapeOK x = true := by
  obtain ⟨hid, hm⟩ := h
  have ht : x.t < 15 := by
    by_contra hc
    rw [gl_nil id x.t (by omega)] at hm
    simp at hm
  have := allOne id hid x.t ht
  have := List.all_eq_true.mp this (x.b, x.j) hm
  simpa [hv] using this


end Gate61Fin
