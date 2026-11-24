import ProximityPrize.SubmissionLower.Gate61Fin
import ProximityPrize.SubmissionLower.Gate61Gs0
import ProximityPrize.SubmissionLower.Gate61Gs1
import ProximityPrize.SubmissionLower.Gate61Gs2
import ProximityPrize.SubmissionLower.Gate61Gs3
import ProximityPrize.SubmissionLower.Gate61Gs4
import ProximityPrize.SubmissionLower.Gate61Gs5
import ProximityPrize.SubmissionLower.Gate61Gs6
import ProximityPrize.SubmissionLower.Gate61Gs7

-- merged module Gate61Gs8
section Merged_Gate61Gs8
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
namespace Gate61Fin

theorem c_5_10 : one 5 10 = true := by decide +kernel
theorem c_5_11 : one 5 11 = true := by decide +kernel
theorem c_5_12 : one 5 12 = true := by decide +kernel
theorem c_5_13 : one 5 13 = true := by decide +kernel
end Gate61Fin

end Merged_Gate61Gs8

-- merged module Gate61Gates
section Merged_Gate61Gates

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000
set_option Elab.async false

namespace Gate61Fin
open Gate61Cell
open K1_13 (Shape shape)

theorem allOne0 (id t : ℕ) (hid : id < 6) (ht : t < 15) : one id t = true := by
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
    · rfl
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
    · rfl
    · rfl
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
    · rfl
    · rfl
    · rfl
    · rfl
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
    · rfl
    · rfl
    · rfl
    · rfl
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
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact c_5_9
    · exact c_5_10
    · exact c_5_11
    · exact c_5_12
    · exact c_5_13
    · rfl

theorem allOne : ∀ id, id < 6 → ∀ t, t < 15 → one id t = true := fun id hid t ht => allOne0 id t hid ht

theorem gated_ok {id : ℕ} {x : Shape} (h : Low6960Gate.Gated id x) : shapeOK x = true := by
  obtain ⟨hid, hm⟩ := h
  have ht : x.t < 15 := by
    by_contra hc
    rw [gl_nil id x.t (by omega)] at hm
    simp at hm
  have := allOne id hid x.t ht
  have := List.all_eq_true.mp this (x.b, x.j) hm
  simpa using this

end Gate61Fin

end Merged_Gate61Gates
