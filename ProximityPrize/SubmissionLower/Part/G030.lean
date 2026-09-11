import ProximityPrize.SubmissionLower.Part.G029


section Compact_SecondJetGlobalReceipt
/-! Concrete global second-jet interpolation receipt at the proposed 68.04
agreement threshold. The geometric counting argument is not included. -/
namespace ProximityPrize.SubmissionLower.SecondJetGlobalReceipt
open scoped BigOperators
open SecondJetGlobalIndex SecondJetGlobalCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem coefficient_count : coefficientCount 21611508 131071 2160 39 18 =
    1632579532658031 := by decide

theorem cutoff : ∀ h : Fin 19, ∀ r : Fin (39-h.val+1),
    yCount 21611508 131071 h.val r.val ≤ 2160+1-h.val-r.val := by
  intro h r
  have hb : budget 21611508 131071 h.val r.val-1 ≤ 21611508 := by
    unfold budget
    omega
  have hd := Nat.div_le_div_right (c := 131071) hb
  have hy : yCount 21611508 131071 h.val r.val ≤ 165 := by
    unfold yCount
    norm_num at hd
    omega
  have hh := h.isLt
  have hr := r.isLt
  omega



variable {K N : Type*} [Field K] [Fintype N]

end ProximityPrize.SubmissionLower.SecondJetGlobalReceipt

end Compact_SecondJetGlobalReceipt
