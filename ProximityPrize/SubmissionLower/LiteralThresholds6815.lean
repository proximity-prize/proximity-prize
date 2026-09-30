import ProximityPrize.SubmissionLower.LiteralThresholds6815_G03
import ProximityPrize.SubmissionLower.FinalPayment6815
namespace ProximityPrize.SubmissionLower.LiteralThresholds6815
set_option autoImplicit false
set_option maxHeartbeats 5000000
def row (r v : ℕ) : Array ℕ := match r with
  | 1 => row1 v
  | 2 => row2 v
  | 3 => row3 v
  | 4 => row4 v
  | 5 => row5 v
  | 6 => row6 v
  | 7 => row7 v
  | 8 => row8 v
  | 9 => row9 v
  | 10 => row10 v
  | 11 => row11 v
  | 12 => row12 v
  | 13 => row13 v
  | 14 => row14 v
  | 15 => row15 v
  | 16 => row16 v
  | 17 => row17 v
  | 18 => row18 v
  | 19 => row19 v
  | _ => #[]
theorem row_eq (r v : ℕ) (hr : 1≤r) (hR : r≤19) (hv : v≤70) : row r v=SingletonCertificate6815.thresholds (FinalLookup6815.single r v) := by
  interval_cases r
  · exact row1_eq v hv
  · exact row2_eq v hv
  · exact row3_eq v hv
  · exact row4_eq v hv
  · exact row5_eq v hv
  · exact row6_eq v hv
  · exact row7_eq v hv
  · exact row8_eq v hv
  · exact row9_eq v hv
  · exact row10_eq v hv
  · exact row11_eq v hv
  · exact row12_eq v hv
  · exact row13_eq v hv
  · exact row14_eq v hv
  · exact row15_eq v hv
  · exact row16_eq v hv
  · exact row17_eq v hv
  · exact row18_eq v hv
  · exact row19_eq v hv
def cut (r v j : ℕ) : ℕ := if 1≤r ∧ r≤19 ∧ v≤70 then MovingFiberSingleCore6815.thresholdAt (row r v) j else FinalPayment6815.fastCut r v j
theorem cut_eq (r v j : ℕ) : cut r v j=FinalPayment6815.fastCut r v j := by
  unfold cut
  split_ifs with h
  · rw [row_eq r v h.1 h.2.1 h.2.2]
    rfl
  · rfl
end ProximityPrize.SubmissionLower.LiteralThresholds6815
