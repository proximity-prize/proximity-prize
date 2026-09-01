import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y0_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y2_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y4_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y6_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y8_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y10_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y12_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y14_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y16_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y18_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y20_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y22_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y24_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y26_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y28_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y30_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y32_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y34_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y36_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y38_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y40_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y42_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y44_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y46_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y48_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y50_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y52_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y54_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y56_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y58_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y60_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y62_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y64_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y66_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y68_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y70_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y72_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y74_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y76_6768
import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR16Y78_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r16_full:
    ∀ y:Fin 79,∀ b:Fin 160,
      Receipt ((⟨15,by decide⟩:Fin 17),y,b):=by
  intro y b
  by_cases h2 : y.val < 2
  · exact receipt_r16_y0 y (Nat.zero_le y.val) h2 b
  by_cases h4 : y.val < 4
  · exact receipt_r16_y2 y (Nat.le_of_not_gt h2) h4 b
  by_cases h6 : y.val < 6
  · exact receipt_r16_y4 y (Nat.le_of_not_gt h4) h6 b
  by_cases h8 : y.val < 8
  · exact receipt_r16_y6 y (Nat.le_of_not_gt h6) h8 b
  by_cases h10 : y.val < 10
  · exact receipt_r16_y8 y (Nat.le_of_not_gt h8) h10 b
  by_cases h12 : y.val < 12
  · exact receipt_r16_y10 y (Nat.le_of_not_gt h10) h12 b
  by_cases h14 : y.val < 14
  · exact receipt_r16_y12 y (Nat.le_of_not_gt h12) h14 b
  by_cases h16 : y.val < 16
  · exact receipt_r16_y14 y (Nat.le_of_not_gt h14) h16 b
  by_cases h18 : y.val < 18
  · exact receipt_r16_y16 y (Nat.le_of_not_gt h16) h18 b
  by_cases h20 : y.val < 20
  · exact receipt_r16_y18 y (Nat.le_of_not_gt h18) h20 b
  by_cases h22 : y.val < 22
  · exact receipt_r16_y20 y (Nat.le_of_not_gt h20) h22 b
  by_cases h24 : y.val < 24
  · exact receipt_r16_y22 y (Nat.le_of_not_gt h22) h24 b
  by_cases h26 : y.val < 26
  · exact receipt_r16_y24 y (Nat.le_of_not_gt h24) h26 b
  by_cases h28 : y.val < 28
  · exact receipt_r16_y26 y (Nat.le_of_not_gt h26) h28 b
  by_cases h30 : y.val < 30
  · exact receipt_r16_y28 y (Nat.le_of_not_gt h28) h30 b
  by_cases h32 : y.val < 32
  · exact receipt_r16_y30 y (Nat.le_of_not_gt h30) h32 b
  by_cases h34 : y.val < 34
  · exact receipt_r16_y32 y (Nat.le_of_not_gt h32) h34 b
  by_cases h36 : y.val < 36
  · exact receipt_r16_y34 y (Nat.le_of_not_gt h34) h36 b
  by_cases h38 : y.val < 38
  · exact receipt_r16_y36 y (Nat.le_of_not_gt h36) h38 b
  by_cases h40 : y.val < 40
  · exact receipt_r16_y38 y (Nat.le_of_not_gt h38) h40 b
  by_cases h42 : y.val < 42
  · exact receipt_r16_y40 y (Nat.le_of_not_gt h40) h42 b
  by_cases h44 : y.val < 44
  · exact receipt_r16_y42 y (Nat.le_of_not_gt h42) h44 b
  by_cases h46 : y.val < 46
  · exact receipt_r16_y44 y (Nat.le_of_not_gt h44) h46 b
  by_cases h48 : y.val < 48
  · exact receipt_r16_y46 y (Nat.le_of_not_gt h46) h48 b
  by_cases h50 : y.val < 50
  · exact receipt_r16_y48 y (Nat.le_of_not_gt h48) h50 b
  by_cases h52 : y.val < 52
  · exact receipt_r16_y50 y (Nat.le_of_not_gt h50) h52 b
  by_cases h54 : y.val < 54
  · exact receipt_r16_y52 y (Nat.le_of_not_gt h52) h54 b
  by_cases h56 : y.val < 56
  · exact receipt_r16_y54 y (Nat.le_of_not_gt h54) h56 b
  by_cases h58 : y.val < 58
  · exact receipt_r16_y56 y (Nat.le_of_not_gt h56) h58 b
  by_cases h60 : y.val < 60
  · exact receipt_r16_y58 y (Nat.le_of_not_gt h58) h60 b
  by_cases h62 : y.val < 62
  · exact receipt_r16_y60 y (Nat.le_of_not_gt h60) h62 b
  by_cases h64 : y.val < 64
  · exact receipt_r16_y62 y (Nat.le_of_not_gt h62) h64 b
  by_cases h66 : y.val < 66
  · exact receipt_r16_y64 y (Nat.le_of_not_gt h64) h66 b
  by_cases h68 : y.val < 68
  · exact receipt_r16_y66 y (Nat.le_of_not_gt h66) h68 b
  by_cases h70 : y.val < 70
  · exact receipt_r16_y68 y (Nat.le_of_not_gt h68) h70 b
  by_cases h72 : y.val < 72
  · exact receipt_r16_y70 y (Nat.le_of_not_gt h70) h72 b
  by_cases h74 : y.val < 74
  · exact receipt_r16_y72 y (Nat.le_of_not_gt h72) h74 b
  by_cases h76 : y.val < 76
  · exact receipt_r16_y74 y (Nat.le_of_not_gt h74) h76 b
  by_cases h78 : y.val < 78
  · exact receipt_r16_y76 y (Nat.le_of_not_gt h76) h78 b
  exact receipt_r16_y78 y (Nat.le_of_not_gt h78) y.isLt b
end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt_r16_full
