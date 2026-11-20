import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_15_22 : CertifiedEndpoint :=
  ⟨⟨15, 22, 3701⟩, 193337489109288761, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_23 : CertifiedEndpoint :=
  ⟨⟨15, 23, 3678⟩, 205822263708199793, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_24 : CertifiedEndpoint :=
  ⟨⟨15, 24, 3654⟩, 218071075480651734, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_25 : CertifiedEndpoint :=
  ⟨⟨15, 25, 3630⟩, 230136367324036025, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_26 : CertifiedEndpoint :=
  ⟨⟨15, 26, 3606⟩, 242018139238352666, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_27 : CertifiedEndpoint :=
  ⟨⟨15, 27, 3581⟩, 253645221802835966, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_15_28_flag : Flag := ⟨15, 28, 3556⟩
private def endpoint_15_28_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_28_base : receiptBase endpoint_15_28_flag endpoint_15_28_sources = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_w0 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 2 181750217410654335 = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_w2 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 2 2 181750217410654335 = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_p4 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 4 181750217410654335 = some 181750217410654335 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 2 2 181750217410654335 181750217410654335 181750217410654335 endpoint_15_28_w0 endpoint_15_28_w2
private theorem endpoint_15_28_w4 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 4 2 181750217410654335 = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_p6 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 6 181750217410654335 = some 181750217410654335 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 4 2 181750217410654335 181750217410654335 181750217410654335 endpoint_15_28_p4 endpoint_15_28_w4
private theorem endpoint_15_28_w6 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 6 2 181750217410654335 = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_p8 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 8 181750217410654335 = some 181750217410654335 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 6 2 181750217410654335 181750217410654335 181750217410654335 endpoint_15_28_p6 endpoint_15_28_w6
private theorem endpoint_15_28_w8 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 8 2 181750217410654335 = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_p10 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 10 181750217410654335 = some 181750217410654335 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 8 2 181750217410654335 181750217410654335 181750217410654335 endpoint_15_28_p8 endpoint_15_28_w8
private theorem endpoint_15_28_w10 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 10 2 181750217410654335 = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_p12 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 12 181750217410654335 = some 181750217410654335 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 10 2 181750217410654335 181750217410654335 181750217410654335 endpoint_15_28_p10 endpoint_15_28_w10
private theorem endpoint_15_28_w12 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 12 2 181750217410654335 = some 181750217410654335 := by decide +kernel
private theorem endpoint_15_28_p14 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 14 181750217410654335 = some 181750217410654335 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 12 2 181750217410654335 181750217410654335 181750217410654335 endpoint_15_28_p12 endpoint_15_28_w12
def endpoint_15_28 : CertifiedEndpoint :=
  ⟨⟨15, 28, 3556⟩, 181750217410654335, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_28_flag endpoint_15_28_sources 14 181750217410654335 181750217410654335 rfl endpoint_15_28_base endpoint_15_28_p14) (by decide)⟩
private def endpoint_15_29_flag : Flag := ⟨15, 29, 3531⟩
private def endpoint_15_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_29_base : receiptBase endpoint_15_29_flag endpoint_15_29_sources = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_w0 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 2 185739743345616993 = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_w2 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 2 2 185739743345616993 = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_p4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 4 185739743345616993 = some 185739743345616993 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 2 2 185739743345616993 185739743345616993 185739743345616993 endpoint_15_29_w0 endpoint_15_29_w2
private theorem endpoint_15_29_w4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 4 2 185739743345616993 = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_p6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 6 185739743345616993 = some 185739743345616993 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 4 2 185739743345616993 185739743345616993 185739743345616993 endpoint_15_29_p4 endpoint_15_29_w4
private theorem endpoint_15_29_w6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 6 2 185739743345616993 = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_p8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 8 185739743345616993 = some 185739743345616993 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 6 2 185739743345616993 185739743345616993 185739743345616993 endpoint_15_29_p6 endpoint_15_29_w6
private theorem endpoint_15_29_w8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 8 2 185739743345616993 = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_p10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 10 185739743345616993 = some 185739743345616993 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 8 2 185739743345616993 185739743345616993 185739743345616993 endpoint_15_29_p8 endpoint_15_29_w8
private theorem endpoint_15_29_w10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 10 2 185739743345616993 = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_p12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 12 185739743345616993 = some 185739743345616993 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 10 2 185739743345616993 185739743345616993 185739743345616993 endpoint_15_29_p10 endpoint_15_29_w10
private theorem endpoint_15_29_w12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 12 2 185739743345616993 = some 185739743345616993 := by decide +kernel
private theorem endpoint_15_29_p14 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 14 185739743345616993 = some 185739743345616993 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 12 2 185739743345616993 185739743345616993 185739743345616993 endpoint_15_29_p12 endpoint_15_29_w12
def endpoint_15_29 : CertifiedEndpoint :=
  ⟨⟨15, 29, 3531⟩, 185739743345616993, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_29_flag endpoint_15_29_sources 14 185739743345616993 185739743345616993 rfl endpoint_15_29_base endpoint_15_29_p14) (by decide)⟩
private def endpoint_15_30_flag : Flag := ⟨15, 30, 3505⟩
private def endpoint_15_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_30_base : receiptBase endpoint_15_30_flag endpoint_15_30_sources = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_w0 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 2 189601651125750201 = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_w2 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 2 2 189601651125750201 = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_p4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 4 189601651125750201 = some 189601651125750201 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 2 2 189601651125750201 189601651125750201 189601651125750201 endpoint_15_30_w0 endpoint_15_30_w2
private theorem endpoint_15_30_w4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 4 2 189601651125750201 = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_p6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 6 189601651125750201 = some 189601651125750201 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 4 2 189601651125750201 189601651125750201 189601651125750201 endpoint_15_30_p4 endpoint_15_30_w4
private theorem endpoint_15_30_w6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 6 2 189601651125750201 = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_p8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 8 189601651125750201 = some 189601651125750201 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 6 2 189601651125750201 189601651125750201 189601651125750201 endpoint_15_30_p6 endpoint_15_30_w6
private theorem endpoint_15_30_w8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 8 2 189601651125750201 = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_p10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 10 189601651125750201 = some 189601651125750201 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 8 2 189601651125750201 189601651125750201 189601651125750201 endpoint_15_30_p8 endpoint_15_30_w8
private theorem endpoint_15_30_w10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 10 2 189601651125750201 = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_p12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 12 189601651125750201 = some 189601651125750201 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 10 2 189601651125750201 189601651125750201 189601651125750201 endpoint_15_30_p10 endpoint_15_30_w10
private theorem endpoint_15_30_w12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 12 2 189601651125750201 = some 189601651125750201 := by decide +kernel
private theorem endpoint_15_30_p14 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 14 189601651125750201 = some 189601651125750201 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 12 2 189601651125750201 189601651125750201 189601651125750201 endpoint_15_30_p12 endpoint_15_30_w12
def endpoint_15_30 : CertifiedEndpoint :=
  ⟨⟨15, 30, 3505⟩, 189601651125750201, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_30_flag endpoint_15_30_sources 14 189601651125750201 189601651125750201 rfl endpoint_15_30_base endpoint_15_30_p14) (by decide)⟩
private def endpoint_15_31_flag : Flag := ⟨15, 31, 3479⟩
private def endpoint_15_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_31_base : receiptBase endpoint_15_31_flag endpoint_15_31_sources = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_w0 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 2 193386396012053471 = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_w2 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 2 2 193386396012053471 = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_p4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 4 193386396012053471 = some 193386396012053471 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 2 2 193386396012053471 193386396012053471 193386396012053471 endpoint_15_31_w0 endpoint_15_31_w2
private theorem endpoint_15_31_w4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 4 2 193386396012053471 = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_p6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 6 193386396012053471 = some 193386396012053471 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 4 2 193386396012053471 193386396012053471 193386396012053471 endpoint_15_31_p4 endpoint_15_31_w4
private theorem endpoint_15_31_w6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 6 2 193386396012053471 = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_p8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 8 193386396012053471 = some 193386396012053471 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 6 2 193386396012053471 193386396012053471 193386396012053471 endpoint_15_31_p6 endpoint_15_31_w6
private theorem endpoint_15_31_w8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 8 2 193386396012053471 = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_p10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 10 193386396012053471 = some 193386396012053471 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 8 2 193386396012053471 193386396012053471 193386396012053471 endpoint_15_31_p8 endpoint_15_31_w8
private theorem endpoint_15_31_w10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 10 2 193386396012053471 = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_p12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 12 193386396012053471 = some 193386396012053471 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 10 2 193386396012053471 193386396012053471 193386396012053471 endpoint_15_31_p10 endpoint_15_31_w10
private theorem endpoint_15_31_w12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 12 2 193386396012053471 = some 193386396012053471 := by decide +kernel
private theorem endpoint_15_31_p14 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 14 193386396012053471 = some 193386396012053471 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 12 2 193386396012053471 193386396012053471 193386396012053471 endpoint_15_31_p12 endpoint_15_31_w12
def endpoint_15_31 : CertifiedEndpoint :=
  ⟨⟨15, 31, 3479⟩, 193386396012053471, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_31_flag endpoint_15_31_sources 14 193386396012053471 193386396012053471 rfl endpoint_15_31_base endpoint_15_31_p14) (by decide)⟩
private def endpoint_15_32_flag : Flag := ⟨15, 32, 3452⟩
private def endpoint_15_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_32_base : receiptBase endpoint_15_32_flag endpoint_15_32_sources = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_w0 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 2 197037700911760981 = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_w2 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 2 2 197037700911760981 = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_p4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 4 197037700911760981 = some 197037700911760981 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 2 2 197037700911760981 197037700911760981 197037700911760981 endpoint_15_32_w0 endpoint_15_32_w2
private theorem endpoint_15_32_w4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 4 2 197037700911760981 = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_p6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 6 197037700911760981 = some 197037700911760981 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 4 2 197037700911760981 197037700911760981 197037700911760981 endpoint_15_32_p4 endpoint_15_32_w4
private theorem endpoint_15_32_w6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 6 2 197037700911760981 = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_p8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 8 197037700911760981 = some 197037700911760981 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 6 2 197037700911760981 197037700911760981 197037700911760981 endpoint_15_32_p6 endpoint_15_32_w6
private theorem endpoint_15_32_w8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 8 2 197037700911760981 = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_p10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 10 197037700911760981 = some 197037700911760981 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 8 2 197037700911760981 197037700911760981 197037700911760981 endpoint_15_32_p8 endpoint_15_32_w8
private theorem endpoint_15_32_w10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 10 2 197037700911760981 = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_p12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 12 197037700911760981 = some 197037700911760981 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 10 2 197037700911760981 197037700911760981 197037700911760981 endpoint_15_32_p10 endpoint_15_32_w10
private theorem endpoint_15_32_w12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 12 2 197037700911760981 = some 197037700911760981 := by decide +kernel
private theorem endpoint_15_32_p14 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 14 197037700911760981 = some 197037700911760981 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 12 2 197037700911760981 197037700911760981 197037700911760981 endpoint_15_32_p12 endpoint_15_32_w12
def endpoint_15_32 : CertifiedEndpoint :=
  ⟨⟨15, 32, 3452⟩, 197037700911760981, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_32_flag endpoint_15_32_sources 14 197037700911760981 197037700911760981 rfl endpoint_15_32_base endpoint_15_32_p14) (by decide)⟩
private def endpoint_15_33_flag : Flag := ⟨15, 33, 3425⟩
private def endpoint_15_33_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_33_base : receiptBase endpoint_15_33_flag endpoint_15_33_sources = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_w0 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 2 200608932001755397 = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_w2 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 2 2 200608932001755397 = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_p4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 4 200608932001755397 = some 200608932001755397 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 2 2 200608932001755397 200608932001755397 200608932001755397 endpoint_15_33_w0 endpoint_15_33_w2
private theorem endpoint_15_33_w4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 4 2 200608932001755397 = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_p6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 6 200608932001755397 = some 200608932001755397 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 4 2 200608932001755397 200608932001755397 200608932001755397 endpoint_15_33_p4 endpoint_15_33_w4
private theorem endpoint_15_33_w6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 6 2 200608932001755397 = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_p8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 8 200608932001755397 = some 200608932001755397 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 6 2 200608932001755397 200608932001755397 200608932001755397 endpoint_15_33_p6 endpoint_15_33_w6
private theorem endpoint_15_33_w8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 8 2 200608932001755397 = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_p10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 10 200608932001755397 = some 200608932001755397 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 8 2 200608932001755397 200608932001755397 200608932001755397 endpoint_15_33_p8 endpoint_15_33_w8
private theorem endpoint_15_33_w10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 10 2 200608932001755397 = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_p12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 12 200608932001755397 = some 200608932001755397 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 10 2 200608932001755397 200608932001755397 200608932001755397 endpoint_15_33_p10 endpoint_15_33_w10
private theorem endpoint_15_33_w12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 12 2 200608932001755397 = some 200608932001755397 := by decide +kernel
private theorem endpoint_15_33_p14 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 14 200608932001755397 = some 200608932001755397 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 12 2 200608932001755397 200608932001755397 200608932001755397 endpoint_15_33_p12 endpoint_15_33_w12
def endpoint_15_33 : CertifiedEndpoint :=
  ⟨⟨15, 33, 3425⟩, 200608932001755397, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_33_flag endpoint_15_33_sources 14 200608932001755397 200608932001755397 rfl endpoint_15_33_base endpoint_15_33_p14) (by decide)⟩
private def endpoint_15_34_flag : Flag := ⟨15, 34, 3398⟩
private def endpoint_15_34_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_34_base : receiptBase endpoint_15_34_flag endpoint_15_34_sources = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_w0 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 2 204068630766862395 = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_w2 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 2 2 204068630766862395 = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_p4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 4 204068630766862395 = some 204068630766862395 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 2 2 204068630766862395 204068630766862395 204068630766862395 endpoint_15_34_w0 endpoint_15_34_w2
private theorem endpoint_15_34_w4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 4 2 204068630766862395 = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_p6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 6 204068630766862395 = some 204068630766862395 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 4 2 204068630766862395 204068630766862395 204068630766862395 endpoint_15_34_p4 endpoint_15_34_w4
private theorem endpoint_15_34_w6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 6 2 204068630766862395 = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_p8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 8 204068630766862395 = some 204068630766862395 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 6 2 204068630766862395 204068630766862395 204068630766862395 endpoint_15_34_p6 endpoint_15_34_w6
private theorem endpoint_15_34_w8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 8 2 204068630766862395 = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_p10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 10 204068630766862395 = some 204068630766862395 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 8 2 204068630766862395 204068630766862395 204068630766862395 endpoint_15_34_p8 endpoint_15_34_w8
private theorem endpoint_15_34_w10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 10 2 204068630766862395 = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_p12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 12 204068630766862395 = some 204068630766862395 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 10 2 204068630766862395 204068630766862395 204068630766862395 endpoint_15_34_p10 endpoint_15_34_w10
private theorem endpoint_15_34_w12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 12 2 204068630766862395 = some 204068630766862395 := by decide +kernel
private theorem endpoint_15_34_p14 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 14 204068630766862395 = some 204068630766862395 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 12 2 204068630766862395 204068630766862395 204068630766862395 endpoint_15_34_p12 endpoint_15_34_w12
def endpoint_15_34 : CertifiedEndpoint :=
  ⟨⟨15, 34, 3398⟩, 204068630766862395, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_34_flag endpoint_15_34_sources 14 204068630766862395 204068630766862395 rfl endpoint_15_34_base endpoint_15_34_p14) (by decide)⟩
private def endpoint_15_35_flag : Flag := ⟨15, 35, 3370⟩
private def endpoint_15_35_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_35_base : receiptBase endpoint_15_35_flag endpoint_15_35_sources = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_w0 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 2 207355542463440149 = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_w2 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 2 2 207355542463440149 = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_p4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 4 207355542463440149 = some 207355542463440149 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 2 2 207355542463440149 207355542463440149 207355542463440149 endpoint_15_35_w0 endpoint_15_35_w2
private theorem endpoint_15_35_w4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 4 2 207355542463440149 = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_p6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 6 207355542463440149 = some 207355542463440149 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 4 2 207355542463440149 207355542463440149 207355542463440149 endpoint_15_35_p4 endpoint_15_35_w4
private theorem endpoint_15_35_w6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 6 2 207355542463440149 = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_p8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 8 207355542463440149 = some 207355542463440149 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 6 2 207355542463440149 207355542463440149 207355542463440149 endpoint_15_35_p6 endpoint_15_35_w6
private theorem endpoint_15_35_w8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 8 2 207355542463440149 = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_p10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 10 207355542463440149 = some 207355542463440149 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 8 2 207355542463440149 207355542463440149 207355542463440149 endpoint_15_35_p8 endpoint_15_35_w8
private theorem endpoint_15_35_w10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 10 2 207355542463440149 = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_p12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 12 207355542463440149 = some 207355542463440149 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 10 2 207355542463440149 207355542463440149 207355542463440149 endpoint_15_35_p10 endpoint_15_35_w10
private theorem endpoint_15_35_w12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 12 2 207355542463440149 = some 207355542463440149 := by decide +kernel
private theorem endpoint_15_35_p14 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 14 207355542463440149 = some 207355542463440149 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 12 2 207355542463440149 207355542463440149 207355542463440149 endpoint_15_35_p12 endpoint_15_35_w12
def endpoint_15_35 : CertifiedEndpoint :=
  ⟨⟨15, 35, 3370⟩, 207355542463440149, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_35_flag endpoint_15_35_sources 14 207355542463440149 207355542463440149 rfl endpoint_15_35_base endpoint_15_35_p14) (by decide)⟩
private def endpoint_15_36_flag : Flag := ⟨15, 36, 3341⟩
private def endpoint_15_36_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_36_base : receiptBase endpoint_15_36_flag endpoint_15_36_sources = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_w0 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 2 211847552031133501 = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_w2 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 2 2 211847552031133501 = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_p4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 4 211847552031133501 = some 211847552031133501 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 2 2 211847552031133501 211847552031133501 211847552031133501 endpoint_15_36_w0 endpoint_15_36_w2
private theorem endpoint_15_36_w4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 4 2 211847552031133501 = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_p6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 6 211847552031133501 = some 211847552031133501 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 4 2 211847552031133501 211847552031133501 211847552031133501 endpoint_15_36_p4 endpoint_15_36_w4
private theorem endpoint_15_36_w6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 6 2 211847552031133501 = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_p8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 8 211847552031133501 = some 211847552031133501 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 6 2 211847552031133501 211847552031133501 211847552031133501 endpoint_15_36_p6 endpoint_15_36_w6
private theorem endpoint_15_36_w8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 8 2 211847552031133501 = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_p10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 10 211847552031133501 = some 211847552031133501 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 8 2 211847552031133501 211847552031133501 211847552031133501 endpoint_15_36_p8 endpoint_15_36_w8
private theorem endpoint_15_36_w10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 10 2 211847552031133501 = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_p12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 12 211847552031133501 = some 211847552031133501 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 10 2 211847552031133501 211847552031133501 211847552031133501 endpoint_15_36_p10 endpoint_15_36_w10
private theorem endpoint_15_36_w12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 12 2 211847552031133501 = some 211847552031133501 := by decide +kernel
private theorem endpoint_15_36_p14 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 14 211847552031133501 = some 211847552031133501 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 12 2 211847552031133501 211847552031133501 211847552031133501 endpoint_15_36_p12 endpoint_15_36_w12
def endpoint_15_36 : CertifiedEndpoint :=
  ⟨⟨15, 36, 3341⟩, 211847552031133501, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_36_flag endpoint_15_36_sources 14 211847552031133501 211847552031133501 rfl endpoint_15_36_base endpoint_15_36_p14) (by decide)⟩
private def endpoint_15_37_flag : Flag := ⟨15, 37, 3312⟩
private def endpoint_15_37_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_37_base : receiptBase endpoint_15_37_flag endpoint_15_37_sources = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_w0 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 2 214902216616078654 = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_w2 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 2 2 214902216616078654 = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_p4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 4 214902216616078654 = some 214902216616078654 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 2 2 214902216616078654 214902216616078654 214902216616078654 endpoint_15_37_w0 endpoint_15_37_w2
private theorem endpoint_15_37_w4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 4 2 214902216616078654 = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_p6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 6 214902216616078654 = some 214902216616078654 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 4 2 214902216616078654 214902216616078654 214902216616078654 endpoint_15_37_p4 endpoint_15_37_w4
private theorem endpoint_15_37_w6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 6 2 214902216616078654 = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_p8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 8 214902216616078654 = some 214902216616078654 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 6 2 214902216616078654 214902216616078654 214902216616078654 endpoint_15_37_p6 endpoint_15_37_w6
private theorem endpoint_15_37_w8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 8 2 214902216616078654 = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_p10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 10 214902216616078654 = some 214902216616078654 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 8 2 214902216616078654 214902216616078654 214902216616078654 endpoint_15_37_p8 endpoint_15_37_w8
private theorem endpoint_15_37_w10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 10 2 214902216616078654 = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_p12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 12 214902216616078654 = some 214902216616078654 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 10 2 214902216616078654 214902216616078654 214902216616078654 endpoint_15_37_p10 endpoint_15_37_w10
private theorem endpoint_15_37_w12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 12 2 214902216616078654 = some 214902216616078654 := by decide +kernel
private theorem endpoint_15_37_p14 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 14 214902216616078654 = some 214902216616078654 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 12 2 214902216616078654 214902216616078654 214902216616078654 endpoint_15_37_p12 endpoint_15_37_w12
def endpoint_15_37 : CertifiedEndpoint :=
  ⟨⟨15, 37, 3312⟩, 214902216616078654, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_37_flag endpoint_15_37_sources 14 214902216616078654 214902216616078654 rfl endpoint_15_37_base endpoint_15_37_p14) (by decide)⟩
private def endpoint_15_38_flag : Flag := ⟨15, 38, 3283⟩
private def endpoint_15_38_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_38_base : receiptBase endpoint_15_38_flag endpoint_15_38_sources = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_w0 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 2 219427477573833009 = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_w2 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 2 2 219427477573833009 = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_p4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 4 219427477573833009 = some 219427477573833009 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 2 2 219427477573833009 219427477573833009 219427477573833009 endpoint_15_38_w0 endpoint_15_38_w2
private theorem endpoint_15_38_w4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 4 2 219427477573833009 = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_p6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 6 219427477573833009 = some 219427477573833009 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 4 2 219427477573833009 219427477573833009 219427477573833009 endpoint_15_38_p4 endpoint_15_38_w4
private theorem endpoint_15_38_w6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 6 2 219427477573833009 = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_p8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 8 219427477573833009 = some 219427477573833009 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 6 2 219427477573833009 219427477573833009 219427477573833009 endpoint_15_38_p6 endpoint_15_38_w6
private theorem endpoint_15_38_w8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 8 2 219427477573833009 = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_p10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 10 219427477573833009 = some 219427477573833009 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 8 2 219427477573833009 219427477573833009 219427477573833009 endpoint_15_38_p8 endpoint_15_38_w8
private theorem endpoint_15_38_w10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 10 2 219427477573833009 = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_p12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 12 219427477573833009 = some 219427477573833009 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 10 2 219427477573833009 219427477573833009 219427477573833009 endpoint_15_38_p10 endpoint_15_38_w10
private theorem endpoint_15_38_w12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 12 2 219427477573833009 = some 219427477573833009 := by decide +kernel
private theorem endpoint_15_38_p14 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 14 219427477573833009 = some 219427477573833009 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 12 2 219427477573833009 219427477573833009 219427477573833009 endpoint_15_38_p12 endpoint_15_38_w12
def endpoint_15_38 : CertifiedEndpoint :=
  ⟨⟨15, 38, 3283⟩, 219427477573833009, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_38_flag endpoint_15_38_sources 14 219427477573833009 219427477573833009 rfl endpoint_15_38_base endpoint_15_38_p14) (by decide)⟩
private def endpoint_15_39_flag : Flag := ⟨15, 39, 3253⟩
private def endpoint_15_39_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_39_base : receiptBase endpoint_15_39_flag endpoint_15_39_sources = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_w0 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 2 222192462771104309 = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_w2 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 2 2 222192462771104309 = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_p4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 4 222192462771104309 = some 222192462771104309 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 2 2 222192462771104309 222192462771104309 222192462771104309 endpoint_15_39_w0 endpoint_15_39_w2
private theorem endpoint_15_39_w4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 4 2 222192462771104309 = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_p6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 6 222192462771104309 = some 222192462771104309 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 4 2 222192462771104309 222192462771104309 222192462771104309 endpoint_15_39_p4 endpoint_15_39_w4
private theorem endpoint_15_39_w6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 6 2 222192462771104309 = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_p8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 8 222192462771104309 = some 222192462771104309 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 6 2 222192462771104309 222192462771104309 222192462771104309 endpoint_15_39_p6 endpoint_15_39_w6
private theorem endpoint_15_39_w8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 8 2 222192462771104309 = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_p10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 10 222192462771104309 = some 222192462771104309 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 8 2 222192462771104309 222192462771104309 222192462771104309 endpoint_15_39_p8 endpoint_15_39_w8
private theorem endpoint_15_39_w10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 10 2 222192462771104309 = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_p12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 12 222192462771104309 = some 222192462771104309 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 10 2 222192462771104309 222192462771104309 222192462771104309 endpoint_15_39_p10 endpoint_15_39_w10
private theorem endpoint_15_39_w12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 12 2 222192462771104309 = some 222192462771104309 := by decide +kernel
private theorem endpoint_15_39_p14 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 14 222192462771104309 = some 222192462771104309 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 12 2 222192462771104309 222192462771104309 222192462771104309 endpoint_15_39_p12 endpoint_15_39_w12
def endpoint_15_39 : CertifiedEndpoint :=
  ⟨⟨15, 39, 3253⟩, 222192462771104309, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_39_flag endpoint_15_39_sources 14 222192462771104309 222192462771104309 rfl endpoint_15_39_base endpoint_15_39_p14) (by decide)⟩
private def endpoint_15_40_flag : Flag := ⟨15, 40, 3222⟩
private def endpoint_15_40_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_40_base : receiptBase endpoint_15_40_flag endpoint_15_40_sources = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_w0 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 2 224801295477039384 = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_w2 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 2 2 224801295477039384 = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_p4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 4 224801295477039384 = some 224801295477039384 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 2 2 224801295477039384 224801295477039384 224801295477039384 endpoint_15_40_w0 endpoint_15_40_w2
private theorem endpoint_15_40_w4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 4 2 224801295477039384 = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_p6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 6 224801295477039384 = some 224801295477039384 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 4 2 224801295477039384 224801295477039384 224801295477039384 endpoint_15_40_p4 endpoint_15_40_w4
private theorem endpoint_15_40_w6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 6 2 224801295477039384 = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_p8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 8 224801295477039384 = some 224801295477039384 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 6 2 224801295477039384 224801295477039384 224801295477039384 endpoint_15_40_p6 endpoint_15_40_w6
private theorem endpoint_15_40_w8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 8 2 224801295477039384 = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_p10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 10 224801295477039384 = some 224801295477039384 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 8 2 224801295477039384 224801295477039384 224801295477039384 endpoint_15_40_p8 endpoint_15_40_w8
private theorem endpoint_15_40_w10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 10 2 224801295477039384 = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_p12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 12 224801295477039384 = some 224801295477039384 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 10 2 224801295477039384 224801295477039384 224801295477039384 endpoint_15_40_p10 endpoint_15_40_w10
private theorem endpoint_15_40_w12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 12 2 224801295477039384 = some 224801295477039384 := by decide +kernel
private theorem endpoint_15_40_p14 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 14 224801295477039384 = some 224801295477039384 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 12 2 224801295477039384 224801295477039384 224801295477039384 endpoint_15_40_p12 endpoint_15_40_w12
def endpoint_15_40 : CertifiedEndpoint :=
  ⟨⟨15, 40, 3222⟩, 224801295477039384, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_40_flag endpoint_15_40_sources 14 224801295477039384 224801295477039384 rfl endpoint_15_40_base endpoint_15_40_p14) (by decide)⟩
private def endpoint_15_41_flag : Flag := ⟨15, 41, 3191⟩
private def endpoint_15_41_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_15_41_base : receiptBase endpoint_15_41_flag endpoint_15_41_sources = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_w0 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 2 226294115279538693 = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_w2 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 2 2 226294115279538693 = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_p4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 4 226294115279538693 = some 226294115279538693 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 2 2 226294115279538693 226294115279538693 226294115279538693 endpoint_15_41_w0 endpoint_15_41_w2
private theorem endpoint_15_41_w4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 4 2 226294115279538693 = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_p6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 6 226294115279538693 = some 226294115279538693 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 4 2 226294115279538693 226294115279538693 226294115279538693 endpoint_15_41_p4 endpoint_15_41_w4
private theorem endpoint_15_41_w6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 6 2 226294115279538693 = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_p8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 8 226294115279538693 = some 226294115279538693 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 6 2 226294115279538693 226294115279538693 226294115279538693 endpoint_15_41_p6 endpoint_15_41_w6
private theorem endpoint_15_41_w8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 8 2 226294115279538693 = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_p10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 10 226294115279538693 = some 226294115279538693 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 8 2 226294115279538693 226294115279538693 226294115279538693 endpoint_15_41_p8 endpoint_15_41_w8
private theorem endpoint_15_41_w10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 10 2 226294115279538693 = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_p12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 12 226294115279538693 = some 226294115279538693 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 10 2 226294115279538693 226294115279538693 226294115279538693 endpoint_15_41_p10 endpoint_15_41_w10
private theorem endpoint_15_41_w12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 12 2 226294115279538693 = some 226294115279538693 := by decide +kernel
private theorem endpoint_15_41_p14 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 14 226294115279538693 = some 226294115279538693 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 12 2 226294115279538693 226294115279538693 226294115279538693 endpoint_15_41_p12 endpoint_15_41_w12
def endpoint_15_41 : CertifiedEndpoint :=
  ⟨⟨15, 41, 3191⟩, 226294115279538693, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_15_41_flag endpoint_15_41_sources 14 226294115279538693 226294115279538693 rfl endpoint_15_41_base endpoint_15_41_p14) (by decide)⟩
private def endpoint_15_42_flag : Flag := ⟨15, 42, 3159⟩
private def endpoint_15_42_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_42_base : receiptBase endpoint_15_42_flag endpoint_15_42_sources = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_w0 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 2 230279913624749567 = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_w2 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 2 2 230279913624749567 = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_p4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 4 230279913624749567 = some 230279913624749567 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 2 2 230279913624749567 230279913624749567 230279913624749567 endpoint_15_42_w0 endpoint_15_42_w2
private theorem endpoint_15_42_w4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 4 2 230279913624749567 = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_p6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 6 230279913624749567 = some 230279913624749567 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 4 2 230279913624749567 230279913624749567 230279913624749567 endpoint_15_42_p4 endpoint_15_42_w4
private theorem endpoint_15_42_w6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 6 2 230279913624749567 = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_p8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 8 230279913624749567 = some 230279913624749567 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 6 2 230279913624749567 230279913624749567 230279913624749567 endpoint_15_42_p6 endpoint_15_42_w6
private theorem endpoint_15_42_w8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 8 2 230279913624749567 = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_p10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 10 230279913624749567 = some 230279913624749567 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 8 2 230279913624749567 230279913624749567 230279913624749567 endpoint_15_42_p8 endpoint_15_42_w8
private theorem endpoint_15_42_w10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 10 2 230279913624749567 = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_p12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 12 230279913624749567 = some 230279913624749567 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 10 2 230279913624749567 230279913624749567 230279913624749567 endpoint_15_42_p10 endpoint_15_42_w10
private theorem endpoint_15_42_w12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 12 2 230279913624749567 = some 230279913624749567 := by decide +kernel
private theorem endpoint_15_42_p14 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 14 230279913624749567 = some 230279913624749567 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 12 2 230279913624749567 230279913624749567 230279913624749567 endpoint_15_42_p12 endpoint_15_42_w12
def endpoint_15_42 : CertifiedEndpoint :=
  ⟨⟨15, 42, 3159⟩, 230279913624749567, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_42_flag endpoint_15_42_sources 14 230279913624749567 230279913624749567 rfl endpoint_15_42_base endpoint_15_42_p14) (by decide)⟩
private def endpoint_15_43_flag : Flag := ⟨15, 43, 3126⟩
private def endpoint_15_43_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_43_base : receiptBase endpoint_15_43_flag endpoint_15_43_sources = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_w0 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 2 232484724762282485 = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_w2 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 2 2 232484724762282485 = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_p4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 4 232484724762282485 = some 232484724762282485 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 2 2 232484724762282485 232484724762282485 232484724762282485 endpoint_15_43_w0 endpoint_15_43_w2
private theorem endpoint_15_43_w4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 4 2 232484724762282485 = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_p6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 6 232484724762282485 = some 232484724762282485 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 4 2 232484724762282485 232484724762282485 232484724762282485 endpoint_15_43_p4 endpoint_15_43_w4
private theorem endpoint_15_43_w6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 6 2 232484724762282485 = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_p8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 8 232484724762282485 = some 232484724762282485 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 6 2 232484724762282485 232484724762282485 232484724762282485 endpoint_15_43_p6 endpoint_15_43_w6
private theorem endpoint_15_43_w8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 8 2 232484724762282485 = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_p10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 10 232484724762282485 = some 232484724762282485 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 8 2 232484724762282485 232484724762282485 232484724762282485 endpoint_15_43_p8 endpoint_15_43_w8
private theorem endpoint_15_43_w10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 10 2 232484724762282485 = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_p12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 12 232484724762282485 = some 232484724762282485 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 10 2 232484724762282485 232484724762282485 232484724762282485 endpoint_15_43_p10 endpoint_15_43_w10
private theorem endpoint_15_43_w12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 12 2 232484724762282485 = some 232484724762282485 := by decide +kernel
private theorem endpoint_15_43_p14 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 14 232484724762282485 = some 232484724762282485 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 12 2 232484724762282485 232484724762282485 232484724762282485 endpoint_15_43_p12 endpoint_15_43_w12
def endpoint_15_43 : CertifiedEndpoint :=
  ⟨⟨15, 43, 3126⟩, 232484724762282485, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_43_flag endpoint_15_43_sources 14 232484724762282485 232484724762282485 rfl endpoint_15_43_base endpoint_15_43_p14) (by decide)⟩
private def endpoint_15_44_flag : Flag := ⟨15, 44, 3093⟩
private def endpoint_15_44_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_44_base : receiptBase endpoint_15_44_flag endpoint_15_44_sources = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_w0 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 2 234593000770017099 = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_w2 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 2 2 234593000770017099 = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_p4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 4 234593000770017099 = some 234593000770017099 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 2 2 234593000770017099 234593000770017099 234593000770017099 endpoint_15_44_w0 endpoint_15_44_w2
private theorem endpoint_15_44_w4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 4 2 234593000770017099 = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_p6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 6 234593000770017099 = some 234593000770017099 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 4 2 234593000770017099 234593000770017099 234593000770017099 endpoint_15_44_p4 endpoint_15_44_w4
private theorem endpoint_15_44_w6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 6 2 234593000770017099 = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_p8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 8 234593000770017099 = some 234593000770017099 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 6 2 234593000770017099 234593000770017099 234593000770017099 endpoint_15_44_p6 endpoint_15_44_w6
private theorem endpoint_15_44_w8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 8 2 234593000770017099 = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_p10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 10 234593000770017099 = some 234593000770017099 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 8 2 234593000770017099 234593000770017099 234593000770017099 endpoint_15_44_p8 endpoint_15_44_w8
private theorem endpoint_15_44_w10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 10 2 234593000770017099 = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_p12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 12 234593000770017099 = some 234593000770017099 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 10 2 234593000770017099 234593000770017099 234593000770017099 endpoint_15_44_p10 endpoint_15_44_w10
private theorem endpoint_15_44_w12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 12 2 234593000770017099 = some 234593000770017099 := by decide +kernel
private theorem endpoint_15_44_p14 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 14 234593000770017099 = some 234593000770017099 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 12 2 234593000770017099 234593000770017099 234593000770017099 endpoint_15_44_p12 endpoint_15_44_w12
def endpoint_15_44 : CertifiedEndpoint :=
  ⟨⟨15, 44, 3093⟩, 234593000770017099, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_44_flag endpoint_15_44_sources 14 234593000770017099 234593000770017099 rfl endpoint_15_44_base endpoint_15_44_p14) (by decide)⟩
private def endpoint_15_45_flag : Flag := ⟨15, 45, 3059⟩
private def endpoint_15_45_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_45_base : receiptBase endpoint_15_45_flag endpoint_15_45_sources = some 236528504444914143 := by decide +kernel
private theorem endpoint_15_45_w0 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 2 236528504444914143 = some 237427011936866013 := by decide +kernel
private theorem endpoint_15_45_w2 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 2 2 237427011936866013 = some 237427011936866013 := by decide +kernel
private theorem endpoint_15_45_p4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 4 236528504444914143 = some 237427011936866013 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 2 2 236528504444914143 237427011936866013 237427011936866013 endpoint_15_45_w0 endpoint_15_45_w2
private theorem endpoint_15_45_w4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 4 2 237427011936866013 = some 237427011936866013 := by decide +kernel
private theorem endpoint_15_45_p6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 6 236528504444914143 = some 237427011936866013 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 4 2 236528504444914143 237427011936866013 237427011936866013 endpoint_15_45_p4 endpoint_15_45_w4
private theorem endpoint_15_45_w6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 6 2 237427011936866013 = some 237427011936866013 := by decide +kernel
private theorem endpoint_15_45_p8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 8 236528504444914143 = some 237427011936866013 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 6 2 236528504444914143 237427011936866013 237427011936866013 endpoint_15_45_p6 endpoint_15_45_w6
private theorem endpoint_15_45_w8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 8 2 237427011936866013 = some 237427011936866013 := by decide +kernel
private theorem endpoint_15_45_p10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 10 236528504444914143 = some 237427011936866013 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 8 2 236528504444914143 237427011936866013 237427011936866013 endpoint_15_45_p8 endpoint_15_45_w8
private theorem endpoint_15_45_w10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 10 2 237427011936866013 = some 237427011936866013 := by decide +kernel
private theorem endpoint_15_45_p12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 12 236528504444914143 = some 237427011936866013 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 10 2 236528504444914143 237427011936866013 237427011936866013 endpoint_15_45_p10 endpoint_15_45_w10
private theorem endpoint_15_45_w12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 12 2 237427011936866013 = some 237427011936866013 := by decide +kernel
private theorem endpoint_15_45_p14 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 14 236528504444914143 = some 237427011936866013 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 12 2 236528504444914143 237427011936866013 237427011936866013 endpoint_15_45_p12 endpoint_15_45_w12
def endpoint_15_45 : CertifiedEndpoint :=
  ⟨⟨15, 45, 3059⟩, 237427011936866013, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_45_flag endpoint_15_45_sources 14 236528504444914143 237427011936866013 rfl endpoint_15_45_base endpoint_15_45_p14) (by decide)⟩
private def endpoint_15_46_flag : Flag := ⟨15, 46, 3024⟩
private def endpoint_15_46_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_46_base : receiptBase endpoint_15_46_flag endpoint_15_46_sources = some 238286913318475187 := by decide +kernel
private theorem endpoint_15_46_w0 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 2 238286913318475187 = some 242375435244030224 := by decide +kernel
private theorem endpoint_15_46_w2 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 2 2 242375435244030224 = some 242375435244030224 := by decide +kernel
private theorem endpoint_15_46_p4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 4 238286913318475187 = some 242375435244030224 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 2 2 238286913318475187 242375435244030224 242375435244030224 endpoint_15_46_w0 endpoint_15_46_w2
private theorem endpoint_15_46_w4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 4 2 242375435244030224 = some 242375435244030224 := by decide +kernel
private theorem endpoint_15_46_p6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 6 238286913318475187 = some 242375435244030224 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 4 2 238286913318475187 242375435244030224 242375435244030224 endpoint_15_46_p4 endpoint_15_46_w4
private theorem endpoint_15_46_w6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 6 2 242375435244030224 = some 242375435244030224 := by decide +kernel
private theorem endpoint_15_46_p8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 8 238286913318475187 = some 242375435244030224 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 6 2 238286913318475187 242375435244030224 242375435244030224 endpoint_15_46_p6 endpoint_15_46_w6
private theorem endpoint_15_46_w8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 8 2 242375435244030224 = some 242375435244030224 := by decide +kernel
private theorem endpoint_15_46_p10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 10 238286913318475187 = some 242375435244030224 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 8 2 238286913318475187 242375435244030224 242375435244030224 endpoint_15_46_p8 endpoint_15_46_w8
private theorem endpoint_15_46_w10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 10 2 242375435244030224 = some 242375435244030224 := by decide +kernel
private theorem endpoint_15_46_p12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 12 238286913318475187 = some 242375435244030224 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 10 2 238286913318475187 242375435244030224 242375435244030224 endpoint_15_46_p10 endpoint_15_46_w10
private theorem endpoint_15_46_w12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 12 2 242375435244030224 = some 242375435244030224 := by decide +kernel
private theorem endpoint_15_46_p14 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 14 238286913318475187 = some 242375435244030224 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 12 2 238286913318475187 242375435244030224 242375435244030224 endpoint_15_46_p12 endpoint_15_46_w12
def endpoint_15_46 : CertifiedEndpoint :=
  ⟨⟨15, 46, 3024⟩, 242375435244030224, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_46_flag endpoint_15_46_sources 14 238286913318475187 242375435244030224 rfl endpoint_15_46_base endpoint_15_46_p14) (by decide)⟩
private def endpoint_15_47_flag : Flag := ⟨15, 47, 2988⟩
private def endpoint_15_47_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_47_base : receiptBase endpoint_15_47_flag endpoint_15_47_sources = some 240581277423352188 := by decide +kernel
private theorem endpoint_15_47_w0 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 2 240581277423352188 = some 241834022766376701 := by decide +kernel
private theorem endpoint_15_47_w2 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 2 2 241834022766376701 = some 241834022766376701 := by decide +kernel
private theorem endpoint_15_47_p4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 4 240581277423352188 = some 241834022766376701 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 2 2 240581277423352188 241834022766376701 241834022766376701 endpoint_15_47_w0 endpoint_15_47_w2
private theorem endpoint_15_47_w4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 4 2 241834022766376701 = some 241834022766376701 := by decide +kernel
private theorem endpoint_15_47_p6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 6 240581277423352188 = some 241834022766376701 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 4 2 240581277423352188 241834022766376701 241834022766376701 endpoint_15_47_p4 endpoint_15_47_w4
private theorem endpoint_15_47_w6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 6 2 241834022766376701 = some 241834022766376701 := by decide +kernel
private theorem endpoint_15_47_p8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 8 240581277423352188 = some 241834022766376701 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 6 2 240581277423352188 241834022766376701 241834022766376701 endpoint_15_47_p6 endpoint_15_47_w6
private theorem endpoint_15_47_w8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 8 2 241834022766376701 = some 241834022766376701 := by decide +kernel
private theorem endpoint_15_47_p10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 10 240581277423352188 = some 241834022766376701 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 8 2 240581277423352188 241834022766376701 241834022766376701 endpoint_15_47_p8 endpoint_15_47_w8
private theorem endpoint_15_47_w10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 10 2 241834022766376701 = some 241834022766376701 := by decide +kernel
private theorem endpoint_15_47_p12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 12 240581277423352188 = some 241834022766376701 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 10 2 240581277423352188 241834022766376701 241834022766376701 endpoint_15_47_p10 endpoint_15_47_w10
private theorem endpoint_15_47_w12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 12 2 241834022766376701 = some 241834022766376701 := by decide +kernel
private theorem endpoint_15_47_p14 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 14 240581277423352188 = some 241834022766376701 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 12 2 240581277423352188 241834022766376701 241834022766376701 endpoint_15_47_p12 endpoint_15_47_w12
def endpoint_15_47 : CertifiedEndpoint :=
  ⟨⟨15, 47, 2988⟩, 241834022766376701, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_47_flag endpoint_15_47_sources 14 240581277423352188 241834022766376701 rfl endpoint_15_47_base endpoint_15_47_p14) (by decide)⟩
private def endpoint_15_48_flag : Flag := ⟨15, 48, 2952⟩
private def endpoint_15_48_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_48_base : receiptBase endpoint_15_48_flag endpoint_15_48_sources = some 242064997092945601 := by decide +kernel
private theorem endpoint_15_48_w0 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 2 242064997092945601 = some 246431151889393152 := by decide +kernel
private theorem endpoint_15_48_w2 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 2 2 246431151889393152 = some 246431151889393152 := by decide +kernel
private theorem endpoint_15_48_p4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 4 242064997092945601 = some 246431151889393152 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 2 2 242064997092945601 246431151889393152 246431151889393152 endpoint_15_48_w0 endpoint_15_48_w2
private theorem endpoint_15_48_w4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 4 2 246431151889393152 = some 246431151889393152 := by decide +kernel
private theorem endpoint_15_48_p6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 6 242064997092945601 = some 246431151889393152 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 4 2 242064997092945601 246431151889393152 246431151889393152 endpoint_15_48_p4 endpoint_15_48_w4
private theorem endpoint_15_48_w6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 6 2 246431151889393152 = some 246431151889393152 := by decide +kernel
private theorem endpoint_15_48_p8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 8 242064997092945601 = some 246431151889393152 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 6 2 242064997092945601 246431151889393152 246431151889393152 endpoint_15_48_p6 endpoint_15_48_w6
private theorem endpoint_15_48_w8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 8 2 246431151889393152 = some 246431151889393152 := by decide +kernel
private theorem endpoint_15_48_p10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 10 242064997092945601 = some 246431151889393152 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 8 2 242064997092945601 246431151889393152 246431151889393152 endpoint_15_48_p8 endpoint_15_48_w8
private theorem endpoint_15_48_w10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 10 2 246431151889393152 = some 246431151889393152 := by decide +kernel
private theorem endpoint_15_48_p12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 12 242064997092945601 = some 246431151889393152 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 10 2 242064997092945601 246431151889393152 246431151889393152 endpoint_15_48_p10 endpoint_15_48_w10
private theorem endpoint_15_48_w12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 12 2 246431151889393152 = some 246431151889393152 := by decide +kernel
private theorem endpoint_15_48_p14 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 14 242064997092945601 = some 246431151889393152 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 12 2 242064997092945601 246431151889393152 246431151889393152 endpoint_15_48_p12 endpoint_15_48_w12
def endpoint_15_48 : CertifiedEndpoint :=
  ⟨⟨15, 48, 2952⟩, 246431151889393152, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_48_flag endpoint_15_48_sources 14 242064997092945601 246431151889393152 rfl endpoint_15_48_base endpoint_15_48_p14) (by decide)⟩
private def endpoint_15_49_flag : Flag := ⟨15, 49, 2914⟩
private def endpoint_15_49_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_49_base : receiptBase endpoint_15_49_flag endpoint_15_49_sources = some 243278273148921860 := by decide +kernel
private theorem endpoint_15_49_w0 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 2 243278273148921860 = some 250850516392340431 := by decide +kernel
private theorem endpoint_15_49_w2 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 2 2 250850516392340431 = some 250850516392340431 := by decide +kernel
private theorem endpoint_15_49_p4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 4 243278273148921860 = some 250850516392340431 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 2 2 243278273148921860 250850516392340431 250850516392340431 endpoint_15_49_w0 endpoint_15_49_w2
private theorem endpoint_15_49_w4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 4 2 250850516392340431 = some 250850516392340431 := by decide +kernel
private theorem endpoint_15_49_p6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 6 243278273148921860 = some 250850516392340431 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 4 2 243278273148921860 250850516392340431 250850516392340431 endpoint_15_49_p4 endpoint_15_49_w4
private theorem endpoint_15_49_w6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 6 2 250850516392340431 = some 250850516392340431 := by decide +kernel
private theorem endpoint_15_49_p8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 8 243278273148921860 = some 250850516392340431 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 6 2 243278273148921860 250850516392340431 250850516392340431 endpoint_15_49_p6 endpoint_15_49_w6
private theorem endpoint_15_49_w8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 8 2 250850516392340431 = some 250850516392340431 := by decide +kernel
private theorem endpoint_15_49_p10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 10 243278273148921860 = some 250850516392340431 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 8 2 243278273148921860 250850516392340431 250850516392340431 endpoint_15_49_p8 endpoint_15_49_w8
private theorem endpoint_15_49_w10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 10 2 250850516392340431 = some 250850516392340431 := by decide +kernel
private theorem endpoint_15_49_p12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 12 243278273148921860 = some 250850516392340431 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 10 2 243278273148921860 250850516392340431 250850516392340431 endpoint_15_49_p10 endpoint_15_49_w10
private theorem endpoint_15_49_w12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 12 2 250850516392340431 = some 250850516392340431 := by decide +kernel
private theorem endpoint_15_49_p14 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 14 243278273148921860 = some 250850516392340431 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 12 2 243278273148921860 250850516392340431 250850516392340431 endpoint_15_49_p12 endpoint_15_49_w12
def endpoint_15_49 : CertifiedEndpoint :=
  ⟨⟨15, 49, 2914⟩, 250850516392340431, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_49_flag endpoint_15_49_sources 14 243278273148921860 250850516392340431 rfl endpoint_15_49_base endpoint_15_49_p14) (by decide)⟩
private def endpoint_15_50_flag : Flag := ⟨15, 50, 2876⟩
private def endpoint_15_50_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_50_base : receiptBase endpoint_15_50_flag endpoint_15_50_sources = some 244379912790636510 := by decide +kernel
private theorem endpoint_15_50_w0 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 2 244379912790636510 = some 255179564049530076 := by decide +kernel
private theorem endpoint_15_50_w2 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 2 2 255179564049530076 = some 255179564049530076 := by decide +kernel
private theorem endpoint_15_50_p4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 4 244379912790636510 = some 255179564049530076 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 2 2 244379912790636510 255179564049530076 255179564049530076 endpoint_15_50_w0 endpoint_15_50_w2
private theorem endpoint_15_50_w4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 4 2 255179564049530076 = some 255179564049530076 := by decide +kernel
private theorem endpoint_15_50_p6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 6 244379912790636510 = some 255179564049530076 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 4 2 244379912790636510 255179564049530076 255179564049530076 endpoint_15_50_p4 endpoint_15_50_w4
private theorem endpoint_15_50_w6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 6 2 255179564049530076 = some 255179564049530076 := by decide +kernel
private theorem endpoint_15_50_p8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 8 244379912790636510 = some 255179564049530076 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 6 2 244379912790636510 255179564049530076 255179564049530076 endpoint_15_50_p6 endpoint_15_50_w6
private theorem endpoint_15_50_w8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 8 2 255179564049530076 = some 255179564049530076 := by decide +kernel
private theorem endpoint_15_50_p10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 10 244379912790636510 = some 255179564049530076 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 8 2 244379912790636510 255179564049530076 255179564049530076 endpoint_15_50_p8 endpoint_15_50_w8
private theorem endpoint_15_50_w10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 10 2 255179564049530076 = some 255179564049530076 := by decide +kernel
private theorem endpoint_15_50_p12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 12 244379912790636510 = some 255179564049530076 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 10 2 244379912790636510 255179564049530076 255179564049530076 endpoint_15_50_p10 endpoint_15_50_w10
private theorem endpoint_15_50_w12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 12 2 255179564049530076 = some 255179564049530076 := by decide +kernel
private theorem endpoint_15_50_p14 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 14 244379912790636510 = some 255179564049530076 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 12 2 244379912790636510 255179564049530076 255179564049530076 endpoint_15_50_p12 endpoint_15_50_w12
def endpoint_15_50 : CertifiedEndpoint :=
  ⟨⟨15, 50, 2876⟩, 255179564049530076, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_50_flag endpoint_15_50_sources 14 244379912790636510 255179564049530076 rfl endpoint_15_50_base endpoint_15_50_p14) (by decide)⟩
private def endpoint_15_51_flag : Flag := ⟨15, 51, 2836⟩
private def endpoint_15_51_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_51_base : receiptBase endpoint_15_51_flag endpoint_15_51_sources = some 246003258333402034 := by decide +kernel
private theorem endpoint_15_51_w0 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 2 246003258333402034 = some 255310794612123621 := by decide +kernel
private theorem endpoint_15_51_w2 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 2 2 255310794612123621 = some 255310794612123621 := by decide +kernel
private theorem endpoint_15_51_p4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 4 246003258333402034 = some 255310794612123621 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 2 2 246003258333402034 255310794612123621 255310794612123621 endpoint_15_51_w0 endpoint_15_51_w2
private theorem endpoint_15_51_w4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 4 2 255310794612123621 = some 255310794612123621 := by decide +kernel
private theorem endpoint_15_51_p6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 6 246003258333402034 = some 255310794612123621 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 4 2 246003258333402034 255310794612123621 255310794612123621 endpoint_15_51_p4 endpoint_15_51_w4
private theorem endpoint_15_51_w6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 6 2 255310794612123621 = some 255310794612123621 := by decide +kernel
private theorem endpoint_15_51_p8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 8 246003258333402034 = some 255310794612123621 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 6 2 246003258333402034 255310794612123621 255310794612123621 endpoint_15_51_p6 endpoint_15_51_w6
private theorem endpoint_15_51_w8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 8 2 255310794612123621 = some 255310794612123621 := by decide +kernel
private theorem endpoint_15_51_p10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 10 246003258333402034 = some 255310794612123621 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 8 2 246003258333402034 255310794612123621 255310794612123621 endpoint_15_51_p8 endpoint_15_51_w8
private theorem endpoint_15_51_w10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 10 2 255310794612123621 = some 255310794612123621 := by decide +kernel
private theorem endpoint_15_51_p12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 12 246003258333402034 = some 255310794612123621 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 10 2 246003258333402034 255310794612123621 255310794612123621 endpoint_15_51_p10 endpoint_15_51_w10
private theorem endpoint_15_51_w12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 12 2 255310794612123621 = some 255310794612123621 := by decide +kernel
private theorem endpoint_15_51_p14 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 14 246003258333402034 = some 255310794612123621 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 12 2 246003258333402034 255310794612123621 255310794612123621 endpoint_15_51_p12 endpoint_15_51_w12
def endpoint_15_51 : CertifiedEndpoint :=
  ⟨⟨15, 51, 2836⟩, 255310794612123621, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_51_flag endpoint_15_51_sources 14 246003258333402034 255310794612123621 rfl endpoint_15_51_base endpoint_15_51_p14) (by decide)⟩
private def endpoint_15_52_flag : Flag := ⟨15, 52, 2795⟩
private def endpoint_15_52_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_52_base : receiptBase endpoint_15_52_flag endpoint_15_52_sources = some 246627609293785043 := by decide +kernel
private theorem endpoint_15_52_w0 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 2 246627609293785043 = some 259214810174144624 := by decide +kernel
private theorem endpoint_15_52_w2 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 2 2 259214810174144624 = some 259214810174144624 := by decide +kernel
private theorem endpoint_15_52_p4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 4 246627609293785043 = some 259214810174144624 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 2 2 246627609293785043 259214810174144624 259214810174144624 endpoint_15_52_w0 endpoint_15_52_w2
private theorem endpoint_15_52_w4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 4 2 259214810174144624 = some 259214810174144624 := by decide +kernel
private theorem endpoint_15_52_p6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 6 246627609293785043 = some 259214810174144624 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 4 2 246627609293785043 259214810174144624 259214810174144624 endpoint_15_52_p4 endpoint_15_52_w4
private theorem endpoint_15_52_w6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 6 2 259214810174144624 = some 259214810174144624 := by decide +kernel
private theorem endpoint_15_52_p8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 8 246627609293785043 = some 259214810174144624 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 6 2 246627609293785043 259214810174144624 259214810174144624 endpoint_15_52_p6 endpoint_15_52_w6
private theorem endpoint_15_52_w8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 8 2 259214810174144624 = some 259214810174144624 := by decide +kernel
private theorem endpoint_15_52_p10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 10 246627609293785043 = some 259214810174144624 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 8 2 246627609293785043 259214810174144624 259214810174144624 endpoint_15_52_p8 endpoint_15_52_w8
private theorem endpoint_15_52_w10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 10 2 259214810174144624 = some 259214810174144624 := by decide +kernel
private theorem endpoint_15_52_p12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 12 246627609293785043 = some 259214810174144624 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 10 2 246627609293785043 259214810174144624 259214810174144624 endpoint_15_52_p10 endpoint_15_52_w10
private theorem endpoint_15_52_w12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 12 2 259214810174144624 = some 259214810174144624 := by decide +kernel
private theorem endpoint_15_52_p14 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 14 246627609293785043 = some 259214810174144624 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 12 2 246627609293785043 259214810174144624 259214810174144624 endpoint_15_52_p12 endpoint_15_52_w12
def endpoint_15_52 : CertifiedEndpoint :=
  ⟨⟨15, 52, 2795⟩, 259214810174144624, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_52_flag endpoint_15_52_sources 14 246627609293785043 259214810174144624 rfl endpoint_15_52_base endpoint_15_52_p14) (by decide)⟩
private def endpoint_15_53_flag : Flag := ⟨15, 53, 2753⟩
private def endpoint_15_53_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_53_base : receiptBase endpoint_15_53_flag endpoint_15_53_sources = some 247900533012186269 := by decide +kernel
private theorem endpoint_15_53_w0 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 2 247900533012186269 = some 260346999262455067 := by decide +kernel
private theorem endpoint_15_53_w2 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 2 2 260346999262455067 = some 260346999262455067 := by decide +kernel
private theorem endpoint_15_53_p4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 4 247900533012186269 = some 260346999262455067 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 2 2 247900533012186269 260346999262455067 260346999262455067 endpoint_15_53_w0 endpoint_15_53_w2
private theorem endpoint_15_53_w4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 4 2 260346999262455067 = some 260346999262455067 := by decide +kernel
private theorem endpoint_15_53_p6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 6 247900533012186269 = some 260346999262455067 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 4 2 247900533012186269 260346999262455067 260346999262455067 endpoint_15_53_p4 endpoint_15_53_w4
private theorem endpoint_15_53_w6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 6 2 260346999262455067 = some 260346999262455067 := by decide +kernel
private theorem endpoint_15_53_p8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 8 247900533012186269 = some 260346999262455067 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 6 2 247900533012186269 260346999262455067 260346999262455067 endpoint_15_53_p6 endpoint_15_53_w6
private theorem endpoint_15_53_w8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 8 2 260346999262455067 = some 260346999262455067 := by decide +kernel
private theorem endpoint_15_53_p10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 10 247900533012186269 = some 260346999262455067 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 8 2 247900533012186269 260346999262455067 260346999262455067 endpoint_15_53_p8 endpoint_15_53_w8
private theorem endpoint_15_53_w10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 10 2 260346999262455067 = some 260346999262455067 := by decide +kernel
private theorem endpoint_15_53_p12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 12 247900533012186269 = some 260346999262455067 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 10 2 247900533012186269 260346999262455067 260346999262455067 endpoint_15_53_p10 endpoint_15_53_w10
private theorem endpoint_15_53_w12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 12 2 260346999262455067 = some 260346999262455067 := by decide +kernel
private theorem endpoint_15_53_p14 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 14 247900533012186269 = some 260346999262455067 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 12 2 247900533012186269 260346999262455067 260346999262455067 endpoint_15_53_p12 endpoint_15_53_w12
def endpoint_15_53 : CertifiedEndpoint :=
  ⟨⟨15, 53, 2753⟩, 260346999262455067, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_53_flag endpoint_15_53_sources 14 247900533012186269 260346999262455067 rfl endpoint_15_53_base endpoint_15_53_p14) (by decide)⟩
private def endpoint_15_54_flag : Flag := ⟨15, 54, 2710⟩
private def endpoint_15_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_54_base : receiptBase endpoint_15_54_flag endpoint_15_54_sources = some 248863371433798512 := by decide +kernel
private theorem endpoint_15_54_w0 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 2 248863371433798512 = some 256489196387492544 := by decide +kernel
private theorem endpoint_15_54_w2 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 2 2 256489196387492544 = some 256489196387492544 := by decide +kernel
private theorem endpoint_15_54_p4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 4 248863371433798512 = some 256489196387492544 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 2 2 248863371433798512 256489196387492544 256489196387492544 endpoint_15_54_w0 endpoint_15_54_w2
private theorem endpoint_15_54_w4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 4 2 256489196387492544 = some 256489196387492544 := by decide +kernel
private theorem endpoint_15_54_p6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 6 248863371433798512 = some 256489196387492544 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 4 2 248863371433798512 256489196387492544 256489196387492544 endpoint_15_54_p4 endpoint_15_54_w4
private theorem endpoint_15_54_w6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 6 2 256489196387492544 = some 256489196387492544 := by decide +kernel
private theorem endpoint_15_54_p8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 8 248863371433798512 = some 256489196387492544 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 6 2 248863371433798512 256489196387492544 256489196387492544 endpoint_15_54_p6 endpoint_15_54_w6
private theorem endpoint_15_54_w8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 8 2 256489196387492544 = some 256489196387492544 := by decide +kernel
private theorem endpoint_15_54_p10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 10 248863371433798512 = some 256489196387492544 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 8 2 248863371433798512 256489196387492544 256489196387492544 endpoint_15_54_p8 endpoint_15_54_w8
private theorem endpoint_15_54_w10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 10 2 256489196387492544 = some 256489196387492544 := by decide +kernel
private theorem endpoint_15_54_p12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 12 248863371433798512 = some 256489196387492544 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 10 2 248863371433798512 256489196387492544 256489196387492544 endpoint_15_54_p10 endpoint_15_54_w10
private theorem endpoint_15_54_w12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 12 2 256489196387492544 = some 256489196387492544 := by decide +kernel
private theorem endpoint_15_54_p14 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 14 248863371433798512 = some 256489196387492544 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 12 2 248863371433798512 256489196387492544 256489196387492544 endpoint_15_54_p12 endpoint_15_54_w12
def endpoint_15_54 : CertifiedEndpoint :=
  ⟨⟨15, 54, 2710⟩, 256489196387492544, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_54_flag endpoint_15_54_sources 14 248863371433798512 256489196387492544 rfl endpoint_15_54_base endpoint_15_54_p14) (by decide)⟩
private def endpoint_15_55_flag : Flag := ⟨15, 55, 2666⟩
private def endpoint_15_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_55_base : receiptBase endpoint_15_55_flag endpoint_15_55_sources = some 248856149362206999 := by decide +kernel
private theorem endpoint_15_55_w0 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 2 248856149362206999 = some 259719237331776465 := by decide +kernel
private theorem endpoint_15_55_w2 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 2 2 259719237331776465 = some 259719237331776465 := by decide +kernel
private theorem endpoint_15_55_p4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 4 248856149362206999 = some 259719237331776465 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 2 2 248856149362206999 259719237331776465 259719237331776465 endpoint_15_55_w0 endpoint_15_55_w2
private theorem endpoint_15_55_w4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 4 2 259719237331776465 = some 259719237331776465 := by decide +kernel
private theorem endpoint_15_55_p6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 6 248856149362206999 = some 259719237331776465 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 4 2 248856149362206999 259719237331776465 259719237331776465 endpoint_15_55_p4 endpoint_15_55_w4
private theorem endpoint_15_55_w6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 6 2 259719237331776465 = some 259719237331776465 := by decide +kernel
private theorem endpoint_15_55_p8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 8 248856149362206999 = some 259719237331776465 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 6 2 248856149362206999 259719237331776465 259719237331776465 endpoint_15_55_p6 endpoint_15_55_w6
private theorem endpoint_15_55_w8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 8 2 259719237331776465 = some 259719237331776465 := by decide +kernel
private theorem endpoint_15_55_p10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 10 248856149362206999 = some 259719237331776465 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 8 2 248856149362206999 259719237331776465 259719237331776465 endpoint_15_55_p8 endpoint_15_55_w8
private theorem endpoint_15_55_w10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 10 2 259719237331776465 = some 259719237331776465 := by decide +kernel
private theorem endpoint_15_55_p12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 12 248856149362206999 = some 259719237331776465 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 10 2 248856149362206999 259719237331776465 259719237331776465 endpoint_15_55_p10 endpoint_15_55_w10
private theorem endpoint_15_55_w12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 12 2 259719237331776465 = some 259719237331776465 := by decide +kernel
private theorem endpoint_15_55_p14 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 14 248856149362206999 = some 259719237331776465 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 12 2 248856149362206999 259719237331776465 259719237331776465 endpoint_15_55_p12 endpoint_15_55_w12
def endpoint_15_55 : CertifiedEndpoint :=
  ⟨⟨15, 55, 2666⟩, 259719237331776465, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_55_flag endpoint_15_55_sources 14 248856149362206999 259719237331776465 rfl endpoint_15_55_base endpoint_15_55_p14) (by decide)⟩
private def endpoint_15_56_flag : Flag := ⟨15, 56, 2621⟩
private def endpoint_15_56_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_56_base : receiptBase endpoint_15_56_flag endpoint_15_56_sources = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_w0 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 2 254814784112480624 = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_w2 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 2 2 254814784112480624 = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_p4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 4 254814784112480624 = some 254814784112480624 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 2 2 254814784112480624 254814784112480624 254814784112480624 endpoint_15_56_w0 endpoint_15_56_w2
private theorem endpoint_15_56_w4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 4 2 254814784112480624 = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_p6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 6 254814784112480624 = some 254814784112480624 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 4 2 254814784112480624 254814784112480624 254814784112480624 endpoint_15_56_p4 endpoint_15_56_w4
private theorem endpoint_15_56_w6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 6 2 254814784112480624 = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_p8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 8 254814784112480624 = some 254814784112480624 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 6 2 254814784112480624 254814784112480624 254814784112480624 endpoint_15_56_p6 endpoint_15_56_w6
private theorem endpoint_15_56_w8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 8 2 254814784112480624 = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_p10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 10 254814784112480624 = some 254814784112480624 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 8 2 254814784112480624 254814784112480624 254814784112480624 endpoint_15_56_p8 endpoint_15_56_w8
private theorem endpoint_15_56_w10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 10 2 254814784112480624 = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_p12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 12 254814784112480624 = some 254814784112480624 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 10 2 254814784112480624 254814784112480624 254814784112480624 endpoint_15_56_p10 endpoint_15_56_w10
private theorem endpoint_15_56_w12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 12 2 254814784112480624 = some 254814784112480624 := by decide +kernel
private theorem endpoint_15_56_p14 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 14 254814784112480624 = some 254814784112480624 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 12 2 254814784112480624 254814784112480624 254814784112480624 endpoint_15_56_p12 endpoint_15_56_w12
def endpoint_15_56 : CertifiedEndpoint :=
  ⟨⟨15, 56, 2621⟩, 254814784112480624, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_56_flag endpoint_15_56_sources 14 254814784112480624 254814784112480624 rfl endpoint_15_56_base endpoint_15_56_p14) (by decide)⟩
private def endpoint_15_57_flag : Flag := ⟨15, 57, 2574⟩
private def endpoint_15_57_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_57_base : receiptBase endpoint_15_57_flag endpoint_15_57_sources = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_w0 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 2 254248112305196119 = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_w2 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 2 2 254248112305196119 = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_p4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 4 254248112305196119 = some 254248112305196119 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 2 2 254248112305196119 254248112305196119 254248112305196119 endpoint_15_57_w0 endpoint_15_57_w2
private theorem endpoint_15_57_w4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 4 2 254248112305196119 = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_p6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 6 254248112305196119 = some 254248112305196119 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 4 2 254248112305196119 254248112305196119 254248112305196119 endpoint_15_57_p4 endpoint_15_57_w4
private theorem endpoint_15_57_w6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 6 2 254248112305196119 = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_p8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 8 254248112305196119 = some 254248112305196119 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 6 2 254248112305196119 254248112305196119 254248112305196119 endpoint_15_57_p6 endpoint_15_57_w6
private theorem endpoint_15_57_w8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 8 2 254248112305196119 = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_p10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 10 254248112305196119 = some 254248112305196119 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 8 2 254248112305196119 254248112305196119 254248112305196119 endpoint_15_57_p8 endpoint_15_57_w8
private theorem endpoint_15_57_w10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 10 2 254248112305196119 = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_p12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 12 254248112305196119 = some 254248112305196119 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 10 2 254248112305196119 254248112305196119 254248112305196119 endpoint_15_57_p10 endpoint_15_57_w10
private theorem endpoint_15_57_w12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 12 2 254248112305196119 = some 254248112305196119 := by decide +kernel
private theorem endpoint_15_57_p14 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 14 254248112305196119 = some 254248112305196119 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 12 2 254248112305196119 254248112305196119 254248112305196119 endpoint_15_57_p12 endpoint_15_57_w12
def endpoint_15_57 : CertifiedEndpoint :=
  ⟨⟨15, 57, 2574⟩, 254248112305196119, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_57_flag endpoint_15_57_sources 14 254248112305196119 254248112305196119 rfl endpoint_15_57_base endpoint_15_57_p14) (by decide)⟩
private def endpoint_15_58_flag : Flag := ⟨15, 58, 2526⟩
private def endpoint_15_58_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_58_base : receiptBase endpoint_15_58_flag endpoint_15_58_sources = some 253442950106923999 := by decide +kernel
private theorem endpoint_15_58_w0 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 2 253442950106923999 = some 255499125146782112 := by decide +kernel
private theorem endpoint_15_58_w2 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 2 2 255499125146782112 = some 255499125146782112 := by decide +kernel
private theorem endpoint_15_58_p4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 4 253442950106923999 = some 255499125146782112 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 2 2 253442950106923999 255499125146782112 255499125146782112 endpoint_15_58_w0 endpoint_15_58_w2
private theorem endpoint_15_58_w4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 4 2 255499125146782112 = some 255499125146782112 := by decide +kernel
private theorem endpoint_15_58_p6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 6 253442950106923999 = some 255499125146782112 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 4 2 253442950106923999 255499125146782112 255499125146782112 endpoint_15_58_p4 endpoint_15_58_w4
private theorem endpoint_15_58_w6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 6 2 255499125146782112 = some 255499125146782112 := by decide +kernel
private theorem endpoint_15_58_p8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 8 253442950106923999 = some 255499125146782112 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 6 2 253442950106923999 255499125146782112 255499125146782112 endpoint_15_58_p6 endpoint_15_58_w6
private theorem endpoint_15_58_w8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 8 2 255499125146782112 = some 255499125146782112 := by decide +kernel
private theorem endpoint_15_58_p10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 10 253442950106923999 = some 255499125146782112 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 8 2 253442950106923999 255499125146782112 255499125146782112 endpoint_15_58_p8 endpoint_15_58_w8
private theorem endpoint_15_58_w10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 10 2 255499125146782112 = some 255499125146782112 := by decide +kernel
private theorem endpoint_15_58_p12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 12 253442950106923999 = some 255499125146782112 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 10 2 253442950106923999 255499125146782112 255499125146782112 endpoint_15_58_p10 endpoint_15_58_w10
private theorem endpoint_15_58_w12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 12 2 255499125146782112 = some 255499125146782112 := by decide +kernel
private theorem endpoint_15_58_p14 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 14 253442950106923999 = some 255499125146782112 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 12 2 253442950106923999 255499125146782112 255499125146782112 endpoint_15_58_p12 endpoint_15_58_w12
def endpoint_15_58 : CertifiedEndpoint :=
  ⟨⟨15, 58, 2526⟩, 255499125146782112, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_58_flag endpoint_15_58_sources 14 253442950106923999 255499125146782112 rfl endpoint_15_58_base endpoint_15_58_p14) (by decide)⟩
private def endpoint_15_59_flag : Flag := ⟨15, 59, 2476⟩
private def endpoint_15_59_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_59_base : receiptBase endpoint_15_59_flag endpoint_15_59_sources = some 252295397196258319 := by decide +kernel
private theorem endpoint_15_59_w0 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 2 252295397196258319 = some 257701354525803305 := by decide +kernel
private theorem endpoint_15_59_w2 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 2 2 257701354525803305 = some 257701354525803305 := by decide +kernel
private theorem endpoint_15_59_p4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 4 252295397196258319 = some 257701354525803305 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 2 2 252295397196258319 257701354525803305 257701354525803305 endpoint_15_59_w0 endpoint_15_59_w2
private theorem endpoint_15_59_w4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 4 2 257701354525803305 = some 257701354525803305 := by decide +kernel
private theorem endpoint_15_59_p6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 6 252295397196258319 = some 257701354525803305 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 4 2 252295397196258319 257701354525803305 257701354525803305 endpoint_15_59_p4 endpoint_15_59_w4
private theorem endpoint_15_59_w6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 6 2 257701354525803305 = some 257701354525803305 := by decide +kernel
private theorem endpoint_15_59_p8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 8 252295397196258319 = some 257701354525803305 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 6 2 252295397196258319 257701354525803305 257701354525803305 endpoint_15_59_p6 endpoint_15_59_w6
private theorem endpoint_15_59_w8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 8 2 257701354525803305 = some 257701354525803305 := by decide +kernel
private theorem endpoint_15_59_p10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 10 252295397196258319 = some 257701354525803305 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 8 2 252295397196258319 257701354525803305 257701354525803305 endpoint_15_59_p8 endpoint_15_59_w8
private theorem endpoint_15_59_w10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 10 2 257701354525803305 = some 257701354525803305 := by decide +kernel
private theorem endpoint_15_59_p12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 12 252295397196258319 = some 257701354525803305 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 10 2 252295397196258319 257701354525803305 257701354525803305 endpoint_15_59_p10 endpoint_15_59_w10
private theorem endpoint_15_59_w12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 12 2 257701354525803305 = some 257701354525803305 := by decide +kernel
private theorem endpoint_15_59_p14 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 14 252295397196258319 = some 257701354525803305 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 12 2 252295397196258319 257701354525803305 257701354525803305 endpoint_15_59_p12 endpoint_15_59_w12
def endpoint_15_59 : CertifiedEndpoint :=
  ⟨⟨15, 59, 2476⟩, 257701354525803305, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_59_flag endpoint_15_59_sources 14 252295397196258319 257701354525803305 rfl endpoint_15_59_base endpoint_15_59_p14) (by decide)⟩
private def endpoint_15_60_flag : Flag := ⟨15, 60, 2425⟩
private def endpoint_15_60_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_60_base : receiptBase endpoint_15_60_flag endpoint_15_60_sources = some 250897521800575867 := by decide +kernel
private theorem endpoint_15_60_w0 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 2 250897521800575867 = some 259727271039276288 := by decide +kernel
private theorem endpoint_15_60_w2 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 2 2 259727271039276288 = some 259727271039276288 := by decide +kernel
private theorem endpoint_15_60_p4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 4 250897521800575867 = some 259727271039276288 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 2 2 250897521800575867 259727271039276288 259727271039276288 endpoint_15_60_w0 endpoint_15_60_w2
private theorem endpoint_15_60_w4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 4 2 259727271039276288 = some 259727271039276288 := by decide +kernel
private theorem endpoint_15_60_p6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 6 250897521800575867 = some 259727271039276288 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 4 2 250897521800575867 259727271039276288 259727271039276288 endpoint_15_60_p4 endpoint_15_60_w4
private theorem endpoint_15_60_w6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 6 2 259727271039276288 = some 259727271039276288 := by decide +kernel
private theorem endpoint_15_60_p8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 8 250897521800575867 = some 259727271039276288 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 6 2 250897521800575867 259727271039276288 259727271039276288 endpoint_15_60_p6 endpoint_15_60_w6
private theorem endpoint_15_60_w8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 8 2 259727271039276288 = some 259727271039276288 := by decide +kernel
private theorem endpoint_15_60_p10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 10 250897521800575867 = some 259727271039276288 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 8 2 250897521800575867 259727271039276288 259727271039276288 endpoint_15_60_p8 endpoint_15_60_w8
private theorem endpoint_15_60_w10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 10 2 259727271039276288 = some 259727271039276288 := by decide +kernel
private theorem endpoint_15_60_p12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 12 250897521800575867 = some 259727271039276288 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 10 2 250897521800575867 259727271039276288 259727271039276288 endpoint_15_60_p10 endpoint_15_60_w10
private theorem endpoint_15_60_w12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 12 2 259727271039276288 = some 259727271039276288 := by decide +kernel
private theorem endpoint_15_60_p14 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 14 250897521800575867 = some 259727271039276288 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 12 2 250897521800575867 259727271039276288 259727271039276288 endpoint_15_60_p12 endpoint_15_60_w12
def endpoint_15_60 : CertifiedEndpoint :=
  ⟨⟨15, 60, 2425⟩, 259727271039276288, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_60_flag endpoint_15_60_sources 14 250897521800575867 259727271039276288 rfl endpoint_15_60_base endpoint_15_60_p14) (by decide)⟩
private def endpoint_15_61_flag : Flag := ⟨15, 61, 2372⟩
private def endpoint_15_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_61_base : receiptBase endpoint_15_61_flag endpoint_15_61_sources = some 249142465574963409 := by decide +kernel
private theorem endpoint_15_61_w0 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 2 249142465574963409 = some 261513728468834705 := by decide +kernel
private theorem endpoint_15_61_w2 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 2 2 261513728468834705 = some 261513728468834705 := by decide +kernel
private theorem endpoint_15_61_p4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 4 249142465574963409 = some 261513728468834705 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 2 2 249142465574963409 261513728468834705 261513728468834705 endpoint_15_61_w0 endpoint_15_61_w2
private theorem endpoint_15_61_w4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 4 2 261513728468834705 = some 261513728468834705 := by decide +kernel
private theorem endpoint_15_61_p6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 6 249142465574963409 = some 261513728468834705 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 4 2 249142465574963409 261513728468834705 261513728468834705 endpoint_15_61_p4 endpoint_15_61_w4
private theorem endpoint_15_61_w6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 6 2 261513728468834705 = some 261513728468834705 := by decide +kernel
private theorem endpoint_15_61_p8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 8 249142465574963409 = some 261513728468834705 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 6 2 249142465574963409 261513728468834705 261513728468834705 endpoint_15_61_p6 endpoint_15_61_w6
private theorem endpoint_15_61_w8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 8 2 261513728468834705 = some 261513728468834705 := by decide +kernel
private theorem endpoint_15_61_p10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 10 249142465574963409 = some 261513728468834705 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 8 2 249142465574963409 261513728468834705 261513728468834705 endpoint_15_61_p8 endpoint_15_61_w8
private theorem endpoint_15_61_w10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 10 2 261513728468834705 = some 261513728468834705 := by decide +kernel
private theorem endpoint_15_61_p12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 12 249142465574963409 = some 261513728468834705 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 10 2 249142465574963409 261513728468834705 261513728468834705 endpoint_15_61_p10 endpoint_15_61_w10
private theorem endpoint_15_61_w12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 12 2 261513728468834705 = some 261513728468834705 := by decide +kernel
private theorem endpoint_15_61_p14 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 14 249142465574963409 = some 261513728468834705 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 12 2 249142465574963409 261513728468834705 261513728468834705 endpoint_15_61_p12 endpoint_15_61_w12
def endpoint_15_61 : CertifiedEndpoint :=
  ⟨⟨15, 61, 2372⟩, 261513728468834705, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_61_flag endpoint_15_61_sources 14 249142465574963409 261513728468834705 rfl endpoint_15_61_base endpoint_15_61_p14) (by decide)⟩
private def endpoint_15_62_flag : Flag := ⟨15, 62, 2318⟩
private def endpoint_15_62_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_15_62_base : receiptBase endpoint_15_62_flag endpoint_15_62_sources = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_w0 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 2 253258050918825068 = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_w2 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 2 2 253258050918825068 = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_p4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 4 253258050918825068 = some 253258050918825068 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 2 2 253258050918825068 253258050918825068 253258050918825068 endpoint_15_62_w0 endpoint_15_62_w2
private theorem endpoint_15_62_w4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 4 2 253258050918825068 = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_p6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 6 253258050918825068 = some 253258050918825068 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 4 2 253258050918825068 253258050918825068 253258050918825068 endpoint_15_62_p4 endpoint_15_62_w4
private theorem endpoint_15_62_w6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 6 2 253258050918825068 = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_p8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 8 253258050918825068 = some 253258050918825068 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 6 2 253258050918825068 253258050918825068 253258050918825068 endpoint_15_62_p6 endpoint_15_62_w6
private theorem endpoint_15_62_w8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 8 2 253258050918825068 = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_p10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 10 253258050918825068 = some 253258050918825068 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 8 2 253258050918825068 253258050918825068 253258050918825068 endpoint_15_62_p8 endpoint_15_62_w8
private theorem endpoint_15_62_w10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 10 2 253258050918825068 = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_p12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 12 253258050918825068 = some 253258050918825068 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 10 2 253258050918825068 253258050918825068 253258050918825068 endpoint_15_62_p10 endpoint_15_62_w10
private theorem endpoint_15_62_w12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 12 2 253258050918825068 = some 253258050918825068 := by decide +kernel
private theorem endpoint_15_62_p14 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 14 253258050918825068 = some 253258050918825068 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 12 2 253258050918825068 253258050918825068 253258050918825068 endpoint_15_62_p12 endpoint_15_62_w12
def endpoint_15_62 : CertifiedEndpoint :=
  ⟨⟨15, 62, 2318⟩, 253258050918825068, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_15_62_flag endpoint_15_62_sources 14 253258050918825068 253258050918825068 rfl endpoint_15_62_base endpoint_15_62_p14) (by decide)⟩
private def endpoint_15_63_flag : Flag := ⟨15, 63, 2262⟩
private def endpoint_15_63_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_63_base : receiptBase endpoint_15_63_flag endpoint_15_63_sources = some 245828571446702015 := by decide +kernel
private theorem endpoint_15_63_w0 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 2 245828571446702015 = some 251238197645506842 := by decide +kernel
private theorem endpoint_15_63_w2 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 2 2 251238197645506842 = some 251238197645506842 := by decide +kernel
private theorem endpoint_15_63_p4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 4 245828571446702015 = some 251238197645506842 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 2 2 245828571446702015 251238197645506842 251238197645506842 endpoint_15_63_w0 endpoint_15_63_w2
private theorem endpoint_15_63_w4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 4 2 251238197645506842 = some 251238197645506842 := by decide +kernel
private theorem endpoint_15_63_p6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 6 245828571446702015 = some 251238197645506842 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 4 2 245828571446702015 251238197645506842 251238197645506842 endpoint_15_63_p4 endpoint_15_63_w4
private theorem endpoint_15_63_w6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 6 2 251238197645506842 = some 251238197645506842 := by decide +kernel
private theorem endpoint_15_63_p8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 8 245828571446702015 = some 251238197645506842 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 6 2 245828571446702015 251238197645506842 251238197645506842 endpoint_15_63_p6 endpoint_15_63_w6
private theorem endpoint_15_63_w8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 8 2 251238197645506842 = some 251238197645506842 := by decide +kernel
private theorem endpoint_15_63_p10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 10 245828571446702015 = some 251238197645506842 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 8 2 245828571446702015 251238197645506842 251238197645506842 endpoint_15_63_p8 endpoint_15_63_w8
private theorem endpoint_15_63_w10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 10 2 251238197645506842 = some 251238197645506842 := by decide +kernel
private theorem endpoint_15_63_p12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 12 245828571446702015 = some 251238197645506842 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 10 2 245828571446702015 251238197645506842 251238197645506842 endpoint_15_63_p10 endpoint_15_63_w10
private theorem endpoint_15_63_w12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 12 2 251238197645506842 = some 251238197645506842 := by decide +kernel
private theorem endpoint_15_63_p14 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 14 245828571446702015 = some 251238197645506842 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 12 2 245828571446702015 251238197645506842 251238197645506842 endpoint_15_63_p12 endpoint_15_63_w12
def endpoint_15_63 : CertifiedEndpoint :=
  ⟨⟨15, 63, 2262⟩, 251238197645506842, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_63_flag endpoint_15_63_sources 14 245828571446702015 251238197645506842 rfl endpoint_15_63_base endpoint_15_63_p14) (by decide)⟩
private def endpoint_15_64_flag : Flag := ⟨15, 64, 2204⟩
private def endpoint_15_64_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_64_base : receiptBase endpoint_15_64_flag endpoint_15_64_sources = some 243036573532332927 := by decide +kernel
private theorem endpoint_15_64_w0 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 2 243036573532332927 = some 252089033021004882 := by decide +kernel
private theorem endpoint_15_64_w2 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 2 2 252089033021004882 = some 252089033021004882 := by decide +kernel
private theorem endpoint_15_64_p4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 4 243036573532332927 = some 252089033021004882 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 2 2 243036573532332927 252089033021004882 252089033021004882 endpoint_15_64_w0 endpoint_15_64_w2
private theorem endpoint_15_64_w4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 4 2 252089033021004882 = some 252089033021004882 := by decide +kernel
private theorem endpoint_15_64_p6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 6 243036573532332927 = some 252089033021004882 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 4 2 243036573532332927 252089033021004882 252089033021004882 endpoint_15_64_p4 endpoint_15_64_w4
private theorem endpoint_15_64_w6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 6 2 252089033021004882 = some 252089033021004882 := by decide +kernel
private theorem endpoint_15_64_p8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 8 243036573532332927 = some 252089033021004882 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 6 2 243036573532332927 252089033021004882 252089033021004882 endpoint_15_64_p6 endpoint_15_64_w6
private theorem endpoint_15_64_w8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 8 2 252089033021004882 = some 252089033021004882 := by decide +kernel
private theorem endpoint_15_64_p10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 10 243036573532332927 = some 252089033021004882 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 8 2 243036573532332927 252089033021004882 252089033021004882 endpoint_15_64_p8 endpoint_15_64_w8
private theorem endpoint_15_64_w10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 10 2 252089033021004882 = some 252089033021004882 := by decide +kernel
private theorem endpoint_15_64_p12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 12 243036573532332927 = some 252089033021004882 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 10 2 243036573532332927 252089033021004882 252089033021004882 endpoint_15_64_p10 endpoint_15_64_w10
private theorem endpoint_15_64_w12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 12 2 252089033021004882 = some 252089033021004882 := by decide +kernel
private theorem endpoint_15_64_p14 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 14 243036573532332927 = some 252089033021004882 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 12 2 243036573532332927 252089033021004882 252089033021004882 endpoint_15_64_p12 endpoint_15_64_w12
def endpoint_15_64 : CertifiedEndpoint :=
  ⟨⟨15, 64, 2204⟩, 252089033021004882, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_64_flag endpoint_15_64_sources 14 243036573532332927 252089033021004882 rfl endpoint_15_64_base endpoint_15_64_p14) (by decide)⟩
private def endpoint_15_65_flag : Flag := ⟨15, 65, 2145⟩
private def endpoint_15_65_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_65_base : receiptBase endpoint_15_65_flag endpoint_15_65_sources = some 239960569339939098 := by decide +kernel
private theorem endpoint_15_65_w0 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 2 239960569339939098 = some 252739563239459281 := by decide +kernel
private theorem endpoint_15_65_w2 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 2 2 252739563239459281 = some 252739563239459281 := by decide +kernel
private theorem endpoint_15_65_p4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 4 239960569339939098 = some 252739563239459281 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 2 2 239960569339939098 252739563239459281 252739563239459281 endpoint_15_65_w0 endpoint_15_65_w2
private theorem endpoint_15_65_w4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 4 2 252739563239459281 = some 252739563239459281 := by decide +kernel
private theorem endpoint_15_65_p6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 6 239960569339939098 = some 252739563239459281 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 4 2 239960569339939098 252739563239459281 252739563239459281 endpoint_15_65_p4 endpoint_15_65_w4
private theorem endpoint_15_65_w6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 6 2 252739563239459281 = some 252739563239459281 := by decide +kernel
private theorem endpoint_15_65_p8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 8 239960569339939098 = some 252739563239459281 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 6 2 239960569339939098 252739563239459281 252739563239459281 endpoint_15_65_p6 endpoint_15_65_w6
private theorem endpoint_15_65_w8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 8 2 252739563239459281 = some 252739563239459281 := by decide +kernel
private theorem endpoint_15_65_p10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 10 239960569339939098 = some 252739563239459281 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 8 2 239960569339939098 252739563239459281 252739563239459281 endpoint_15_65_p8 endpoint_15_65_w8
private theorem endpoint_15_65_w10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 10 2 252739563239459281 = some 252739563239459281 := by decide +kernel
private theorem endpoint_15_65_p12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 12 239960569339939098 = some 252739563239459281 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 10 2 239960569339939098 252739563239459281 252739563239459281 endpoint_15_65_p10 endpoint_15_65_w10
private theorem endpoint_15_65_w12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 12 2 252739563239459281 = some 252739563239459281 := by decide +kernel
private theorem endpoint_15_65_p14 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 14 239960569339939098 = some 252739563239459281 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 12 2 239960569339939098 252739563239459281 252739563239459281 endpoint_15_65_p12 endpoint_15_65_w12
def endpoint_15_65 : CertifiedEndpoint :=
  ⟨⟨15, 65, 2145⟩, 252739563239459281, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_65_flag endpoint_15_65_sources 14 239960569339939098 252739563239459281 rfl endpoint_15_65_base endpoint_15_65_p14) (by decide)⟩
private def endpoint_15_66_flag : Flag := ⟨15, 66, 2083⟩
private def endpoint_15_66_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_15_66_base : receiptBase endpoint_15_66_flag endpoint_15_66_sources = some 237824331771854061 := by decide +kernel
private theorem endpoint_15_66_w0 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 2 237824331771854061 = some 246147575567437314 := by decide +kernel
private theorem endpoint_15_66_w2 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 2 2 246147575567437314 = some 246147575567437314 := by decide +kernel
private theorem endpoint_15_66_p4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 4 237824331771854061 = some 246147575567437314 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 2 2 237824331771854061 246147575567437314 246147575567437314 endpoint_15_66_w0 endpoint_15_66_w2
private theorem endpoint_15_66_w4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 4 2 246147575567437314 = some 246147575567437314 := by decide +kernel
private theorem endpoint_15_66_p6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 6 237824331771854061 = some 246147575567437314 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 4 2 237824331771854061 246147575567437314 246147575567437314 endpoint_15_66_p4 endpoint_15_66_w4
private theorem endpoint_15_66_w6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 6 2 246147575567437314 = some 246147575567437314 := by decide +kernel
private theorem endpoint_15_66_p8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 8 237824331771854061 = some 246147575567437314 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 6 2 237824331771854061 246147575567437314 246147575567437314 endpoint_15_66_p6 endpoint_15_66_w6
private theorem endpoint_15_66_w8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 8 2 246147575567437314 = some 246147575567437314 := by decide +kernel
private theorem endpoint_15_66_p10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 10 237824331771854061 = some 246147575567437314 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 8 2 237824331771854061 246147575567437314 246147575567437314 endpoint_15_66_p8 endpoint_15_66_w8
private theorem endpoint_15_66_w10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 10 2 246147575567437314 = some 246147575567437314 := by decide +kernel
private theorem endpoint_15_66_p12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 12 237824331771854061 = some 246147575567437314 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 10 2 237824331771854061 246147575567437314 246147575567437314 endpoint_15_66_p10 endpoint_15_66_w10
private theorem endpoint_15_66_w12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 12 2 246147575567437314 = some 246147575567437314 := by decide +kernel
private theorem endpoint_15_66_p14 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 14 237824331771854061 = some 246147575567437314 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 12 2 237824331771854061 246147575567437314 246147575567437314 endpoint_15_66_p12 endpoint_15_66_w12
def endpoint_15_66 : CertifiedEndpoint :=
  ⟨⟨15, 66, 2083⟩, 246147575567437314, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_15_66_flag endpoint_15_66_sources 14 237824331771854061 246147575567437314 rfl endpoint_15_66_base endpoint_15_66_p14) (by decide)⟩
private def endpoint_15_67_flag : Flag := ⟨15, 67, 2019⟩
private def endpoint_15_67_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_67_base : receiptBase endpoint_15_67_flag endpoint_15_67_sources = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_w0 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 2 236924885565500215 = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_w2 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 2 2 236924885565500215 = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_p4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 4 236924885565500215 = some 236924885565500215 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 2 2 236924885565500215 236924885565500215 236924885565500215 endpoint_15_67_w0 endpoint_15_67_w2
private theorem endpoint_15_67_w4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 4 2 236924885565500215 = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_p6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 6 236924885565500215 = some 236924885565500215 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 4 2 236924885565500215 236924885565500215 236924885565500215 endpoint_15_67_p4 endpoint_15_67_w4
private theorem endpoint_15_67_w6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 6 2 236924885565500215 = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_p8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 8 236924885565500215 = some 236924885565500215 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 6 2 236924885565500215 236924885565500215 236924885565500215 endpoint_15_67_p6 endpoint_15_67_w6
private theorem endpoint_15_67_w8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 8 2 236924885565500215 = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_p10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 10 236924885565500215 = some 236924885565500215 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 8 2 236924885565500215 236924885565500215 236924885565500215 endpoint_15_67_p8 endpoint_15_67_w8
private theorem endpoint_15_67_w10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 10 2 236924885565500215 = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_p12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 12 236924885565500215 = some 236924885565500215 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 10 2 236924885565500215 236924885565500215 236924885565500215 endpoint_15_67_p10 endpoint_15_67_w10
private theorem endpoint_15_67_w12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 12 2 236924885565500215 = some 236924885565500215 := by decide +kernel
private theorem endpoint_15_67_p14 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 14 236924885565500215 = some 236924885565500215 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 12 2 236924885565500215 236924885565500215 236924885565500215 endpoint_15_67_p12 endpoint_15_67_w12
def endpoint_15_67 : CertifiedEndpoint :=
  ⟨⟨15, 67, 2019⟩, 236924885565500215, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_67_flag endpoint_15_67_sources 14 236924885565500215 236924885565500215 rfl endpoint_15_67_base endpoint_15_67_p14) (by decide)⟩
private def endpoint_15_68_flag : Flag := ⟨15, 68, 1954⟩
private def endpoint_15_68_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_68_base : receiptBase endpoint_15_68_flag endpoint_15_68_sources = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_w0 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 2 232395218440185572 = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_w2 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 2 2 232395218440185572 = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_p4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 4 232395218440185572 = some 232395218440185572 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 2 2 232395218440185572 232395218440185572 232395218440185572 endpoint_15_68_w0 endpoint_15_68_w2
private theorem endpoint_15_68_w4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 4 2 232395218440185572 = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_p6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 6 232395218440185572 = some 232395218440185572 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 4 2 232395218440185572 232395218440185572 232395218440185572 endpoint_15_68_p4 endpoint_15_68_w4
private theorem endpoint_15_68_w6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 6 2 232395218440185572 = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_p8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 8 232395218440185572 = some 232395218440185572 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 6 2 232395218440185572 232395218440185572 232395218440185572 endpoint_15_68_p6 endpoint_15_68_w6
private theorem endpoint_15_68_w8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 8 2 232395218440185572 = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_p10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 10 232395218440185572 = some 232395218440185572 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 8 2 232395218440185572 232395218440185572 232395218440185572 endpoint_15_68_p8 endpoint_15_68_w8
private theorem endpoint_15_68_w10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 10 2 232395218440185572 = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_p12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 12 232395218440185572 = some 232395218440185572 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 10 2 232395218440185572 232395218440185572 232395218440185572 endpoint_15_68_p10 endpoint_15_68_w10
private theorem endpoint_15_68_w12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 12 2 232395218440185572 = some 232395218440185572 := by decide +kernel
private theorem endpoint_15_68_p14 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 14 232395218440185572 = some 232395218440185572 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 12 2 232395218440185572 232395218440185572 232395218440185572 endpoint_15_68_p12 endpoint_15_68_w12
def endpoint_15_68 : CertifiedEndpoint :=
  ⟨⟨15, 68, 1954⟩, 232395218440185572, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_68_flag endpoint_15_68_sources 14 232395218440185572 232395218440185572 rfl endpoint_15_68_base endpoint_15_68_p14) (by decide)⟩
private def endpoint_15_69_flag : Flag := ⟨15, 69, 1885⟩
private def endpoint_15_69_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_69_base : receiptBase endpoint_15_69_flag endpoint_15_69_sources = some 227185206049815643 := by decide +kernel
private theorem endpoint_15_69_w0 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 2 227185206049815643 = some 227656191586147872 := by decide +kernel
private theorem endpoint_15_69_w2 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 2 2 227656191586147872 = some 227656191586147872 := by decide +kernel
private theorem endpoint_15_69_p4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 4 227185206049815643 = some 227656191586147872 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 2 2 227185206049815643 227656191586147872 227656191586147872 endpoint_15_69_w0 endpoint_15_69_w2
private theorem endpoint_15_69_w4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 4 2 227656191586147872 = some 227656191586147872 := by decide +kernel
private theorem endpoint_15_69_p6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 6 227185206049815643 = some 227656191586147872 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 4 2 227185206049815643 227656191586147872 227656191586147872 endpoint_15_69_p4 endpoint_15_69_w4
private theorem endpoint_15_69_w6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 6 2 227656191586147872 = some 227656191586147872 := by decide +kernel
private theorem endpoint_15_69_p8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 8 227185206049815643 = some 227656191586147872 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 6 2 227185206049815643 227656191586147872 227656191586147872 endpoint_15_69_p6 endpoint_15_69_w6
private theorem endpoint_15_69_w8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 8 2 227656191586147872 = some 227656191586147872 := by decide +kernel
private theorem endpoint_15_69_p10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 10 227185206049815643 = some 227656191586147872 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 8 2 227185206049815643 227656191586147872 227656191586147872 endpoint_15_69_p8 endpoint_15_69_w8
private theorem endpoint_15_69_w10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 10 2 227656191586147872 = some 227656191586147872 := by decide +kernel
private theorem endpoint_15_69_p12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 12 227185206049815643 = some 227656191586147872 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 10 2 227185206049815643 227656191586147872 227656191586147872 endpoint_15_69_p10 endpoint_15_69_w10
private theorem endpoint_15_69_w12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 12 2 227656191586147872 = some 227656191586147872 := by decide +kernel
private theorem endpoint_15_69_p14 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 14 227185206049815643 = some 227656191586147872 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 12 2 227185206049815643 227656191586147872 227656191586147872 endpoint_15_69_p12 endpoint_15_69_w12
def endpoint_15_69 : CertifiedEndpoint :=
  ⟨⟨15, 69, 1885⟩, 227656191586147872, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_69_flag endpoint_15_69_sources 14 227185206049815643 227656191586147872 rfl endpoint_15_69_base endpoint_15_69_p14) (by decide)⟩
private def endpoint_15_70_flag : Flag := ⟨15, 70, 1815⟩
private def endpoint_15_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_15_70_base : receiptBase endpoint_15_70_flag endpoint_15_70_sources = some 220203425349100807 := by decide +kernel
private theorem endpoint_15_70_w0 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 2 220203425349100807 = some 227425887438387922 := by decide +kernel
private theorem endpoint_15_70_w2 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 2 2 227425887438387922 = some 227425887438387922 := by decide +kernel
private theorem endpoint_15_70_p4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 4 220203425349100807 = some 227425887438387922 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 2 2 220203425349100807 227425887438387922 227425887438387922 endpoint_15_70_w0 endpoint_15_70_w2
private theorem endpoint_15_70_w4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 4 2 227425887438387922 = some 227425887438387922 := by decide +kernel
private theorem endpoint_15_70_p6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 6 220203425349100807 = some 227425887438387922 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 4 2 220203425349100807 227425887438387922 227425887438387922 endpoint_15_70_p4 endpoint_15_70_w4
private theorem endpoint_15_70_w6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 6 2 227425887438387922 = some 227425887438387922 := by decide +kernel
private theorem endpoint_15_70_p8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 8 220203425349100807 = some 227425887438387922 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 6 2 220203425349100807 227425887438387922 227425887438387922 endpoint_15_70_p6 endpoint_15_70_w6
private theorem endpoint_15_70_w8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 8 2 227425887438387922 = some 227425887438387922 := by decide +kernel
private theorem endpoint_15_70_p10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 10 220203425349100807 = some 227425887438387922 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 8 2 220203425349100807 227425887438387922 227425887438387922 endpoint_15_70_p8 endpoint_15_70_w8
private theorem endpoint_15_70_w10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 10 2 227425887438387922 = some 227425887438387922 := by decide +kernel
private theorem endpoint_15_70_p12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 12 220203425349100807 = some 227425887438387922 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 10 2 220203425349100807 227425887438387922 227425887438387922 endpoint_15_70_p10 endpoint_15_70_w10
private theorem endpoint_15_70_w12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 12 2 227425887438387922 = some 227425887438387922 := by decide +kernel
private theorem endpoint_15_70_p14 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 14 220203425349100807 = some 227425887438387922 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 12 2 220203425349100807 227425887438387922 227425887438387922 endpoint_15_70_p12 endpoint_15_70_w12
def endpoint_15_70 : CertifiedEndpoint :=
  ⟨⟨15, 70, 1815⟩, 227425887438387922, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_15_70_flag endpoint_15_70_sources 14 220203425349100807 227425887438387922 rfl endpoint_15_70_base endpoint_15_70_p14) (by decide)⟩
private def endpoint_15_71_flag : Flag := ⟨15, 71, 1742⟩
private def endpoint_15_71_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_71_base : receiptBase endpoint_15_71_flag endpoint_15_71_sources = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_w0 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 2 217230522718297441 = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_w2 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 2 2 217230522718297441 = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_p4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 4 217230522718297441 = some 217230522718297441 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 2 2 217230522718297441 217230522718297441 217230522718297441 endpoint_15_71_w0 endpoint_15_71_w2
private theorem endpoint_15_71_w4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 4 2 217230522718297441 = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_p6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 6 217230522718297441 = some 217230522718297441 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 4 2 217230522718297441 217230522718297441 217230522718297441 endpoint_15_71_p4 endpoint_15_71_w4
private theorem endpoint_15_71_w6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 6 2 217230522718297441 = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_p8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 8 217230522718297441 = some 217230522718297441 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 6 2 217230522718297441 217230522718297441 217230522718297441 endpoint_15_71_p6 endpoint_15_71_w6
private theorem endpoint_15_71_w8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 8 2 217230522718297441 = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_p10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 10 217230522718297441 = some 217230522718297441 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 8 2 217230522718297441 217230522718297441 217230522718297441 endpoint_15_71_p8 endpoint_15_71_w8
private theorem endpoint_15_71_w10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 10 2 217230522718297441 = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_p12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 12 217230522718297441 = some 217230522718297441 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 10 2 217230522718297441 217230522718297441 217230522718297441 endpoint_15_71_p10 endpoint_15_71_w10
private theorem endpoint_15_71_w12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 12 2 217230522718297441 = some 217230522718297441 := by decide +kernel
private theorem endpoint_15_71_p14 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 14 217230522718297441 = some 217230522718297441 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 12 2 217230522718297441 217230522718297441 217230522718297441 endpoint_15_71_p12 endpoint_15_71_w12
def endpoint_15_71 : CertifiedEndpoint :=
  ⟨⟨15, 71, 1742⟩, 217230522718297441, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_71_flag endpoint_15_71_sources 14 217230522718297441 217230522718297441 rfl endpoint_15_71_base endpoint_15_71_p14) (by decide)⟩
private def endpoint_15_72_flag : Flag := ⟨15, 72, 1667⟩
private def endpoint_15_72_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_72_base : receiptBase endpoint_15_72_flag endpoint_15_72_sources = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_w0 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 2 210556759421358873 = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_w2 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 2 2 210556759421358873 = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_p4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 4 210556759421358873 = some 210556759421358873 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 2 2 210556759421358873 210556759421358873 210556759421358873 endpoint_15_72_w0 endpoint_15_72_w2
private theorem endpoint_15_72_w4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 4 2 210556759421358873 = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_p6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 6 210556759421358873 = some 210556759421358873 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 4 2 210556759421358873 210556759421358873 210556759421358873 endpoint_15_72_p4 endpoint_15_72_w4
private theorem endpoint_15_72_w6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 6 2 210556759421358873 = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_p8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 8 210556759421358873 = some 210556759421358873 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 6 2 210556759421358873 210556759421358873 210556759421358873 endpoint_15_72_p6 endpoint_15_72_w6
private theorem endpoint_15_72_w8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 8 2 210556759421358873 = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_p10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 10 210556759421358873 = some 210556759421358873 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 8 2 210556759421358873 210556759421358873 210556759421358873 endpoint_15_72_p8 endpoint_15_72_w8
private theorem endpoint_15_72_w10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 10 2 210556759421358873 = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_p12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 12 210556759421358873 = some 210556759421358873 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 10 2 210556759421358873 210556759421358873 210556759421358873 endpoint_15_72_p10 endpoint_15_72_w10
private theorem endpoint_15_72_w12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 12 2 210556759421358873 = some 210556759421358873 := by decide +kernel
private theorem endpoint_15_72_p14 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 14 210556759421358873 = some 210556759421358873 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 12 2 210556759421358873 210556759421358873 210556759421358873 endpoint_15_72_p12 endpoint_15_72_w12
def endpoint_15_72 : CertifiedEndpoint :=
  ⟨⟨15, 72, 1667⟩, 210556759421358873, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_72_flag endpoint_15_72_sources 14 210556759421358873 210556759421358873 rfl endpoint_15_72_base endpoint_15_72_p14) (by decide)⟩
private def endpoint_15_73_flag : Flag := ⟨15, 73, 1590⟩
private def endpoint_15_73_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_15_73_base : receiptBase endpoint_15_73_flag endpoint_15_73_sources = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_w0 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 2 203710703935972396 = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_w2 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 2 2 203710703935972396 = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_p4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 4 203710703935972396 = some 203710703935972396 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 2 2 203710703935972396 203710703935972396 203710703935972396 endpoint_15_73_w0 endpoint_15_73_w2
private theorem endpoint_15_73_w4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 4 2 203710703935972396 = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_p6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 6 203710703935972396 = some 203710703935972396 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 4 2 203710703935972396 203710703935972396 203710703935972396 endpoint_15_73_p4 endpoint_15_73_w4
private theorem endpoint_15_73_w6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 6 2 203710703935972396 = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_p8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 8 203710703935972396 = some 203710703935972396 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 6 2 203710703935972396 203710703935972396 203710703935972396 endpoint_15_73_p6 endpoint_15_73_w6
private theorem endpoint_15_73_w8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 8 2 203710703935972396 = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_p10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 10 203710703935972396 = some 203710703935972396 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 8 2 203710703935972396 203710703935972396 203710703935972396 endpoint_15_73_p8 endpoint_15_73_w8
private theorem endpoint_15_73_w10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 10 2 203710703935972396 = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_p12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 12 203710703935972396 = some 203710703935972396 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 10 2 203710703935972396 203710703935972396 203710703935972396 endpoint_15_73_p10 endpoint_15_73_w10
private theorem endpoint_15_73_w12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 12 2 203710703935972396 = some 203710703935972396 := by decide +kernel
private theorem endpoint_15_73_p14 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 14 203710703935972396 = some 203710703935972396 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 12 2 203710703935972396 203710703935972396 203710703935972396 endpoint_15_73_p12 endpoint_15_73_w12
def endpoint_15_73 : CertifiedEndpoint :=
  ⟨⟨15, 73, 1590⟩, 203710703935972396, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_15_73_flag endpoint_15_73_sources 14 203710703935972396 203710703935972396 rfl endpoint_15_73_base endpoint_15_73_p14) (by decide)⟩
private def endpoint_15_74_flag : Flag := ⟨15, 74, 1510⟩
private def endpoint_15_74_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_15_74_base : receiptBase endpoint_15_74_flag endpoint_15_74_sources = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_w0 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 2 197222165055238556 = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_w2 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 2 2 197222165055238556 = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_p4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 4 197222165055238556 = some 197222165055238556 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 2 2 197222165055238556 197222165055238556 197222165055238556 endpoint_15_74_w0 endpoint_15_74_w2
private theorem endpoint_15_74_w4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 4 2 197222165055238556 = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_p6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 6 197222165055238556 = some 197222165055238556 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 4 2 197222165055238556 197222165055238556 197222165055238556 endpoint_15_74_p4 endpoint_15_74_w4
private theorem endpoint_15_74_w6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 6 2 197222165055238556 = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_p8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 8 197222165055238556 = some 197222165055238556 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 6 2 197222165055238556 197222165055238556 197222165055238556 endpoint_15_74_p6 endpoint_15_74_w6
private theorem endpoint_15_74_w8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 8 2 197222165055238556 = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_p10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 10 197222165055238556 = some 197222165055238556 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 8 2 197222165055238556 197222165055238556 197222165055238556 endpoint_15_74_p8 endpoint_15_74_w8
private theorem endpoint_15_74_w10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 10 2 197222165055238556 = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_p12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 12 197222165055238556 = some 197222165055238556 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 10 2 197222165055238556 197222165055238556 197222165055238556 endpoint_15_74_p10 endpoint_15_74_w10
private theorem endpoint_15_74_w12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 12 2 197222165055238556 = some 197222165055238556 := by decide +kernel
private theorem endpoint_15_74_p14 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 14 197222165055238556 = some 197222165055238556 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 12 2 197222165055238556 197222165055238556 197222165055238556 endpoint_15_74_p12 endpoint_15_74_w12
def endpoint_15_74 : CertifiedEndpoint :=
  ⟨⟨15, 74, 1510⟩, 197222165055238556, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_15_74_flag endpoint_15_74_sources 14 197222165055238556 197222165055238556 rfl endpoint_15_74_base endpoint_15_74_p14) (by decide)⟩
private def endpoint_15_75_flag : Flag := ⟨15, 75, 1428⟩
private def endpoint_15_75_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_75_base : receiptBase endpoint_15_75_flag endpoint_15_75_sources = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_w0 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 2 190559619863743771 = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_w2 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 2 2 190559619863743771 = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_p4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 4 190559619863743771 = some 190559619863743771 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 2 2 190559619863743771 190559619863743771 190559619863743771 endpoint_15_75_w0 endpoint_15_75_w2
private theorem endpoint_15_75_w4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 4 2 190559619863743771 = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_p6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 6 190559619863743771 = some 190559619863743771 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 4 2 190559619863743771 190559619863743771 190559619863743771 endpoint_15_75_p4 endpoint_15_75_w4
private theorem endpoint_15_75_w6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 6 2 190559619863743771 = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_p8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 8 190559619863743771 = some 190559619863743771 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 6 2 190559619863743771 190559619863743771 190559619863743771 endpoint_15_75_p6 endpoint_15_75_w6
private theorem endpoint_15_75_w8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 8 2 190559619863743771 = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_p10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 10 190559619863743771 = some 190559619863743771 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 8 2 190559619863743771 190559619863743771 190559619863743771 endpoint_15_75_p8 endpoint_15_75_w8
private theorem endpoint_15_75_w10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 10 2 190559619863743771 = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_p12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 12 190559619863743771 = some 190559619863743771 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 10 2 190559619863743771 190559619863743771 190559619863743771 endpoint_15_75_p10 endpoint_15_75_w10
private theorem endpoint_15_75_w12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 12 2 190559619863743771 = some 190559619863743771 := by decide +kernel
private theorem endpoint_15_75_p14 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 14 190559619863743771 = some 190559619863743771 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 12 2 190559619863743771 190559619863743771 190559619863743771 endpoint_15_75_p12 endpoint_15_75_w12
def endpoint_15_75 : CertifiedEndpoint :=
  ⟨⟨15, 75, 1428⟩, 190559619863743771, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_75_flag endpoint_15_75_sources 14 190559619863743771 190559619863743771 rfl endpoint_15_75_base endpoint_15_75_p14) (by decide)⟩
private def endpoint_15_76_flag : Flag := ⟨15, 76, 1343⟩
private def endpoint_15_76_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_76_base : receiptBase endpoint_15_76_flag endpoint_15_76_sources = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_w0 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 2 181433435748419202 = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_w2 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 2 2 181433435748419202 = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_p4 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 4 181433435748419202 = some 181433435748419202 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 2 2 181433435748419202 181433435748419202 181433435748419202 endpoint_15_76_w0 endpoint_15_76_w2
private theorem endpoint_15_76_w4 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 4 2 181433435748419202 = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_p6 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 6 181433435748419202 = some 181433435748419202 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 4 2 181433435748419202 181433435748419202 181433435748419202 endpoint_15_76_p4 endpoint_15_76_w4
private theorem endpoint_15_76_w6 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 6 2 181433435748419202 = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_p8 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 8 181433435748419202 = some 181433435748419202 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 6 2 181433435748419202 181433435748419202 181433435748419202 endpoint_15_76_p6 endpoint_15_76_w6
private theorem endpoint_15_76_w8 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 8 2 181433435748419202 = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_p10 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 10 181433435748419202 = some 181433435748419202 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 8 2 181433435748419202 181433435748419202 181433435748419202 endpoint_15_76_p8 endpoint_15_76_w8
private theorem endpoint_15_76_w10 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 10 2 181433435748419202 = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_p12 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 12 181433435748419202 = some 181433435748419202 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 10 2 181433435748419202 181433435748419202 181433435748419202 endpoint_15_76_p10 endpoint_15_76_w10
private theorem endpoint_15_76_w12 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 12 2 181433435748419202 = some 181433435748419202 := by decide +kernel
private theorem endpoint_15_76_p14 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 14 181433435748419202 = some 181433435748419202 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 12 2 181433435748419202 181433435748419202 181433435748419202 endpoint_15_76_p12 endpoint_15_76_w12
def endpoint_15_76 : CertifiedEndpoint :=
  ⟨⟨15, 76, 1343⟩, 181433435748419202, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_76_flag endpoint_15_76_sources 14 181433435748419202 181433435748419202 rfl endpoint_15_76_base endpoint_15_76_p14) (by decide)⟩
private def endpoint_15_77_flag : Flag := ⟨15, 77, 1255⟩
private def endpoint_15_77_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_77_base : receiptBase endpoint_15_77_flag endpoint_15_77_sources = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_w0 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 2 171636051592598060 = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_w2 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 2 2 171636051592598060 = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_p4 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 4 171636051592598060 = some 171636051592598060 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 2 2 171636051592598060 171636051592598060 171636051592598060 endpoint_15_77_w0 endpoint_15_77_w2
private theorem endpoint_15_77_w4 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 4 2 171636051592598060 = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_p6 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 6 171636051592598060 = some 171636051592598060 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 4 2 171636051592598060 171636051592598060 171636051592598060 endpoint_15_77_p4 endpoint_15_77_w4
private theorem endpoint_15_77_w6 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 6 2 171636051592598060 = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_p8 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 8 171636051592598060 = some 171636051592598060 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 6 2 171636051592598060 171636051592598060 171636051592598060 endpoint_15_77_p6 endpoint_15_77_w6
private theorem endpoint_15_77_w8 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 8 2 171636051592598060 = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_p10 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 10 171636051592598060 = some 171636051592598060 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 8 2 171636051592598060 171636051592598060 171636051592598060 endpoint_15_77_p8 endpoint_15_77_w8
private theorem endpoint_15_77_w10 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 10 2 171636051592598060 = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_p12 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 12 171636051592598060 = some 171636051592598060 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 10 2 171636051592598060 171636051592598060 171636051592598060 endpoint_15_77_p10 endpoint_15_77_w10
private theorem endpoint_15_77_w12 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 12 2 171636051592598060 = some 171636051592598060 := by decide +kernel
private theorem endpoint_15_77_p14 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 14 171636051592598060 = some 171636051592598060 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 12 2 171636051592598060 171636051592598060 171636051592598060 endpoint_15_77_p12 endpoint_15_77_w12
def endpoint_15_77 : CertifiedEndpoint :=
  ⟨⟨15, 77, 1255⟩, 171636051592598060, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_77_flag endpoint_15_77_sources 14 171636051592598060 171636051592598060 rfl endpoint_15_77_base endpoint_15_77_p14) (by decide)⟩
private def endpoint_15_78_flag : Flag := ⟨15, 78, 1166⟩
private def endpoint_15_78_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_78_base : receiptBase endpoint_15_78_flag endpoint_15_78_sources = some 161426446213626597 := by decide +kernel
private theorem endpoint_15_78_w0 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 0 2 161426446213626597 = some 165088074405220572 := by decide +kernel
private theorem endpoint_15_78_w2 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 2 2 165088074405220572 = some 165088074405220572 := by decide +kernel
private theorem endpoint_15_78_p4 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 0 4 161426446213626597 = some 165088074405220572 :=
  join_receipt_window endpoint_15_78_flag endpoint_15_78_sources 0 2 2 161426446213626597 165088074405220572 165088074405220572 endpoint_15_78_w0 endpoint_15_78_w2
private theorem endpoint_15_78_w4 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 4 2 165088074405220572 = some 165088074405220572 := by decide +kernel
private theorem endpoint_15_78_p6 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 0 6 161426446213626597 = some 165088074405220572 :=
  join_receipt_window endpoint_15_78_flag endpoint_15_78_sources 0 4 2 161426446213626597 165088074405220572 165088074405220572 endpoint_15_78_p4 endpoint_15_78_w4
private theorem endpoint_15_78_w6 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 6 2 165088074405220572 = some 165088074405220572 := by decide +kernel
private theorem endpoint_15_78_p8 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 0 8 161426446213626597 = some 165088074405220572 :=
  join_receipt_window endpoint_15_78_flag endpoint_15_78_sources 0 6 2 161426446213626597 165088074405220572 165088074405220572 endpoint_15_78_p6 endpoint_15_78_w6
private theorem endpoint_15_78_w8 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 8 2 165088074405220572 = some 165088074405220572 := by decide +kernel
private theorem endpoint_15_78_p10 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 0 10 161426446213626597 = some 165088074405220572 :=
  join_receipt_window endpoint_15_78_flag endpoint_15_78_sources 0 8 2 161426446213626597 165088074405220572 165088074405220572 endpoint_15_78_p8 endpoint_15_78_w8
private theorem endpoint_15_78_w10 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 10 2 165088074405220572 = some 165088074405220572 := by decide +kernel
private theorem endpoint_15_78_p12 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 0 12 161426446213626597 = some 165088074405220572 :=
  join_receipt_window endpoint_15_78_flag endpoint_15_78_sources 0 10 2 161426446213626597 165088074405220572 165088074405220572 endpoint_15_78_p10 endpoint_15_78_w10
private theorem endpoint_15_78_w12 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 12 2 165088074405220572 = some 165088074405220572 := by decide +kernel
private theorem endpoint_15_78_p14 : receiptWindow endpoint_15_78_flag endpoint_15_78_sources 0 14 161426446213626597 = some 165088074405220572 :=
  join_receipt_window endpoint_15_78_flag endpoint_15_78_sources 0 12 2 161426446213626597 165088074405220572 165088074405220572 endpoint_15_78_p12 endpoint_15_78_w12
def endpoint_15_78 : CertifiedEndpoint :=
  ⟨⟨15, 78, 1166⟩, 165088074405220572, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_78_flag endpoint_15_78_sources 14 161426446213626597 165088074405220572 rfl endpoint_15_78_base endpoint_15_78_p14) (by decide)⟩
private def endpoint_15_79_flag : Flag := ⟨15, 79, 1073⟩
private def endpoint_15_79_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_79_base : receiptBase endpoint_15_79_flag endpoint_15_79_sources = some 150385775240128379 := by decide +kernel
private theorem endpoint_15_79_w0 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 0 2 150385775240128379 = some 159873730373375685 := by decide +kernel
private theorem endpoint_15_79_w2 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 2 2 159873730373375685 = some 159873730373375685 := by decide +kernel
private theorem endpoint_15_79_p4 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 0 4 150385775240128379 = some 159873730373375685 :=
  join_receipt_window endpoint_15_79_flag endpoint_15_79_sources 0 2 2 150385775240128379 159873730373375685 159873730373375685 endpoint_15_79_w0 endpoint_15_79_w2
private theorem endpoint_15_79_w4 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 4 2 159873730373375685 = some 159873730373375685 := by decide +kernel
private theorem endpoint_15_79_p6 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 0 6 150385775240128379 = some 159873730373375685 :=
  join_receipt_window endpoint_15_79_flag endpoint_15_79_sources 0 4 2 150385775240128379 159873730373375685 159873730373375685 endpoint_15_79_p4 endpoint_15_79_w4
private theorem endpoint_15_79_w6 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 6 2 159873730373375685 = some 159873730373375685 := by decide +kernel
private theorem endpoint_15_79_p8 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 0 8 150385775240128379 = some 159873730373375685 :=
  join_receipt_window endpoint_15_79_flag endpoint_15_79_sources 0 6 2 150385775240128379 159873730373375685 159873730373375685 endpoint_15_79_p6 endpoint_15_79_w6
private theorem endpoint_15_79_w8 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 8 2 159873730373375685 = some 159873730373375685 := by decide +kernel
private theorem endpoint_15_79_p10 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 0 10 150385775240128379 = some 159873730373375685 :=
  join_receipt_window endpoint_15_79_flag endpoint_15_79_sources 0 8 2 150385775240128379 159873730373375685 159873730373375685 endpoint_15_79_p8 endpoint_15_79_w8
private theorem endpoint_15_79_w10 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 10 2 159873730373375685 = some 159873730373375685 := by decide +kernel
private theorem endpoint_15_79_p12 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 0 12 150385775240128379 = some 159873730373375685 :=
  join_receipt_window endpoint_15_79_flag endpoint_15_79_sources 0 10 2 150385775240128379 159873730373375685 159873730373375685 endpoint_15_79_p10 endpoint_15_79_w10
private theorem endpoint_15_79_w12 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 12 2 159873730373375685 = some 159873730373375685 := by decide +kernel
private theorem endpoint_15_79_p14 : receiptWindow endpoint_15_79_flag endpoint_15_79_sources 0 14 150385775240128379 = some 159873730373375685 :=
  join_receipt_window endpoint_15_79_flag endpoint_15_79_sources 0 12 2 150385775240128379 159873730373375685 159873730373375685 endpoint_15_79_p12 endpoint_15_79_w12
def endpoint_15_79 : CertifiedEndpoint :=
  ⟨⟨15, 79, 1073⟩, 159873730373375685, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_79_flag endpoint_15_79_sources 14 150385775240128379 159873730373375685 rfl endpoint_15_79_base endpoint_15_79_p14) (by decide)⟩
def endpoint_15_80 : CertifiedEndpoint :=
  ⟨⟨15, 80, 978⟩, 251905530660380018, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_81 : CertifiedEndpoint :=
  ⟨⟨15, 81, 881⟩, 228745601904921566, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_82 : CertifiedEndpoint :=
  ⟨⟨15, 82, 781⟩, 204023855204220041, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_83 : CertifiedEndpoint :=
  ⟨⟨15, 83, 678⟩, 177706582816201793, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_84 : CertifiedEndpoint :=
  ⟨⟨15, 84, 573⟩, 150044728786025313, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_85 : CertifiedEndpoint :=
  ⟨⟨15, 85, 465⟩, 120727424193734510, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_86 : CertifiedEndpoint :=
  ⟨⟨15, 86, 355⟩, 90013103693837575, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_87 : CertifiedEndpoint :=
  ⟨⟨15, 87, 242⟩, 57583407757028717, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_88 : CertifiedEndpoint :=
  ⟨⟨15, 88, 127⟩, 23704261647165827, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_16 : CertifiedEndpoint :=
  ⟨⟨16, 16, 3704⟩, 130737131065703064, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_17 : CertifiedEndpoint :=
  ⟨⟨16, 17, 3681⟩, 134736987577708366, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_18 : CertifiedEndpoint :=
  ⟨⟨16, 18, 3658⟩, 138676386613674234, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_19 : CertifiedEndpoint :=
  ⟨⟨16, 19, 3634⟩, 152236372380791023, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_20 : CertifiedEndpoint :=
  ⟨⟨16, 20, 3611⟩, 165646253945015601, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_21 : CertifiedEndpoint :=
  ⟨⟨16, 21, 3587⟩, 178817947838734496, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_22 : CertifiedEndpoint :=
  ⟨⟨16, 22, 3562⟩, 191739445034935402, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_23 : CertifiedEndpoint :=
  ⟨⟨16, 23, 3538⟩, 204514841037248199, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_24 : CertifiedEndpoint :=
  ⟨⟨16, 24, 3512⟩, 216969979049709608, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_25 : CertifiedEndpoint :=
  ⟨⟨16, 25, 3487⟩, 229279015868282908, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_26 : CertifiedEndpoint :=
  ⟨⟨16, 26, 3461⟩, 241313837935313607, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_27 : CertifiedEndpoint :=
  ⟨⟨16, 27, 3435⟩, 253136500525126900, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_16_28_flag : Flag := ⟨16, 28, 3408⟩
private def endpoint_16_28_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_28_base : receiptBase endpoint_16_28_flag endpoint_16_28_sources = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_w0 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 2 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_w2 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 2 2 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_p4 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 4 181424009767342806 = some 181424009767342806 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 2 2 181424009767342806 181424009767342806 181424009767342806 endpoint_16_28_w0 endpoint_16_28_w2
private theorem endpoint_16_28_w4 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 4 2 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_p6 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 6 181424009767342806 = some 181424009767342806 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 4 2 181424009767342806 181424009767342806 181424009767342806 endpoint_16_28_p4 endpoint_16_28_w4
private theorem endpoint_16_28_w6 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 6 2 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_p8 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 8 181424009767342806 = some 181424009767342806 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 6 2 181424009767342806 181424009767342806 181424009767342806 endpoint_16_28_p6 endpoint_16_28_w6
private theorem endpoint_16_28_w8 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 8 2 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_p10 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 10 181424009767342806 = some 181424009767342806 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 8 2 181424009767342806 181424009767342806 181424009767342806 endpoint_16_28_p8 endpoint_16_28_w8
private theorem endpoint_16_28_w10 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 10 2 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_p12 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 12 181424009767342806 = some 181424009767342806 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 10 2 181424009767342806 181424009767342806 181424009767342806 endpoint_16_28_p10 endpoint_16_28_w10
private theorem endpoint_16_28_w12 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 12 2 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_p14 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 14 181424009767342806 = some 181424009767342806 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 12 2 181424009767342806 181424009767342806 181424009767342806 endpoint_16_28_p12 endpoint_16_28_w12
private theorem endpoint_16_28_w14 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 14 1 181424009767342806 = some 181424009767342806 := by decide +kernel
private theorem endpoint_16_28_p15 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 15 181424009767342806 = some 181424009767342806 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 14 1 181424009767342806 181424009767342806 181424009767342806 endpoint_16_28_p14 endpoint_16_28_w14
def endpoint_16_28 : CertifiedEndpoint :=
  ⟨⟨16, 28, 3408⟩, 181424009767342806, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_28_flag endpoint_16_28_sources 15 181424009767342806 181424009767342806 rfl endpoint_16_28_base endpoint_16_28_p15) (by decide)⟩
private def endpoint_16_29_flag : Flag := ⟨16, 29, 3381⟩
private def endpoint_16_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_29_base : receiptBase endpoint_16_29_flag endpoint_16_29_sources = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_w0 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 2 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_w2 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 2 2 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_p4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 4 185279266257896176 = some 185279266257896176 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 2 2 185279266257896176 185279266257896176 185279266257896176 endpoint_16_29_w0 endpoint_16_29_w2
private theorem endpoint_16_29_w4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 4 2 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_p6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 6 185279266257896176 = some 185279266257896176 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 4 2 185279266257896176 185279266257896176 185279266257896176 endpoint_16_29_p4 endpoint_16_29_w4
private theorem endpoint_16_29_w6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 6 2 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_p8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 8 185279266257896176 = some 185279266257896176 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 6 2 185279266257896176 185279266257896176 185279266257896176 endpoint_16_29_p6 endpoint_16_29_w6
private theorem endpoint_16_29_w8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 8 2 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_p10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 10 185279266257896176 = some 185279266257896176 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 8 2 185279266257896176 185279266257896176 185279266257896176 endpoint_16_29_p8 endpoint_16_29_w8
private theorem endpoint_16_29_w10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 10 2 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_p12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 12 185279266257896176 = some 185279266257896176 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 10 2 185279266257896176 185279266257896176 185279266257896176 endpoint_16_29_p10 endpoint_16_29_w10
private theorem endpoint_16_29_w12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 12 2 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_p14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 14 185279266257896176 = some 185279266257896176 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 12 2 185279266257896176 185279266257896176 185279266257896176 endpoint_16_29_p12 endpoint_16_29_w12
private theorem endpoint_16_29_w14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 14 1 185279266257896176 = some 185279266257896176 := by decide +kernel
private theorem endpoint_16_29_p15 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 15 185279266257896176 = some 185279266257896176 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 14 1 185279266257896176 185279266257896176 185279266257896176 endpoint_16_29_p14 endpoint_16_29_w14
def endpoint_16_29 : CertifiedEndpoint :=
  ⟨⟨16, 29, 3381⟩, 185279266257896176, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_29_flag endpoint_16_29_sources 15 185279266257896176 185279266257896176 rfl endpoint_16_29_base endpoint_16_29_p15) (by decide)⟩
private def endpoint_16_30_flag : Flag := ⟨16, 30, 3354⟩
private def endpoint_16_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_30_base : receiptBase endpoint_16_30_flag endpoint_16_30_sources = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_w0 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 2 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_w2 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 2 2 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_p4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 4 189050669309844292 = some 189050669309844292 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 2 2 189050669309844292 189050669309844292 189050669309844292 endpoint_16_30_w0 endpoint_16_30_w2
private theorem endpoint_16_30_w4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 4 2 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_p6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 6 189050669309844292 = some 189050669309844292 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 4 2 189050669309844292 189050669309844292 189050669309844292 endpoint_16_30_p4 endpoint_16_30_w4
private theorem endpoint_16_30_w6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 6 2 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_p8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 8 189050669309844292 = some 189050669309844292 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 6 2 189050669309844292 189050669309844292 189050669309844292 endpoint_16_30_p6 endpoint_16_30_w6
private theorem endpoint_16_30_w8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 8 2 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_p10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 10 189050669309844292 = some 189050669309844292 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 8 2 189050669309844292 189050669309844292 189050669309844292 endpoint_16_30_p8 endpoint_16_30_w8
private theorem endpoint_16_30_w10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 10 2 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_p12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 12 189050669309844292 = some 189050669309844292 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 10 2 189050669309844292 189050669309844292 189050669309844292 endpoint_16_30_p10 endpoint_16_30_w10
private theorem endpoint_16_30_w12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 12 2 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_p14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 14 189050669309844292 = some 189050669309844292 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 12 2 189050669309844292 189050669309844292 189050669309844292 endpoint_16_30_p12 endpoint_16_30_w12
private theorem endpoint_16_30_w14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 14 1 189050669309844292 = some 189050669309844292 := by decide +kernel
private theorem endpoint_16_30_p15 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 15 189050669309844292 = some 189050669309844292 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 14 1 189050669309844292 189050669309844292 189050669309844292 endpoint_16_30_p14 endpoint_16_30_w14
def endpoint_16_30 : CertifiedEndpoint :=
  ⟨⟨16, 30, 3354⟩, 189050669309844292, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_30_flag endpoint_16_30_sources 15 189050669309844292 189050669309844292 rfl endpoint_16_30_base endpoint_16_30_p15) (by decide)⟩
private def endpoint_16_31_flag : Flag := ⟨16, 31, 3326⟩
private def endpoint_16_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_31_base : receiptBase endpoint_16_31_flag endpoint_16_31_sources = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_w0 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 2 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_w2 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 2 2 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_p4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 4 192681119857569330 = some 192681119857569330 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 2 2 192681119857569330 192681119857569330 192681119857569330 endpoint_16_31_w0 endpoint_16_31_w2
private theorem endpoint_16_31_w4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 4 2 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_p6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 6 192681119857569330 = some 192681119857569330 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 4 2 192681119857569330 192681119857569330 192681119857569330 endpoint_16_31_p4 endpoint_16_31_w4
private theorem endpoint_16_31_w6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 6 2 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_p8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 8 192681119857569330 = some 192681119857569330 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 6 2 192681119857569330 192681119857569330 192681119857569330 endpoint_16_31_p6 endpoint_16_31_w6
private theorem endpoint_16_31_w8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 8 2 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_p10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 10 192681119857569330 = some 192681119857569330 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 8 2 192681119857569330 192681119857569330 192681119857569330 endpoint_16_31_p8 endpoint_16_31_w8
private theorem endpoint_16_31_w10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 10 2 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_p12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 12 192681119857569330 = some 192681119857569330 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 10 2 192681119857569330 192681119857569330 192681119857569330 endpoint_16_31_p10 endpoint_16_31_w10
private theorem endpoint_16_31_w12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 12 2 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_p14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 14 192681119857569330 = some 192681119857569330 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 12 2 192681119857569330 192681119857569330 192681119857569330 endpoint_16_31_p12 endpoint_16_31_w12
private theorem endpoint_16_31_w14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 14 1 192681119857569330 = some 192681119857569330 := by decide +kernel
private theorem endpoint_16_31_p15 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 15 192681119857569330 = some 192681119857569330 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 14 1 192681119857569330 192681119857569330 192681119857569330 endpoint_16_31_p14 endpoint_16_31_w14
def endpoint_16_31 : CertifiedEndpoint :=
  ⟨⟨16, 31, 3326⟩, 192681119857569330, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_31_flag endpoint_16_31_sources 15 192681119857569330 192681119857569330 rfl endpoint_16_31_base endpoint_16_31_p15) (by decide)⟩
private def endpoint_16_32_flag : Flag := ⟨16, 32, 3297⟩
private def endpoint_16_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_32_base : receiptBase endpoint_16_32_flag endpoint_16_32_sources = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_w0 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 2 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_w2 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 2 2 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_p4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 4 196166045365670620 = some 196166045365670620 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 2 2 196166045365670620 196166045365670620 196166045365670620 endpoint_16_32_w0 endpoint_16_32_w2
private theorem endpoint_16_32_w4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 4 2 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_p6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 6 196166045365670620 = some 196166045365670620 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 4 2 196166045365670620 196166045365670620 196166045365670620 endpoint_16_32_p4 endpoint_16_32_w4
private theorem endpoint_16_32_w6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 6 2 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_p8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 8 196166045365670620 = some 196166045365670620 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 6 2 196166045365670620 196166045365670620 196166045365670620 endpoint_16_32_p6 endpoint_16_32_w6
private theorem endpoint_16_32_w8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 8 2 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_p10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 10 196166045365670620 = some 196166045365670620 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 8 2 196166045365670620 196166045365670620 196166045365670620 endpoint_16_32_p8 endpoint_16_32_w8
private theorem endpoint_16_32_w10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 10 2 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_p12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 12 196166045365670620 = some 196166045365670620 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 10 2 196166045365670620 196166045365670620 196166045365670620 endpoint_16_32_p10 endpoint_16_32_w10
private theorem endpoint_16_32_w12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 12 2 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_p14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 14 196166045365670620 = some 196166045365670620 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 12 2 196166045365670620 196166045365670620 196166045365670620 endpoint_16_32_p12 endpoint_16_32_w12
private theorem endpoint_16_32_w14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 14 1 196166045365670620 = some 196166045365670620 := by decide +kernel
private theorem endpoint_16_32_p15 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 15 196166045365670620 = some 196166045365670620 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 14 1 196166045365670620 196166045365670620 196166045365670620 endpoint_16_32_p14 endpoint_16_32_w14
def endpoint_16_32 : CertifiedEndpoint :=
  ⟨⟨16, 32, 3297⟩, 196166045365670620, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_32_flag endpoint_16_32_sources 15 196166045365670620 196166045365670620 rfl endpoint_16_32_base endpoint_16_32_p15) (by decide)⟩
private def endpoint_16_33_flag : Flag := ⟨16, 33, 3268⟩
private def endpoint_16_33_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_16_33_base : receiptBase endpoint_16_33_flag endpoint_16_33_sources = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_w0 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 2 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_w2 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 2 2 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_p4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 4 201375778574995283 = some 201375778574995283 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 2 2 201375778574995283 201375778574995283 201375778574995283 endpoint_16_33_w0 endpoint_16_33_w2
private theorem endpoint_16_33_w4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 4 2 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_p6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 6 201375778574995283 = some 201375778574995283 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 4 2 201375778574995283 201375778574995283 201375778574995283 endpoint_16_33_p4 endpoint_16_33_w4
private theorem endpoint_16_33_w6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 6 2 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_p8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 8 201375778574995283 = some 201375778574995283 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 6 2 201375778574995283 201375778574995283 201375778574995283 endpoint_16_33_p6 endpoint_16_33_w6
private theorem endpoint_16_33_w8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 8 2 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_p10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 10 201375778574995283 = some 201375778574995283 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 8 2 201375778574995283 201375778574995283 201375778574995283 endpoint_16_33_p8 endpoint_16_33_w8
private theorem endpoint_16_33_w10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 10 2 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_p12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 12 201375778574995283 = some 201375778574995283 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 10 2 201375778574995283 201375778574995283 201375778574995283 endpoint_16_33_p10 endpoint_16_33_w10
private theorem endpoint_16_33_w12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 12 2 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_p14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 14 201375778574995283 = some 201375778574995283 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 12 2 201375778574995283 201375778574995283 201375778574995283 endpoint_16_33_p12 endpoint_16_33_w12
private theorem endpoint_16_33_w14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 14 1 201375778574995283 = some 201375778574995283 := by decide +kernel
private theorem endpoint_16_33_p15 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 15 201375778574995283 = some 201375778574995283 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 14 1 201375778574995283 201375778574995283 201375778574995283 endpoint_16_33_p14 endpoint_16_33_w14
def endpoint_16_33 : CertifiedEndpoint :=
  ⟨⟨16, 33, 3268⟩, 201375778574995283, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_16_33_flag endpoint_16_33_sources 15 201375778574995283 201375778574995283 rfl endpoint_16_33_base endpoint_16_33_p15) (by decide)⟩
private def endpoint_16_34_flag : Flag := ⟨16, 34, 3239⟩
private def endpoint_16_34_sources : Sources := ⟨contact25, contact03, contact25⟩
private theorem endpoint_16_34_base : receiptBase endpoint_16_34_flag endpoint_16_34_sources = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_w0 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 2 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_w2 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 2 2 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_p4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 4 204885842031129635 = some 204885842031129635 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 2 2 204885842031129635 204885842031129635 204885842031129635 endpoint_16_34_w0 endpoint_16_34_w2
private theorem endpoint_16_34_w4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 4 2 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_p6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 6 204885842031129635 = some 204885842031129635 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 4 2 204885842031129635 204885842031129635 204885842031129635 endpoint_16_34_p4 endpoint_16_34_w4
private theorem endpoint_16_34_w6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 6 2 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_p8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 8 204885842031129635 = some 204885842031129635 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 6 2 204885842031129635 204885842031129635 204885842031129635 endpoint_16_34_p6 endpoint_16_34_w6
private theorem endpoint_16_34_w8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 8 2 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_p10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 10 204885842031129635 = some 204885842031129635 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 8 2 204885842031129635 204885842031129635 204885842031129635 endpoint_16_34_p8 endpoint_16_34_w8
private theorem endpoint_16_34_w10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 10 2 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_p12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 12 204885842031129635 = some 204885842031129635 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 10 2 204885842031129635 204885842031129635 204885842031129635 endpoint_16_34_p10 endpoint_16_34_w10
private theorem endpoint_16_34_w12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 12 2 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_p14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 14 204885842031129635 = some 204885842031129635 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 12 2 204885842031129635 204885842031129635 204885842031129635 endpoint_16_34_p12 endpoint_16_34_w12
private theorem endpoint_16_34_w14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 14 1 204885842031129635 = some 204885842031129635 := by decide +kernel
private theorem endpoint_16_34_p15 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 15 204885842031129635 = some 204885842031129635 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 14 1 204885842031129635 204885842031129635 204885842031129635 endpoint_16_34_p14 endpoint_16_34_w14
def endpoint_16_34 : CertifiedEndpoint :=
  ⟨⟨16, 34, 3239⟩, 204885842031129635, .terminal ⟨contact25, contact03, contact25⟩ (finish_receipt_window endpoint_16_34_flag endpoint_16_34_sources 15 204885842031129635 204885842031129635 rfl endpoint_16_34_base endpoint_16_34_p15) (by decide)⟩
private def endpoint_16_35_flag : Flag := ⟨16, 35, 3209⟩
private def endpoint_16_35_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_35_base : receiptBase endpoint_16_35_flag endpoint_16_35_sources = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_w0 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 2 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_w2 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 2 2 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_p4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 4 209622117000765615 = some 209622117000765615 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 2 2 209622117000765615 209622117000765615 209622117000765615 endpoint_16_35_w0 endpoint_16_35_w2
private theorem endpoint_16_35_w4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 4 2 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_p6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 6 209622117000765615 = some 209622117000765615 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 4 2 209622117000765615 209622117000765615 209622117000765615 endpoint_16_35_p4 endpoint_16_35_w4
private theorem endpoint_16_35_w6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 6 2 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_p8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 8 209622117000765615 = some 209622117000765615 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 6 2 209622117000765615 209622117000765615 209622117000765615 endpoint_16_35_p6 endpoint_16_35_w6
private theorem endpoint_16_35_w8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 8 2 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_p10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 10 209622117000765615 = some 209622117000765615 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 8 2 209622117000765615 209622117000765615 209622117000765615 endpoint_16_35_p8 endpoint_16_35_w8
private theorem endpoint_16_35_w10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 10 2 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_p12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 12 209622117000765615 = some 209622117000765615 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 10 2 209622117000765615 209622117000765615 209622117000765615 endpoint_16_35_p10 endpoint_16_35_w10
private theorem endpoint_16_35_w12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 12 2 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_p14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 14 209622117000765615 = some 209622117000765615 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 12 2 209622117000765615 209622117000765615 209622117000765615 endpoint_16_35_p12 endpoint_16_35_w12
private theorem endpoint_16_35_w14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 14 1 209622117000765615 = some 209622117000765615 := by decide +kernel
private theorem endpoint_16_35_p15 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 15 209622117000765615 = some 209622117000765615 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 14 1 209622117000765615 209622117000765615 209622117000765615 endpoint_16_35_p14 endpoint_16_35_w14
def endpoint_16_35 : CertifiedEndpoint :=
  ⟨⟨16, 35, 3209⟩, 209622117000765615, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_35_flag endpoint_16_35_sources 15 209622117000765615 209622117000765615 rfl endpoint_16_35_base endpoint_16_35_p15) (by decide)⟩
private def endpoint_16_36_flag : Flag := ⟨16, 36, 3178⟩
private def endpoint_16_36_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_36_base : receiptBase endpoint_16_36_flag endpoint_16_36_sources = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_w0 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 2 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_w2 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 2 2 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_p4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 4 212510882554523092 = some 212510882554523092 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 2 2 212510882554523092 212510882554523092 212510882554523092 endpoint_16_36_w0 endpoint_16_36_w2
private theorem endpoint_16_36_w4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 4 2 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_p6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 6 212510882554523092 = some 212510882554523092 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 4 2 212510882554523092 212510882554523092 212510882554523092 endpoint_16_36_p4 endpoint_16_36_w4
private theorem endpoint_16_36_w6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 6 2 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_p8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 8 212510882554523092 = some 212510882554523092 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 6 2 212510882554523092 212510882554523092 212510882554523092 endpoint_16_36_p6 endpoint_16_36_w6
private theorem endpoint_16_36_w8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 8 2 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_p10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 10 212510882554523092 = some 212510882554523092 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 8 2 212510882554523092 212510882554523092 212510882554523092 endpoint_16_36_p8 endpoint_16_36_w8
private theorem endpoint_16_36_w10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 10 2 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_p12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 12 212510882554523092 = some 212510882554523092 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 10 2 212510882554523092 212510882554523092 212510882554523092 endpoint_16_36_p10 endpoint_16_36_w10
private theorem endpoint_16_36_w12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 12 2 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_p14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 14 212510882554523092 = some 212510882554523092 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 12 2 212510882554523092 212510882554523092 212510882554523092 endpoint_16_36_p12 endpoint_16_36_w12
private theorem endpoint_16_36_w14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 14 1 212510882554523092 = some 212510882554523092 := by decide +kernel
private theorem endpoint_16_36_p15 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 15 212510882554523092 = some 212510882554523092 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 14 1 212510882554523092 212510882554523092 212510882554523092 endpoint_16_36_p14 endpoint_16_36_w14
def endpoint_16_36 : CertifiedEndpoint :=
  ⟨⟨16, 36, 3178⟩, 212510882554523092, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_36_flag endpoint_16_36_sources 15 212510882554523092 212510882554523092 rfl endpoint_16_36_base endpoint_16_36_p15) (by decide)⟩
private def endpoint_16_37_flag : Flag := ⟨16, 37, 3147⟩
private def endpoint_16_37_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_37_base : receiptBase endpoint_16_37_flag endpoint_16_37_sources = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_w0 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 2 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_w2 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 2 2 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_p4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 4 215304546876718851 = some 215304546876718851 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 2 2 215304546876718851 215304546876718851 215304546876718851 endpoint_16_37_w0 endpoint_16_37_w2
private theorem endpoint_16_37_w4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 4 2 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_p6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 6 215304546876718851 = some 215304546876718851 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 4 2 215304546876718851 215304546876718851 215304546876718851 endpoint_16_37_p4 endpoint_16_37_w4
private theorem endpoint_16_37_w6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 6 2 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_p8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 8 215304546876718851 = some 215304546876718851 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 6 2 215304546876718851 215304546876718851 215304546876718851 endpoint_16_37_p6 endpoint_16_37_w6
private theorem endpoint_16_37_w8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 8 2 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_p10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 10 215304546876718851 = some 215304546876718851 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 8 2 215304546876718851 215304546876718851 215304546876718851 endpoint_16_37_p8 endpoint_16_37_w8
private theorem endpoint_16_37_w10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 10 2 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_p12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 12 215304546876718851 = some 215304546876718851 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 10 2 215304546876718851 215304546876718851 215304546876718851 endpoint_16_37_p10 endpoint_16_37_w10
private theorem endpoint_16_37_w12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 12 2 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_p14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 14 215304546876718851 = some 215304546876718851 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 12 2 215304546876718851 215304546876718851 215304546876718851 endpoint_16_37_p12 endpoint_16_37_w12
private theorem endpoint_16_37_w14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 14 1 215304546876718851 = some 215304546876718851 := by decide +kernel
private theorem endpoint_16_37_p15 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 15 215304546876718851 = some 215304546876718851 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 14 1 215304546876718851 215304546876718851 215304546876718851 endpoint_16_37_p14 endpoint_16_37_w14
def endpoint_16_37 : CertifiedEndpoint :=
  ⟨⟨16, 37, 3147⟩, 215304546876718851, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_37_flag endpoint_16_37_sources 15 215304546876718851 215304546876718851 rfl endpoint_16_37_base endpoint_16_37_p15) (by decide)⟩
private def endpoint_16_38_flag : Flag := ⟨16, 38, 3115⟩
private def endpoint_16_38_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_38_base : receiptBase endpoint_16_38_flag endpoint_16_38_sources = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_w0 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 2 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_w2 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 2 2 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_p4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 4 217934084195476316 = some 217934084195476316 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 2 2 217934084195476316 217934084195476316 217934084195476316 endpoint_16_38_w0 endpoint_16_38_w2
private theorem endpoint_16_38_w4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 4 2 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_p6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 6 217934084195476316 = some 217934084195476316 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 4 2 217934084195476316 217934084195476316 217934084195476316 endpoint_16_38_p4 endpoint_16_38_w4
private theorem endpoint_16_38_w6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 6 2 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_p8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 8 217934084195476316 = some 217934084195476316 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 6 2 217934084195476316 217934084195476316 217934084195476316 endpoint_16_38_p6 endpoint_16_38_w6
private theorem endpoint_16_38_w8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 8 2 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_p10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 10 217934084195476316 = some 217934084195476316 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 8 2 217934084195476316 217934084195476316 217934084195476316 endpoint_16_38_p8 endpoint_16_38_w8
private theorem endpoint_16_38_w10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 10 2 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_p12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 12 217934084195476316 = some 217934084195476316 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 10 2 217934084195476316 217934084195476316 217934084195476316 endpoint_16_38_p10 endpoint_16_38_w10
private theorem endpoint_16_38_w12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 12 2 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_p14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 14 217934084195476316 = some 217934084195476316 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 12 2 217934084195476316 217934084195476316 217934084195476316 endpoint_16_38_p12 endpoint_16_38_w12
private theorem endpoint_16_38_w14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 14 1 217934084195476316 = some 217934084195476316 := by decide +kernel
private theorem endpoint_16_38_p15 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 15 217934084195476316 = some 217934084195476316 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 14 1 217934084195476316 217934084195476316 217934084195476316 endpoint_16_38_p14 endpoint_16_38_w14
def endpoint_16_38 : CertifiedEndpoint :=
  ⟨⟨16, 38, 3115⟩, 217934084195476316, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_38_flag endpoint_16_38_sources 15 217934084195476316 217934084195476316 rfl endpoint_16_38_base endpoint_16_38_p15) (by decide)⟩
private def endpoint_16_39_flag : Flag := ⟨16, 39, 3082⟩
private def endpoint_16_39_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_39_base : receiptBase endpoint_16_39_flag endpoint_16_39_sources = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_w0 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 2 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_w2 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 2 2 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_p4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 4 220922616533380149 = some 220922616533380149 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 2 2 220922616533380149 220922616533380149 220922616533380149 endpoint_16_39_w0 endpoint_16_39_w2
private theorem endpoint_16_39_w4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 4 2 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_p6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 6 220922616533380149 = some 220922616533380149 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 4 2 220922616533380149 220922616533380149 220922616533380149 endpoint_16_39_p4 endpoint_16_39_w4
private theorem endpoint_16_39_w6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 6 2 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_p8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 8 220922616533380149 = some 220922616533380149 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 6 2 220922616533380149 220922616533380149 220922616533380149 endpoint_16_39_p6 endpoint_16_39_w6
private theorem endpoint_16_39_w8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 8 2 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_p10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 10 220922616533380149 = some 220922616533380149 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 8 2 220922616533380149 220922616533380149 220922616533380149 endpoint_16_39_p8 endpoint_16_39_w8
private theorem endpoint_16_39_w10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 10 2 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_p12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 12 220922616533380149 = some 220922616533380149 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 10 2 220922616533380149 220922616533380149 220922616533380149 endpoint_16_39_p10 endpoint_16_39_w10
private theorem endpoint_16_39_w12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 12 2 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_p14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 14 220922616533380149 = some 220922616533380149 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 12 2 220922616533380149 220922616533380149 220922616533380149 endpoint_16_39_p12 endpoint_16_39_w12
private theorem endpoint_16_39_w14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 14 1 220922616533380149 = some 220922616533380149 := by decide +kernel
private theorem endpoint_16_39_p15 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 15 220922616533380149 = some 220922616533380149 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 14 1 220922616533380149 220922616533380149 220922616533380149 endpoint_16_39_p14 endpoint_16_39_w14
def endpoint_16_39 : CertifiedEndpoint :=
  ⟨⟨16, 39, 3082⟩, 220922616533380149, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_39_flag endpoint_16_39_sources 15 220922616533380149 220922616533380149 rfl endpoint_16_39_base endpoint_16_39_p15) (by decide)⟩
private def endpoint_16_40_flag : Flag := ⟨16, 40, 3048⟩
private def endpoint_16_40_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_40_base : receiptBase endpoint_16_40_flag endpoint_16_40_sources = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_w0 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 2 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_w2 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 2 2 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_p4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 4 223226216322230686 = some 223226216322230686 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 2 2 223226216322230686 223226216322230686 223226216322230686 endpoint_16_40_w0 endpoint_16_40_w2
private theorem endpoint_16_40_w4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 4 2 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_p6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 6 223226216322230686 = some 223226216322230686 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 4 2 223226216322230686 223226216322230686 223226216322230686 endpoint_16_40_p4 endpoint_16_40_w4
private theorem endpoint_16_40_w6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 6 2 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_p8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 8 223226216322230686 = some 223226216322230686 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 6 2 223226216322230686 223226216322230686 223226216322230686 endpoint_16_40_p6 endpoint_16_40_w6
private theorem endpoint_16_40_w8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 8 2 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_p10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 10 223226216322230686 = some 223226216322230686 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 8 2 223226216322230686 223226216322230686 223226216322230686 endpoint_16_40_p8 endpoint_16_40_w8
private theorem endpoint_16_40_w10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 10 2 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_p12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 12 223226216322230686 = some 223226216322230686 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 10 2 223226216322230686 223226216322230686 223226216322230686 endpoint_16_40_p10 endpoint_16_40_w10
private theorem endpoint_16_40_w12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 12 2 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_p14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 14 223226216322230686 = some 223226216322230686 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 12 2 223226216322230686 223226216322230686 223226216322230686 endpoint_16_40_p12 endpoint_16_40_w12
private theorem endpoint_16_40_w14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 14 1 223226216322230686 = some 223226216322230686 := by decide +kernel
private theorem endpoint_16_40_p15 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 15 223226216322230686 = some 223226216322230686 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 14 1 223226216322230686 223226216322230686 223226216322230686 endpoint_16_40_p14 endpoint_16_40_w14
def endpoint_16_40 : CertifiedEndpoint :=
  ⟨⟨16, 40, 3048⟩, 223226216322230686, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_40_flag endpoint_16_40_sources 15 223226216322230686 223226216322230686 rfl endpoint_16_40_base endpoint_16_40_p15) (by decide)⟩
private def endpoint_16_41_flag : Flag := ⟨16, 41, 3014⟩
private def endpoint_16_41_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_41_base : receiptBase endpoint_16_41_flag endpoint_16_41_sources = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_w0 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 2 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_w2 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 2 2 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_p4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 4 225425036569067798 = some 225425036569067798 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 2 2 225425036569067798 225425036569067798 225425036569067798 endpoint_16_41_w0 endpoint_16_41_w2
private theorem endpoint_16_41_w4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 4 2 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_p6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 6 225425036569067798 = some 225425036569067798 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 4 2 225425036569067798 225425036569067798 225425036569067798 endpoint_16_41_p4 endpoint_16_41_w4
private theorem endpoint_16_41_w6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 6 2 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_p8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 8 225425036569067798 = some 225425036569067798 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 6 2 225425036569067798 225425036569067798 225425036569067798 endpoint_16_41_p6 endpoint_16_41_w6
private theorem endpoint_16_41_w8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 8 2 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_p10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 10 225425036569067798 = some 225425036569067798 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 8 2 225425036569067798 225425036569067798 225425036569067798 endpoint_16_41_p8 endpoint_16_41_w8
private theorem endpoint_16_41_w10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 10 2 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_p12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 12 225425036569067798 = some 225425036569067798 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 10 2 225425036569067798 225425036569067798 225425036569067798 endpoint_16_41_p10 endpoint_16_41_w10
private theorem endpoint_16_41_w12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 12 2 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_p14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 14 225425036569067798 = some 225425036569067798 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 12 2 225425036569067798 225425036569067798 225425036569067798 endpoint_16_41_p12 endpoint_16_41_w12
private theorem endpoint_16_41_w14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 14 1 225425036569067798 = some 225425036569067798 := by decide +kernel
private theorem endpoint_16_41_p15 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 15 225425036569067798 = some 225425036569067798 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 14 1 225425036569067798 225425036569067798 225425036569067798 endpoint_16_41_p14 endpoint_16_41_w14
def endpoint_16_41 : CertifiedEndpoint :=
  ⟨⟨16, 41, 3014⟩, 225425036569067798, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_41_flag endpoint_16_41_sources 15 225425036569067798 225425036569067798 rfl endpoint_16_41_base endpoint_16_41_p15) (by decide)⟩
private def endpoint_16_42_flag : Flag := ⟨16, 42, 2980⟩
private def endpoint_16_42_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_42_base : receiptBase endpoint_16_42_flag endpoint_16_42_sources = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_w0 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 2 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_w2 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 2 2 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_p4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 4 227519077273891484 = some 227519077273891484 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 2 2 227519077273891484 227519077273891484 227519077273891484 endpoint_16_42_w0 endpoint_16_42_w2
private theorem endpoint_16_42_w4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 4 2 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_p6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 6 227519077273891484 = some 227519077273891484 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 4 2 227519077273891484 227519077273891484 227519077273891484 endpoint_16_42_p4 endpoint_16_42_w4
private theorem endpoint_16_42_w6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 6 2 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_p8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 8 227519077273891484 = some 227519077273891484 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 6 2 227519077273891484 227519077273891484 227519077273891484 endpoint_16_42_p6 endpoint_16_42_w6
private theorem endpoint_16_42_w8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 8 2 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_p10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 10 227519077273891484 = some 227519077273891484 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 8 2 227519077273891484 227519077273891484 227519077273891484 endpoint_16_42_p8 endpoint_16_42_w8
private theorem endpoint_16_42_w10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 10 2 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_p12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 12 227519077273891484 = some 227519077273891484 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 10 2 227519077273891484 227519077273891484 227519077273891484 endpoint_16_42_p10 endpoint_16_42_w10
private theorem endpoint_16_42_w12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 12 2 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_p14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 14 227519077273891484 = some 227519077273891484 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 12 2 227519077273891484 227519077273891484 227519077273891484 endpoint_16_42_p12 endpoint_16_42_w12
private theorem endpoint_16_42_w14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 14 1 227519077273891484 = some 227519077273891484 := by decide +kernel
private theorem endpoint_16_42_p15 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 15 227519077273891484 = some 227519077273891484 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 14 1 227519077273891484 227519077273891484 227519077273891484 endpoint_16_42_p14 endpoint_16_42_w14
def endpoint_16_42 : CertifiedEndpoint :=
  ⟨⟨16, 42, 2980⟩, 227519077273891484, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_42_flag endpoint_16_42_sources 15 227519077273891484 227519077273891484 rfl endpoint_16_42_base endpoint_16_42_p15) (by decide)⟩
private def endpoint_16_43_flag : Flag := ⟨16, 43, 2944⟩
private def endpoint_16_43_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_43_base : receiptBase endpoint_16_43_flag endpoint_16_43_sources = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_w0 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 2 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_w2 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 2 2 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_p4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 4 229977719793010544 = some 229977719793010544 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 2 2 229977719793010544 229977719793010544 229977719793010544 endpoint_16_43_w0 endpoint_16_43_w2
private theorem endpoint_16_43_w4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 4 2 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_p6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 6 229977719793010544 = some 229977719793010544 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 4 2 229977719793010544 229977719793010544 229977719793010544 endpoint_16_43_p4 endpoint_16_43_w4
private theorem endpoint_16_43_w6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 6 2 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_p8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 8 229977719793010544 = some 229977719793010544 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 6 2 229977719793010544 229977719793010544 229977719793010544 endpoint_16_43_p6 endpoint_16_43_w6
private theorem endpoint_16_43_w8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 8 2 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_p10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 10 229977719793010544 = some 229977719793010544 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 8 2 229977719793010544 229977719793010544 229977719793010544 endpoint_16_43_p8 endpoint_16_43_w8
private theorem endpoint_16_43_w10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 10 2 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_p12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 12 229977719793010544 = some 229977719793010544 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 10 2 229977719793010544 229977719793010544 229977719793010544 endpoint_16_43_p10 endpoint_16_43_w10
private theorem endpoint_16_43_w12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 12 2 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_p14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 14 229977719793010544 = some 229977719793010544 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 12 2 229977719793010544 229977719793010544 229977719793010544 endpoint_16_43_p12 endpoint_16_43_w12
private theorem endpoint_16_43_w14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 14 1 229977719793010544 = some 229977719793010544 := by decide +kernel
private theorem endpoint_16_43_p15 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 15 229977719793010544 = some 229977719793010544 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 14 1 229977719793010544 229977719793010544 229977719793010544 endpoint_16_43_p14 endpoint_16_43_w14
def endpoint_16_43 : CertifiedEndpoint :=
  ⟨⟨16, 43, 2944⟩, 229977719793010544, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_43_flag endpoint_16_43_sources 15 229977719793010544 229977719793010544 rfl endpoint_16_43_base endpoint_16_43_p15) (by decide)⟩
private def endpoint_16_44_flag : Flag := ⟨16, 44, 2908⟩
private def endpoint_16_44_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_44_base : receiptBase endpoint_16_44_flag endpoint_16_44_sources = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_w0 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 2 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_w2 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 2 2 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_p4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 4 231716771761147317 = some 231716771761147317 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 2 2 231716771761147317 231716771761147317 231716771761147317 endpoint_16_44_w0 endpoint_16_44_w2
private theorem endpoint_16_44_w4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 4 2 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_p6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 6 231716771761147317 = some 231716771761147317 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 4 2 231716771761147317 231716771761147317 231716771761147317 endpoint_16_44_p4 endpoint_16_44_w4
private theorem endpoint_16_44_w6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 6 2 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_p8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 8 231716771761147317 = some 231716771761147317 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 6 2 231716771761147317 231716771761147317 231716771761147317 endpoint_16_44_p6 endpoint_16_44_w6
private theorem endpoint_16_44_w8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 8 2 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_p10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 10 231716771761147317 = some 231716771761147317 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 8 2 231716771761147317 231716771761147317 231716771761147317 endpoint_16_44_p8 endpoint_16_44_w8
private theorem endpoint_16_44_w10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 10 2 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_p12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 12 231716771761147317 = some 231716771761147317 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 10 2 231716771761147317 231716771761147317 231716771761147317 endpoint_16_44_p10 endpoint_16_44_w10
private theorem endpoint_16_44_w12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 12 2 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_p14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 14 231716771761147317 = some 231716771761147317 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 12 2 231716771761147317 231716771761147317 231716771761147317 endpoint_16_44_p12 endpoint_16_44_w12
private theorem endpoint_16_44_w14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 14 1 231716771761147317 = some 231716771761147317 := by decide +kernel
private theorem endpoint_16_44_p15 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 15 231716771761147317 = some 231716771761147317 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 14 1 231716771761147317 231716771761147317 231716771761147317 endpoint_16_44_p14 endpoint_16_44_w14
def endpoint_16_44 : CertifiedEndpoint :=
  ⟨⟨16, 44, 2908⟩, 231716771761147317, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_44_flag endpoint_16_44_sources 15 231716771761147317 231716771761147317 rfl endpoint_16_44_base endpoint_16_44_p15) (by decide)⟩
private def endpoint_16_45_flag : Flag := ⟨16, 45, 2870⟩
private def endpoint_16_45_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_45_base : receiptBase endpoint_16_45_flag endpoint_16_45_sources = some 233184096811792910 := by decide +kernel
private theorem endpoint_16_45_w0 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 2 233184096811792910 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_w2 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 2 2 234167788488043681 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_p4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 4 233184096811792910 = some 234167788488043681 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 2 2 233184096811792910 234167788488043681 234167788488043681 endpoint_16_45_w0 endpoint_16_45_w2
private theorem endpoint_16_45_w4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 4 2 234167788488043681 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_p6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 6 233184096811792910 = some 234167788488043681 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 4 2 233184096811792910 234167788488043681 234167788488043681 endpoint_16_45_p4 endpoint_16_45_w4
private theorem endpoint_16_45_w6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 6 2 234167788488043681 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_p8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 8 233184096811792910 = some 234167788488043681 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 6 2 233184096811792910 234167788488043681 234167788488043681 endpoint_16_45_p6 endpoint_16_45_w6
private theorem endpoint_16_45_w8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 8 2 234167788488043681 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_p10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 10 233184096811792910 = some 234167788488043681 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 8 2 233184096811792910 234167788488043681 234167788488043681 endpoint_16_45_p8 endpoint_16_45_w8
private theorem endpoint_16_45_w10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 10 2 234167788488043681 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_p12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 12 233184096811792910 = some 234167788488043681 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 10 2 233184096811792910 234167788488043681 234167788488043681 endpoint_16_45_p10 endpoint_16_45_w10
private theorem endpoint_16_45_w12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 12 2 234167788488043681 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_p14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 14 233184096811792910 = some 234167788488043681 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 12 2 233184096811792910 234167788488043681 234167788488043681 endpoint_16_45_p12 endpoint_16_45_w12
private theorem endpoint_16_45_w14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 14 1 234167788488043681 = some 234167788488043681 := by decide +kernel
private theorem endpoint_16_45_p15 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 15 233184096811792910 = some 234167788488043681 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 14 1 233184096811792910 234167788488043681 234167788488043681 endpoint_16_45_p14 endpoint_16_45_w14
def endpoint_16_45 : CertifiedEndpoint :=
  ⟨⟨16, 45, 2870⟩, 234167788488043681, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_45_flag endpoint_16_45_sources 15 233184096811792910 234167788488043681 rfl endpoint_16_45_base endpoint_16_45_p15) (by decide)⟩
private def endpoint_16_46_flag : Flag := ⟨16, 46, 2832⟩
private def endpoint_16_46_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_46_base : receiptBase endpoint_16_46_flag endpoint_16_46_sources = some 235184790940904906 := by decide +kernel
private theorem endpoint_16_46_w0 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 2 235184790940904906 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_w2 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 2 2 238043439265133154 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_p4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 4 235184790940904906 = some 238043439265133154 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 2 2 235184790940904906 238043439265133154 238043439265133154 endpoint_16_46_w0 endpoint_16_46_w2
private theorem endpoint_16_46_w4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 4 2 238043439265133154 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_p6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 6 235184790940904906 = some 238043439265133154 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 4 2 235184790940904906 238043439265133154 238043439265133154 endpoint_16_46_p4 endpoint_16_46_w4
private theorem endpoint_16_46_w6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 6 2 238043439265133154 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_p8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 8 235184790940904906 = some 238043439265133154 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 6 2 235184790940904906 238043439265133154 238043439265133154 endpoint_16_46_p6 endpoint_16_46_w6
private theorem endpoint_16_46_w8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 8 2 238043439265133154 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_p10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 10 235184790940904906 = some 238043439265133154 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 8 2 235184790940904906 238043439265133154 238043439265133154 endpoint_16_46_p8 endpoint_16_46_w8
private theorem endpoint_16_46_w10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 10 2 238043439265133154 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_p12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 12 235184790940904906 = some 238043439265133154 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 10 2 235184790940904906 238043439265133154 238043439265133154 endpoint_16_46_p10 endpoint_16_46_w10
private theorem endpoint_16_46_w12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 12 2 238043439265133154 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_p14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 14 235184790940904906 = some 238043439265133154 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 12 2 235184790940904906 238043439265133154 238043439265133154 endpoint_16_46_p12 endpoint_16_46_w12
private theorem endpoint_16_46_w14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 14 1 238043439265133154 = some 238043439265133154 := by decide +kernel
private theorem endpoint_16_46_p15 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 15 235184790940904906 = some 238043439265133154 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 14 1 235184790940904906 238043439265133154 238043439265133154 endpoint_16_46_p14 endpoint_16_46_w14
def endpoint_16_46 : CertifiedEndpoint :=
  ⟨⟨16, 46, 2832⟩, 238043439265133154, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_46_flag endpoint_16_46_sources 15 235184790940904906 238043439265133154 rfl endpoint_16_46_base endpoint_16_46_p15) (by decide)⟩
private def endpoint_16_47_flag : Flag := ⟨16, 47, 2794⟩
private def endpoint_16_47_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_47_base : receiptBase endpoint_16_47_flag endpoint_16_47_sources = some 236450009129618224 := by decide +kernel
private theorem endpoint_16_47_w0 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 2 236450009129618224 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_w2 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 2 2 242643110782096796 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_p4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 4 236450009129618224 = some 242643110782096796 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 2 2 236450009129618224 242643110782096796 242643110782096796 endpoint_16_47_w0 endpoint_16_47_w2
private theorem endpoint_16_47_w4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 4 2 242643110782096796 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_p6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 6 236450009129618224 = some 242643110782096796 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 4 2 236450009129618224 242643110782096796 242643110782096796 endpoint_16_47_p4 endpoint_16_47_w4
private theorem endpoint_16_47_w6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 6 2 242643110782096796 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_p8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 8 236450009129618224 = some 242643110782096796 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 6 2 236450009129618224 242643110782096796 242643110782096796 endpoint_16_47_p6 endpoint_16_47_w6
private theorem endpoint_16_47_w8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 8 2 242643110782096796 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_p10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 10 236450009129618224 = some 242643110782096796 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 8 2 236450009129618224 242643110782096796 242643110782096796 endpoint_16_47_p8 endpoint_16_47_w8
private theorem endpoint_16_47_w10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 10 2 242643110782096796 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_p12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 12 236450009129618224 = some 242643110782096796 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 10 2 236450009129618224 242643110782096796 242643110782096796 endpoint_16_47_p10 endpoint_16_47_w10
private theorem endpoint_16_47_w12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 12 2 242643110782096796 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_p14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 14 236450009129618224 = some 242643110782096796 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 12 2 236450009129618224 242643110782096796 242643110782096796 endpoint_16_47_p12 endpoint_16_47_w12
private theorem endpoint_16_47_w14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 14 1 242643110782096796 = some 242643110782096796 := by decide +kernel
private theorem endpoint_16_47_p15 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 15 236450009129618224 = some 242643110782096796 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 14 1 236450009129618224 242643110782096796 242643110782096796 endpoint_16_47_p14 endpoint_16_47_w14
def endpoint_16_47 : CertifiedEndpoint :=
  ⟨⟨16, 47, 2794⟩, 242643110782096796, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_47_flag endpoint_16_47_sources 15 236450009129618224 242643110782096796 rfl endpoint_16_47_base endpoint_16_47_p15) (by decide)⟩
private def endpoint_16_48_flag : Flag := ⟨16, 48, 2754⟩
private def endpoint_16_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_48_base : receiptBase endpoint_16_48_flag endpoint_16_48_sources = some 238051244207339991 := by decide +kernel
private theorem endpoint_16_48_w0 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 2 238051244207339991 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_w2 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 2 2 238653560646649776 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_p4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 4 238051244207339991 = some 238653560646649776 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 2 2 238051244207339991 238653560646649776 238653560646649776 endpoint_16_48_w0 endpoint_16_48_w2
private theorem endpoint_16_48_w4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 4 2 238653560646649776 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_p6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 6 238051244207339991 = some 238653560646649776 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 4 2 238051244207339991 238653560646649776 238653560646649776 endpoint_16_48_p4 endpoint_16_48_w4
private theorem endpoint_16_48_w6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 6 2 238653560646649776 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_p8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 8 238051244207339991 = some 238653560646649776 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 6 2 238051244207339991 238653560646649776 238653560646649776 endpoint_16_48_p6 endpoint_16_48_w6
private theorem endpoint_16_48_w8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 8 2 238653560646649776 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_p10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 10 238051244207339991 = some 238653560646649776 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 8 2 238051244207339991 238653560646649776 238653560646649776 endpoint_16_48_p8 endpoint_16_48_w8
private theorem endpoint_16_48_w10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 10 2 238653560646649776 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_p12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 12 238051244207339991 = some 238653560646649776 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 10 2 238051244207339991 238653560646649776 238653560646649776 endpoint_16_48_p10 endpoint_16_48_w10
private theorem endpoint_16_48_w12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 12 2 238653560646649776 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_p14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 14 238051244207339991 = some 238653560646649776 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 12 2 238051244207339991 238653560646649776 238653560646649776 endpoint_16_48_p12 endpoint_16_48_w12
private theorem endpoint_16_48_w14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 14 1 238653560646649776 = some 238653560646649776 := by decide +kernel
private theorem endpoint_16_48_p15 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 15 238051244207339991 = some 238653560646649776 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 14 1 238051244207339991 238653560646649776 238653560646649776 endpoint_16_48_p14 endpoint_16_48_w14
def endpoint_16_48 : CertifiedEndpoint :=
  ⟨⟨16, 48, 2754⟩, 238653560646649776, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_48_flag endpoint_16_48_sources 15 238051244207339991 238653560646649776 rfl endpoint_16_48_base endpoint_16_48_p15) (by decide)⟩
private def endpoint_16_49_flag : Flag := ⟨16, 49, 2713⟩
private def endpoint_16_49_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_49_base : receiptBase endpoint_16_49_flag endpoint_16_49_sources = some 238804290168071492 := by decide +kernel
private theorem endpoint_16_49_w0 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 2 238804290168071492 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_w2 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 2 2 242696075024312480 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_p4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 4 238804290168071492 = some 242696075024312480 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 2 2 238804290168071492 242696075024312480 242696075024312480 endpoint_16_49_w0 endpoint_16_49_w2
private theorem endpoint_16_49_w4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 4 2 242696075024312480 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_p6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 6 238804290168071492 = some 242696075024312480 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 4 2 238804290168071492 242696075024312480 242696075024312480 endpoint_16_49_p4 endpoint_16_49_w4
private theorem endpoint_16_49_w6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 6 2 242696075024312480 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_p8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 8 238804290168071492 = some 242696075024312480 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 6 2 238804290168071492 242696075024312480 242696075024312480 endpoint_16_49_p6 endpoint_16_49_w6
private theorem endpoint_16_49_w8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 8 2 242696075024312480 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_p10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 10 238804290168071492 = some 242696075024312480 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 8 2 238804290168071492 242696075024312480 242696075024312480 endpoint_16_49_p8 endpoint_16_49_w8
private theorem endpoint_16_49_w10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 10 2 242696075024312480 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_p12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 12 238804290168071492 = some 242696075024312480 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 10 2 238804290168071492 242696075024312480 242696075024312480 endpoint_16_49_p10 endpoint_16_49_w10
private theorem endpoint_16_49_w12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 12 2 242696075024312480 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_p14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 14 238804290168071492 = some 242696075024312480 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 12 2 238804290168071492 242696075024312480 242696075024312480 endpoint_16_49_p12 endpoint_16_49_w12
private theorem endpoint_16_49_w14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 14 1 242696075024312480 = some 242696075024312480 := by decide +kernel
private theorem endpoint_16_49_p15 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 15 238804290168071492 = some 242696075024312480 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 14 1 238804290168071492 242696075024312480 242696075024312480 endpoint_16_49_p14 endpoint_16_49_w14
def endpoint_16_49 : CertifiedEndpoint :=
  ⟨⟨16, 49, 2713⟩, 242696075024312480, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_49_flag endpoint_16_49_sources 15 238804290168071492 242696075024312480 rfl endpoint_16_49_base endpoint_16_49_p15) (by decide)⟩
private def endpoint_16_50_flag : Flag := ⟨16, 50, 2671⟩
private def endpoint_16_50_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_50_base : receiptBase endpoint_16_50_flag endpoint_16_50_sources = some 239340704865132775 := by decide +kernel
private theorem endpoint_16_50_w0 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 2 239340704865132775 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_w2 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 2 2 246584035395579638 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_p4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 4 239340704865132775 = some 246584035395579638 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 2 2 239340704865132775 246584035395579638 246584035395579638 endpoint_16_50_w0 endpoint_16_50_w2
private theorem endpoint_16_50_w4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 4 2 246584035395579638 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_p6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 6 239340704865132775 = some 246584035395579638 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 4 2 239340704865132775 246584035395579638 246584035395579638 endpoint_16_50_p4 endpoint_16_50_w4
private theorem endpoint_16_50_w6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 6 2 246584035395579638 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_p8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 8 239340704865132775 = some 246584035395579638 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 6 2 239340704865132775 246584035395579638 246584035395579638 endpoint_16_50_p6 endpoint_16_50_w6
private theorem endpoint_16_50_w8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 8 2 246584035395579638 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_p10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 10 239340704865132775 = some 246584035395579638 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 8 2 239340704865132775 246584035395579638 246584035395579638 endpoint_16_50_p8 endpoint_16_50_w8
private theorem endpoint_16_50_w10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 10 2 246584035395579638 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_p12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 12 239340704865132775 = some 246584035395579638 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 10 2 239340704865132775 246584035395579638 246584035395579638 endpoint_16_50_p10 endpoint_16_50_w10
private theorem endpoint_16_50_w12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 12 2 246584035395579638 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_p14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 14 239340704865132775 = some 246584035395579638 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 12 2 239340704865132775 246584035395579638 246584035395579638 endpoint_16_50_p12 endpoint_16_50_w12
private theorem endpoint_16_50_w14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 14 1 246584035395579638 = some 246584035395579638 := by decide +kernel
private theorem endpoint_16_50_p15 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 15 239340704865132775 = some 246584035395579638 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 14 1 239340704865132775 246584035395579638 246584035395579638 endpoint_16_50_p14 endpoint_16_50_w14
def endpoint_16_50 : CertifiedEndpoint :=
  ⟨⟨16, 50, 2671⟩, 246584035395579638, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_50_flag endpoint_16_50_sources 15 239340704865132775 246584035395579638 rfl endpoint_16_50_base endpoint_16_50_p15) (by decide)⟩
private def endpoint_16_51_flag : Flag := ⟨16, 51, 2629⟩
private def endpoint_16_51_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_51_base : receiptBase endpoint_16_51_flag endpoint_16_51_sources = some 239745748387113070 := by decide +kernel
private theorem endpoint_16_51_w0 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 2 239745748387113070 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_w2 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 2 2 250365065574971166 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_p4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 4 239745748387113070 = some 250365065574971166 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 2 2 239745748387113070 250365065574971166 250365065574971166 endpoint_16_51_w0 endpoint_16_51_w2
private theorem endpoint_16_51_w4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 4 2 250365065574971166 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_p6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 6 239745748387113070 = some 250365065574971166 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 4 2 239745748387113070 250365065574971166 250365065574971166 endpoint_16_51_p4 endpoint_16_51_w4
private theorem endpoint_16_51_w6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 6 2 250365065574971166 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_p8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 8 239745748387113070 = some 250365065574971166 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 6 2 239745748387113070 250365065574971166 250365065574971166 endpoint_16_51_p6 endpoint_16_51_w6
private theorem endpoint_16_51_w8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 8 2 250365065574971166 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_p10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 10 239745748387113070 = some 250365065574971166 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 8 2 239745748387113070 250365065574971166 250365065574971166 endpoint_16_51_p8 endpoint_16_51_w8
private theorem endpoint_16_51_w10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 10 2 250365065574971166 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_p12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 12 239745748387113070 = some 250365065574971166 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 10 2 239745748387113070 250365065574971166 250365065574971166 endpoint_16_51_p10 endpoint_16_51_w10
private theorem endpoint_16_51_w12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 12 2 250365065574971166 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_p14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 14 239745748387113070 = some 250365065574971166 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 12 2 239745748387113070 250365065574971166 250365065574971166 endpoint_16_51_p12 endpoint_16_51_w12
private theorem endpoint_16_51_w14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 14 1 250365065574971166 = some 250365065574971166 := by decide +kernel
private theorem endpoint_16_51_p15 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 15 239745748387113070 = some 250365065574971166 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 14 1 239745748387113070 250365065574971166 250365065574971166 endpoint_16_51_p14 endpoint_16_51_w14
def endpoint_16_51 : CertifiedEndpoint :=
  ⟨⟨16, 51, 2629⟩, 250365065574971166, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_51_flag endpoint_16_51_sources 15 239745748387113070 250365065574971166 rfl endpoint_16_51_base endpoint_16_51_p15) (by decide)⟩
private def endpoint_16_52_flag : Flag := ⟨16, 52, 2585⟩
private def endpoint_16_52_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_52_base : receiptBase endpoint_16_52_flag endpoint_16_52_sources = some 239836536210943942 := by decide +kernel
private theorem endpoint_16_52_w0 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 2 239836536210943942 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_w2 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 2 2 253934090801332872 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_p4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 4 239836536210943942 = some 253934090801332872 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 2 2 239836536210943942 253934090801332872 253934090801332872 endpoint_16_52_w0 endpoint_16_52_w2
private theorem endpoint_16_52_w4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 4 2 253934090801332872 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_p6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 6 239836536210943942 = some 253934090801332872 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 4 2 239836536210943942 253934090801332872 253934090801332872 endpoint_16_52_p4 endpoint_16_52_w4
private theorem endpoint_16_52_w6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 6 2 253934090801332872 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_p8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 8 239836536210943942 = some 253934090801332872 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 6 2 239836536210943942 253934090801332872 253934090801332872 endpoint_16_52_p6 endpoint_16_52_w6
private theorem endpoint_16_52_w8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 8 2 253934090801332872 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_p10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 10 239836536210943942 = some 253934090801332872 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 8 2 239836536210943942 253934090801332872 253934090801332872 endpoint_16_52_p8 endpoint_16_52_w8
private theorem endpoint_16_52_w10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 10 2 253934090801332872 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_p12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 12 239836536210943942 = some 253934090801332872 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 10 2 239836536210943942 253934090801332872 253934090801332872 endpoint_16_52_p10 endpoint_16_52_w10
private theorem endpoint_16_52_w12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 12 2 253934090801332872 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_p14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 14 239836536210943942 = some 253934090801332872 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 12 2 239836536210943942 253934090801332872 253934090801332872 endpoint_16_52_p12 endpoint_16_52_w12
private theorem endpoint_16_52_w14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 14 1 253934090801332872 = some 253934090801332872 := by decide +kernel
private theorem endpoint_16_52_p15 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 15 239836536210943942 = some 253934090801332872 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 14 1 239836536210943942 253934090801332872 253934090801332872 endpoint_16_52_p14 endpoint_16_52_w14
def endpoint_16_52 : CertifiedEndpoint :=
  ⟨⟨16, 52, 2585⟩, 253934090801332872, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_52_flag endpoint_16_52_sources 15 239836536210943942 253934090801332872 rfl endpoint_16_52_base endpoint_16_52_p15) (by decide)⟩
private def endpoint_16_53_flag : Flag := ⟨16, 53, 2540⟩
private def endpoint_16_53_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_53_base : receiptBase endpoint_16_53_flag endpoint_16_53_sources = some 239696782881978373 := by decide +kernel
private theorem endpoint_16_53_w0 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 2 239696782881978373 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_w2 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 2 2 257337506497670377 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_p4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 4 239696782881978373 = some 257337506497670377 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 2 2 239696782881978373 257337506497670377 257337506497670377 endpoint_16_53_w0 endpoint_16_53_w2
private theorem endpoint_16_53_w4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 4 2 257337506497670377 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_p6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 6 239696782881978373 = some 257337506497670377 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 4 2 239696782881978373 257337506497670377 257337506497670377 endpoint_16_53_p4 endpoint_16_53_w4
private theorem endpoint_16_53_w6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 6 2 257337506497670377 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_p8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 8 239696782881978373 = some 257337506497670377 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 6 2 239696782881978373 257337506497670377 257337506497670377 endpoint_16_53_p6 endpoint_16_53_w6
private theorem endpoint_16_53_w8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 8 2 257337506497670377 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_p10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 10 239696782881978373 = some 257337506497670377 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 8 2 239696782881978373 257337506497670377 257337506497670377 endpoint_16_53_p8 endpoint_16_53_w8
private theorem endpoint_16_53_w10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 10 2 257337506497670377 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_p12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 12 239696782881978373 = some 257337506497670377 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 10 2 239696782881978373 257337506497670377 257337506497670377 endpoint_16_53_p10 endpoint_16_53_w10
private theorem endpoint_16_53_w12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 12 2 257337506497670377 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_p14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 14 239696782881978373 = some 257337506497670377 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 12 2 239696782881978373 257337506497670377 257337506497670377 endpoint_16_53_p12 endpoint_16_53_w12
private theorem endpoint_16_53_w14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 14 1 257337506497670377 = some 257337506497670377 := by decide +kernel
private theorem endpoint_16_53_p15 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 15 239696782881978373 = some 257337506497670377 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 14 1 239696782881978373 257337506497670377 257337506497670377 endpoint_16_53_p14 endpoint_16_53_w14
def endpoint_16_53 : CertifiedEndpoint :=
  ⟨⟨16, 53, 2540⟩, 257337506497670377, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_53_flag endpoint_16_53_sources 15 239696782881978373 257337506497670377 rfl endpoint_16_53_base endpoint_16_53_p15) (by decide)⟩
private def endpoint_16_54_flag : Flag := ⟨16, 54, 2494⟩
private def endpoint_16_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_54_base : receiptBase endpoint_16_54_flag endpoint_16_54_sources = some 239321851770507623 := by decide +kernel
private theorem endpoint_16_54_w0 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 2 239321851770507623 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_w2 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 2 2 260571627489440796 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_p4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 4 239321851770507623 = some 260571627489440796 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 2 2 239321851770507623 260571627489440796 260571627489440796 endpoint_16_54_w0 endpoint_16_54_w2
private theorem endpoint_16_54_w4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 4 2 260571627489440796 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_p6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 6 239321851770507623 = some 260571627489440796 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 4 2 239321851770507623 260571627489440796 260571627489440796 endpoint_16_54_p4 endpoint_16_54_w4
private theorem endpoint_16_54_w6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 6 2 260571627489440796 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_p8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 8 239321851770507623 = some 260571627489440796 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 6 2 239321851770507623 260571627489440796 260571627489440796 endpoint_16_54_p6 endpoint_16_54_w6
private theorem endpoint_16_54_w8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 8 2 260571627489440796 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_p10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 10 239321851770507623 = some 260571627489440796 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 8 2 239321851770507623 260571627489440796 260571627489440796 endpoint_16_54_p8 endpoint_16_54_w8
private theorem endpoint_16_54_w10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 10 2 260571627489440796 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_p12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 12 239321851770507623 = some 260571627489440796 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 10 2 239321851770507623 260571627489440796 260571627489440796 endpoint_16_54_p10 endpoint_16_54_w10
private theorem endpoint_16_54_w12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 12 2 260571627489440796 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_p14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 14 239321851770507623 = some 260571627489440796 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 12 2 239321851770507623 260571627489440796 260571627489440796 endpoint_16_54_p12 endpoint_16_54_w12
private theorem endpoint_16_54_w14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 14 1 260571627489440796 = some 260571627489440796 := by decide +kernel
private theorem endpoint_16_54_p15 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 15 239321851770507623 = some 260571627489440796 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 14 1 239321851770507623 260571627489440796 260571627489440796 endpoint_16_54_p14 endpoint_16_54_w14
def endpoint_16_54 : CertifiedEndpoint :=
  ⟨⟨16, 54, 2494⟩, 260571627489440796, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_54_flag endpoint_16_54_sources 15 239321851770507623 260571627489440796 rfl endpoint_16_54_base endpoint_16_54_p15) (by decide)⟩
private def endpoint_16_55_flag : Flag := ⟨16, 55, 2447⟩
private def endpoint_16_55_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_55_base : receiptBase endpoint_16_55_flag endpoint_16_55_sources = some 244624187770501997 := by decide +kernel
private theorem endpoint_16_55_w0 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 2 244624187770501997 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_w2 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 2 2 255717221166789416 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_p4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 4 244624187770501997 = some 255717221166789416 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 2 2 244624187770501997 255717221166789416 255717221166789416 endpoint_16_55_w0 endpoint_16_55_w2
private theorem endpoint_16_55_w4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 4 2 255717221166789416 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_p6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 6 244624187770501997 = some 255717221166789416 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 4 2 244624187770501997 255717221166789416 255717221166789416 endpoint_16_55_p4 endpoint_16_55_w4
private theorem endpoint_16_55_w6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 6 2 255717221166789416 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_p8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 8 244624187770501997 = some 255717221166789416 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 6 2 244624187770501997 255717221166789416 255717221166789416 endpoint_16_55_p6 endpoint_16_55_w6
private theorem endpoint_16_55_w8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 8 2 255717221166789416 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_p10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 10 244624187770501997 = some 255717221166789416 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 8 2 244624187770501997 255717221166789416 255717221166789416 endpoint_16_55_p8 endpoint_16_55_w8
private theorem endpoint_16_55_w10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 10 2 255717221166789416 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_p12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 12 244624187770501997 = some 255717221166789416 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 10 2 244624187770501997 255717221166789416 255717221166789416 endpoint_16_55_p10 endpoint_16_55_w10
private theorem endpoint_16_55_w12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 12 2 255717221166789416 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_p14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 14 244624187770501997 = some 255717221166789416 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 12 2 244624187770501997 255717221166789416 255717221166789416 endpoint_16_55_p12 endpoint_16_55_w12
private theorem endpoint_16_55_w14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 14 1 255717221166789416 = some 255717221166789416 := by decide +kernel
private theorem endpoint_16_55_p15 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 15 244624187770501997 = some 255717221166789416 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 14 1 244624187770501997 255717221166789416 255717221166789416 endpoint_16_55_p14 endpoint_16_55_w14
def endpoint_16_55 : CertifiedEndpoint :=
  ⟨⟨16, 55, 2447⟩, 255717221166789416, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_55_flag endpoint_16_55_sources 15 244624187770501997 255717221166789416 rfl endpoint_16_55_base endpoint_16_55_p15) (by decide)⟩
private def endpoint_16_56_flag : Flag := ⟨16, 56, 2399⟩
private def endpoint_16_56_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_56_base : receiptBase endpoint_16_56_flag endpoint_16_56_sources = some 243805444924472132 := by decide +kernel
private theorem endpoint_16_56_w0 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 2 243805444924472132 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_w2 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 2 2 258430547130879268 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_p4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 4 243805444924472132 = some 258430547130879268 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 2 2 243805444924472132 258430547130879268 258430547130879268 endpoint_16_56_w0 endpoint_16_56_w2
private theorem endpoint_16_56_w4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 4 2 258430547130879268 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_p6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 6 243805444924472132 = some 258430547130879268 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 4 2 243805444924472132 258430547130879268 258430547130879268 endpoint_16_56_p4 endpoint_16_56_w4
private theorem endpoint_16_56_w6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 6 2 258430547130879268 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_p8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 8 243805444924472132 = some 258430547130879268 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 6 2 243805444924472132 258430547130879268 258430547130879268 endpoint_16_56_p6 endpoint_16_56_w6
private theorem endpoint_16_56_w8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 8 2 258430547130879268 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_p10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 10 243805444924472132 = some 258430547130879268 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 8 2 243805444924472132 258430547130879268 258430547130879268 endpoint_16_56_p8 endpoint_16_56_w8
private theorem endpoint_16_56_w10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 10 2 258430547130879268 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_p12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 12 243805444924472132 = some 258430547130879268 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 10 2 243805444924472132 258430547130879268 258430547130879268 endpoint_16_56_p10 endpoint_16_56_w10
private theorem endpoint_16_56_w12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 12 2 258430547130879268 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_p14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 14 243805444924472132 = some 258430547130879268 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 12 2 243805444924472132 258430547130879268 258430547130879268 endpoint_16_56_p12 endpoint_16_56_w12
private theorem endpoint_16_56_w14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 14 1 258430547130879268 = some 258430547130879268 := by decide +kernel
private theorem endpoint_16_56_p15 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 15 243805444924472132 = some 258430547130879268 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 14 1 243805444924472132 258430547130879268 258430547130879268 endpoint_16_56_p14 endpoint_16_56_w14
def endpoint_16_56 : CertifiedEndpoint :=
  ⟨⟨16, 56, 2399⟩, 258430547130879268, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_56_flag endpoint_16_56_sources 15 243805444924472132 258430547130879268 rfl endpoint_16_56_base endpoint_16_56_p15) (by decide)⟩
private def endpoint_16_57_flag : Flag := ⟨16, 57, 2349⟩
private def endpoint_16_57_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_57_base : receiptBase endpoint_16_57_flag endpoint_16_57_sources = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_w0 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 2 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_w2 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 2 2 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_p4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 4 243777942825302425 = some 243777942825302425 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 2 2 243777942825302425 243777942825302425 243777942825302425 endpoint_16_57_w0 endpoint_16_57_w2
private theorem endpoint_16_57_w4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 4 2 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_p6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 6 243777942825302425 = some 243777942825302425 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 4 2 243777942825302425 243777942825302425 243777942825302425 endpoint_16_57_p4 endpoint_16_57_w4
private theorem endpoint_16_57_w6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 6 2 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_p8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 8 243777942825302425 = some 243777942825302425 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 6 2 243777942825302425 243777942825302425 243777942825302425 endpoint_16_57_p6 endpoint_16_57_w6
private theorem endpoint_16_57_w8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 8 2 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_p10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 10 243777942825302425 = some 243777942825302425 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 8 2 243777942825302425 243777942825302425 243777942825302425 endpoint_16_57_p8 endpoint_16_57_w8
private theorem endpoint_16_57_w10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 10 2 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_p12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 12 243777942825302425 = some 243777942825302425 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 10 2 243777942825302425 243777942825302425 243777942825302425 endpoint_16_57_p10 endpoint_16_57_w10
private theorem endpoint_16_57_w12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 12 2 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_p14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 14 243777942825302425 = some 243777942825302425 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 12 2 243777942825302425 243777942825302425 243777942825302425 endpoint_16_57_p12 endpoint_16_57_w12
private theorem endpoint_16_57_w14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 14 1 243777942825302425 = some 243777942825302425 := by decide +kernel
private theorem endpoint_16_57_p15 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 15 243777942825302425 = some 243777942825302425 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 14 1 243777942825302425 243777942825302425 243777942825302425 endpoint_16_57_p14 endpoint_16_57_w14
def endpoint_16_57 : CertifiedEndpoint :=
  ⟨⟨16, 57, 2349⟩, 243777942825302425, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_57_flag endpoint_16_57_sources 15 243777942825302425 243777942825302425 rfl endpoint_16_57_base endpoint_16_57_p15) (by decide)⟩
private def endpoint_16_58_flag : Flag := ⟨16, 58, 2299⟩
private def endpoint_16_58_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_58_base : receiptBase endpoint_16_58_flag endpoint_16_58_sources = some 242388511880402341 := by decide +kernel
private theorem endpoint_16_58_w0 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 2 242388511880402341 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_w2 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 2 2 245278957390715528 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_p4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 4 242388511880402341 = some 245278957390715528 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 2 2 242388511880402341 245278957390715528 245278957390715528 endpoint_16_58_w0 endpoint_16_58_w2
private theorem endpoint_16_58_w4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 4 2 245278957390715528 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_p6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 6 242388511880402341 = some 245278957390715528 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 4 2 242388511880402341 245278957390715528 245278957390715528 endpoint_16_58_p4 endpoint_16_58_w4
private theorem endpoint_16_58_w6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 6 2 245278957390715528 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_p8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 8 242388511880402341 = some 245278957390715528 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 6 2 242388511880402341 245278957390715528 245278957390715528 endpoint_16_58_p6 endpoint_16_58_w6
private theorem endpoint_16_58_w8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 8 2 245278957390715528 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_p10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 10 242388511880402341 = some 245278957390715528 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 8 2 242388511880402341 245278957390715528 245278957390715528 endpoint_16_58_p8 endpoint_16_58_w8
private theorem endpoint_16_58_w10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 10 2 245278957390715528 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_p12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 12 242388511880402341 = some 245278957390715528 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 10 2 242388511880402341 245278957390715528 245278957390715528 endpoint_16_58_p10 endpoint_16_58_w10
private theorem endpoint_16_58_w12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 12 2 245278957390715528 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_p14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 14 242388511880402341 = some 245278957390715528 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 12 2 242388511880402341 245278957390715528 245278957390715528 endpoint_16_58_p12 endpoint_16_58_w12
private theorem endpoint_16_58_w14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 14 1 245278957390715528 = some 245278957390715528 := by decide +kernel
private theorem endpoint_16_58_p15 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 15 242388511880402341 = some 245278957390715528 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 14 1 242388511880402341 245278957390715528 245278957390715528 endpoint_16_58_p14 endpoint_16_58_w14
def endpoint_16_58 : CertifiedEndpoint :=
  ⟨⟨16, 58, 2299⟩, 245278957390715528, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_58_flag endpoint_16_58_sources 15 242388511880402341 245278957390715528 rfl endpoint_16_58_base endpoint_16_58_p15) (by decide)⟩
private def endpoint_16_59_flag : Flag := ⟨16, 59, 2246⟩
private def endpoint_16_59_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_59_base : receiptBase endpoint_16_59_flag endpoint_16_59_sources = some 240527640668267590 := by decide +kernel
private theorem endpoint_16_59_w0 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 2 240527640668267590 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_w2 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 2 2 246951724104440410 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_p4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 4 240527640668267590 = some 246951724104440410 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 2 2 240527640668267590 246951724104440410 246951724104440410 endpoint_16_59_w0 endpoint_16_59_w2
private theorem endpoint_16_59_w4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 4 2 246951724104440410 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_p6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 6 240527640668267590 = some 246951724104440410 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 4 2 240527640668267590 246951724104440410 246951724104440410 endpoint_16_59_p4 endpoint_16_59_w4
private theorem endpoint_16_59_w6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 6 2 246951724104440410 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_p8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 8 240527640668267590 = some 246951724104440410 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 6 2 240527640668267590 246951724104440410 246951724104440410 endpoint_16_59_p6 endpoint_16_59_w6
private theorem endpoint_16_59_w8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 8 2 246951724104440410 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_p10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 10 240527640668267590 = some 246951724104440410 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 8 2 240527640668267590 246951724104440410 246951724104440410 endpoint_16_59_p8 endpoint_16_59_w8
private theorem endpoint_16_59_w10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 10 2 246951724104440410 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_p12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 12 240527640668267590 = some 246951724104440410 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 10 2 240527640668267590 246951724104440410 246951724104440410 endpoint_16_59_p10 endpoint_16_59_w10
private theorem endpoint_16_59_w12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 12 2 246951724104440410 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_p14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 14 240527640668267590 = some 246951724104440410 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 12 2 240527640668267590 246951724104440410 246951724104440410 endpoint_16_59_p12 endpoint_16_59_w12
private theorem endpoint_16_59_w14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 14 1 246951724104440410 = some 246951724104440410 := by decide +kernel
private theorem endpoint_16_59_p15 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 15 240527640668267590 = some 246951724104440410 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 14 1 240527640668267590 246951724104440410 246951724104440410 endpoint_16_59_p14 endpoint_16_59_w14
def endpoint_16_59 : CertifiedEndpoint :=
  ⟨⟨16, 59, 2246⟩, 246951724104440410, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_59_flag endpoint_16_59_sources 15 240527640668267590 246951724104440410 rfl endpoint_16_59_base endpoint_16_59_p15) (by decide)⟩
private def endpoint_16_60_flag : Flag := ⟨16, 60, 2193⟩
private def endpoint_16_60_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_60_base : receiptBase endpoint_16_60_flag endpoint_16_60_sources = some 238499476837673213 := by decide +kernel
private theorem endpoint_16_60_w0 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 2 238499476837673213 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_w2 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 2 2 248490536012975172 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_p4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 4 238499476837673213 = some 248490536012975172 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 2 2 238499476837673213 248490536012975172 248490536012975172 endpoint_16_60_w0 endpoint_16_60_w2
private theorem endpoint_16_60_w4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 4 2 248490536012975172 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_p6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 6 238499476837673213 = some 248490536012975172 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 4 2 238499476837673213 248490536012975172 248490536012975172 endpoint_16_60_p4 endpoint_16_60_w4
private theorem endpoint_16_60_w6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 6 2 248490536012975172 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_p8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 8 238499476837673213 = some 248490536012975172 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 6 2 238499476837673213 248490536012975172 248490536012975172 endpoint_16_60_p6 endpoint_16_60_w6
private theorem endpoint_16_60_w8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 8 2 248490536012975172 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_p10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 10 238499476837673213 = some 248490536012975172 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 8 2 238499476837673213 248490536012975172 248490536012975172 endpoint_16_60_p8 endpoint_16_60_w8
private theorem endpoint_16_60_w10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 10 2 248490536012975172 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_p12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 12 238499476837673213 = some 248490536012975172 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 10 2 238499476837673213 248490536012975172 248490536012975172 endpoint_16_60_p10 endpoint_16_60_w10
private theorem endpoint_16_60_w12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 12 2 248490536012975172 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_p14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 14 238499476837673213 = some 248490536012975172 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 12 2 238499476837673213 248490536012975172 248490536012975172 endpoint_16_60_p12 endpoint_16_60_w12
private theorem endpoint_16_60_w14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 14 1 248490536012975172 = some 248490536012975172 := by decide +kernel
private theorem endpoint_16_60_p15 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 15 238499476837673213 = some 248490536012975172 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 14 1 238499476837673213 248490536012975172 248490536012975172 endpoint_16_60_p14 endpoint_16_60_w14
def endpoint_16_60 : CertifiedEndpoint :=
  ⟨⟨16, 60, 2193⟩, 248490536012975172, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_60_flag endpoint_16_60_sources 15 238499476837673213 248490536012975172 rfl endpoint_16_60_base endpoint_16_60_p15) (by decide)⟩
private def endpoint_16_61_flag : Flag := ⟨16, 61, 2138⟩
private def endpoint_16_61_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_61_base : receiptBase endpoint_16_61_flag endpoint_16_61_sources = some 236088747430111765 := by decide +kernel
private theorem endpoint_16_61_w0 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 2 236088747430111765 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_w2 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 2 2 249768207307908312 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_p4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 4 236088747430111765 = some 249768207307908312 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 2 2 236088747430111765 249768207307908312 249768207307908312 endpoint_16_61_w0 endpoint_16_61_w2
private theorem endpoint_16_61_w4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 4 2 249768207307908312 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_p6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 6 236088747430111765 = some 249768207307908312 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 4 2 236088747430111765 249768207307908312 249768207307908312 endpoint_16_61_p4 endpoint_16_61_w4
private theorem endpoint_16_61_w6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 6 2 249768207307908312 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_p8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 8 236088747430111765 = some 249768207307908312 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 6 2 236088747430111765 249768207307908312 249768207307908312 endpoint_16_61_p6 endpoint_16_61_w6
private theorem endpoint_16_61_w8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 8 2 249768207307908312 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_p10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 10 236088747430111765 = some 249768207307908312 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 8 2 236088747430111765 249768207307908312 249768207307908312 endpoint_16_61_p8 endpoint_16_61_w8
private theorem endpoint_16_61_w10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 10 2 249768207307908312 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_p12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 12 236088747430111765 = some 249768207307908312 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 10 2 236088747430111765 249768207307908312 249768207307908312 endpoint_16_61_p10 endpoint_16_61_w10
private theorem endpoint_16_61_w12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 12 2 249768207307908312 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_p14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 14 236088747430111765 = some 249768207307908312 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 12 2 236088747430111765 249768207307908312 249768207307908312 endpoint_16_61_p12 endpoint_16_61_w12
private theorem endpoint_16_61_w14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 14 1 249768207307908312 = some 249768207307908312 := by decide +kernel
private theorem endpoint_16_61_p15 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 15 236088747430111765 = some 249768207307908312 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 14 1 236088747430111765 249768207307908312 249768207307908312 endpoint_16_61_p14 endpoint_16_61_w14
def endpoint_16_61 : CertifiedEndpoint :=
  ⟨⟨16, 61, 2138⟩, 249768207307908312, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_61_flag endpoint_16_61_sources 15 236088747430111765 249768207307908312 rfl endpoint_16_61_base endpoint_16_61_p15) (by decide)⟩
private def endpoint_16_62_flag : Flag := ⟨16, 62, 2081⟩
private def endpoint_16_62_sources : Sources := ⟨contact15, contact15, contact12⟩
private theorem endpoint_16_62_base : receiptBase endpoint_16_62_flag endpoint_16_62_sources = some 234462726247326334 := by decide +kernel
private theorem endpoint_16_62_w0 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 2 234462726247326334 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_w2 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 2 2 243942169065352054 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_p4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 4 234462726247326334 = some 243942169065352054 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 2 2 234462726247326334 243942169065352054 243942169065352054 endpoint_16_62_w0 endpoint_16_62_w2
private theorem endpoint_16_62_w4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 4 2 243942169065352054 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_p6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 6 234462726247326334 = some 243942169065352054 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 4 2 234462726247326334 243942169065352054 243942169065352054 endpoint_16_62_p4 endpoint_16_62_w4
private theorem endpoint_16_62_w6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 6 2 243942169065352054 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_p8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 8 234462726247326334 = some 243942169065352054 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 6 2 234462726247326334 243942169065352054 243942169065352054 endpoint_16_62_p6 endpoint_16_62_w6
private theorem endpoint_16_62_w8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 8 2 243942169065352054 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_p10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 10 234462726247326334 = some 243942169065352054 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 8 2 234462726247326334 243942169065352054 243942169065352054 endpoint_16_62_p8 endpoint_16_62_w8
private theorem endpoint_16_62_w10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 10 2 243942169065352054 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_p12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 12 234462726247326334 = some 243942169065352054 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 10 2 234462726247326334 243942169065352054 243942169065352054 endpoint_16_62_p10 endpoint_16_62_w10
private theorem endpoint_16_62_w12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 12 2 243942169065352054 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_p14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 14 234462726247326334 = some 243942169065352054 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 12 2 234462726247326334 243942169065352054 243942169065352054 endpoint_16_62_p12 endpoint_16_62_w12
private theorem endpoint_16_62_w14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 14 1 243942169065352054 = some 243942169065352054 := by decide +kernel
private theorem endpoint_16_62_p15 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 15 234462726247326334 = some 243942169065352054 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 14 1 234462726247326334 243942169065352054 243942169065352054 endpoint_16_62_p14 endpoint_16_62_w14
def endpoint_16_62 : CertifiedEndpoint :=
  ⟨⟨16, 62, 2081⟩, 243942169065352054, .terminal ⟨contact15, contact15, contact12⟩ (finish_receipt_window endpoint_16_62_flag endpoint_16_62_sources 15 234462726247326334 243942169065352054 rfl endpoint_16_62_base endpoint_16_62_p15) (by decide)⟩
private def endpoint_16_63_flag : Flag := ⟨16, 63, 2023⟩
private def endpoint_16_63_sources : Sources := ⟨contact29, contact16, contact13⟩
private theorem endpoint_16_63_base : receiptBase endpoint_16_63_flag endpoint_16_63_sources = some 232298911306492621 := by decide +kernel
private theorem endpoint_16_63_w0 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 2 232298911306492621 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_w2 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 2 2 243247731055598066 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_p4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 4 232298911306492621 = some 243247731055598066 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 2 2 232298911306492621 243247731055598066 243247731055598066 endpoint_16_63_w0 endpoint_16_63_w2
private theorem endpoint_16_63_w4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 4 2 243247731055598066 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_p6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 6 232298911306492621 = some 243247731055598066 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 4 2 232298911306492621 243247731055598066 243247731055598066 endpoint_16_63_p4 endpoint_16_63_w4
private theorem endpoint_16_63_w6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 6 2 243247731055598066 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_p8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 8 232298911306492621 = some 243247731055598066 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 6 2 232298911306492621 243247731055598066 243247731055598066 endpoint_16_63_p6 endpoint_16_63_w6
private theorem endpoint_16_63_w8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 8 2 243247731055598066 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_p10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 10 232298911306492621 = some 243247731055598066 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 8 2 232298911306492621 243247731055598066 243247731055598066 endpoint_16_63_p8 endpoint_16_63_w8
private theorem endpoint_16_63_w10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 10 2 243247731055598066 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_p12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 12 232298911306492621 = some 243247731055598066 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 10 2 232298911306492621 243247731055598066 243247731055598066 endpoint_16_63_p10 endpoint_16_63_w10
private theorem endpoint_16_63_w12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 12 2 243247731055598066 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_p14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 14 232298911306492621 = some 243247731055598066 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 12 2 232298911306492621 243247731055598066 243247731055598066 endpoint_16_63_p12 endpoint_16_63_w12
private theorem endpoint_16_63_w14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 14 1 243247731055598066 = some 243247731055598066 := by decide +kernel
private theorem endpoint_16_63_p15 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 15 232298911306492621 = some 243247731055598066 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 14 1 232298911306492621 243247731055598066 243247731055598066 endpoint_16_63_p14 endpoint_16_63_w14
def endpoint_16_63 : CertifiedEndpoint :=
  ⟨⟨16, 63, 2023⟩, 243247731055598066, .terminal ⟨contact29, contact16, contact13⟩ (finish_receipt_window endpoint_16_63_flag endpoint_16_63_sources 15 232298911306492621 243247731055598066 rfl endpoint_16_63_base endpoint_16_63_p15) (by decide)⟩
private def endpoint_16_64_flag : Flag := ⟨16, 64, 1964⟩
private def endpoint_16_64_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_64_base : receiptBase endpoint_16_64_flag endpoint_16_64_sources = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_w0 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 2 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_w2 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 2 2 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_p4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 4 230863982724969947 = some 230863982724969947 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 2 2 230863982724969947 230863982724969947 230863982724969947 endpoint_16_64_w0 endpoint_16_64_w2
private theorem endpoint_16_64_w4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 4 2 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_p6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 6 230863982724969947 = some 230863982724969947 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 4 2 230863982724969947 230863982724969947 230863982724969947 endpoint_16_64_p4 endpoint_16_64_w4
private theorem endpoint_16_64_w6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 6 2 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_p8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 8 230863982724969947 = some 230863982724969947 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 6 2 230863982724969947 230863982724969947 230863982724969947 endpoint_16_64_p6 endpoint_16_64_w6
private theorem endpoint_16_64_w8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 8 2 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_p10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 10 230863982724969947 = some 230863982724969947 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 8 2 230863982724969947 230863982724969947 230863982724969947 endpoint_16_64_p8 endpoint_16_64_w8
private theorem endpoint_16_64_w10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 10 2 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_p12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 12 230863982724969947 = some 230863982724969947 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 10 2 230863982724969947 230863982724969947 230863982724969947 endpoint_16_64_p10 endpoint_16_64_w10
private theorem endpoint_16_64_w12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 12 2 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_p14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 14 230863982724969947 = some 230863982724969947 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 12 2 230863982724969947 230863982724969947 230863982724969947 endpoint_16_64_p12 endpoint_16_64_w12
private theorem endpoint_16_64_w14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 14 1 230863982724969947 = some 230863982724969947 := by decide +kernel
private theorem endpoint_16_64_p15 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 15 230863982724969947 = some 230863982724969947 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 14 1 230863982724969947 230863982724969947 230863982724969947 endpoint_16_64_p14 endpoint_16_64_w14
def endpoint_16_64 : CertifiedEndpoint :=
  ⟨⟨16, 64, 1964⟩, 230863982724969947, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_64_flag endpoint_16_64_sources 15 230863982724969947 230863982724969947 rfl endpoint_16_64_base endpoint_16_64_p15) (by decide)⟩
private def endpoint_16_65_flag : Flag := ⟨16, 65, 1902⟩
private def endpoint_16_65_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_65_base : receiptBase endpoint_16_65_flag endpoint_16_65_sources = some 226734845711166233 := by decide +kernel
private theorem endpoint_16_65_w0 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 2 226734845711166233 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_w2 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 2 2 227901761566892793 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_p4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 4 226734845711166233 = some 227901761566892793 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 2 2 226734845711166233 227901761566892793 227901761566892793 endpoint_16_65_w0 endpoint_16_65_w2
private theorem endpoint_16_65_w4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 4 2 227901761566892793 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_p6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 6 226734845711166233 = some 227901761566892793 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 4 2 226734845711166233 227901761566892793 227901761566892793 endpoint_16_65_p4 endpoint_16_65_w4
private theorem endpoint_16_65_w6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 6 2 227901761566892793 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_p8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 8 226734845711166233 = some 227901761566892793 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 6 2 226734845711166233 227901761566892793 227901761566892793 endpoint_16_65_p6 endpoint_16_65_w6
private theorem endpoint_16_65_w8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 8 2 227901761566892793 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_p10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 10 226734845711166233 = some 227901761566892793 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 8 2 226734845711166233 227901761566892793 227901761566892793 endpoint_16_65_p8 endpoint_16_65_w8
private theorem endpoint_16_65_w10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 10 2 227901761566892793 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_p12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 12 226734845711166233 = some 227901761566892793 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 10 2 226734845711166233 227901761566892793 227901761566892793 endpoint_16_65_p10 endpoint_16_65_w10
private theorem endpoint_16_65_w12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 12 2 227901761566892793 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_p14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 14 226734845711166233 = some 227901761566892793 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 12 2 226734845711166233 227901761566892793 227901761566892793 endpoint_16_65_p12 endpoint_16_65_w12
private theorem endpoint_16_65_w14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 14 1 227901761566892793 = some 227901761566892793 := by decide +kernel
private theorem endpoint_16_65_p15 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 15 226734845711166233 = some 227901761566892793 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 14 1 226734845711166233 227901761566892793 227901761566892793 endpoint_16_65_p14 endpoint_16_65_w14
def endpoint_16_65 : CertifiedEndpoint :=
  ⟨⟨16, 65, 1902⟩, 227901761566892793, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_65_flag endpoint_16_65_sources 15 226734845711166233 227901761566892793 rfl endpoint_16_65_base endpoint_16_65_p15) (by decide)⟩
private def endpoint_16_66_flag : Flag := ⟨16, 66, 1839⟩
private def endpoint_16_66_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_66_base : receiptBase endpoint_16_66_flag endpoint_16_66_sources = some 222283836736357107 := by decide +kernel
private theorem endpoint_16_66_w0 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 2 222283836736357107 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_w2 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 2 2 227472131870366890 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_p4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 4 222283836736357107 = some 227472131870366890 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 2 2 222283836736357107 227472131870366890 227472131870366890 endpoint_16_66_w0 endpoint_16_66_w2
private theorem endpoint_16_66_w4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 4 2 227472131870366890 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_p6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 6 222283836736357107 = some 227472131870366890 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 4 2 222283836736357107 227472131870366890 227472131870366890 endpoint_16_66_p4 endpoint_16_66_w4
private theorem endpoint_16_66_w6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 6 2 227472131870366890 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_p8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 8 222283836736357107 = some 227472131870366890 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 6 2 222283836736357107 227472131870366890 227472131870366890 endpoint_16_66_p6 endpoint_16_66_w6
private theorem endpoint_16_66_w8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 8 2 227472131870366890 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_p10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 10 222283836736357107 = some 227472131870366890 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 8 2 222283836736357107 227472131870366890 227472131870366890 endpoint_16_66_p8 endpoint_16_66_w8
private theorem endpoint_16_66_w10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 10 2 227472131870366890 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_p12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 12 222283836736357107 = some 227472131870366890 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 10 2 222283836736357107 227472131870366890 227472131870366890 endpoint_16_66_p10 endpoint_16_66_w10
private theorem endpoint_16_66_w12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 12 2 227472131870366890 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_p14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 14 222283836736357107 = some 227472131870366890 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 12 2 222283836736357107 227472131870366890 227472131870366890 endpoint_16_66_p12 endpoint_16_66_w12
private theorem endpoint_16_66_w14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 14 1 227472131870366890 = some 227472131870366890 := by decide +kernel
private theorem endpoint_16_66_p15 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 15 222283836736357107 = some 227472131870366890 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 14 1 222283836736357107 227472131870366890 227472131870366890 endpoint_16_66_p14 endpoint_16_66_w14
def endpoint_16_66 : CertifiedEndpoint :=
  ⟨⟨16, 66, 1839⟩, 227472131870366890, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_66_flag endpoint_16_66_sources 15 222283836736357107 227472131870366890 rfl endpoint_16_66_base endpoint_16_66_p15) (by decide)⟩
private def endpoint_16_67_flag : Flag := ⟨16, 67, 1774⟩
private def endpoint_16_67_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_67_base : receiptBase endpoint_16_67_flag endpoint_16_67_sources = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_w0 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 2 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_w2 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 2 2 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_p4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 4 219145837883653232 = some 219145837883653232 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 2 2 219145837883653232 219145837883653232 219145837883653232 endpoint_16_67_w0 endpoint_16_67_w2
private theorem endpoint_16_67_w4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 4 2 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_p6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 6 219145837883653232 = some 219145837883653232 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 4 2 219145837883653232 219145837883653232 219145837883653232 endpoint_16_67_p4 endpoint_16_67_w4
private theorem endpoint_16_67_w6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 6 2 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_p8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 8 219145837883653232 = some 219145837883653232 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 6 2 219145837883653232 219145837883653232 219145837883653232 endpoint_16_67_p6 endpoint_16_67_w6
private theorem endpoint_16_67_w8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 8 2 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_p10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 10 219145837883653232 = some 219145837883653232 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 8 2 219145837883653232 219145837883653232 219145837883653232 endpoint_16_67_p8 endpoint_16_67_w8
private theorem endpoint_16_67_w10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 10 2 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_p12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 12 219145837883653232 = some 219145837883653232 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 10 2 219145837883653232 219145837883653232 219145837883653232 endpoint_16_67_p10 endpoint_16_67_w10
private theorem endpoint_16_67_w12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 12 2 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_p14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 14 219145837883653232 = some 219145837883653232 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 12 2 219145837883653232 219145837883653232 219145837883653232 endpoint_16_67_p12 endpoint_16_67_w12
private theorem endpoint_16_67_w14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 14 1 219145837883653232 = some 219145837883653232 := by decide +kernel
private theorem endpoint_16_67_p15 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 15 219145837883653232 = some 219145837883653232 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 14 1 219145837883653232 219145837883653232 219145837883653232 endpoint_16_67_p14 endpoint_16_67_w14
def endpoint_16_67 : CertifiedEndpoint :=
  ⟨⟨16, 67, 1774⟩, 219145837883653232, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_67_flag endpoint_16_67_sources 15 219145837883653232 219145837883653232 rfl endpoint_16_67_base endpoint_16_67_p15) (by decide)⟩
private def endpoint_16_68_flag : Flag := ⟨16, 68, 1707⟩
private def endpoint_16_68_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_68_base : receiptBase endpoint_16_68_flag endpoint_16_68_sources = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_w0 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 2 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_w2 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 2 2 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_p4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 4 213732074090372635 = some 213732074090372635 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 2 2 213732074090372635 213732074090372635 213732074090372635 endpoint_16_68_w0 endpoint_16_68_w2
private theorem endpoint_16_68_w4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 4 2 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_p6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 6 213732074090372635 = some 213732074090372635 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 4 2 213732074090372635 213732074090372635 213732074090372635 endpoint_16_68_p4 endpoint_16_68_w4
private theorem endpoint_16_68_w6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 6 2 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_p8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 8 213732074090372635 = some 213732074090372635 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 6 2 213732074090372635 213732074090372635 213732074090372635 endpoint_16_68_p6 endpoint_16_68_w6
private theorem endpoint_16_68_w8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 8 2 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_p10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 10 213732074090372635 = some 213732074090372635 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 8 2 213732074090372635 213732074090372635 213732074090372635 endpoint_16_68_p8 endpoint_16_68_w8
private theorem endpoint_16_68_w10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 10 2 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_p12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 12 213732074090372635 = some 213732074090372635 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 10 2 213732074090372635 213732074090372635 213732074090372635 endpoint_16_68_p10 endpoint_16_68_w10
private theorem endpoint_16_68_w12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 12 2 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_p14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 14 213732074090372635 = some 213732074090372635 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 12 2 213732074090372635 213732074090372635 213732074090372635 endpoint_16_68_p12 endpoint_16_68_w12
private theorem endpoint_16_68_w14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 14 1 213732074090372635 = some 213732074090372635 := by decide +kernel
private theorem endpoint_16_68_p15 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 15 213732074090372635 = some 213732074090372635 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 14 1 213732074090372635 213732074090372635 213732074090372635 endpoint_16_68_p14 endpoint_16_68_w14
def endpoint_16_68 : CertifiedEndpoint :=
  ⟨⟨16, 68, 1707⟩, 213732074090372635, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_68_flag endpoint_16_68_sources 15 213732074090372635 213732074090372635 rfl endpoint_16_68_base endpoint_16_68_p15) (by decide)⟩
private def endpoint_16_69_flag : Flag := ⟨16, 69, 1638⟩
private def endpoint_16_69_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_69_base : receiptBase endpoint_16_69_flag endpoint_16_69_sources = some 207847822147261181 := by decide +kernel
private theorem endpoint_16_69_w0 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 2 207847822147261181 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_w2 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 2 2 208125383917898492 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_p4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 4 207847822147261181 = some 208125383917898492 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 2 2 207847822147261181 208125383917898492 208125383917898492 endpoint_16_69_w0 endpoint_16_69_w2
private theorem endpoint_16_69_w4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 4 2 208125383917898492 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_p6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 6 207847822147261181 = some 208125383917898492 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 4 2 207847822147261181 208125383917898492 208125383917898492 endpoint_16_69_p4 endpoint_16_69_w4
private theorem endpoint_16_69_w6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 6 2 208125383917898492 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_p8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 8 207847822147261181 = some 208125383917898492 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 6 2 207847822147261181 208125383917898492 208125383917898492 endpoint_16_69_p6 endpoint_16_69_w6
private theorem endpoint_16_69_w8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 8 2 208125383917898492 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_p10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 10 207847822147261181 = some 208125383917898492 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 8 2 207847822147261181 208125383917898492 208125383917898492 endpoint_16_69_p8 endpoint_16_69_w8
private theorem endpoint_16_69_w10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 10 2 208125383917898492 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_p12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 12 207847822147261181 = some 208125383917898492 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 10 2 207847822147261181 208125383917898492 208125383917898492 endpoint_16_69_p10 endpoint_16_69_w10
private theorem endpoint_16_69_w12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 12 2 208125383917898492 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_p14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 14 207847822147261181 = some 208125383917898492 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 12 2 207847822147261181 208125383917898492 208125383917898492 endpoint_16_69_p12 endpoint_16_69_w12
private theorem endpoint_16_69_w14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 14 1 208125383917898492 = some 208125383917898492 := by decide +kernel
private theorem endpoint_16_69_p15 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 15 207847822147261181 = some 208125383917898492 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 14 1 207847822147261181 208125383917898492 208125383917898492 endpoint_16_69_p14 endpoint_16_69_w14
def endpoint_16_69 : CertifiedEndpoint :=
  ⟨⟨16, 69, 1638⟩, 208125383917898492, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_69_flag endpoint_16_69_sources 15 207847822147261181 208125383917898492 rfl endpoint_16_69_base endpoint_16_69_p15) (by decide)⟩
private def endpoint_16_70_flag : Flag := ⟨16, 70, 1567⟩
private def endpoint_16_70_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_16_70_base : receiptBase endpoint_16_70_flag endpoint_16_70_sources = some 201791429364650011 := by decide +kernel
private theorem endpoint_16_70_w0 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 2 201791429364650011 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_w2 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 2 2 203097249715419416 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_p4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 4 201791429364650011 = some 203097249715419416 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 2 2 201791429364650011 203097249715419416 203097249715419416 endpoint_16_70_w0 endpoint_16_70_w2
private theorem endpoint_16_70_w4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 4 2 203097249715419416 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_p6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 6 201791429364650011 = some 203097249715419416 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 4 2 201791429364650011 203097249715419416 203097249715419416 endpoint_16_70_p4 endpoint_16_70_w4
private theorem endpoint_16_70_w6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 6 2 203097249715419416 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_p8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 8 201791429364650011 = some 203097249715419416 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 6 2 201791429364650011 203097249715419416 203097249715419416 endpoint_16_70_p6 endpoint_16_70_w6
private theorem endpoint_16_70_w8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 8 2 203097249715419416 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_p10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 10 201791429364650011 = some 203097249715419416 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 8 2 201791429364650011 203097249715419416 203097249715419416 endpoint_16_70_p8 endpoint_16_70_w8
private theorem endpoint_16_70_w10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 10 2 203097249715419416 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_p12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 12 201791429364650011 = some 203097249715419416 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 10 2 201791429364650011 203097249715419416 203097249715419416 endpoint_16_70_p10 endpoint_16_70_w10
private theorem endpoint_16_70_w12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 12 2 203097249715419416 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_p14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 14 201791429364650011 = some 203097249715419416 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 12 2 201791429364650011 203097249715419416 203097249715419416 endpoint_16_70_p12 endpoint_16_70_w12
private theorem endpoint_16_70_w14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 14 1 203097249715419416 = some 203097249715419416 := by decide +kernel
private theorem endpoint_16_70_p15 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 15 201791429364650011 = some 203097249715419416 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 14 1 201791429364650011 203097249715419416 203097249715419416 endpoint_16_70_p14 endpoint_16_70_w14
def endpoint_16_70 : CertifiedEndpoint :=
  ⟨⟨16, 70, 1567⟩, 203097249715419416, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_16_70_flag endpoint_16_70_sources 15 201791429364650011 203097249715419416 rfl endpoint_16_70_base endpoint_16_70_p15) (by decide)⟩
private def endpoint_16_71_flag : Flag := ⟨16, 71, 1493⟩
private def endpoint_16_71_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_16_71_base : receiptBase endpoint_16_71_flag endpoint_16_71_sources = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_w0 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 2 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_w2 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 2 2 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_p4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 4 196173170254560896 = some 196173170254560896 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 2 2 196173170254560896 196173170254560896 196173170254560896 endpoint_16_71_w0 endpoint_16_71_w2
private theorem endpoint_16_71_w4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 4 2 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_p6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 6 196173170254560896 = some 196173170254560896 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 4 2 196173170254560896 196173170254560896 196173170254560896 endpoint_16_71_p4 endpoint_16_71_w4
private theorem endpoint_16_71_w6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 6 2 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_p8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 8 196173170254560896 = some 196173170254560896 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 6 2 196173170254560896 196173170254560896 196173170254560896 endpoint_16_71_p6 endpoint_16_71_w6
private theorem endpoint_16_71_w8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 8 2 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_p10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 10 196173170254560896 = some 196173170254560896 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 8 2 196173170254560896 196173170254560896 196173170254560896 endpoint_16_71_p8 endpoint_16_71_w8
private theorem endpoint_16_71_w10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 10 2 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_p12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 12 196173170254560896 = some 196173170254560896 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 10 2 196173170254560896 196173170254560896 196173170254560896 endpoint_16_71_p10 endpoint_16_71_w10
private theorem endpoint_16_71_w12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 12 2 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_p14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 14 196173170254560896 = some 196173170254560896 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 12 2 196173170254560896 196173170254560896 196173170254560896 endpoint_16_71_p12 endpoint_16_71_w12
private theorem endpoint_16_71_w14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 14 1 196173170254560896 = some 196173170254560896 := by decide +kernel
private theorem endpoint_16_71_p15 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 15 196173170254560896 = some 196173170254560896 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 14 1 196173170254560896 196173170254560896 196173170254560896 endpoint_16_71_p14 endpoint_16_71_w14
def endpoint_16_71 : CertifiedEndpoint :=
  ⟨⟨16, 71, 1493⟩, 196173170254560896, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_16_71_flag endpoint_16_71_sources 15 196173170254560896 196173170254560896 rfl endpoint_16_71_base endpoint_16_71_p15) (by decide)⟩
private def endpoint_16_72_flag : Flag := ⟨16, 72, 1417⟩
private def endpoint_16_72_sources : Sources := ⟨contact31, contact21, contact22⟩
private theorem endpoint_16_72_base : receiptBase endpoint_16_72_flag endpoint_16_72_sources = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_w0 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 2 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_w2 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 2 2 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_p4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 4 189438082075637767 = some 189438082075637767 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 2 2 189438082075637767 189438082075637767 189438082075637767 endpoint_16_72_w0 endpoint_16_72_w2
private theorem endpoint_16_72_w4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 4 2 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_p6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 6 189438082075637767 = some 189438082075637767 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 4 2 189438082075637767 189438082075637767 189438082075637767 endpoint_16_72_p4 endpoint_16_72_w4
private theorem endpoint_16_72_w6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 6 2 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_p8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 8 189438082075637767 = some 189438082075637767 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 6 2 189438082075637767 189438082075637767 189438082075637767 endpoint_16_72_p6 endpoint_16_72_w6
private theorem endpoint_16_72_w8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 8 2 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_p10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 10 189438082075637767 = some 189438082075637767 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 8 2 189438082075637767 189438082075637767 189438082075637767 endpoint_16_72_p8 endpoint_16_72_w8
private theorem endpoint_16_72_w10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 10 2 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_p12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 12 189438082075637767 = some 189438082075637767 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 10 2 189438082075637767 189438082075637767 189438082075637767 endpoint_16_72_p10 endpoint_16_72_w10
private theorem endpoint_16_72_w12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 12 2 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_p14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 14 189438082075637767 = some 189438082075637767 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 12 2 189438082075637767 189438082075637767 189438082075637767 endpoint_16_72_p12 endpoint_16_72_w12
private theorem endpoint_16_72_w14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 14 1 189438082075637767 = some 189438082075637767 := by decide +kernel
private theorem endpoint_16_72_p15 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 15 189438082075637767 = some 189438082075637767 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 14 1 189438082075637767 189438082075637767 189438082075637767 endpoint_16_72_p14 endpoint_16_72_w14
def endpoint_16_72 : CertifiedEndpoint :=
  ⟨⟨16, 72, 1417⟩, 189438082075637767, .terminal ⟨contact31, contact21, contact22⟩ (finish_receipt_window endpoint_16_72_flag endpoint_16_72_sources 15 189438082075637767 189438082075637767 rfl endpoint_16_72_base endpoint_16_72_p15) (by decide)⟩
private def endpoint_16_73_flag : Flag := ⟨16, 73, 1339⟩
private def endpoint_16_73_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_73_base : receiptBase endpoint_16_73_flag endpoint_16_73_sources = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_w0 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 2 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_w2 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 2 2 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_p4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 4 182267167825763472 = some 182267167825763472 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 2 2 182267167825763472 182267167825763472 182267167825763472 endpoint_16_73_w0 endpoint_16_73_w2
private theorem endpoint_16_73_w4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 4 2 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_p6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 6 182267167825763472 = some 182267167825763472 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 4 2 182267167825763472 182267167825763472 182267167825763472 endpoint_16_73_p4 endpoint_16_73_w4
private theorem endpoint_16_73_w6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 6 2 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_p8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 8 182267167825763472 = some 182267167825763472 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 6 2 182267167825763472 182267167825763472 182267167825763472 endpoint_16_73_p6 endpoint_16_73_w6
private theorem endpoint_16_73_w8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 8 2 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_p10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 10 182267167825763472 = some 182267167825763472 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 8 2 182267167825763472 182267167825763472 182267167825763472 endpoint_16_73_p8 endpoint_16_73_w8
private theorem endpoint_16_73_w10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 10 2 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_p12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 12 182267167825763472 = some 182267167825763472 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 10 2 182267167825763472 182267167825763472 182267167825763472 endpoint_16_73_p10 endpoint_16_73_w10
private theorem endpoint_16_73_w12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 12 2 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_p14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 14 182267167825763472 = some 182267167825763472 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 12 2 182267167825763472 182267167825763472 182267167825763472 endpoint_16_73_p12 endpoint_16_73_w12
private theorem endpoint_16_73_w14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 14 1 182267167825763472 = some 182267167825763472 := by decide +kernel
private theorem endpoint_16_73_p15 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 15 182267167825763472 = some 182267167825763472 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 14 1 182267167825763472 182267167825763472 182267167825763472 endpoint_16_73_p14 endpoint_16_73_w14
def endpoint_16_73 : CertifiedEndpoint :=
  ⟨⟨16, 73, 1339⟩, 182267167825763472, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_73_flag endpoint_16_73_sources 15 182267167825763472 182267167825763472 rfl endpoint_16_73_base endpoint_16_73_p15) (by decide)⟩
private def endpoint_16_74_flag : Flag := ⟨16, 74, 1259⟩
private def endpoint_16_74_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_74_base : receiptBase endpoint_16_74_flag endpoint_16_74_sources = some 173567715968706081 := by decide +kernel
private theorem endpoint_16_74_w0 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 2 173567715968706081 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_w2 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 2 2 173688349927821400 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_p4 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 4 173567715968706081 = some 173688349927821400 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 2 2 173567715968706081 173688349927821400 173688349927821400 endpoint_16_74_w0 endpoint_16_74_w2
private theorem endpoint_16_74_w4 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 4 2 173688349927821400 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_p6 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 6 173567715968706081 = some 173688349927821400 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 4 2 173567715968706081 173688349927821400 173688349927821400 endpoint_16_74_p4 endpoint_16_74_w4
private theorem endpoint_16_74_w6 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 6 2 173688349927821400 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_p8 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 8 173567715968706081 = some 173688349927821400 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 6 2 173567715968706081 173688349927821400 173688349927821400 endpoint_16_74_p6 endpoint_16_74_w6
private theorem endpoint_16_74_w8 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 8 2 173688349927821400 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_p10 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 10 173567715968706081 = some 173688349927821400 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 8 2 173567715968706081 173688349927821400 173688349927821400 endpoint_16_74_p8 endpoint_16_74_w8
private theorem endpoint_16_74_w10 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 10 2 173688349927821400 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_p12 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 12 173567715968706081 = some 173688349927821400 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 10 2 173567715968706081 173688349927821400 173688349927821400 endpoint_16_74_p10 endpoint_16_74_w10
private theorem endpoint_16_74_w12 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 12 2 173688349927821400 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_p14 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 14 173567715968706081 = some 173688349927821400 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 12 2 173567715968706081 173688349927821400 173688349927821400 endpoint_16_74_p12 endpoint_16_74_w12
private theorem endpoint_16_74_w14 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 14 1 173688349927821400 = some 173688349927821400 := by decide +kernel
private theorem endpoint_16_74_p15 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 15 173567715968706081 = some 173688349927821400 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 14 1 173567715968706081 173688349927821400 173688349927821400 endpoint_16_74_p14 endpoint_16_74_w14
def endpoint_16_74 : CertifiedEndpoint :=
  ⟨⟨16, 74, 1259⟩, 173688349927821400, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_74_flag endpoint_16_74_sources 15 173567715968706081 173688349927821400 rfl endpoint_16_74_base endpoint_16_74_p15) (by decide)⟩
private def endpoint_16_75_flag : Flag := ⟨16, 75, 1176⟩
private def endpoint_16_75_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_75_base : receiptBase endpoint_16_75_flag endpoint_16_75_sources = some 164193918727192072 := by decide +kernel
private theorem endpoint_16_75_w0 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 2 164193918727192072 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_w2 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 2 2 169531376456076852 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_p4 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 4 164193918727192072 = some 169531376456076852 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 2 2 164193918727192072 169531376456076852 169531376456076852 endpoint_16_75_w0 endpoint_16_75_w2
private theorem endpoint_16_75_w4 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 4 2 169531376456076852 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_p6 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 6 164193918727192072 = some 169531376456076852 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 4 2 164193918727192072 169531376456076852 169531376456076852 endpoint_16_75_p4 endpoint_16_75_w4
private theorem endpoint_16_75_w6 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 6 2 169531376456076852 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_p8 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 8 164193918727192072 = some 169531376456076852 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 6 2 164193918727192072 169531376456076852 169531376456076852 endpoint_16_75_p6 endpoint_16_75_w6
private theorem endpoint_16_75_w8 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 8 2 169531376456076852 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_p10 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 10 164193918727192072 = some 169531376456076852 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 8 2 164193918727192072 169531376456076852 169531376456076852 endpoint_16_75_p8 endpoint_16_75_w8
private theorem endpoint_16_75_w10 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 10 2 169531376456076852 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_p12 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 12 164193918727192072 = some 169531376456076852 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 10 2 164193918727192072 169531376456076852 169531376456076852 endpoint_16_75_p10 endpoint_16_75_w10
private theorem endpoint_16_75_w12 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 12 2 169531376456076852 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_p14 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 14 164193918727192072 = some 169531376456076852 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 12 2 164193918727192072 169531376456076852 169531376456076852 endpoint_16_75_p12 endpoint_16_75_w12
private theorem endpoint_16_75_w14 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 14 1 169531376456076852 = some 169531376456076852 := by decide +kernel
private theorem endpoint_16_75_p15 : receiptWindow endpoint_16_75_flag endpoint_16_75_sources 0 15 164193918727192072 = some 169531376456076852 :=
  join_receipt_window endpoint_16_75_flag endpoint_16_75_sources 0 14 1 164193918727192072 169531376456076852 169531376456076852 endpoint_16_75_p14 endpoint_16_75_w14
def endpoint_16_75 : CertifiedEndpoint :=
  ⟨⟨16, 75, 1176⟩, 169531376456076852, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_75_flag endpoint_16_75_sources 15 164193918727192072 169531376456076852 rfl endpoint_16_75_base endpoint_16_75_p15) (by decide)⟩
private def endpoint_16_76_flag : Flag := ⟨16, 76, 1090⟩
private def endpoint_16_76_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_76_base : receiptBase endpoint_16_76_flag endpoint_16_76_sources = some 154131137857098073 := by decide +kernel
private theorem endpoint_16_76_w0 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 2 154131137857098073 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_w2 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 2 2 164920688357523956 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_p4 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 4 154131137857098073 = some 164920688357523956 :=
  join_receipt_window endpoint_16_76_flag endpoint_16_76_sources 0 2 2 154131137857098073 164920688357523956 164920688357523956 endpoint_16_76_w0 endpoint_16_76_w2
private theorem endpoint_16_76_w4 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 4 2 164920688357523956 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_p6 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 6 154131137857098073 = some 164920688357523956 :=
  join_receipt_window endpoint_16_76_flag endpoint_16_76_sources 0 4 2 154131137857098073 164920688357523956 164920688357523956 endpoint_16_76_p4 endpoint_16_76_w4
private theorem endpoint_16_76_w6 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 6 2 164920688357523956 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_p8 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 8 154131137857098073 = some 164920688357523956 :=
  join_receipt_window endpoint_16_76_flag endpoint_16_76_sources 0 6 2 154131137857098073 164920688357523956 164920688357523956 endpoint_16_76_p6 endpoint_16_76_w6
private theorem endpoint_16_76_w8 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 8 2 164920688357523956 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_p10 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 10 154131137857098073 = some 164920688357523956 :=
  join_receipt_window endpoint_16_76_flag endpoint_16_76_sources 0 8 2 154131137857098073 164920688357523956 164920688357523956 endpoint_16_76_p8 endpoint_16_76_w8
private theorem endpoint_16_76_w10 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 10 2 164920688357523956 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_p12 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 12 154131137857098073 = some 164920688357523956 :=
  join_receipt_window endpoint_16_76_flag endpoint_16_76_sources 0 10 2 154131137857098073 164920688357523956 164920688357523956 endpoint_16_76_p10 endpoint_16_76_w10
private theorem endpoint_16_76_w12 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 12 2 164920688357523956 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_p14 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 14 154131137857098073 = some 164920688357523956 :=
  join_receipt_window endpoint_16_76_flag endpoint_16_76_sources 0 12 2 154131137857098073 164920688357523956 164920688357523956 endpoint_16_76_p12 endpoint_16_76_w12
private theorem endpoint_16_76_w14 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 14 1 164920688357523956 = some 164920688357523956 := by decide +kernel
private theorem endpoint_16_76_p15 : receiptWindow endpoint_16_76_flag endpoint_16_76_sources 0 15 154131137857098073 = some 164920688357523956 :=
  join_receipt_window endpoint_16_76_flag endpoint_16_76_sources 0 14 1 154131137857098073 164920688357523956 164920688357523956 endpoint_16_76_p14 endpoint_16_76_w14
def endpoint_16_76 : CertifiedEndpoint :=
  ⟨⟨16, 76, 1090⟩, 164920688357523956, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_76_flag endpoint_16_76_sources 15 154131137857098073 164920688357523956 rfl endpoint_16_76_base endpoint_16_76_p15) (by decide)⟩
private def endpoint_16_77_flag : Flag := ⟨16, 77, 1002⟩
private def endpoint_16_77_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_77_base : receiptBase endpoint_16_77_flag endpoint_16_77_sources = some 143505482544707639 := by decide +kernel
private theorem endpoint_16_77_w0 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 2 143505482544707639 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_w2 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 2 2 159928477276968528 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_p4 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 4 143505482544707639 = some 159928477276968528 :=
  join_receipt_window endpoint_16_77_flag endpoint_16_77_sources 0 2 2 143505482544707639 159928477276968528 159928477276968528 endpoint_16_77_w0 endpoint_16_77_w2
private theorem endpoint_16_77_w4 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 4 2 159928477276968528 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_p6 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 6 143505482544707639 = some 159928477276968528 :=
  join_receipt_window endpoint_16_77_flag endpoint_16_77_sources 0 4 2 143505482544707639 159928477276968528 159928477276968528 endpoint_16_77_p4 endpoint_16_77_w4
private theorem endpoint_16_77_w6 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 6 2 159928477276968528 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_p8 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 8 143505482544707639 = some 159928477276968528 :=
  join_receipt_window endpoint_16_77_flag endpoint_16_77_sources 0 6 2 143505482544707639 159928477276968528 159928477276968528 endpoint_16_77_p6 endpoint_16_77_w6
private theorem endpoint_16_77_w8 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 8 2 159928477276968528 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_p10 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 10 143505482544707639 = some 159928477276968528 :=
  join_receipt_window endpoint_16_77_flag endpoint_16_77_sources 0 8 2 143505482544707639 159928477276968528 159928477276968528 endpoint_16_77_p8 endpoint_16_77_w8
private theorem endpoint_16_77_w10 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 10 2 159928477276968528 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_p12 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 12 143505482544707639 = some 159928477276968528 :=
  join_receipt_window endpoint_16_77_flag endpoint_16_77_sources 0 10 2 143505482544707639 159928477276968528 159928477276968528 endpoint_16_77_p10 endpoint_16_77_w10
private theorem endpoint_16_77_w12 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 12 2 159928477276968528 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_p14 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 14 143505482544707639 = some 159928477276968528 :=
  join_receipt_window endpoint_16_77_flag endpoint_16_77_sources 0 12 2 143505482544707639 159928477276968528 159928477276968528 endpoint_16_77_p12 endpoint_16_77_w12
private theorem endpoint_16_77_w14 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 14 1 159928477276968528 = some 159928477276968528 := by decide +kernel
private theorem endpoint_16_77_p15 : receiptWindow endpoint_16_77_flag endpoint_16_77_sources 0 15 143505482544707639 = some 159928477276968528 :=
  join_receipt_window endpoint_16_77_flag endpoint_16_77_sources 0 14 1 143505482544707639 159928477276968528 159928477276968528 endpoint_16_77_p14 endpoint_16_77_w14
def endpoint_16_77 : CertifiedEndpoint :=
  ⟨⟨16, 77, 1002⟩, 159928477276968528, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_77_flag endpoint_16_77_sources 15 143505482544707639 159928477276968528 rfl endpoint_16_77_base endpoint_16_77_p15) (by decide)⟩
def endpoint_16_78 : CertifiedEndpoint :=
  ⟨⟨16, 78, 911⟩, 241463948680374293, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock10 : List CertifiedEndpoint := [
  endpoint_15_22, endpoint_15_23, endpoint_15_24, endpoint_15_25, endpoint_15_26, endpoint_15_27, endpoint_15_28,
  endpoint_15_29, endpoint_15_30, endpoint_15_31, endpoint_15_32, endpoint_15_33, endpoint_15_34, endpoint_15_35,
  endpoint_15_36, endpoint_15_37, endpoint_15_38, endpoint_15_39, endpoint_15_40, endpoint_15_41, endpoint_15_42,
  endpoint_15_43, endpoint_15_44, endpoint_15_45, endpoint_15_46, endpoint_15_47, endpoint_15_48, endpoint_15_49,
  endpoint_15_50, endpoint_15_51, endpoint_15_52, endpoint_15_53, endpoint_15_54, endpoint_15_55, endpoint_15_56,
  endpoint_15_57, endpoint_15_58, endpoint_15_59, endpoint_15_60, endpoint_15_61, endpoint_15_62, endpoint_15_63,
  endpoint_15_64, endpoint_15_65, endpoint_15_66, endpoint_15_67, endpoint_15_68, endpoint_15_69, endpoint_15_70,
  endpoint_15_71, endpoint_15_72, endpoint_15_73, endpoint_15_74, endpoint_15_75, endpoint_15_76, endpoint_15_77,
  endpoint_15_78, endpoint_15_79, endpoint_15_80, endpoint_15_81, endpoint_15_82, endpoint_15_83, endpoint_15_84,
  endpoint_15_85, endpoint_15_86, endpoint_15_87, endpoint_15_88, endpoint_16_16, endpoint_16_17, endpoint_16_18,
  endpoint_16_19, endpoint_16_20, endpoint_16_21, endpoint_16_22, endpoint_16_23, endpoint_16_24, endpoint_16_25,
  endpoint_16_26, endpoint_16_27, endpoint_16_28, endpoint_16_29, endpoint_16_30, endpoint_16_31, endpoint_16_32,
  endpoint_16_33, endpoint_16_34, endpoint_16_35, endpoint_16_36, endpoint_16_37, endpoint_16_38, endpoint_16_39,
  endpoint_16_40, endpoint_16_41, endpoint_16_42, endpoint_16_43, endpoint_16_44, endpoint_16_45, endpoint_16_46,
  endpoint_16_47, endpoint_16_48, endpoint_16_49, endpoint_16_50, endpoint_16_51, endpoint_16_52, endpoint_16_53,
  endpoint_16_54, endpoint_16_55, endpoint_16_56, endpoint_16_57, endpoint_16_58, endpoint_16_59, endpoint_16_60,
  endpoint_16_61, endpoint_16_62, endpoint_16_63, endpoint_16_64, endpoint_16_65, endpoint_16_66, endpoint_16_67,
  endpoint_16_68, endpoint_16_69, endpoint_16_70, endpoint_16_71, endpoint_16_72, endpoint_16_73, endpoint_16_74,
  endpoint_16_75, endpoint_16_76, endpoint_16_77, endpoint_16_78
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
