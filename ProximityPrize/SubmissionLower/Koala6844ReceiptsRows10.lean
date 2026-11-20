import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_14_56_flag : Flag := ⟨14, 56, 2881⟩
private def endpoint_14_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_56_base : receiptBase endpoint_14_56_flag endpoint_14_56_sources = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_w0 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 2 260801786564379551 = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_w2 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 2 2 260801786564379551 = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_p4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 4 260801786564379551 = some 260801786564379551 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 2 2 260801786564379551 260801786564379551 260801786564379551 endpoint_14_56_w0 endpoint_14_56_w2
private theorem endpoint_14_56_w4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 4 2 260801786564379551 = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_p6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 6 260801786564379551 = some 260801786564379551 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 4 2 260801786564379551 260801786564379551 260801786564379551 endpoint_14_56_p4 endpoint_14_56_w4
private theorem endpoint_14_56_w6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 6 2 260801786564379551 = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_p8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 8 260801786564379551 = some 260801786564379551 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 6 2 260801786564379551 260801786564379551 260801786564379551 endpoint_14_56_p6 endpoint_14_56_w6
private theorem endpoint_14_56_w8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 8 2 260801786564379551 = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_p10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 10 260801786564379551 = some 260801786564379551 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 8 2 260801786564379551 260801786564379551 260801786564379551 endpoint_14_56_p8 endpoint_14_56_w8
private theorem endpoint_14_56_w10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 10 2 260801786564379551 = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_p12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 12 260801786564379551 = some 260801786564379551 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 10 2 260801786564379551 260801786564379551 260801786564379551 endpoint_14_56_p10 endpoint_14_56_w10
private theorem endpoint_14_56_w12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 12 1 260801786564379551 = some 260801786564379551 := by decide +kernel
private theorem endpoint_14_56_p13 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 13 260801786564379551 = some 260801786564379551 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 12 1 260801786564379551 260801786564379551 260801786564379551 endpoint_14_56_p12 endpoint_14_56_w12
def endpoint_14_56 : CertifiedEndpoint :=
  ⟨⟨14, 56, 2881⟩, 260801786564379551, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_56_flag endpoint_14_56_sources 13 260801786564379551 260801786564379551 rfl endpoint_14_56_base endpoint_14_56_p13) (by decide)⟩
private def endpoint_14_57_flag : Flag := ⟨14, 57, 2825⟩
private def endpoint_14_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_57_base : receiptBase endpoint_14_57_flag endpoint_14_57_sources = some 259807703480420006 := by decide +kernel
private theorem endpoint_14_57_w0 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 2 259807703480420006 = some 261772277258648381 := by decide +kernel
private theorem endpoint_14_57_w2 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 2 2 261772277258648381 = some 261772277258648381 := by decide +kernel
private theorem endpoint_14_57_p4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 4 259807703480420006 = some 261772277258648381 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 2 2 259807703480420006 261772277258648381 261772277258648381 endpoint_14_57_w0 endpoint_14_57_w2
private theorem endpoint_14_57_w4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 4 2 261772277258648381 = some 261772277258648381 := by decide +kernel
private theorem endpoint_14_57_p6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 6 259807703480420006 = some 261772277258648381 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 4 2 259807703480420006 261772277258648381 261772277258648381 endpoint_14_57_p4 endpoint_14_57_w4
private theorem endpoint_14_57_w6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 6 2 261772277258648381 = some 261772277258648381 := by decide +kernel
private theorem endpoint_14_57_p8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 8 259807703480420006 = some 261772277258648381 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 6 2 259807703480420006 261772277258648381 261772277258648381 endpoint_14_57_p6 endpoint_14_57_w6
private theorem endpoint_14_57_w8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 8 2 261772277258648381 = some 261772277258648381 := by decide +kernel
private theorem endpoint_14_57_p10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 10 259807703480420006 = some 261772277258648381 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 8 2 259807703480420006 261772277258648381 261772277258648381 endpoint_14_57_p8 endpoint_14_57_w8
private theorem endpoint_14_57_w10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 10 2 261772277258648381 = some 261772277258648381 := by decide +kernel
private theorem endpoint_14_57_p12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 12 259807703480420006 = some 261772277258648381 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 10 2 259807703480420006 261772277258648381 261772277258648381 endpoint_14_57_p10 endpoint_14_57_w10
private theorem endpoint_14_57_w12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 12 1 261772277258648381 = some 261772277258648381 := by decide +kernel
private theorem endpoint_14_57_p13 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 13 259807703480420006 = some 261772277258648381 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 12 1 259807703480420006 261772277258648381 261772277258648381 endpoint_14_57_p12 endpoint_14_57_w12
def endpoint_14_57 : CertifiedEndpoint :=
  ⟨⟨14, 57, 2825⟩, 261772277258648381, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_57_flag endpoint_14_57_sources 13 259807703480420006 261772277258648381 rfl endpoint_14_57_base endpoint_14_57_p13) (by decide)⟩
private def endpoint_14_58_flag : Flag := ⟨14, 58, 2767⟩
private def endpoint_14_58_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_58_base : receiptBase endpoint_14_58_flag endpoint_14_58_sources = some 258470062199508261 := by decide +kernel
private theorem endpoint_14_58_w0 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 2 258470062199508261 = some 263983620746230048 := by decide +kernel
private theorem endpoint_14_58_w2 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 2 2 263983620746230048 = some 263983620746230048 := by decide +kernel
private theorem endpoint_14_58_p4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 4 258470062199508261 = some 263983620746230048 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 2 2 258470062199508261 263983620746230048 263983620746230048 endpoint_14_58_w0 endpoint_14_58_w2
private theorem endpoint_14_58_w4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 4 2 263983620746230048 = some 263983620746230048 := by decide +kernel
private theorem endpoint_14_58_p6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 6 258470062199508261 = some 263983620746230048 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 4 2 258470062199508261 263983620746230048 263983620746230048 endpoint_14_58_p4 endpoint_14_58_w4
private theorem endpoint_14_58_w6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 6 2 263983620746230048 = some 263983620746230048 := by decide +kernel
private theorem endpoint_14_58_p8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 8 258470062199508261 = some 263983620746230048 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 6 2 258470062199508261 263983620746230048 263983620746230048 endpoint_14_58_p6 endpoint_14_58_w6
private theorem endpoint_14_58_w8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 8 2 263983620746230048 = some 263983620746230048 := by decide +kernel
private theorem endpoint_14_58_p10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 10 258470062199508261 = some 263983620746230048 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 8 2 258470062199508261 263983620746230048 263983620746230048 endpoint_14_58_p8 endpoint_14_58_w8
private theorem endpoint_14_58_w10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 10 2 263983620746230048 = some 263983620746230048 := by decide +kernel
private theorem endpoint_14_58_p12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 12 258470062199508261 = some 263983620746230048 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 10 2 258470062199508261 263983620746230048 263983620746230048 endpoint_14_58_p10 endpoint_14_58_w10
private theorem endpoint_14_58_w12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 12 1 263983620746230048 = some 263983620746230048 := by decide +kernel
private theorem endpoint_14_58_p13 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 13 258470062199508261 = some 263983620746230048 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 12 1 258470062199508261 263983620746230048 263983620746230048 endpoint_14_58_p12 endpoint_14_58_w12
def endpoint_14_58 : CertifiedEndpoint :=
  ⟨⟨14, 58, 2767⟩, 263983620746230048, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_58_flag endpoint_14_58_sources 13 258470062199508261 263983620746230048 rfl endpoint_14_58_base endpoint_14_58_p13) (by decide)⟩
private def endpoint_14_59_flag : Flag := ⟨14, 59, 2707⟩
private def endpoint_14_59_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_59_base : receiptBase endpoint_14_59_flag endpoint_14_59_sources = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_w0 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 2 262922514111585331 = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_w2 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 2 2 262922514111585331 = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_p4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 4 262922514111585331 = some 262922514111585331 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 2 2 262922514111585331 262922514111585331 262922514111585331 endpoint_14_59_w0 endpoint_14_59_w2
private theorem endpoint_14_59_w4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 4 2 262922514111585331 = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_p6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 6 262922514111585331 = some 262922514111585331 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 4 2 262922514111585331 262922514111585331 262922514111585331 endpoint_14_59_p4 endpoint_14_59_w4
private theorem endpoint_14_59_w6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 6 2 262922514111585331 = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_p8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 8 262922514111585331 = some 262922514111585331 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 6 2 262922514111585331 262922514111585331 262922514111585331 endpoint_14_59_p6 endpoint_14_59_w6
private theorem endpoint_14_59_w8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 8 2 262922514111585331 = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_p10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 10 262922514111585331 = some 262922514111585331 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 8 2 262922514111585331 262922514111585331 262922514111585331 endpoint_14_59_p8 endpoint_14_59_w8
private theorem endpoint_14_59_w10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 10 2 262922514111585331 = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_p12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 12 262922514111585331 = some 262922514111585331 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 10 2 262922514111585331 262922514111585331 262922514111585331 endpoint_14_59_p10 endpoint_14_59_w10
private theorem endpoint_14_59_w12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 12 1 262922514111585331 = some 262922514111585331 := by decide +kernel
private theorem endpoint_14_59_p13 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 13 262922514111585331 = some 262922514111585331 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 12 1 262922514111585331 262922514111585331 262922514111585331 endpoint_14_59_p12 endpoint_14_59_w12
def endpoint_14_59 : CertifiedEndpoint :=
  ⟨⟨14, 59, 2707⟩, 262922514111585331, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_59_flag endpoint_14_59_sources 13 262922514111585331 262922514111585331 rfl endpoint_14_59_base endpoint_14_59_p13) (by decide)⟩
private def endpoint_14_60_flag : Flag := ⟨14, 60, 2646⟩
private def endpoint_14_60_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_60_base : receiptBase endpoint_14_60_flag endpoint_14_60_sources = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_w0 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 2 260939055188970906 = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_w2 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 2 2 260939055188970906 = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_p4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 4 260939055188970906 = some 260939055188970906 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 2 2 260939055188970906 260939055188970906 260939055188970906 endpoint_14_60_w0 endpoint_14_60_w2
private theorem endpoint_14_60_w4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 4 2 260939055188970906 = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_p6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 6 260939055188970906 = some 260939055188970906 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 4 2 260939055188970906 260939055188970906 260939055188970906 endpoint_14_60_p4 endpoint_14_60_w4
private theorem endpoint_14_60_w6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 6 2 260939055188970906 = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_p8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 8 260939055188970906 = some 260939055188970906 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 6 2 260939055188970906 260939055188970906 260939055188970906 endpoint_14_60_p6 endpoint_14_60_w6
private theorem endpoint_14_60_w8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 8 2 260939055188970906 = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_p10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 10 260939055188970906 = some 260939055188970906 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 8 2 260939055188970906 260939055188970906 260939055188970906 endpoint_14_60_p8 endpoint_14_60_w8
private theorem endpoint_14_60_w10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 10 2 260939055188970906 = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_p12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 12 260939055188970906 = some 260939055188970906 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 10 2 260939055188970906 260939055188970906 260939055188970906 endpoint_14_60_p10 endpoint_14_60_w10
private theorem endpoint_14_60_w12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 12 1 260939055188970906 = some 260939055188970906 := by decide +kernel
private theorem endpoint_14_60_p13 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 13 260939055188970906 = some 260939055188970906 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 12 1 260939055188970906 260939055188970906 260939055188970906 endpoint_14_60_p12 endpoint_14_60_w12
def endpoint_14_60 : CertifiedEndpoint :=
  ⟨⟨14, 60, 2646⟩, 260939055188970906, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_60_flag endpoint_14_60_sources 13 260939055188970906 260939055188970906 rfl endpoint_14_60_base endpoint_14_60_p13) (by decide)⟩
private def endpoint_14_61_flag : Flag := ⟨14, 61, 2582⟩
private def endpoint_14_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_61_base : receiptBase endpoint_14_61_flag endpoint_14_61_sources = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_w0 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 2 258488609097946787 = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_w2 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 2 2 258488609097946787 = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_p4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 4 258488609097946787 = some 258488609097946787 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 2 2 258488609097946787 258488609097946787 258488609097946787 endpoint_14_61_w0 endpoint_14_61_w2
private theorem endpoint_14_61_w4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 4 2 258488609097946787 = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_p6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 6 258488609097946787 = some 258488609097946787 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 4 2 258488609097946787 258488609097946787 258488609097946787 endpoint_14_61_p4 endpoint_14_61_w4
private theorem endpoint_14_61_w6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 6 2 258488609097946787 = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_p8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 8 258488609097946787 = some 258488609097946787 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 6 2 258488609097946787 258488609097946787 258488609097946787 endpoint_14_61_p6 endpoint_14_61_w6
private theorem endpoint_14_61_w8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 8 2 258488609097946787 = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_p10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 10 258488609097946787 = some 258488609097946787 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 8 2 258488609097946787 258488609097946787 258488609097946787 endpoint_14_61_p8 endpoint_14_61_w8
private theorem endpoint_14_61_w10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 10 2 258488609097946787 = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_p12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 12 258488609097946787 = some 258488609097946787 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 10 2 258488609097946787 258488609097946787 258488609097946787 endpoint_14_61_p10 endpoint_14_61_w10
private theorem endpoint_14_61_w12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 12 1 258488609097946787 = some 258488609097946787 := by decide +kernel
private theorem endpoint_14_61_p13 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 13 258488609097946787 = some 258488609097946787 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 12 1 258488609097946787 258488609097946787 258488609097946787 endpoint_14_61_p12 endpoint_14_61_w12
def endpoint_14_61 : CertifiedEndpoint :=
  ⟨⟨14, 61, 2582⟩, 258488609097946787, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_61_flag endpoint_14_61_sources 13 258488609097946787 258488609097946787 rfl endpoint_14_61_base endpoint_14_61_p13) (by decide)⟩
private def endpoint_14_62_flag : Flag := ⟨14, 62, 2515⟩
private def endpoint_14_62_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_62_base : receiptBase endpoint_14_62_flag endpoint_14_62_sources = some 255558483217453861 := by decide +kernel
private theorem endpoint_14_62_w0 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 2 255558483217453861 = some 257696930408868960 := by decide +kernel
private theorem endpoint_14_62_w2 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 2 2 257696930408868960 = some 257696930408868960 := by decide +kernel
private theorem endpoint_14_62_p4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 4 255558483217453861 = some 257696930408868960 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 2 2 255558483217453861 257696930408868960 257696930408868960 endpoint_14_62_w0 endpoint_14_62_w2
private theorem endpoint_14_62_w4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 4 2 257696930408868960 = some 257696930408868960 := by decide +kernel
private theorem endpoint_14_62_p6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 6 255558483217453861 = some 257696930408868960 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 4 2 255558483217453861 257696930408868960 257696930408868960 endpoint_14_62_p4 endpoint_14_62_w4
private theorem endpoint_14_62_w6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 6 2 257696930408868960 = some 257696930408868960 := by decide +kernel
private theorem endpoint_14_62_p8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 8 255558483217453861 = some 257696930408868960 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 6 2 255558483217453861 257696930408868960 257696930408868960 endpoint_14_62_p6 endpoint_14_62_w6
private theorem endpoint_14_62_w8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 8 2 257696930408868960 = some 257696930408868960 := by decide +kernel
private theorem endpoint_14_62_p10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 10 255558483217453861 = some 257696930408868960 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 8 2 255558483217453861 257696930408868960 257696930408868960 endpoint_14_62_p8 endpoint_14_62_w8
private theorem endpoint_14_62_w10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 10 2 257696930408868960 = some 257696930408868960 := by decide +kernel
private theorem endpoint_14_62_p12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 12 255558483217453861 = some 257696930408868960 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 10 2 255558483217453861 257696930408868960 257696930408868960 endpoint_14_62_p10 endpoint_14_62_w10
private theorem endpoint_14_62_w12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 12 1 257696930408868960 = some 257696930408868960 := by decide +kernel
private theorem endpoint_14_62_p13 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 13 255558483217453861 = some 257696930408868960 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 12 1 255558483217453861 257696930408868960 257696930408868960 endpoint_14_62_p12 endpoint_14_62_w12
def endpoint_14_62 : CertifiedEndpoint :=
  ⟨⟨14, 62, 2515⟩, 257696930408868960, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_62_flag endpoint_14_62_sources 13 255558483217453861 257696930408868960 rfl endpoint_14_62_base endpoint_14_62_p13) (by decide)⟩
private def endpoint_14_63_flag : Flag := ⟨14, 63, 2447⟩
private def endpoint_14_63_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_63_base : receiptBase endpoint_14_63_flag endpoint_14_63_sources = some 252337306989527176 := by decide +kernel
private theorem endpoint_14_63_w0 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 2 252337306989527176 = some 258444735362436395 := by decide +kernel
private theorem endpoint_14_63_w2 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 2 2 258444735362436395 = some 258444735362436395 := by decide +kernel
private theorem endpoint_14_63_p4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 4 252337306989527176 = some 258444735362436395 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 2 2 252337306989527176 258444735362436395 258444735362436395 endpoint_14_63_w0 endpoint_14_63_w2
private theorem endpoint_14_63_w4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 4 2 258444735362436395 = some 258444735362436395 := by decide +kernel
private theorem endpoint_14_63_p6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 6 252337306989527176 = some 258444735362436395 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 4 2 252337306989527176 258444735362436395 258444735362436395 endpoint_14_63_p4 endpoint_14_63_w4
private theorem endpoint_14_63_w6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 6 2 258444735362436395 = some 258444735362436395 := by decide +kernel
private theorem endpoint_14_63_p8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 8 252337306989527176 = some 258444735362436395 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 6 2 252337306989527176 258444735362436395 258444735362436395 endpoint_14_63_p6 endpoint_14_63_w6
private theorem endpoint_14_63_w8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 8 2 258444735362436395 = some 258444735362436395 := by decide +kernel
private theorem endpoint_14_63_p10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 10 252337306989527176 = some 258444735362436395 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 8 2 252337306989527176 258444735362436395 258444735362436395 endpoint_14_63_p8 endpoint_14_63_w8
private theorem endpoint_14_63_w10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 10 2 258444735362436395 = some 258444735362436395 := by decide +kernel
private theorem endpoint_14_63_p12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 12 252337306989527176 = some 258444735362436395 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 10 2 252337306989527176 258444735362436395 258444735362436395 endpoint_14_63_p10 endpoint_14_63_w10
private theorem endpoint_14_63_w12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 12 1 258444735362436395 = some 258444735362436395 := by decide +kernel
private theorem endpoint_14_63_p13 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 13 252337306989527176 = some 258444735362436395 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 12 1 252337306989527176 258444735362436395 258444735362436395 endpoint_14_63_p12 endpoint_14_63_w12
def endpoint_14_63 : CertifiedEndpoint :=
  ⟨⟨14, 63, 2447⟩, 258444735362436395, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_63_flag endpoint_14_63_sources 13 252337306989527176 258444735362436395 rfl endpoint_14_63_base endpoint_14_63_p13) (by decide)⟩
private def endpoint_14_64_flag : Flag := ⟨14, 64, 2375⟩
private def endpoint_14_64_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_64_base : receiptBase endpoint_14_64_flag endpoint_14_64_sources = some 248514635572152750 := by decide +kernel
private theorem endpoint_14_64_w0 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 2 248514635572152750 = some 258809900540398244 := by decide +kernel
private theorem endpoint_14_64_w2 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 2 2 258809900540398244 = some 258809900540398244 := by decide +kernel
private theorem endpoint_14_64_p4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 4 248514635572152750 = some 258809900540398244 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 2 2 248514635572152750 258809900540398244 258809900540398244 endpoint_14_64_w0 endpoint_14_64_w2
private theorem endpoint_14_64_w4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 4 2 258809900540398244 = some 258809900540398244 := by decide +kernel
private theorem endpoint_14_64_p6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 6 248514635572152750 = some 258809900540398244 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 4 2 248514635572152750 258809900540398244 258809900540398244 endpoint_14_64_p4 endpoint_14_64_w4
private theorem endpoint_14_64_w6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 6 2 258809900540398244 = some 258809900540398244 := by decide +kernel
private theorem endpoint_14_64_p8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 8 248514635572152750 = some 258809900540398244 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 6 2 248514635572152750 258809900540398244 258809900540398244 endpoint_14_64_p6 endpoint_14_64_w6
private theorem endpoint_14_64_w8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 8 2 258809900540398244 = some 258809900540398244 := by decide +kernel
private theorem endpoint_14_64_p10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 10 248514635572152750 = some 258809900540398244 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 8 2 248514635572152750 258809900540398244 258809900540398244 endpoint_14_64_p8 endpoint_14_64_w8
private theorem endpoint_14_64_w10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 10 2 258809900540398244 = some 258809900540398244 := by decide +kernel
private theorem endpoint_14_64_p12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 12 248514635572152750 = some 258809900540398244 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 10 2 248514635572152750 258809900540398244 258809900540398244 endpoint_14_64_p10 endpoint_14_64_w10
private theorem endpoint_14_64_w12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 12 1 258809900540398244 = some 258809900540398244 := by decide +kernel
private theorem endpoint_14_64_p13 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 13 248514635572152750 = some 258809900540398244 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 12 1 248514635572152750 258809900540398244 258809900540398244 endpoint_14_64_p12 endpoint_14_64_w12
def endpoint_14_64 : CertifiedEndpoint :=
  ⟨⟨14, 64, 2375⟩, 258809900540398244, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_64_flag endpoint_14_64_sources 13 248514635572152750 258809900540398244 rfl endpoint_14_64_base endpoint_14_64_p13) (by decide)⟩
private def endpoint_14_65_flag : Flag := ⟨14, 65, 2301⟩
private def endpoint_14_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_65_base : receiptBase endpoint_14_65_flag endpoint_14_65_sources = some 244280508698594423 := by decide +kernel
private theorem endpoint_14_65_w0 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 2 244280508698594423 = some 258899716969555221 := by decide +kernel
private theorem endpoint_14_65_w2 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 2 2 258899716969555221 = some 258899716969555221 := by decide +kernel
private theorem endpoint_14_65_p4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 4 244280508698594423 = some 258899716969555221 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 2 2 244280508698594423 258899716969555221 258899716969555221 endpoint_14_65_w0 endpoint_14_65_w2
private theorem endpoint_14_65_w4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 4 2 258899716969555221 = some 258899716969555221 := by decide +kernel
private theorem endpoint_14_65_p6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 6 244280508698594423 = some 258899716969555221 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 4 2 244280508698594423 258899716969555221 258899716969555221 endpoint_14_65_p4 endpoint_14_65_w4
private theorem endpoint_14_65_w6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 6 2 258899716969555221 = some 258899716969555221 := by decide +kernel
private theorem endpoint_14_65_p8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 8 244280508698594423 = some 258899716969555221 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 6 2 244280508698594423 258899716969555221 258899716969555221 endpoint_14_65_p6 endpoint_14_65_w6
private theorem endpoint_14_65_w8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 8 2 258899716969555221 = some 258899716969555221 := by decide +kernel
private theorem endpoint_14_65_p10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 10 244280508698594423 = some 258899716969555221 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 8 2 244280508698594423 258899716969555221 258899716969555221 endpoint_14_65_p8 endpoint_14_65_w8
private theorem endpoint_14_65_w10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 10 2 258899716969555221 = some 258899716969555221 := by decide +kernel
private theorem endpoint_14_65_p12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 12 244280508698594423 = some 258899716969555221 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 10 2 244280508698594423 258899716969555221 258899716969555221 endpoint_14_65_p10 endpoint_14_65_w10
private theorem endpoint_14_65_w12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 12 1 258899716969555221 = some 258899716969555221 := by decide +kernel
private theorem endpoint_14_65_p13 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 13 244280508698594423 = some 258899716969555221 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 12 1 244280508698594423 258899716969555221 258899716969555221 endpoint_14_65_p12 endpoint_14_65_w12
def endpoint_14_65 : CertifiedEndpoint :=
  ⟨⟨14, 65, 2301⟩, 258899716969555221, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_65_flag endpoint_14_65_sources 13 244280508698594423 258899716969555221 rfl endpoint_14_65_base endpoint_14_65_p13) (by decide)⟩
private def endpoint_14_66_flag : Flag := ⟨14, 66, 2225⟩
private def endpoint_14_66_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_66_base : receiptBase endpoint_14_66_flag endpoint_14_66_sources = some 240815366604159628 := by decide +kernel
private theorem endpoint_14_66_w0 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 2 240815366604159628 = some 245537703308963252 := by decide +kernel
private theorem endpoint_14_66_w2 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 2 2 245537703308963252 = some 245537703308963252 := by decide +kernel
private theorem endpoint_14_66_p4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 4 240815366604159628 = some 245537703308963252 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 2 2 240815366604159628 245537703308963252 245537703308963252 endpoint_14_66_w0 endpoint_14_66_w2
private theorem endpoint_14_66_w4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 4 2 245537703308963252 = some 245537703308963252 := by decide +kernel
private theorem endpoint_14_66_p6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 6 240815366604159628 = some 245537703308963252 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 4 2 240815366604159628 245537703308963252 245537703308963252 endpoint_14_66_p4 endpoint_14_66_w4
private theorem endpoint_14_66_w6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 6 2 245537703308963252 = some 245537703308963252 := by decide +kernel
private theorem endpoint_14_66_p8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 8 240815366604159628 = some 245537703308963252 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 6 2 240815366604159628 245537703308963252 245537703308963252 endpoint_14_66_p6 endpoint_14_66_w6
private theorem endpoint_14_66_w8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 8 2 245537703308963252 = some 245537703308963252 := by decide +kernel
private theorem endpoint_14_66_p10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 10 240815366604159628 = some 245537703308963252 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 8 2 240815366604159628 245537703308963252 245537703308963252 endpoint_14_66_p8 endpoint_14_66_w8
private theorem endpoint_14_66_w10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 10 2 245537703308963252 = some 245537703308963252 := by decide +kernel
private theorem endpoint_14_66_p12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 12 240815366604159628 = some 245537703308963252 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 10 2 240815366604159628 245537703308963252 245537703308963252 endpoint_14_66_p10 endpoint_14_66_w10
private theorem endpoint_14_66_w12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 12 1 245537703308963252 = some 245537703308963252 := by decide +kernel
private theorem endpoint_14_66_p13 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 13 240815366604159628 = some 245537703308963252 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 12 1 240815366604159628 245537703308963252 245537703308963252 endpoint_14_66_p12 endpoint_14_66_w12
def endpoint_14_66 : CertifiedEndpoint :=
  ⟨⟨14, 66, 2225⟩, 245537703308963252, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_66_flag endpoint_14_66_sources 13 240815366604159628 245537703308963252 rfl endpoint_14_66_base endpoint_14_66_p13) (by decide)⟩
private def endpoint_14_67_flag : Flag := ⟨14, 67, 2146⟩
private def endpoint_14_67_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_67_base : receiptBase endpoint_14_67_flag endpoint_14_67_sources = some 235583677504756883 := by decide +kernel
private theorem endpoint_14_67_w0 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 2 235583677504756883 = some 244769681454404050 := by decide +kernel
private theorem endpoint_14_67_w2 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 2 2 244769681454404050 = some 244769681454404050 := by decide +kernel
private theorem endpoint_14_67_p4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 4 235583677504756883 = some 244769681454404050 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 2 2 235583677504756883 244769681454404050 244769681454404050 endpoint_14_67_w0 endpoint_14_67_w2
private theorem endpoint_14_67_w4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 4 2 244769681454404050 = some 244769681454404050 := by decide +kernel
private theorem endpoint_14_67_p6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 6 235583677504756883 = some 244769681454404050 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 4 2 235583677504756883 244769681454404050 244769681454404050 endpoint_14_67_p4 endpoint_14_67_w4
private theorem endpoint_14_67_w6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 6 2 244769681454404050 = some 244769681454404050 := by decide +kernel
private theorem endpoint_14_67_p8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 8 235583677504756883 = some 244769681454404050 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 6 2 235583677504756883 244769681454404050 244769681454404050 endpoint_14_67_p6 endpoint_14_67_w6
private theorem endpoint_14_67_w8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 8 2 244769681454404050 = some 244769681454404050 := by decide +kernel
private theorem endpoint_14_67_p10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 10 235583677504756883 = some 244769681454404050 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 8 2 235583677504756883 244769681454404050 244769681454404050 endpoint_14_67_p8 endpoint_14_67_w8
private theorem endpoint_14_67_w10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 10 2 244769681454404050 = some 244769681454404050 := by decide +kernel
private theorem endpoint_14_67_p12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 12 235583677504756883 = some 244769681454404050 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 10 2 235583677504756883 244769681454404050 244769681454404050 endpoint_14_67_p10 endpoint_14_67_w10
private theorem endpoint_14_67_w12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 12 1 244769681454404050 = some 244769681454404050 := by decide +kernel
private theorem endpoint_14_67_p13 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 13 235583677504756883 = some 244769681454404050 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 12 1 235583677504756883 244769681454404050 244769681454404050 endpoint_14_67_p12 endpoint_14_67_w12
def endpoint_14_67 : CertifiedEndpoint :=
  ⟨⟨14, 67, 2146⟩, 244769681454404050, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_67_flag endpoint_14_67_sources 13 235583677504756883 244769681454404050 rfl endpoint_14_67_base endpoint_14_67_p13) (by decide)⟩
private def endpoint_14_68_flag : Flag := ⟨14, 68, 2064⟩
private def endpoint_14_68_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_14_68_base : receiptBase endpoint_14_68_flag endpoint_14_68_sources = some 229832026876359520 := by decide +kernel
private theorem endpoint_14_68_w0 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 2 229832026876359520 = some 243642024267423936 := by decide +kernel
private theorem endpoint_14_68_w2 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 2 2 243642024267423936 = some 243642024267423936 := by decide +kernel
private theorem endpoint_14_68_p4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 4 229832026876359520 = some 243642024267423936 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 2 2 229832026876359520 243642024267423936 243642024267423936 endpoint_14_68_w0 endpoint_14_68_w2
private theorem endpoint_14_68_w4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 4 2 243642024267423936 = some 243642024267423936 := by decide +kernel
private theorem endpoint_14_68_p6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 6 229832026876359520 = some 243642024267423936 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 4 2 229832026876359520 243642024267423936 243642024267423936 endpoint_14_68_p4 endpoint_14_68_w4
private theorem endpoint_14_68_w6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 6 2 243642024267423936 = some 243642024267423936 := by decide +kernel
private theorem endpoint_14_68_p8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 8 229832026876359520 = some 243642024267423936 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 6 2 229832026876359520 243642024267423936 243642024267423936 endpoint_14_68_p6 endpoint_14_68_w6
private theorem endpoint_14_68_w8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 8 2 243642024267423936 = some 243642024267423936 := by decide +kernel
private theorem endpoint_14_68_p10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 10 229832026876359520 = some 243642024267423936 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 8 2 229832026876359520 243642024267423936 243642024267423936 endpoint_14_68_p8 endpoint_14_68_w8
private theorem endpoint_14_68_w10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 10 2 243642024267423936 = some 243642024267423936 := by decide +kernel
private theorem endpoint_14_68_p12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 12 229832026876359520 = some 243642024267423936 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 10 2 229832026876359520 243642024267423936 243642024267423936 endpoint_14_68_p10 endpoint_14_68_w10
private theorem endpoint_14_68_w12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 12 1 243642024267423936 = some 243642024267423936 := by decide +kernel
private theorem endpoint_14_68_p13 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 13 229832026876359520 = some 243642024267423936 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 12 1 229832026876359520 243642024267423936 243642024267423936 endpoint_14_68_p12 endpoint_14_68_w12
def endpoint_14_68 : CertifiedEndpoint :=
  ⟨⟨14, 68, 2064⟩, 243642024267423936, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_14_68_flag endpoint_14_68_sources 13 229832026876359520 243642024267423936 rfl endpoint_14_68_base endpoint_14_68_p13) (by decide)⟩
private def endpoint_14_69_flag : Flag := ⟨14, 69, 1979⟩
private def endpoint_14_69_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_14_69_base : receiptBase endpoint_14_69_flag endpoint_14_69_sources = some 224746124131634325 := by decide +kernel
private theorem endpoint_14_69_w0 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 2 224746124131634325 = some 235354271494318982 := by decide +kernel
private theorem endpoint_14_69_w2 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 2 2 235354271494318982 = some 235354271494318982 := by decide +kernel
private theorem endpoint_14_69_p4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 4 224746124131634325 = some 235354271494318982 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 2 2 224746124131634325 235354271494318982 235354271494318982 endpoint_14_69_w0 endpoint_14_69_w2
private theorem endpoint_14_69_w4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 4 2 235354271494318982 = some 235354271494318982 := by decide +kernel
private theorem endpoint_14_69_p6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 6 224746124131634325 = some 235354271494318982 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 4 2 224746124131634325 235354271494318982 235354271494318982 endpoint_14_69_p4 endpoint_14_69_w4
private theorem endpoint_14_69_w6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 6 2 235354271494318982 = some 235354271494318982 := by decide +kernel
private theorem endpoint_14_69_p8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 8 224746124131634325 = some 235354271494318982 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 6 2 224746124131634325 235354271494318982 235354271494318982 endpoint_14_69_p6 endpoint_14_69_w6
private theorem endpoint_14_69_w8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 8 2 235354271494318982 = some 235354271494318982 := by decide +kernel
private theorem endpoint_14_69_p10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 10 224746124131634325 = some 235354271494318982 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 8 2 224746124131634325 235354271494318982 235354271494318982 endpoint_14_69_p8 endpoint_14_69_w8
private theorem endpoint_14_69_w10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 10 2 235354271494318982 = some 235354271494318982 := by decide +kernel
private theorem endpoint_14_69_p12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 12 224746124131634325 = some 235354271494318982 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 10 2 224746124131634325 235354271494318982 235354271494318982 endpoint_14_69_p10 endpoint_14_69_w10
private theorem endpoint_14_69_w12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 12 1 235354271494318982 = some 235354271494318982 := by decide +kernel
private theorem endpoint_14_69_p13 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 13 224746124131634325 = some 235354271494318982 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 12 1 224746124131634325 235354271494318982 235354271494318982 endpoint_14_69_p12 endpoint_14_69_w12
def endpoint_14_69 : CertifiedEndpoint :=
  ⟨⟨14, 69, 1979⟩, 235354271494318982, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_14_69_flag endpoint_14_69_sources 13 224746124131634325 235354271494318982 rfl endpoint_14_69_base endpoint_14_69_p13) (by decide)⟩
private def endpoint_14_70_flag : Flag := ⟨14, 70, 1891⟩
private def endpoint_14_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_14_70_base : receiptBase endpoint_14_70_flag endpoint_14_70_sources = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_w0 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 2 219180449807651795 = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_w2 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 2 2 219180449807651795 = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_p4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 4 219180449807651795 = some 219180449807651795 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 2 2 219180449807651795 219180449807651795 219180449807651795 endpoint_14_70_w0 endpoint_14_70_w2
private theorem endpoint_14_70_w4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 4 2 219180449807651795 = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_p6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 6 219180449807651795 = some 219180449807651795 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 4 2 219180449807651795 219180449807651795 219180449807651795 endpoint_14_70_p4 endpoint_14_70_w4
private theorem endpoint_14_70_w6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 6 2 219180449807651795 = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_p8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 8 219180449807651795 = some 219180449807651795 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 6 2 219180449807651795 219180449807651795 219180449807651795 endpoint_14_70_p6 endpoint_14_70_w6
private theorem endpoint_14_70_w8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 8 2 219180449807651795 = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_p10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 10 219180449807651795 = some 219180449807651795 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 8 2 219180449807651795 219180449807651795 219180449807651795 endpoint_14_70_p8 endpoint_14_70_w8
private theorem endpoint_14_70_w10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 10 2 219180449807651795 = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_p12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 12 219180449807651795 = some 219180449807651795 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 10 2 219180449807651795 219180449807651795 219180449807651795 endpoint_14_70_p10 endpoint_14_70_w10
private theorem endpoint_14_70_w12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 12 1 219180449807651795 = some 219180449807651795 := by decide +kernel
private theorem endpoint_14_70_p13 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 13 219180449807651795 = some 219180449807651795 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 12 1 219180449807651795 219180449807651795 219180449807651795 endpoint_14_70_p12 endpoint_14_70_w12
def endpoint_14_70 : CertifiedEndpoint :=
  ⟨⟨14, 70, 1891⟩, 219180449807651795, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_14_70_flag endpoint_14_70_sources 13 219180449807651795 219180449807651795 rfl endpoint_14_70_base endpoint_14_70_p13) (by decide)⟩
private def endpoint_14_71_flag : Flag := ⟨14, 71, 1800⟩
private def endpoint_14_71_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_71_base : receiptBase endpoint_14_71_flag endpoint_14_71_sources = some 212926198477606417 := by decide +kernel
private theorem endpoint_14_71_w0 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 2 212926198477606417 = some 214080709973094390 := by decide +kernel
private theorem endpoint_14_71_w2 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 2 2 214080709973094390 = some 214080709973094390 := by decide +kernel
private theorem endpoint_14_71_p4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 4 212926198477606417 = some 214080709973094390 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 2 2 212926198477606417 214080709973094390 214080709973094390 endpoint_14_71_w0 endpoint_14_71_w2
private theorem endpoint_14_71_w4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 4 2 214080709973094390 = some 214080709973094390 := by decide +kernel
private theorem endpoint_14_71_p6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 6 212926198477606417 = some 214080709973094390 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 4 2 212926198477606417 214080709973094390 214080709973094390 endpoint_14_71_p4 endpoint_14_71_w4
private theorem endpoint_14_71_w6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 6 2 214080709973094390 = some 214080709973094390 := by decide +kernel
private theorem endpoint_14_71_p8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 8 212926198477606417 = some 214080709973094390 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 6 2 212926198477606417 214080709973094390 214080709973094390 endpoint_14_71_p6 endpoint_14_71_w6
private theorem endpoint_14_71_w8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 8 2 214080709973094390 = some 214080709973094390 := by decide +kernel
private theorem endpoint_14_71_p10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 10 212926198477606417 = some 214080709973094390 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 8 2 212926198477606417 214080709973094390 214080709973094390 endpoint_14_71_p8 endpoint_14_71_w8
private theorem endpoint_14_71_w10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 10 2 214080709973094390 = some 214080709973094390 := by decide +kernel
private theorem endpoint_14_71_p12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 12 212926198477606417 = some 214080709973094390 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 10 2 212926198477606417 214080709973094390 214080709973094390 endpoint_14_71_p10 endpoint_14_71_w10
private theorem endpoint_14_71_w12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 12 1 214080709973094390 = some 214080709973094390 := by decide +kernel
private theorem endpoint_14_71_p13 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 13 212926198477606417 = some 214080709973094390 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 12 1 212926198477606417 214080709973094390 214080709973094390 endpoint_14_71_p12 endpoint_14_71_w12
def endpoint_14_71 : CertifiedEndpoint :=
  ⟨⟨14, 71, 1800⟩, 214080709973094390, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_71_flag endpoint_14_71_sources 13 212926198477606417 214080709973094390 rfl endpoint_14_71_base endpoint_14_71_p13) (by decide)⟩
private def endpoint_14_72_flag : Flag := ⟨14, 72, 1707⟩
private def endpoint_14_72_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_72_base : receiptBase endpoint_14_72_flag endpoint_14_72_sources = some 204549144281812713 := by decide +kernel
private theorem endpoint_14_72_w0 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 2 204549144281812713 = some 211108644159915100 := by decide +kernel
private theorem endpoint_14_72_w2 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 2 2 211108644159915100 = some 211108644159915100 := by decide +kernel
private theorem endpoint_14_72_p4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 4 204549144281812713 = some 211108644159915100 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 2 2 204549144281812713 211108644159915100 211108644159915100 endpoint_14_72_w0 endpoint_14_72_w2
private theorem endpoint_14_72_w4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 4 2 211108644159915100 = some 211108644159915100 := by decide +kernel
private theorem endpoint_14_72_p6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 6 204549144281812713 = some 211108644159915100 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 4 2 204549144281812713 211108644159915100 211108644159915100 endpoint_14_72_p4 endpoint_14_72_w4
private theorem endpoint_14_72_w6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 6 2 211108644159915100 = some 211108644159915100 := by decide +kernel
private theorem endpoint_14_72_p8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 8 204549144281812713 = some 211108644159915100 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 6 2 204549144281812713 211108644159915100 211108644159915100 endpoint_14_72_p6 endpoint_14_72_w6
private theorem endpoint_14_72_w8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 8 2 211108644159915100 = some 211108644159915100 := by decide +kernel
private theorem endpoint_14_72_p10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 10 204549144281812713 = some 211108644159915100 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 8 2 204549144281812713 211108644159915100 211108644159915100 endpoint_14_72_p8 endpoint_14_72_w8
private theorem endpoint_14_72_w10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 10 2 211108644159915100 = some 211108644159915100 := by decide +kernel
private theorem endpoint_14_72_p12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 12 204549144281812713 = some 211108644159915100 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 10 2 204549144281812713 211108644159915100 211108644159915100 endpoint_14_72_p10 endpoint_14_72_w10
private theorem endpoint_14_72_w12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 12 1 211108644159915100 = some 211108644159915100 := by decide +kernel
private theorem endpoint_14_72_p13 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 13 204549144281812713 = some 211108644159915100 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 12 1 204549144281812713 211108644159915100 211108644159915100 endpoint_14_72_p12 endpoint_14_72_w12
def endpoint_14_72 : CertifiedEndpoint :=
  ⟨⟨14, 72, 1707⟩, 211108644159915100, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_72_flag endpoint_14_72_sources 13 204549144281812713 211108644159915100 rfl endpoint_14_72_base endpoint_14_72_p13) (by decide)⟩
private def endpoint_14_73_flag : Flag := ⟨14, 73, 1610⟩
private def endpoint_14_73_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_73_base : receiptBase endpoint_14_73_flag endpoint_14_73_sources = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_w0 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 2 196976019860349827 = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_w2 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 2 2 196976019860349827 = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_p4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 4 196976019860349827 = some 196976019860349827 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 2 2 196976019860349827 196976019860349827 196976019860349827 endpoint_14_73_w0 endpoint_14_73_w2
private theorem endpoint_14_73_w4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 4 2 196976019860349827 = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_p6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 6 196976019860349827 = some 196976019860349827 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 4 2 196976019860349827 196976019860349827 196976019860349827 endpoint_14_73_p4 endpoint_14_73_w4
private theorem endpoint_14_73_w6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 6 2 196976019860349827 = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_p8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 8 196976019860349827 = some 196976019860349827 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 6 2 196976019860349827 196976019860349827 196976019860349827 endpoint_14_73_p6 endpoint_14_73_w6
private theorem endpoint_14_73_w8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 8 2 196976019860349827 = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_p10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 10 196976019860349827 = some 196976019860349827 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 8 2 196976019860349827 196976019860349827 196976019860349827 endpoint_14_73_p8 endpoint_14_73_w8
private theorem endpoint_14_73_w10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 10 2 196976019860349827 = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_p12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 12 196976019860349827 = some 196976019860349827 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 10 2 196976019860349827 196976019860349827 196976019860349827 endpoint_14_73_p10 endpoint_14_73_w10
private theorem endpoint_14_73_w12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 12 1 196976019860349827 = some 196976019860349827 := by decide +kernel
private theorem endpoint_14_73_p13 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 13 196976019860349827 = some 196976019860349827 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 12 1 196976019860349827 196976019860349827 196976019860349827 endpoint_14_73_p12 endpoint_14_73_w12
def endpoint_14_73 : CertifiedEndpoint :=
  ⟨⟨14, 73, 1610⟩, 196976019860349827, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_73_flag endpoint_14_73_sources 13 196976019860349827 196976019860349827 rfl endpoint_14_73_base endpoint_14_73_p13) (by decide)⟩
private def endpoint_14_74_flag : Flag := ⟨14, 74, 1511⟩
private def endpoint_14_74_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_74_base : receiptBase endpoint_14_74_flag endpoint_14_74_sources = some 187219301087566183 := by decide +kernel
private theorem endpoint_14_74_w0 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 2 187219301087566183 = some 188171857216415826 := by decide +kernel
private theorem endpoint_14_74_w2 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 2 2 188171857216415826 = some 188171857216415826 := by decide +kernel
private theorem endpoint_14_74_p4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 4 187219301087566183 = some 188171857216415826 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 2 2 187219301087566183 188171857216415826 188171857216415826 endpoint_14_74_w0 endpoint_14_74_w2
private theorem endpoint_14_74_w4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 4 2 188171857216415826 = some 188171857216415826 := by decide +kernel
private theorem endpoint_14_74_p6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 6 187219301087566183 = some 188171857216415826 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 4 2 187219301087566183 188171857216415826 188171857216415826 endpoint_14_74_p4 endpoint_14_74_w4
private theorem endpoint_14_74_w6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 6 2 188171857216415826 = some 188171857216415826 := by decide +kernel
private theorem endpoint_14_74_p8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 8 187219301087566183 = some 188171857216415826 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 6 2 187219301087566183 188171857216415826 188171857216415826 endpoint_14_74_p6 endpoint_14_74_w6
private theorem endpoint_14_74_w8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 8 2 188171857216415826 = some 188171857216415826 := by decide +kernel
private theorem endpoint_14_74_p10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 10 187219301087566183 = some 188171857216415826 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 8 2 187219301087566183 188171857216415826 188171857216415826 endpoint_14_74_p8 endpoint_14_74_w8
private theorem endpoint_14_74_w10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 10 2 188171857216415826 = some 188171857216415826 := by decide +kernel
private theorem endpoint_14_74_p12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 12 187219301087566183 = some 188171857216415826 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 10 2 187219301087566183 188171857216415826 188171857216415826 endpoint_14_74_p10 endpoint_14_74_w10
private theorem endpoint_14_74_w12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 12 1 188171857216415826 = some 188171857216415826 := by decide +kernel
private theorem endpoint_14_74_p13 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 13 187219301087566183 = some 188171857216415826 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 12 1 187219301087566183 188171857216415826 188171857216415826 endpoint_14_74_p12 endpoint_14_74_w12
def endpoint_14_74 : CertifiedEndpoint :=
  ⟨⟨14, 74, 1511⟩, 188171857216415826, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_74_flag endpoint_14_74_sources 13 187219301087566183 188171857216415826 rfl endpoint_14_74_base endpoint_14_74_p13) (by decide)⟩
private def endpoint_14_75_flag : Flag := ⟨14, 75, 1408⟩
private def endpoint_14_75_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_75_base : receiptBase endpoint_14_75_flag endpoint_14_75_sources = some 176669861450598424 := by decide +kernel
private theorem endpoint_14_75_w0 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 2 176669861450598424 = some 183647559554591601 := by decide +kernel
private theorem endpoint_14_75_w2 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 2 2 183647559554591601 = some 183647559554591601 := by decide +kernel
private theorem endpoint_14_75_p4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 4 176669861450598424 = some 183647559554591601 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 2 2 176669861450598424 183647559554591601 183647559554591601 endpoint_14_75_w0 endpoint_14_75_w2
private theorem endpoint_14_75_w4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 4 2 183647559554591601 = some 183647559554591601 := by decide +kernel
private theorem endpoint_14_75_p6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 6 176669861450598424 = some 183647559554591601 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 4 2 176669861450598424 183647559554591601 183647559554591601 endpoint_14_75_p4 endpoint_14_75_w4
private theorem endpoint_14_75_w6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 6 2 183647559554591601 = some 183647559554591601 := by decide +kernel
private theorem endpoint_14_75_p8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 8 176669861450598424 = some 183647559554591601 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 6 2 176669861450598424 183647559554591601 183647559554591601 endpoint_14_75_p6 endpoint_14_75_w6
private theorem endpoint_14_75_w8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 8 2 183647559554591601 = some 183647559554591601 := by decide +kernel
private theorem endpoint_14_75_p10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 10 176669861450598424 = some 183647559554591601 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 8 2 176669861450598424 183647559554591601 183647559554591601 endpoint_14_75_p8 endpoint_14_75_w8
private theorem endpoint_14_75_w10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 10 2 183647559554591601 = some 183647559554591601 := by decide +kernel
private theorem endpoint_14_75_p12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 12 176669861450598424 = some 183647559554591601 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 10 2 176669861450598424 183647559554591601 183647559554591601 endpoint_14_75_p10 endpoint_14_75_w10
private theorem endpoint_14_75_w12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 12 1 183647559554591601 = some 183647559554591601 := by decide +kernel
private theorem endpoint_14_75_p13 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 13 176669861450598424 = some 183647559554591601 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 12 1 176669861450598424 183647559554591601 183647559554591601 endpoint_14_75_p12 endpoint_14_75_w12
def endpoint_14_75 : CertifiedEndpoint :=
  ⟨⟨14, 75, 1408⟩, 183647559554591601, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_75_flag endpoint_14_75_sources 13 176669861450598424 183647559554591601 rfl endpoint_14_75_base endpoint_14_75_p13) (by decide)⟩
private def endpoint_14_76_flag : Flag := ⟨14, 76, 1303⟩
private def endpoint_14_76_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_76_base : receiptBase endpoint_14_76_flag endpoint_14_76_sources = some 166976627660383801 := by decide +kernel
private theorem endpoint_14_76_w0 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 2 166976627660383801 = some 168670064107673212 := by decide +kernel
private theorem endpoint_14_76_w2 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 2 2 168670064107673212 = some 168670064107673212 := by decide +kernel
private theorem endpoint_14_76_p4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 4 166976627660383801 = some 168670064107673212 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 2 2 166976627660383801 168670064107673212 168670064107673212 endpoint_14_76_w0 endpoint_14_76_w2
private theorem endpoint_14_76_w4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 4 2 168670064107673212 = some 168670064107673212 := by decide +kernel
private theorem endpoint_14_76_p6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 6 166976627660383801 = some 168670064107673212 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 4 2 166976627660383801 168670064107673212 168670064107673212 endpoint_14_76_p4 endpoint_14_76_w4
private theorem endpoint_14_76_w6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 6 2 168670064107673212 = some 168670064107673212 := by decide +kernel
private theorem endpoint_14_76_p8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 8 166976627660383801 = some 168670064107673212 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 6 2 166976627660383801 168670064107673212 168670064107673212 endpoint_14_76_p6 endpoint_14_76_w6
private theorem endpoint_14_76_w8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 8 2 168670064107673212 = some 168670064107673212 := by decide +kernel
private theorem endpoint_14_76_p10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 10 166976627660383801 = some 168670064107673212 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 8 2 166976627660383801 168670064107673212 168670064107673212 endpoint_14_76_p8 endpoint_14_76_w8
private theorem endpoint_14_76_w10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 10 2 168670064107673212 = some 168670064107673212 := by decide +kernel
private theorem endpoint_14_76_p12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 12 166976627660383801 = some 168670064107673212 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 10 2 166976627660383801 168670064107673212 168670064107673212 endpoint_14_76_p10 endpoint_14_76_w10
private theorem endpoint_14_76_w12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 12 1 168670064107673212 = some 168670064107673212 := by decide +kernel
private theorem endpoint_14_76_p13 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 13 166976627660383801 = some 168670064107673212 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 12 1 166976627660383801 168670064107673212 168670064107673212 endpoint_14_76_p12 endpoint_14_76_w12
def endpoint_14_76 : CertifiedEndpoint :=
  ⟨⟨14, 76, 1303⟩, 168670064107673212, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_76_flag endpoint_14_76_sources 13 166976627660383801 168670064107673212 rfl endpoint_14_76_base endpoint_14_76_p13) (by decide)⟩
private def endpoint_14_77_flag : Flag := ⟨14, 77, 1194⟩
private def endpoint_14_77_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_77_base : receiptBase endpoint_14_77_flag endpoint_14_77_sources = some 154991464269162858 := by decide +kernel
private theorem endpoint_14_77_w0 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 2 154991464269162858 = some 163118109407132967 := by decide +kernel
private theorem endpoint_14_77_w2 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 2 2 163118109407132967 = some 163118109407132967 := by decide +kernel
private theorem endpoint_14_77_p4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 4 154991464269162858 = some 163118109407132967 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 2 2 154991464269162858 163118109407132967 163118109407132967 endpoint_14_77_w0 endpoint_14_77_w2
private theorem endpoint_14_77_w4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 4 2 163118109407132967 = some 163118109407132967 := by decide +kernel
private theorem endpoint_14_77_p6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 6 154991464269162858 = some 163118109407132967 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 4 2 154991464269162858 163118109407132967 163118109407132967 endpoint_14_77_p4 endpoint_14_77_w4
private theorem endpoint_14_77_w6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 6 2 163118109407132967 = some 163118109407132967 := by decide +kernel
private theorem endpoint_14_77_p8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 8 154991464269162858 = some 163118109407132967 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 6 2 154991464269162858 163118109407132967 163118109407132967 endpoint_14_77_p6 endpoint_14_77_w6
private theorem endpoint_14_77_w8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 8 2 163118109407132967 = some 163118109407132967 := by decide +kernel
private theorem endpoint_14_77_p10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 10 154991464269162858 = some 163118109407132967 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 8 2 154991464269162858 163118109407132967 163118109407132967 endpoint_14_77_p8 endpoint_14_77_w8
private theorem endpoint_14_77_w10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 10 2 163118109407132967 = some 163118109407132967 := by decide +kernel
private theorem endpoint_14_77_p12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 12 154991464269162858 = some 163118109407132967 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 10 2 154991464269162858 163118109407132967 163118109407132967 endpoint_14_77_p10 endpoint_14_77_w10
private theorem endpoint_14_77_w12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 12 1 163118109407132967 = some 163118109407132967 := by decide +kernel
private theorem endpoint_14_77_p13 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 13 154991464269162858 = some 163118109407132967 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 12 1 154991464269162858 163118109407132967 163118109407132967 endpoint_14_77_p12 endpoint_14_77_w12
def endpoint_14_77 : CertifiedEndpoint :=
  ⟨⟨14, 77, 1194⟩, 163118109407132967, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_77_flag endpoint_14_77_sources 13 154991464269162858 163118109407132967 rfl endpoint_14_77_base endpoint_14_77_p13) (by decide)⟩
def endpoint_14_78 : CertifiedEndpoint :=
  ⟨⟨14, 78, 1083⟩, 255808174139604289, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_79 : CertifiedEndpoint :=
  ⟨⟨14, 79, 968⟩, 230633682495649105, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_80 : CertifiedEndpoint :=
  ⟨⟨14, 80, 850⟩, 203894976209316814, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_81 : CertifiedEndpoint :=
  ⟨⟨14, 81, 730⟩, 175817014132023955, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_82 : CertifiedEndpoint :=
  ⟨⟨14, 82, 606⟩, 145859200951951902, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_83 : CertifiedEndpoint :=
  ⟨⟨14, 83, 479⟩, 114243007920171596, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_84 : CertifiedEndpoint :=
  ⟨⟨14, 84, 349⟩, 80937046633572655, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_85 : CertifiedEndpoint :=
  ⟨⟨14, 85, 216⟩, 45909928689044697, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_15 : CertifiedEndpoint :=
  ⟨⟨15, 15, 4164⟩, 129818195257384089, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_16 : CertifiedEndpoint :=
  ⟨⟨15, 16, 4139⟩, 134100135304593054, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_17 : CertifiedEndpoint :=
  ⟨⟨15, 17, 4113⟩, 138286939402070078, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_18 : CertifiedEndpoint :=
  ⟨⟨15, 18, 4087⟩, 152651831051925187, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_19 : CertifiedEndpoint :=
  ⟨⟨15, 19, 4060⟩, 166777014570646355, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_20 : CertifiedEndpoint :=
  ⟨⟨15, 20, 4033⟩, 180696206332250773, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_21 : CertifiedEndpoint :=
  ⟨⟨15, 21, 4006⟩, 194409406336738441, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_22 : CertifiedEndpoint :=
  ⟨⟨15, 22, 3978⟩, 207864171686717918, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_23 : CertifiedEndpoint :=
  ⟨⟨15, 23, 3950⟩, 221105454670230945, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_24 : CertifiedEndpoint :=
  ⟨⟨15, 24, 3922⟩, 234133255287277522, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_25 : CertifiedEndpoint :=
  ⟨⟨15, 25, 3893⟩, 246883894726441658, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_26 : CertifiedEndpoint :=
  ⟨⟨15, 26, 3864⟩, 259413561189789644, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_15_27_flag : Flag := ⟨15, 27, 3834⟩
private def endpoint_15_27_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_27_base : receiptBase endpoint_15_27_flag endpoint_15_27_sources = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_w0 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 2 190097062159118616 = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_w2 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 2 2 190097062159118616 = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_p4 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 4 190097062159118616 = some 190097062159118616 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 2 2 190097062159118616 190097062159118616 190097062159118616 endpoint_15_27_w0 endpoint_15_27_w2
private theorem endpoint_15_27_w4 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 4 2 190097062159118616 = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_p6 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 6 190097062159118616 = some 190097062159118616 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 4 2 190097062159118616 190097062159118616 190097062159118616 endpoint_15_27_p4 endpoint_15_27_w4
private theorem endpoint_15_27_w6 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 6 2 190097062159118616 = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_p8 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 8 190097062159118616 = some 190097062159118616 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 6 2 190097062159118616 190097062159118616 190097062159118616 endpoint_15_27_p6 endpoint_15_27_w6
private theorem endpoint_15_27_w8 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 8 2 190097062159118616 = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_p10 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 10 190097062159118616 = some 190097062159118616 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 8 2 190097062159118616 190097062159118616 190097062159118616 endpoint_15_27_p8 endpoint_15_27_w8
private theorem endpoint_15_27_w10 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 10 2 190097062159118616 = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_p12 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 12 190097062159118616 = some 190097062159118616 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 10 2 190097062159118616 190097062159118616 190097062159118616 endpoint_15_27_p10 endpoint_15_27_w10
private theorem endpoint_15_27_w12 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 12 2 190097062159118616 = some 190097062159118616 := by decide +kernel
private theorem endpoint_15_27_p14 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 14 190097062159118616 = some 190097062159118616 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 12 2 190097062159118616 190097062159118616 190097062159118616 endpoint_15_27_p12 endpoint_15_27_w12
def endpoint_15_27 : CertifiedEndpoint :=
  ⟨⟨15, 27, 3834⟩, 190097062159118616, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_27_flag endpoint_15_27_sources 14 190097062159118616 190097062159118616 rfl endpoint_15_27_base endpoint_15_27_p14) (by decide)⟩
private def endpoint_15_28_flag : Flag := ⟨15, 28, 3804⟩
private def endpoint_15_28_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_28_base : receiptBase endpoint_15_28_flag endpoint_15_28_sources = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_w0 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 2 194277536954572895 = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_w2 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 2 2 194277536954572895 = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_p4 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 4 194277536954572895 = some 194277536954572895 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 2 2 194277536954572895 194277536954572895 194277536954572895 endpoint_15_28_w0 endpoint_15_28_w2
private theorem endpoint_15_28_w4 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 4 2 194277536954572895 = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_p6 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 6 194277536954572895 = some 194277536954572895 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 4 2 194277536954572895 194277536954572895 194277536954572895 endpoint_15_28_p4 endpoint_15_28_w4
private theorem endpoint_15_28_w6 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 6 2 194277536954572895 = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_p8 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 8 194277536954572895 = some 194277536954572895 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 6 2 194277536954572895 194277536954572895 194277536954572895 endpoint_15_28_p6 endpoint_15_28_w6
private theorem endpoint_15_28_w8 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 8 2 194277536954572895 = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_p10 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 10 194277536954572895 = some 194277536954572895 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 8 2 194277536954572895 194277536954572895 194277536954572895 endpoint_15_28_p8 endpoint_15_28_w8
private theorem endpoint_15_28_w10 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 10 2 194277536954572895 = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_p12 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 12 194277536954572895 = some 194277536954572895 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 10 2 194277536954572895 194277536954572895 194277536954572895 endpoint_15_28_p10 endpoint_15_28_w10
private theorem endpoint_15_28_w12 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 12 2 194277536954572895 = some 194277536954572895 := by decide +kernel
private theorem endpoint_15_28_p14 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 14 194277536954572895 = some 194277536954572895 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 12 2 194277536954572895 194277536954572895 194277536954572895 endpoint_15_28_p12 endpoint_15_28_w12
def endpoint_15_28 : CertifiedEndpoint :=
  ⟨⟨15, 28, 3804⟩, 194277536954572895, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_28_flag endpoint_15_28_sources 14 194277536954572895 194277536954572895 rfl endpoint_15_28_base endpoint_15_28_p14) (by decide)⟩
private def endpoint_15_29_flag : Flag := ⟨15, 29, 3773⟩
private def endpoint_15_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_29_base : receiptBase endpoint_15_29_flag endpoint_15_29_sources = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_w0 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 2 198317294473621622 = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_w2 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 2 2 198317294473621622 = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_p4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 4 198317294473621622 = some 198317294473621622 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 2 2 198317294473621622 198317294473621622 198317294473621622 endpoint_15_29_w0 endpoint_15_29_w2
private theorem endpoint_15_29_w4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 4 2 198317294473621622 = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_p6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 6 198317294473621622 = some 198317294473621622 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 4 2 198317294473621622 198317294473621622 198317294473621622 endpoint_15_29_p4 endpoint_15_29_w4
private theorem endpoint_15_29_w6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 6 2 198317294473621622 = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_p8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 8 198317294473621622 = some 198317294473621622 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 6 2 198317294473621622 198317294473621622 198317294473621622 endpoint_15_29_p6 endpoint_15_29_w6
private theorem endpoint_15_29_w8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 8 2 198317294473621622 = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_p10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 10 198317294473621622 = some 198317294473621622 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 8 2 198317294473621622 198317294473621622 198317294473621622 endpoint_15_29_p8 endpoint_15_29_w8
private theorem endpoint_15_29_w10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 10 2 198317294473621622 = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_p12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 12 198317294473621622 = some 198317294473621622 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 10 2 198317294473621622 198317294473621622 198317294473621622 endpoint_15_29_p10 endpoint_15_29_w10
private theorem endpoint_15_29_w12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 12 2 198317294473621622 = some 198317294473621622 := by decide +kernel
private theorem endpoint_15_29_p14 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 14 198317294473621622 = some 198317294473621622 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 12 2 198317294473621622 198317294473621622 198317294473621622 endpoint_15_29_p12 endpoint_15_29_w12
def endpoint_15_29 : CertifiedEndpoint :=
  ⟨⟨15, 29, 3773⟩, 198317294473621622, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_29_flag endpoint_15_29_sources 14 198317294473621622 198317294473621622 rfl endpoint_15_29_base endpoint_15_29_p14) (by decide)⟩
private def endpoint_15_30_flag : Flag := ⟨15, 30, 3742⟩
private def endpoint_15_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_30_base : receiptBase endpoint_15_30_flag endpoint_15_30_sources = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_w0 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 2 202265334519371754 = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_w2 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 2 2 202265334519371754 = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_p4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 4 202265334519371754 = some 202265334519371754 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 2 2 202265334519371754 202265334519371754 202265334519371754 endpoint_15_30_w0 endpoint_15_30_w2
private theorem endpoint_15_30_w4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 4 2 202265334519371754 = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_p6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 6 202265334519371754 = some 202265334519371754 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 4 2 202265334519371754 202265334519371754 202265334519371754 endpoint_15_30_p4 endpoint_15_30_w4
private theorem endpoint_15_30_w6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 6 2 202265334519371754 = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_p8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 8 202265334519371754 = some 202265334519371754 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 6 2 202265334519371754 202265334519371754 202265334519371754 endpoint_15_30_p6 endpoint_15_30_w6
private theorem endpoint_15_30_w8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 8 2 202265334519371754 = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_p10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 10 202265334519371754 = some 202265334519371754 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 8 2 202265334519371754 202265334519371754 202265334519371754 endpoint_15_30_p8 endpoint_15_30_w8
private theorem endpoint_15_30_w10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 10 2 202265334519371754 = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_p12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 12 202265334519371754 = some 202265334519371754 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 10 2 202265334519371754 202265334519371754 202265334519371754 endpoint_15_30_p10 endpoint_15_30_w10
private theorem endpoint_15_30_w12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 12 2 202265334519371754 = some 202265334519371754 := by decide +kernel
private theorem endpoint_15_30_p14 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 14 202265334519371754 = some 202265334519371754 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 12 2 202265334519371754 202265334519371754 202265334519371754 endpoint_15_30_p12 endpoint_15_30_w12
def endpoint_15_30 : CertifiedEndpoint :=
  ⟨⟨15, 30, 3742⟩, 202265334519371754, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_30_flag endpoint_15_30_sources 14 202265334519371754 202265334519371754 rfl endpoint_15_30_base endpoint_15_30_p14) (by decide)⟩
private def endpoint_15_31_flag : Flag := ⟨15, 31, 3710⟩
private def endpoint_15_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_31_base : receiptBase endpoint_15_31_flag endpoint_15_31_sources = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_w0 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 2 206066835456946666 = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_w2 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 2 2 206066835456946666 = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_p4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 4 206066835456946666 = some 206066835456946666 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 2 2 206066835456946666 206066835456946666 206066835456946666 endpoint_15_31_w0 endpoint_15_31_w2
private theorem endpoint_15_31_w4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 4 2 206066835456946666 = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_p6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 6 206066835456946666 = some 206066835456946666 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 4 2 206066835456946666 206066835456946666 206066835456946666 endpoint_15_31_p4 endpoint_15_31_w4
private theorem endpoint_15_31_w6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 6 2 206066835456946666 = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_p8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 8 206066835456946666 = some 206066835456946666 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 6 2 206066835456946666 206066835456946666 206066835456946666 endpoint_15_31_p6 endpoint_15_31_w6
private theorem endpoint_15_31_w8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 8 2 206066835456946666 = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_p10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 10 206066835456946666 = some 206066835456946666 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 8 2 206066835456946666 206066835456946666 206066835456946666 endpoint_15_31_p8 endpoint_15_31_w8
private theorem endpoint_15_31_w10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 10 2 206066835456946666 = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_p12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 12 206066835456946666 = some 206066835456946666 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 10 2 206066835456946666 206066835456946666 206066835456946666 endpoint_15_31_p10 endpoint_15_31_w10
private theorem endpoint_15_31_w12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 12 2 206066835456946666 = some 206066835456946666 := by decide +kernel
private theorem endpoint_15_31_p14 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 14 206066835456946666 = some 206066835456946666 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 12 2 206066835456946666 206066835456946666 206066835456946666 endpoint_15_31_p12 endpoint_15_31_w12
def endpoint_15_31 : CertifiedEndpoint :=
  ⟨⟨15, 31, 3710⟩, 206066835456946666, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_31_flag endpoint_15_31_sources 14 206066835456946666 206066835456946666 rfl endpoint_15_31_base endpoint_15_31_p14) (by decide)⟩
private def endpoint_15_32_flag : Flag := ⟨15, 32, 3678⟩
private def endpoint_15_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_32_base : receiptBase endpoint_15_32_flag endpoint_15_32_sources = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_w0 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 2 209773708005338149 = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_w2 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 2 2 209773708005338149 = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_p4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 4 209773708005338149 = some 209773708005338149 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 2 2 209773708005338149 209773708005338149 209773708005338149 endpoint_15_32_w0 endpoint_15_32_w2
private theorem endpoint_15_32_w4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 4 2 209773708005338149 = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_p6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 6 209773708005338149 = some 209773708005338149 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 4 2 209773708005338149 209773708005338149 209773708005338149 endpoint_15_32_p4 endpoint_15_32_w4
private theorem endpoint_15_32_w6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 6 2 209773708005338149 = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_p8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 8 209773708005338149 = some 209773708005338149 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 6 2 209773708005338149 209773708005338149 209773708005338149 endpoint_15_32_p6 endpoint_15_32_w6
private theorem endpoint_15_32_w8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 8 2 209773708005338149 = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_p10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 10 209773708005338149 = some 209773708005338149 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 8 2 209773708005338149 209773708005338149 209773708005338149 endpoint_15_32_p8 endpoint_15_32_w8
private theorem endpoint_15_32_w10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 10 2 209773708005338149 = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_p12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 12 209773708005338149 = some 209773708005338149 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 10 2 209773708005338149 209773708005338149 209773708005338149 endpoint_15_32_p10 endpoint_15_32_w10
private theorem endpoint_15_32_w12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 12 2 209773708005338149 = some 209773708005338149 := by decide +kernel
private theorem endpoint_15_32_p14 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 14 209773708005338149 = some 209773708005338149 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 12 2 209773708005338149 209773708005338149 209773708005338149 endpoint_15_32_p12 endpoint_15_32_w12
def endpoint_15_32 : CertifiedEndpoint :=
  ⟨⟨15, 32, 3678⟩, 209773708005338149, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_32_flag endpoint_15_32_sources 14 209773708005338149 209773708005338149 rfl endpoint_15_32_base endpoint_15_32_p14) (by decide)⟩
private def endpoint_15_33_flag : Flag := ⟨15, 33, 3645⟩
private def endpoint_15_33_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_33_base : receiptBase endpoint_15_33_flag endpoint_15_33_sources = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_w0 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 2 213328219613784746 = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_w2 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 2 2 213328219613784746 = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_p4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 4 213328219613784746 = some 213328219613784746 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 2 2 213328219613784746 213328219613784746 213328219613784746 endpoint_15_33_w0 endpoint_15_33_w2
private theorem endpoint_15_33_w4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 4 2 213328219613784746 = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_p6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 6 213328219613784746 = some 213328219613784746 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 4 2 213328219613784746 213328219613784746 213328219613784746 endpoint_15_33_p4 endpoint_15_33_w4
private theorem endpoint_15_33_w6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 6 2 213328219613784746 = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_p8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 8 213328219613784746 = some 213328219613784746 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 6 2 213328219613784746 213328219613784746 213328219613784746 endpoint_15_33_p6 endpoint_15_33_w6
private theorem endpoint_15_33_w8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 8 2 213328219613784746 = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_p10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 10 213328219613784746 = some 213328219613784746 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 8 2 213328219613784746 213328219613784746 213328219613784746 endpoint_15_33_p8 endpoint_15_33_w8
private theorem endpoint_15_33_w10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 10 2 213328219613784746 = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_p12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 12 213328219613784746 = some 213328219613784746 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 10 2 213328219613784746 213328219613784746 213328219613784746 endpoint_15_33_p10 endpoint_15_33_w10
private theorem endpoint_15_33_w12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 12 2 213328219613784746 = some 213328219613784746 := by decide +kernel
private theorem endpoint_15_33_p14 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 14 213328219613784746 = some 213328219613784746 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 12 2 213328219613784746 213328219613784746 213328219613784746 endpoint_15_33_p12 endpoint_15_33_w12
def endpoint_15_33 : CertifiedEndpoint :=
  ⟨⟨15, 33, 3645⟩, 213328219613784746, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_33_flag endpoint_15_33_sources 14 213328219613784746 213328219613784746 rfl endpoint_15_33_base endpoint_15_33_p14) (by decide)⟩
private def endpoint_15_34_flag : Flag := ⟨15, 34, 3612⟩
private def endpoint_15_34_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_34_base : receiptBase endpoint_15_34_flag endpoint_15_34_sources = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_w0 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 2 216751732925598556 = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_w2 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 2 2 216751732925598556 = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_p4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 4 216751732925598556 = some 216751732925598556 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 2 2 216751732925598556 216751732925598556 216751732925598556 endpoint_15_34_w0 endpoint_15_34_w2
private theorem endpoint_15_34_w4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 4 2 216751732925598556 = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_p6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 6 216751732925598556 = some 216751732925598556 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 4 2 216751732925598556 216751732925598556 216751732925598556 endpoint_15_34_p4 endpoint_15_34_w4
private theorem endpoint_15_34_w6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 6 2 216751732925598556 = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_p8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 8 216751732925598556 = some 216751732925598556 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 6 2 216751732925598556 216751732925598556 216751732925598556 endpoint_15_34_p6 endpoint_15_34_w6
private theorem endpoint_15_34_w8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 8 2 216751732925598556 = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_p10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 10 216751732925598556 = some 216751732925598556 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 8 2 216751732925598556 216751732925598556 216751732925598556 endpoint_15_34_p8 endpoint_15_34_w8
private theorem endpoint_15_34_w10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 10 2 216751732925598556 = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_p12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 12 216751732925598556 = some 216751732925598556 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 10 2 216751732925598556 216751732925598556 216751732925598556 endpoint_15_34_p10 endpoint_15_34_w10
private theorem endpoint_15_34_w12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 12 2 216751732925598556 = some 216751732925598556 := by decide +kernel
private theorem endpoint_15_34_p14 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 14 216751732925598556 = some 216751732925598556 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 12 2 216751732925598556 216751732925598556 216751732925598556 endpoint_15_34_p12 endpoint_15_34_w12
def endpoint_15_34 : CertifiedEndpoint :=
  ⟨⟨15, 34, 3612⟩, 216751732925598556, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_34_flag endpoint_15_34_sources 14 216751732925598556 216751732925598556 rfl endpoint_15_34_base endpoint_15_34_p14) (by decide)⟩
private def endpoint_15_35_flag : Flag := ⟨15, 35, 3578⟩
private def endpoint_15_35_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_35_base : receiptBase endpoint_15_35_flag endpoint_15_35_sources = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_w0 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 2 219983071184223286 = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_w2 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 2 2 219983071184223286 = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_p4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 4 219983071184223286 = some 219983071184223286 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 2 2 219983071184223286 219983071184223286 219983071184223286 endpoint_15_35_w0 endpoint_15_35_w2
private theorem endpoint_15_35_w4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 4 2 219983071184223286 = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_p6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 6 219983071184223286 = some 219983071184223286 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 4 2 219983071184223286 219983071184223286 219983071184223286 endpoint_15_35_p4 endpoint_15_35_w4
private theorem endpoint_15_35_w6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 6 2 219983071184223286 = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_p8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 8 219983071184223286 = some 219983071184223286 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 6 2 219983071184223286 219983071184223286 219983071184223286 endpoint_15_35_p6 endpoint_15_35_w6
private theorem endpoint_15_35_w8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 8 2 219983071184223286 = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_p10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 10 219983071184223286 = some 219983071184223286 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 8 2 219983071184223286 219983071184223286 219983071184223286 endpoint_15_35_p8 endpoint_15_35_w8
private theorem endpoint_15_35_w10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 10 2 219983071184223286 = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_p12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 12 219983071184223286 = some 219983071184223286 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 10 2 219983071184223286 219983071184223286 219983071184223286 endpoint_15_35_p10 endpoint_15_35_w10
private theorem endpoint_15_35_w12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 12 2 219983071184223286 = some 219983071184223286 := by decide +kernel
private theorem endpoint_15_35_p14 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 14 219983071184223286 = some 219983071184223286 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 12 2 219983071184223286 219983071184223286 219983071184223286 endpoint_15_35_p12 endpoint_15_35_w12
def endpoint_15_35 : CertifiedEndpoint :=
  ⟨⟨15, 35, 3578⟩, 219983071184223286, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_35_flag endpoint_15_35_sources 14 219983071184223286 219983071184223286 rfl endpoint_15_35_base endpoint_15_35_p14) (by decide)⟩
private def endpoint_15_36_flag : Flag := ⟨15, 36, 3543⟩
private def endpoint_15_36_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_36_base : receiptBase endpoint_15_36_flag endpoint_15_36_sources = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_w0 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 2 224472045385137155 = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_w2 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 2 2 224472045385137155 = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_p4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 4 224472045385137155 = some 224472045385137155 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 2 2 224472045385137155 224472045385137155 224472045385137155 endpoint_15_36_w0 endpoint_15_36_w2
private theorem endpoint_15_36_w4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 4 2 224472045385137155 = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_p6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 6 224472045385137155 = some 224472045385137155 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 4 2 224472045385137155 224472045385137155 224472045385137155 endpoint_15_36_p4 endpoint_15_36_w4
private theorem endpoint_15_36_w6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 6 2 224472045385137155 = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_p8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 8 224472045385137155 = some 224472045385137155 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 6 2 224472045385137155 224472045385137155 224472045385137155 endpoint_15_36_p6 endpoint_15_36_w6
private theorem endpoint_15_36_w8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 8 2 224472045385137155 = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_p10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 10 224472045385137155 = some 224472045385137155 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 8 2 224472045385137155 224472045385137155 224472045385137155 endpoint_15_36_p8 endpoint_15_36_w8
private theorem endpoint_15_36_w10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 10 2 224472045385137155 = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_p12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 12 224472045385137155 = some 224472045385137155 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 10 2 224472045385137155 224472045385137155 224472045385137155 endpoint_15_36_p10 endpoint_15_36_w10
private theorem endpoint_15_36_w12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 12 2 224472045385137155 = some 224472045385137155 := by decide +kernel
private theorem endpoint_15_36_p14 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 14 224472045385137155 = some 224472045385137155 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 12 2 224472045385137155 224472045385137155 224472045385137155 endpoint_15_36_p12 endpoint_15_36_w12
def endpoint_15_36 : CertifiedEndpoint :=
  ⟨⟨15, 36, 3543⟩, 224472045385137155, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_36_flag endpoint_15_36_sources 14 224472045385137155 224472045385137155 rfl endpoint_15_36_base endpoint_15_36_p14) (by decide)⟩
private def endpoint_15_37_flag : Flag := ⟨15, 37, 3507⟩
private def endpoint_15_37_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_37_base : receiptBase endpoint_15_37_flag endpoint_15_37_sources = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_w0 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 2 227370866329199469 = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_w2 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 2 2 227370866329199469 = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_p4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 4 227370866329199469 = some 227370866329199469 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 2 2 227370866329199469 227370866329199469 227370866329199469 endpoint_15_37_w0 endpoint_15_37_w2
private theorem endpoint_15_37_w4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 4 2 227370866329199469 = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_p6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 6 227370866329199469 = some 227370866329199469 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 4 2 227370866329199469 227370866329199469 227370866329199469 endpoint_15_37_p4 endpoint_15_37_w4
private theorem endpoint_15_37_w6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 6 2 227370866329199469 = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_p8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 8 227370866329199469 = some 227370866329199469 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 6 2 227370866329199469 227370866329199469 227370866329199469 endpoint_15_37_p6 endpoint_15_37_w6
private theorem endpoint_15_37_w8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 8 2 227370866329199469 = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_p10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 10 227370866329199469 = some 227370866329199469 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 8 2 227370866329199469 227370866329199469 227370866329199469 endpoint_15_37_p8 endpoint_15_37_w8
private theorem endpoint_15_37_w10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 10 2 227370866329199469 = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_p12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 12 227370866329199469 = some 227370866329199469 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 10 2 227370866329199469 227370866329199469 227370866329199469 endpoint_15_37_p10 endpoint_15_37_w10
private theorem endpoint_15_37_w12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 12 2 227370866329199469 = some 227370866329199469 := by decide +kernel
private theorem endpoint_15_37_p14 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 14 227370866329199469 = some 227370866329199469 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 12 2 227370866329199469 227370866329199469 227370866329199469 endpoint_15_37_p12 endpoint_15_37_w12
def endpoint_15_37 : CertifiedEndpoint :=
  ⟨⟨15, 37, 3507⟩, 227370866329199469, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_37_flag endpoint_15_37_sources 14 227370866329199469 227370866329199469 rfl endpoint_15_37_base endpoint_15_37_p14) (by decide)⟩
private def endpoint_15_38_flag : Flag := ⟨15, 38, 3471⟩
private def endpoint_15_38_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_38_base : receiptBase endpoint_15_38_flag endpoint_15_38_sources = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_w0 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 2 231841991078810995 = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_w2 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 2 2 231841991078810995 = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_p4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 4 231841991078810995 = some 231841991078810995 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 2 2 231841991078810995 231841991078810995 231841991078810995 endpoint_15_38_w0 endpoint_15_38_w2
private theorem endpoint_15_38_w4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 4 2 231841991078810995 = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_p6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 6 231841991078810995 = some 231841991078810995 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 4 2 231841991078810995 231841991078810995 231841991078810995 endpoint_15_38_p4 endpoint_15_38_w4
private theorem endpoint_15_38_w6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 6 2 231841991078810995 = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_p8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 8 231841991078810995 = some 231841991078810995 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 6 2 231841991078810995 231841991078810995 231841991078810995 endpoint_15_38_p6 endpoint_15_38_w6
private theorem endpoint_15_38_w8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 8 2 231841991078810995 = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_p10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 10 231841991078810995 = some 231841991078810995 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 8 2 231841991078810995 231841991078810995 231841991078810995 endpoint_15_38_p8 endpoint_15_38_w8
private theorem endpoint_15_38_w10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 10 2 231841991078810995 = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_p12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 12 231841991078810995 = some 231841991078810995 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 10 2 231841991078810995 231841991078810995 231841991078810995 endpoint_15_38_p10 endpoint_15_38_w10
private theorem endpoint_15_38_w12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 12 2 231841991078810995 = some 231841991078810995 := by decide +kernel
private theorem endpoint_15_38_p14 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 14 231841991078810995 = some 231841991078810995 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 12 2 231841991078810995 231841991078810995 231841991078810995 endpoint_15_38_p12 endpoint_15_38_w12
def endpoint_15_38 : CertifiedEndpoint :=
  ⟨⟨15, 38, 3471⟩, 231841991078810995, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_38_flag endpoint_15_38_sources 14 231841991078810995 231841991078810995 rfl endpoint_15_38_base endpoint_15_38_p14) (by decide)⟩
private def endpoint_15_39_flag : Flag := ⟨15, 39, 3434⟩
private def endpoint_15_39_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_39_base : receiptBase endpoint_15_39_flag endpoint_15_39_sources = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_w0 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 2 234405099980685221 = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_w2 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 2 2 234405099980685221 = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_p4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 4 234405099980685221 = some 234405099980685221 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 2 2 234405099980685221 234405099980685221 234405099980685221 endpoint_15_39_w0 endpoint_15_39_w2
private theorem endpoint_15_39_w4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 4 2 234405099980685221 = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_p6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 6 234405099980685221 = some 234405099980685221 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 4 2 234405099980685221 234405099980685221 234405099980685221 endpoint_15_39_p4 endpoint_15_39_w4
private theorem endpoint_15_39_w6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 6 2 234405099980685221 = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_p8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 8 234405099980685221 = some 234405099980685221 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 6 2 234405099980685221 234405099980685221 234405099980685221 endpoint_15_39_p6 endpoint_15_39_w6
private theorem endpoint_15_39_w8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 8 2 234405099980685221 = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_p10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 10 234405099980685221 = some 234405099980685221 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 8 2 234405099980685221 234405099980685221 234405099980685221 endpoint_15_39_p8 endpoint_15_39_w8
private theorem endpoint_15_39_w10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 10 2 234405099980685221 = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_p12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 12 234405099980685221 = some 234405099980685221 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 10 2 234405099980685221 234405099980685221 234405099980685221 endpoint_15_39_p10 endpoint_15_39_w10
private theorem endpoint_15_39_w12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 12 2 234405099980685221 = some 234405099980685221 := by decide +kernel
private theorem endpoint_15_39_p14 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 14 234405099980685221 = some 234405099980685221 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 12 2 234405099980685221 234405099980685221 234405099980685221 endpoint_15_39_p12 endpoint_15_39_w12
def endpoint_15_39 : CertifiedEndpoint :=
  ⟨⟨15, 39, 3434⟩, 234405099980685221, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_39_flag endpoint_15_39_sources 14 234405099980685221 234405099980685221 rfl endpoint_15_39_base endpoint_15_39_p14) (by decide)⟩
private def endpoint_15_40_flag : Flag := ⟨15, 40, 3396⟩
private def endpoint_15_40_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_40_base : receiptBase endpoint_15_40_flag endpoint_15_40_sources = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_w0 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 2 236792010881656283 = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_w2 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 2 2 236792010881656283 = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_p4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 4 236792010881656283 = some 236792010881656283 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 2 2 236792010881656283 236792010881656283 236792010881656283 endpoint_15_40_w0 endpoint_15_40_w2
private theorem endpoint_15_40_w4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 4 2 236792010881656283 = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_p6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 6 236792010881656283 = some 236792010881656283 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 4 2 236792010881656283 236792010881656283 236792010881656283 endpoint_15_40_p4 endpoint_15_40_w4
private theorem endpoint_15_40_w6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 6 2 236792010881656283 = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_p8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 8 236792010881656283 = some 236792010881656283 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 6 2 236792010881656283 236792010881656283 236792010881656283 endpoint_15_40_p6 endpoint_15_40_w6
private theorem endpoint_15_40_w8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 8 2 236792010881656283 = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_p10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 10 236792010881656283 = some 236792010881656283 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 8 2 236792010881656283 236792010881656283 236792010881656283 endpoint_15_40_p8 endpoint_15_40_w8
private theorem endpoint_15_40_w10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 10 2 236792010881656283 = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_p12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 12 236792010881656283 = some 236792010881656283 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 10 2 236792010881656283 236792010881656283 236792010881656283 endpoint_15_40_p10 endpoint_15_40_w10
private theorem endpoint_15_40_w12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 12 2 236792010881656283 = some 236792010881656283 := by decide +kernel
private theorem endpoint_15_40_p14 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 14 236792010881656283 = some 236792010881656283 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 12 2 236792010881656283 236792010881656283 236792010881656283 endpoint_15_40_p12 endpoint_15_40_w12
def endpoint_15_40 : CertifiedEndpoint :=
  ⟨⟨15, 40, 3396⟩, 236792010881656283, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_40_flag endpoint_15_40_sources 14 236792010881656283 236792010881656283 rfl endpoint_15_40_base endpoint_15_40_p14) (by decide)⟩
private def endpoint_15_41_flag : Flag := ⟨15, 41, 3357⟩
private def endpoint_15_41_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_15_41_base : receiptBase endpoint_15_41_flag endpoint_15_41_sources = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_w0 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 2 237888158731068164 = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_w2 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 2 2 237888158731068164 = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_p4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 4 237888158731068164 = some 237888158731068164 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 2 2 237888158731068164 237888158731068164 237888158731068164 endpoint_15_41_w0 endpoint_15_41_w2
private theorem endpoint_15_41_w4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 4 2 237888158731068164 = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_p6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 6 237888158731068164 = some 237888158731068164 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 4 2 237888158731068164 237888158731068164 237888158731068164 endpoint_15_41_p4 endpoint_15_41_w4
private theorem endpoint_15_41_w6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 6 2 237888158731068164 = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_p8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 8 237888158731068164 = some 237888158731068164 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 6 2 237888158731068164 237888158731068164 237888158731068164 endpoint_15_41_p6 endpoint_15_41_w6
private theorem endpoint_15_41_w8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 8 2 237888158731068164 = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_p10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 10 237888158731068164 = some 237888158731068164 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 8 2 237888158731068164 237888158731068164 237888158731068164 endpoint_15_41_p8 endpoint_15_41_w8
private theorem endpoint_15_41_w10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 10 2 237888158731068164 = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_p12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 12 237888158731068164 = some 237888158731068164 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 10 2 237888158731068164 237888158731068164 237888158731068164 endpoint_15_41_p10 endpoint_15_41_w10
private theorem endpoint_15_41_w12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 12 2 237888158731068164 = some 237888158731068164 := by decide +kernel
private theorem endpoint_15_41_p14 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 14 237888158731068164 = some 237888158731068164 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 12 2 237888158731068164 237888158731068164 237888158731068164 endpoint_15_41_p12 endpoint_15_41_w12
def endpoint_15_41 : CertifiedEndpoint :=
  ⟨⟨15, 41, 3357⟩, 237888158731068164, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_15_41_flag endpoint_15_41_sources 14 237888158731068164 237888158731068164 rfl endpoint_15_41_base endpoint_15_41_p14) (by decide)⟩
private def endpoint_15_42_flag : Flag := ⟨15, 42, 3317⟩
private def endpoint_15_42_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_42_base : receiptBase endpoint_15_42_flag endpoint_15_42_sources = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_w0 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 2 241659404985608379 = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_w2 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 2 2 241659404985608379 = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_p4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 4 241659404985608379 = some 241659404985608379 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 2 2 241659404985608379 241659404985608379 241659404985608379 endpoint_15_42_w0 endpoint_15_42_w2
private theorem endpoint_15_42_w4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 4 2 241659404985608379 = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_p6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 6 241659404985608379 = some 241659404985608379 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 4 2 241659404985608379 241659404985608379 241659404985608379 endpoint_15_42_p4 endpoint_15_42_w4
private theorem endpoint_15_42_w6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 6 2 241659404985608379 = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_p8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 8 241659404985608379 = some 241659404985608379 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 6 2 241659404985608379 241659404985608379 241659404985608379 endpoint_15_42_p6 endpoint_15_42_w6
private theorem endpoint_15_42_w8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 8 2 241659404985608379 = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_p10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 10 241659404985608379 = some 241659404985608379 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 8 2 241659404985608379 241659404985608379 241659404985608379 endpoint_15_42_p8 endpoint_15_42_w8
private theorem endpoint_15_42_w10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 10 2 241659404985608379 = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_p12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 12 241659404985608379 = some 241659404985608379 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 10 2 241659404985608379 241659404985608379 241659404985608379 endpoint_15_42_p10 endpoint_15_42_w10
private theorem endpoint_15_42_w12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 12 2 241659404985608379 = some 241659404985608379 := by decide +kernel
private theorem endpoint_15_42_p14 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 14 241659404985608379 = some 241659404985608379 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 12 2 241659404985608379 241659404985608379 241659404985608379 endpoint_15_42_p12 endpoint_15_42_w12
def endpoint_15_42 : CertifiedEndpoint :=
  ⟨⟨15, 42, 3317⟩, 241659404985608379, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_42_flag endpoint_15_42_sources 14 241659404985608379 241659404985608379 rfl endpoint_15_42_base endpoint_15_42_p14) (by decide)⟩
private def endpoint_15_43_flag : Flag := ⟨15, 43, 3276⟩
private def endpoint_15_43_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_43_base : receiptBase endpoint_15_43_flag endpoint_15_43_sources = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_w0 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 2 243505551950577509 = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_w2 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 2 2 243505551950577509 = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_p4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 4 243505551950577509 = some 243505551950577509 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 2 2 243505551950577509 243505551950577509 243505551950577509 endpoint_15_43_w0 endpoint_15_43_w2
private theorem endpoint_15_43_w4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 4 2 243505551950577509 = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_p6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 6 243505551950577509 = some 243505551950577509 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 4 2 243505551950577509 243505551950577509 243505551950577509 endpoint_15_43_p4 endpoint_15_43_w4
private theorem endpoint_15_43_w6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 6 2 243505551950577509 = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_p8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 8 243505551950577509 = some 243505551950577509 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 6 2 243505551950577509 243505551950577509 243505551950577509 endpoint_15_43_p6 endpoint_15_43_w6
private theorem endpoint_15_43_w8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 8 2 243505551950577509 = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_p10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 10 243505551950577509 = some 243505551950577509 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 8 2 243505551950577509 243505551950577509 243505551950577509 endpoint_15_43_p8 endpoint_15_43_w8
private theorem endpoint_15_43_w10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 10 2 243505551950577509 = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_p12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 12 243505551950577509 = some 243505551950577509 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 10 2 243505551950577509 243505551950577509 243505551950577509 endpoint_15_43_p10 endpoint_15_43_w10
private theorem endpoint_15_43_w12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 12 2 243505551950577509 = some 243505551950577509 := by decide +kernel
private theorem endpoint_15_43_p14 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 14 243505551950577509 = some 243505551950577509 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 12 2 243505551950577509 243505551950577509 243505551950577509 endpoint_15_43_p12 endpoint_15_43_w12
def endpoint_15_43 : CertifiedEndpoint :=
  ⟨⟨15, 43, 3276⟩, 243505551950577509, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_43_flag endpoint_15_43_sources 14 243505551950577509 243505551950577509 rfl endpoint_15_43_base endpoint_15_43_p14) (by decide)⟩
private def endpoint_15_44_flag : Flag := ⟨15, 44, 3235⟩
private def endpoint_15_44_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_44_base : receiptBase endpoint_15_44_flag endpoint_15_44_sources = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_w0 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 2 245232110620358921 = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_w2 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 2 2 245232110620358921 = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_p4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 4 245232110620358921 = some 245232110620358921 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 2 2 245232110620358921 245232110620358921 245232110620358921 endpoint_15_44_w0 endpoint_15_44_w2
private theorem endpoint_15_44_w4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 4 2 245232110620358921 = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_p6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 6 245232110620358921 = some 245232110620358921 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 4 2 245232110620358921 245232110620358921 245232110620358921 endpoint_15_44_p4 endpoint_15_44_w4
private theorem endpoint_15_44_w6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 6 2 245232110620358921 = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_p8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 8 245232110620358921 = some 245232110620358921 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 6 2 245232110620358921 245232110620358921 245232110620358921 endpoint_15_44_p6 endpoint_15_44_w6
private theorem endpoint_15_44_w8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 8 2 245232110620358921 = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_p10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 10 245232110620358921 = some 245232110620358921 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 8 2 245232110620358921 245232110620358921 245232110620358921 endpoint_15_44_p8 endpoint_15_44_w8
private theorem endpoint_15_44_w10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 10 2 245232110620358921 = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_p12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 12 245232110620358921 = some 245232110620358921 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 10 2 245232110620358921 245232110620358921 245232110620358921 endpoint_15_44_p10 endpoint_15_44_w10
private theorem endpoint_15_44_w12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 12 2 245232110620358921 = some 245232110620358921 := by decide +kernel
private theorem endpoint_15_44_p14 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 14 245232110620358921 = some 245232110620358921 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 12 2 245232110620358921 245232110620358921 245232110620358921 endpoint_15_44_p12 endpoint_15_44_w12
def endpoint_15_44 : CertifiedEndpoint :=
  ⟨⟨15, 44, 3235⟩, 245232110620358921, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_44_flag endpoint_15_44_sources 14 245232110620358921 245232110620358921 rfl endpoint_15_44_base endpoint_15_44_p14) (by decide)⟩
private def endpoint_15_45_flag : Flag := ⟨15, 45, 3192⟩
private def endpoint_15_45_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_45_base : receiptBase endpoint_15_45_flag endpoint_15_45_sources = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_w0 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 2 246686606588753127 = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_w2 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 2 2 246686606588753127 = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_p4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 4 246686606588753127 = some 246686606588753127 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 2 2 246686606588753127 246686606588753127 246686606588753127 endpoint_15_45_w0 endpoint_15_45_w2
private theorem endpoint_15_45_w4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 4 2 246686606588753127 = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_p6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 6 246686606588753127 = some 246686606588753127 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 4 2 246686606588753127 246686606588753127 246686606588753127 endpoint_15_45_p4 endpoint_15_45_w4
private theorem endpoint_15_45_w6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 6 2 246686606588753127 = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_p8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 8 246686606588753127 = some 246686606588753127 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 6 2 246686606588753127 246686606588753127 246686606588753127 endpoint_15_45_p6 endpoint_15_45_w6
private theorem endpoint_15_45_w8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 8 2 246686606588753127 = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_p10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 10 246686606588753127 = some 246686606588753127 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 8 2 246686606588753127 246686606588753127 246686606588753127 endpoint_15_45_p8 endpoint_15_45_w8
private theorem endpoint_15_45_w10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 10 2 246686606588753127 = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_p12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 12 246686606588753127 = some 246686606588753127 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 10 2 246686606588753127 246686606588753127 246686606588753127 endpoint_15_45_p10 endpoint_15_45_w10
private theorem endpoint_15_45_w12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 12 2 246686606588753127 = some 246686606588753127 := by decide +kernel
private theorem endpoint_15_45_p14 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 14 246686606588753127 = some 246686606588753127 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 12 2 246686606588753127 246686606588753127 246686606588753127 endpoint_15_45_p12 endpoint_15_45_w12
def endpoint_15_45 : CertifiedEndpoint :=
  ⟨⟨15, 45, 3192⟩, 246686606588753127, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_45_flag endpoint_15_45_sources 14 246686606588753127 246686606588753127 rfl endpoint_15_45_base endpoint_15_45_p14) (by decide)⟩
private def endpoint_15_46_flag : Flag := ⟨15, 46, 3148⟩
private def endpoint_15_46_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_46_base : receiptBase endpoint_15_46_flag endpoint_15_46_sources = some 247938072944691936 := by decide +kernel
private theorem endpoint_15_46_w0 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 2 247938072944691936 = some 248098264794900396 := by decide +kernel
private theorem endpoint_15_46_w2 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 2 2 248098264794900396 = some 248098264794900396 := by decide +kernel
private theorem endpoint_15_46_p4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 4 247938072944691936 = some 248098264794900396 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 2 2 247938072944691936 248098264794900396 248098264794900396 endpoint_15_46_w0 endpoint_15_46_w2
private theorem endpoint_15_46_w4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 4 2 248098264794900396 = some 248098264794900396 := by decide +kernel
private theorem endpoint_15_46_p6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 6 247938072944691936 = some 248098264794900396 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 4 2 247938072944691936 248098264794900396 248098264794900396 endpoint_15_46_p4 endpoint_15_46_w4
private theorem endpoint_15_46_w6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 6 2 248098264794900396 = some 248098264794900396 := by decide +kernel
private theorem endpoint_15_46_p8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 8 247938072944691936 = some 248098264794900396 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 6 2 247938072944691936 248098264794900396 248098264794900396 endpoint_15_46_p6 endpoint_15_46_w6
private theorem endpoint_15_46_w8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 8 2 248098264794900396 = some 248098264794900396 := by decide +kernel
private theorem endpoint_15_46_p10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 10 247938072944691936 = some 248098264794900396 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 8 2 247938072944691936 248098264794900396 248098264794900396 endpoint_15_46_p8 endpoint_15_46_w8
private theorem endpoint_15_46_w10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 10 2 248098264794900396 = some 248098264794900396 := by decide +kernel
private theorem endpoint_15_46_p12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 12 247938072944691936 = some 248098264794900396 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 10 2 247938072944691936 248098264794900396 248098264794900396 endpoint_15_46_p10 endpoint_15_46_w10
private theorem endpoint_15_46_w12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 12 2 248098264794900396 = some 248098264794900396 := by decide +kernel
private theorem endpoint_15_46_p14 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 14 247938072944691936 = some 248098264794900396 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 12 2 247938072944691936 248098264794900396 248098264794900396 endpoint_15_46_p12 endpoint_15_46_w12
def endpoint_15_46 : CertifiedEndpoint :=
  ⟨⟨15, 46, 3148⟩, 248098264794900396, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_46_flag endpoint_15_46_sources 14 247938072944691936 248098264794900396 rfl endpoint_15_46_base endpoint_15_46_p14) (by decide)⟩
private def endpoint_15_47_flag : Flag := ⟨15, 47, 3103⟩
private def endpoint_15_47_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_47_base : receiptBase endpoint_15_47_flag endpoint_15_47_sources = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_w0 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 2 249732306083250185 = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_w2 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 2 2 249732306083250185 = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_p4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 4 249732306083250185 = some 249732306083250185 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 2 2 249732306083250185 249732306083250185 249732306083250185 endpoint_15_47_w0 endpoint_15_47_w2
private theorem endpoint_15_47_w4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 4 2 249732306083250185 = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_p6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 6 249732306083250185 = some 249732306083250185 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 4 2 249732306083250185 249732306083250185 249732306083250185 endpoint_15_47_p4 endpoint_15_47_w4
private theorem endpoint_15_47_w6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 6 2 249732306083250185 = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_p8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 8 249732306083250185 = some 249732306083250185 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 6 2 249732306083250185 249732306083250185 249732306083250185 endpoint_15_47_p6 endpoint_15_47_w6
private theorem endpoint_15_47_w8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 8 2 249732306083250185 = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_p10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 10 249732306083250185 = some 249732306083250185 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 8 2 249732306083250185 249732306083250185 249732306083250185 endpoint_15_47_p8 endpoint_15_47_w8
private theorem endpoint_15_47_w10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 10 2 249732306083250185 = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_p12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 12 249732306083250185 = some 249732306083250185 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 10 2 249732306083250185 249732306083250185 249732306083250185 endpoint_15_47_p10 endpoint_15_47_w10
private theorem endpoint_15_47_w12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 12 2 249732306083250185 = some 249732306083250185 := by decide +kernel
private theorem endpoint_15_47_p14 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 14 249732306083250185 = some 249732306083250185 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 12 2 249732306083250185 249732306083250185 249732306083250185 endpoint_15_47_p12 endpoint_15_47_w12
def endpoint_15_47 : CertifiedEndpoint :=
  ⟨⟨15, 47, 3103⟩, 249732306083250185, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_47_flag endpoint_15_47_sources 14 249732306083250185 249732306083250185 rfl endpoint_15_47_base endpoint_15_47_p14) (by decide)⟩
private def endpoint_15_48_flag : Flag := ⟨15, 48, 3057⟩
private def endpoint_15_48_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_48_base : receiptBase endpoint_15_48_flag endpoint_15_48_sources = some 250574751508262766 := by decide +kernel
private theorem endpoint_15_48_w0 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 2 250574751508262766 = some 251608308913354902 := by decide +kernel
private theorem endpoint_15_48_w2 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 2 2 251608308913354902 = some 251608308913354902 := by decide +kernel
private theorem endpoint_15_48_p4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 4 250574751508262766 = some 251608308913354902 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 2 2 250574751508262766 251608308913354902 251608308913354902 endpoint_15_48_w0 endpoint_15_48_w2
private theorem endpoint_15_48_w4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 4 2 251608308913354902 = some 251608308913354902 := by decide +kernel
private theorem endpoint_15_48_p6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 6 250574751508262766 = some 251608308913354902 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 4 2 250574751508262766 251608308913354902 251608308913354902 endpoint_15_48_p4 endpoint_15_48_w4
private theorem endpoint_15_48_w6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 6 2 251608308913354902 = some 251608308913354902 := by decide +kernel
private theorem endpoint_15_48_p8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 8 250574751508262766 = some 251608308913354902 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 6 2 250574751508262766 251608308913354902 251608308913354902 endpoint_15_48_p6 endpoint_15_48_w6
private theorem endpoint_15_48_w8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 8 2 251608308913354902 = some 251608308913354902 := by decide +kernel
private theorem endpoint_15_48_p10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 10 250574751508262766 = some 251608308913354902 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 8 2 250574751508262766 251608308913354902 251608308913354902 endpoint_15_48_p8 endpoint_15_48_w8
private theorem endpoint_15_48_w10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 10 2 251608308913354902 = some 251608308913354902 := by decide +kernel
private theorem endpoint_15_48_p12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 12 250574751508262766 = some 251608308913354902 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 10 2 250574751508262766 251608308913354902 251608308913354902 endpoint_15_48_p10 endpoint_15_48_w10
private theorem endpoint_15_48_w12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 12 2 251608308913354902 = some 251608308913354902 := by decide +kernel
private theorem endpoint_15_48_p14 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 14 250574751508262766 = some 251608308913354902 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 12 2 250574751508262766 251608308913354902 251608308913354902 endpoint_15_48_p12 endpoint_15_48_w12
def endpoint_15_48 : CertifiedEndpoint :=
  ⟨⟨15, 48, 3057⟩, 251608308913354902, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_48_flag endpoint_15_48_sources 14 250574751508262766 251608308913354902 rfl endpoint_15_48_base endpoint_15_48_p14) (by decide)⟩
private def endpoint_15_49_flag : Flag := ⟨15, 49, 3009⟩
private def endpoint_15_49_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_49_base : receiptBase endpoint_15_49_flag endpoint_15_49_sources = some 251117756848220682 := by decide +kernel
private theorem endpoint_15_49_w0 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 2 251117756848220682 = some 255699271752169361 := by decide +kernel
private theorem endpoint_15_49_w2 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 2 2 255699271752169361 = some 255699271752169361 := by decide +kernel
private theorem endpoint_15_49_p4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 4 251117756848220682 = some 255699271752169361 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 2 2 251117756848220682 255699271752169361 255699271752169361 endpoint_15_49_w0 endpoint_15_49_w2
private theorem endpoint_15_49_w4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 4 2 255699271752169361 = some 255699271752169361 := by decide +kernel
private theorem endpoint_15_49_p6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 6 251117756848220682 = some 255699271752169361 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 4 2 251117756848220682 255699271752169361 255699271752169361 endpoint_15_49_p4 endpoint_15_49_w4
private theorem endpoint_15_49_w6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 6 2 255699271752169361 = some 255699271752169361 := by decide +kernel
private theorem endpoint_15_49_p8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 8 251117756848220682 = some 255699271752169361 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 6 2 251117756848220682 255699271752169361 255699271752169361 endpoint_15_49_p6 endpoint_15_49_w6
private theorem endpoint_15_49_w8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 8 2 255699271752169361 = some 255699271752169361 := by decide +kernel
private theorem endpoint_15_49_p10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 10 251117756848220682 = some 255699271752169361 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 8 2 251117756848220682 255699271752169361 255699271752169361 endpoint_15_49_p8 endpoint_15_49_w8
private theorem endpoint_15_49_w10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 10 2 255699271752169361 = some 255699271752169361 := by decide +kernel
private theorem endpoint_15_49_p12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 12 251117756848220682 = some 255699271752169361 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 10 2 251117756848220682 255699271752169361 255699271752169361 endpoint_15_49_p10 endpoint_15_49_w10
private theorem endpoint_15_49_w12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 12 2 255699271752169361 = some 255699271752169361 := by decide +kernel
private theorem endpoint_15_49_p14 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 14 251117756848220682 = some 255699271752169361 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 12 2 251117756848220682 255699271752169361 255699271752169361 endpoint_15_49_p12 endpoint_15_49_w12
def endpoint_15_49 : CertifiedEndpoint :=
  ⟨⟨15, 49, 3009⟩, 255699271752169361, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_49_flag endpoint_15_49_sources 14 251117756848220682 255699271752169361 rfl endpoint_15_49_base endpoint_15_49_p14) (by decide)⟩
private def endpoint_15_50_flag : Flag := ⟨15, 50, 2961⟩
private def endpoint_15_50_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_50_base : receiptBase endpoint_15_50_flag endpoint_15_50_sources = some 251520129302604075 := by decide +kernel
private theorem endpoint_15_50_w0 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 2 251520129302604075 = some 259677067943801966 := by decide +kernel
private theorem endpoint_15_50_w2 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 2 2 259677067943801966 = some 259677067943801966 := by decide +kernel
private theorem endpoint_15_50_p4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 4 251520129302604075 = some 259677067943801966 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 2 2 251520129302604075 259677067943801966 259677067943801966 endpoint_15_50_w0 endpoint_15_50_w2
private theorem endpoint_15_50_w4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 4 2 259677067943801966 = some 259677067943801966 := by decide +kernel
private theorem endpoint_15_50_p6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 6 251520129302604075 = some 259677067943801966 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 4 2 251520129302604075 259677067943801966 259677067943801966 endpoint_15_50_p4 endpoint_15_50_w4
private theorem endpoint_15_50_w6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 6 2 259677067943801966 = some 259677067943801966 := by decide +kernel
private theorem endpoint_15_50_p8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 8 251520129302604075 = some 259677067943801966 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 6 2 251520129302604075 259677067943801966 259677067943801966 endpoint_15_50_p6 endpoint_15_50_w6
private theorem endpoint_15_50_w8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 8 2 259677067943801966 = some 259677067943801966 := by decide +kernel
private theorem endpoint_15_50_p10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 10 251520129302604075 = some 259677067943801966 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 8 2 251520129302604075 259677067943801966 259677067943801966 endpoint_15_50_p8 endpoint_15_50_w8
private theorem endpoint_15_50_w10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 10 2 259677067943801966 = some 259677067943801966 := by decide +kernel
private theorem endpoint_15_50_p12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 12 251520129302604075 = some 259677067943801966 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 10 2 251520129302604075 259677067943801966 259677067943801966 endpoint_15_50_p10 endpoint_15_50_w10
private theorem endpoint_15_50_w12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 12 2 259677067943801966 = some 259677067943801966 := by decide +kernel
private theorem endpoint_15_50_p14 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 14 251520129302604075 = some 259677067943801966 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 12 2 251520129302604075 259677067943801966 259677067943801966 endpoint_15_50_p12 endpoint_15_50_w12
def endpoint_15_50 : CertifiedEndpoint :=
  ⟨⟨15, 50, 2961⟩, 259677067943801966, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_50_flag endpoint_15_50_sources 14 251520129302604075 259677067943801966 rfl endpoint_15_50_base endpoint_15_50_p14) (by decide)⟩
private def endpoint_15_51_flag : Flag := ⟨15, 51, 2911⟩
private def endpoint_15_51_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_51_base : receiptBase endpoint_15_51_flag endpoint_15_51_sources = some 252439267728928743 := by decide +kernel
private theorem endpoint_15_51_w0 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 2 252439267728928743 = some 259434197239414251 := by decide +kernel
private theorem endpoint_15_51_w2 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 2 2 259434197239414251 = some 259434197239414251 := by decide +kernel
private theorem endpoint_15_51_p4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 4 252439267728928743 = some 259434197239414251 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 2 2 252439267728928743 259434197239414251 259434197239414251 endpoint_15_51_w0 endpoint_15_51_w2
private theorem endpoint_15_51_w4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 4 2 259434197239414251 = some 259434197239414251 := by decide +kernel
private theorem endpoint_15_51_p6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 6 252439267728928743 = some 259434197239414251 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 4 2 252439267728928743 259434197239414251 259434197239414251 endpoint_15_51_p4 endpoint_15_51_w4
private theorem endpoint_15_51_w6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 6 2 259434197239414251 = some 259434197239414251 := by decide +kernel
private theorem endpoint_15_51_p8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 8 252439267728928743 = some 259434197239414251 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 6 2 252439267728928743 259434197239414251 259434197239414251 endpoint_15_51_p6 endpoint_15_51_w6
private theorem endpoint_15_51_w8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 8 2 259434197239414251 = some 259434197239414251 := by decide +kernel
private theorem endpoint_15_51_p10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 10 252439267728928743 = some 259434197239414251 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 8 2 252439267728928743 259434197239414251 259434197239414251 endpoint_15_51_p8 endpoint_15_51_w8
private theorem endpoint_15_51_w10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 10 2 259434197239414251 = some 259434197239414251 := by decide +kernel
private theorem endpoint_15_51_p12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 12 252439267728928743 = some 259434197239414251 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 10 2 252439267728928743 259434197239414251 259434197239414251 endpoint_15_51_p10 endpoint_15_51_w10
private theorem endpoint_15_51_w12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 12 2 259434197239414251 = some 259434197239414251 := by decide +kernel
private theorem endpoint_15_51_p14 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 14 252439267728928743 = some 259434197239414251 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 12 2 252439267728928743 259434197239414251 259434197239414251 endpoint_15_51_p12 endpoint_15_51_w12
def endpoint_15_51 : CertifiedEndpoint :=
  ⟨⟨15, 51, 2911⟩, 259434197239414251, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_51_flag endpoint_15_51_sources 14 252439267728928743 259434197239414251 rfl endpoint_15_51_base endpoint_15_51_p14) (by decide)⟩
private def endpoint_15_52_flag : Flag := ⟨15, 52, 2860⟩
private def endpoint_15_52_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_52_base : receiptBase endpoint_15_52_flag endpoint_15_52_sources = some 252303736067654591 := by decide +kernel
private theorem endpoint_15_52_w0 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 2 252303736067654591 = some 262941261733029774 := by decide +kernel
private theorem endpoint_15_52_w2 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 2 2 262941261733029774 = some 262941261733029774 := by decide +kernel
private theorem endpoint_15_52_p4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 4 252303736067654591 = some 262941261733029774 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 2 2 252303736067654591 262941261733029774 262941261733029774 endpoint_15_52_w0 endpoint_15_52_w2
private theorem endpoint_15_52_w4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 4 2 262941261733029774 = some 262941261733029774 := by decide +kernel
private theorem endpoint_15_52_p6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 6 252303736067654591 = some 262941261733029774 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 4 2 252303736067654591 262941261733029774 262941261733029774 endpoint_15_52_p4 endpoint_15_52_w4
private theorem endpoint_15_52_w6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 6 2 262941261733029774 = some 262941261733029774 := by decide +kernel
private theorem endpoint_15_52_p8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 8 252303736067654591 = some 262941261733029774 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 6 2 252303736067654591 262941261733029774 262941261733029774 endpoint_15_52_p6 endpoint_15_52_w6
private theorem endpoint_15_52_w8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 8 2 262941261733029774 = some 262941261733029774 := by decide +kernel
private theorem endpoint_15_52_p10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 10 252303736067654591 = some 262941261733029774 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 8 2 252303736067654591 262941261733029774 262941261733029774 endpoint_15_52_p8 endpoint_15_52_w8
private theorem endpoint_15_52_w10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 10 2 262941261733029774 = some 262941261733029774 := by decide +kernel
private theorem endpoint_15_52_p12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 12 252303736067654591 = some 262941261733029774 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 10 2 252303736067654591 262941261733029774 262941261733029774 endpoint_15_52_p10 endpoint_15_52_w10
private theorem endpoint_15_52_w12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 12 2 262941261733029774 = some 262941261733029774 := by decide +kernel
private theorem endpoint_15_52_p14 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 14 252303736067654591 = some 262941261733029774 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 12 2 252303736067654591 262941261733029774 262941261733029774 endpoint_15_52_p12 endpoint_15_52_w12
def endpoint_15_52 : CertifiedEndpoint :=
  ⟨⟨15, 52, 2860⟩, 262941261733029774, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_52_flag endpoint_15_52_sources 14 252303736067654591 262941261733029774 rfl endpoint_15_52_base endpoint_15_52_p14) (by decide)⟩
private def endpoint_15_53_flag : Flag := ⟨15, 53, 2807⟩
private def endpoint_15_53_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_53_base : receiptBase endpoint_15_53_flag endpoint_15_53_sources = some 252717452171457065 := by decide +kernel
private theorem endpoint_15_53_w0 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 2 252717452171457065 = some 263603071123927482 := by decide +kernel
private theorem endpoint_15_53_w2 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 2 2 263603071123927482 = some 263603071123927482 := by decide +kernel
private theorem endpoint_15_53_p4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 4 252717452171457065 = some 263603071123927482 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 2 2 252717452171457065 263603071123927482 263603071123927482 endpoint_15_53_w0 endpoint_15_53_w2
private theorem endpoint_15_53_w4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 4 2 263603071123927482 = some 263603071123927482 := by decide +kernel
private theorem endpoint_15_53_p6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 6 252717452171457065 = some 263603071123927482 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 4 2 252717452171457065 263603071123927482 263603071123927482 endpoint_15_53_p4 endpoint_15_53_w4
private theorem endpoint_15_53_w6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 6 2 263603071123927482 = some 263603071123927482 := by decide +kernel
private theorem endpoint_15_53_p8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 8 252717452171457065 = some 263603071123927482 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 6 2 252717452171457065 263603071123927482 263603071123927482 endpoint_15_53_p6 endpoint_15_53_w6
private theorem endpoint_15_53_w8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 8 2 263603071123927482 = some 263603071123927482 := by decide +kernel
private theorem endpoint_15_53_p10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 10 252717452171457065 = some 263603071123927482 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 8 2 252717452171457065 263603071123927482 263603071123927482 endpoint_15_53_p8 endpoint_15_53_w8
private theorem endpoint_15_53_w10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 10 2 263603071123927482 = some 263603071123927482 := by decide +kernel
private theorem endpoint_15_53_p12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 12 252717452171457065 = some 263603071123927482 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 10 2 252717452171457065 263603071123927482 263603071123927482 endpoint_15_53_p10 endpoint_15_53_w10
private theorem endpoint_15_53_w12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 12 2 263603071123927482 = some 263603071123927482 := by decide +kernel
private theorem endpoint_15_53_p14 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 14 252717452171457065 = some 263603071123927482 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 12 2 252717452171457065 263603071123927482 263603071123927482 endpoint_15_53_p12 endpoint_15_53_w12
def endpoint_15_53 : CertifiedEndpoint :=
  ⟨⟨15, 53, 2807⟩, 263603071123927482, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_53_flag endpoint_15_53_sources 14 252717452171457065 263603071123927482 rfl endpoint_15_53_base endpoint_15_53_p14) (by decide)⟩
private def endpoint_15_54_flag : Flag := ⟨15, 54, 2753⟩
private def endpoint_15_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_54_base : receiptBase endpoint_15_54_flag endpoint_15_54_sources = some 252777135840653004 := by decide +kernel
private theorem endpoint_15_54_w0 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 2 252777135840653004 = some 259035137480641398 := by decide +kernel
private theorem endpoint_15_54_w2 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 2 2 259035137480641398 = some 259035137480641398 := by decide +kernel
private theorem endpoint_15_54_p4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 4 252777135840653004 = some 259035137480641398 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 2 2 252777135840653004 259035137480641398 259035137480641398 endpoint_15_54_w0 endpoint_15_54_w2
private theorem endpoint_15_54_w4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 4 2 259035137480641398 = some 259035137480641398 := by decide +kernel
private theorem endpoint_15_54_p6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 6 252777135840653004 = some 259035137480641398 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 4 2 252777135840653004 259035137480641398 259035137480641398 endpoint_15_54_p4 endpoint_15_54_w4
private theorem endpoint_15_54_w6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 6 2 259035137480641398 = some 259035137480641398 := by decide +kernel
private theorem endpoint_15_54_p8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 8 252777135840653004 = some 259035137480641398 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 6 2 252777135840653004 259035137480641398 259035137480641398 endpoint_15_54_p6 endpoint_15_54_w6
private theorem endpoint_15_54_w8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 8 2 259035137480641398 = some 259035137480641398 := by decide +kernel
private theorem endpoint_15_54_p10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 10 252777135840653004 = some 259035137480641398 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 8 2 252777135840653004 259035137480641398 259035137480641398 endpoint_15_54_p8 endpoint_15_54_w8
private theorem endpoint_15_54_w10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 10 2 259035137480641398 = some 259035137480641398 := by decide +kernel
private theorem endpoint_15_54_p12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 12 252777135840653004 = some 259035137480641398 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 10 2 252777135840653004 259035137480641398 259035137480641398 endpoint_15_54_p10 endpoint_15_54_w10
private theorem endpoint_15_54_w12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 12 2 259035137480641398 = some 259035137480641398 := by decide +kernel
private theorem endpoint_15_54_p14 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 14 252777135840653004 = some 259035137480641398 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 12 2 252777135840653004 259035137480641398 259035137480641398 endpoint_15_54_p12 endpoint_15_54_w12
def endpoint_15_54 : CertifiedEndpoint :=
  ⟨⟨15, 54, 2753⟩, 259035137480641398, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_54_flag endpoint_15_54_sources 14 252777135840653004 259035137480641398 rfl endpoint_15_54_base endpoint_15_54_p14) (by decide)⟩
private def endpoint_15_55_flag : Flag := ⟨15, 55, 2697⟩
private def endpoint_15_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_55_base : receiptBase endpoint_15_55_flag endpoint_15_55_sources = some 251728944609896163 := by decide +kernel
private theorem endpoint_15_55_w0 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 2 251728944609896163 = some 261686975136105069 := by decide +kernel
private theorem endpoint_15_55_w2 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 2 2 261686975136105069 = some 261686975136105069 := by decide +kernel
private theorem endpoint_15_55_p4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 4 251728944609896163 = some 261686975136105069 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 2 2 251728944609896163 261686975136105069 261686975136105069 endpoint_15_55_w0 endpoint_15_55_w2
private theorem endpoint_15_55_w4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 4 2 261686975136105069 = some 261686975136105069 := by decide +kernel
private theorem endpoint_15_55_p6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 6 251728944609896163 = some 261686975136105069 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 4 2 251728944609896163 261686975136105069 261686975136105069 endpoint_15_55_p4 endpoint_15_55_w4
private theorem endpoint_15_55_w6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 6 2 261686975136105069 = some 261686975136105069 := by decide +kernel
private theorem endpoint_15_55_p8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 8 251728944609896163 = some 261686975136105069 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 6 2 251728944609896163 261686975136105069 261686975136105069 endpoint_15_55_p6 endpoint_15_55_w6
private theorem endpoint_15_55_w8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 8 2 261686975136105069 = some 261686975136105069 := by decide +kernel
private theorem endpoint_15_55_p10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 10 251728944609896163 = some 261686975136105069 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 8 2 251728944609896163 261686975136105069 261686975136105069 endpoint_15_55_p8 endpoint_15_55_w8
private theorem endpoint_15_55_w10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 10 2 261686975136105069 = some 261686975136105069 := by decide +kernel
private theorem endpoint_15_55_p12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 12 251728944609896163 = some 261686975136105069 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 10 2 251728944609896163 261686975136105069 261686975136105069 endpoint_15_55_p10 endpoint_15_55_w10
private theorem endpoint_15_55_w12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 12 2 261686975136105069 = some 261686975136105069 := by decide +kernel
private theorem endpoint_15_55_p14 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 14 251728944609896163 = some 261686975136105069 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 12 2 251728944609896163 261686975136105069 261686975136105069 endpoint_15_55_p12 endpoint_15_55_w12
def endpoint_15_55 : CertifiedEndpoint :=
  ⟨⟨15, 55, 2697⟩, 261686975136105069, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_55_flag endpoint_15_55_sources 14 251728944609896163 261686975136105069 rfl endpoint_15_55_base endpoint_15_55_p14) (by decide)⟩
private def endpoint_15_56_flag : Flag := ⟨15, 56, 2640⟩
private def endpoint_15_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_56_base : receiptBase endpoint_15_56_flag endpoint_15_56_sources = some 250420323274890729 := by decide +kernel
private theorem endpoint_15_56_w0 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 2 250420323274890729 = some 264153360005450842 := by decide +kernel
private theorem endpoint_15_56_w2 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 2 2 264153360005450842 = some 264153360005450842 := by decide +kernel
private theorem endpoint_15_56_p4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 4 250420323274890729 = some 264153360005450842 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 2 2 250420323274890729 264153360005450842 264153360005450842 endpoint_15_56_w0 endpoint_15_56_w2
private theorem endpoint_15_56_w4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 4 2 264153360005450842 = some 264153360005450842 := by decide +kernel
private theorem endpoint_15_56_p6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 6 250420323274890729 = some 264153360005450842 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 4 2 250420323274890729 264153360005450842 264153360005450842 endpoint_15_56_p4 endpoint_15_56_w4
private theorem endpoint_15_56_w6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 6 2 264153360005450842 = some 264153360005450842 := by decide +kernel
private theorem endpoint_15_56_p8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 8 250420323274890729 = some 264153360005450842 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 6 2 250420323274890729 264153360005450842 264153360005450842 endpoint_15_56_p6 endpoint_15_56_w6
private theorem endpoint_15_56_w8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 8 2 264153360005450842 = some 264153360005450842 := by decide +kernel
private theorem endpoint_15_56_p10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 10 250420323274890729 = some 264153360005450842 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 8 2 250420323274890729 264153360005450842 264153360005450842 endpoint_15_56_p8 endpoint_15_56_w8
private theorem endpoint_15_56_w10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 10 2 264153360005450842 = some 264153360005450842 := by decide +kernel
private theorem endpoint_15_56_p12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 12 250420323274890729 = some 264153360005450842 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 10 2 250420323274890729 264153360005450842 264153360005450842 endpoint_15_56_p10 endpoint_15_56_w10
private theorem endpoint_15_56_w12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 12 2 264153360005450842 = some 264153360005450842 := by decide +kernel
private theorem endpoint_15_56_p14 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 14 250420323274890729 = some 264153360005450842 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 12 2 250420323274890729 264153360005450842 264153360005450842 endpoint_15_56_p12 endpoint_15_56_w12
def endpoint_15_56 : CertifiedEndpoint :=
  ⟨⟨15, 56, 2640⟩, 264153360005450842, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_56_flag endpoint_15_56_sources 14 250420323274890729 264153360005450842 rfl endpoint_15_56_base endpoint_15_56_p14) (by decide)⟩
private def endpoint_15_57_flag : Flag := ⟨15, 57, 2581⟩
private def endpoint_15_57_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_57_base : receiptBase endpoint_15_57_flag endpoint_15_57_sources = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_w0 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 2 254967249214015523 = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_w2 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 2 2 254967249214015523 = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_p4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 4 254967249214015523 = some 254967249214015523 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 2 2 254967249214015523 254967249214015523 254967249214015523 endpoint_15_57_w0 endpoint_15_57_w2
private theorem endpoint_15_57_w4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 4 2 254967249214015523 = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_p6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 6 254967249214015523 = some 254967249214015523 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 4 2 254967249214015523 254967249214015523 254967249214015523 endpoint_15_57_p4 endpoint_15_57_w4
private theorem endpoint_15_57_w6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 6 2 254967249214015523 = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_p8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 8 254967249214015523 = some 254967249214015523 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 6 2 254967249214015523 254967249214015523 254967249214015523 endpoint_15_57_p6 endpoint_15_57_w6
private theorem endpoint_15_57_w8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 8 2 254967249214015523 = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_p10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 10 254967249214015523 = some 254967249214015523 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 8 2 254967249214015523 254967249214015523 254967249214015523 endpoint_15_57_p8 endpoint_15_57_w8
private theorem endpoint_15_57_w10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 10 2 254967249214015523 = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_p12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 12 254967249214015523 = some 254967249214015523 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 10 2 254967249214015523 254967249214015523 254967249214015523 endpoint_15_57_p10 endpoint_15_57_w10
private theorem endpoint_15_57_w12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 12 2 254967249214015523 = some 254967249214015523 := by decide +kernel
private theorem endpoint_15_57_p14 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 14 254967249214015523 = some 254967249214015523 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 12 2 254967249214015523 254967249214015523 254967249214015523 endpoint_15_57_p12 endpoint_15_57_w12
def endpoint_15_57 : CertifiedEndpoint :=
  ⟨⟨15, 57, 2581⟩, 254967249214015523, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_57_flag endpoint_15_57_sources 14 254967249214015523 254967249214015523 rfl endpoint_15_57_base endpoint_15_57_p14) (by decide)⟩
private def endpoint_15_58_flag : Flag := ⟨15, 58, 2520⟩
private def endpoint_15_58_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_58_base : receiptBase endpoint_15_58_flag endpoint_15_58_sources = some 252899572409724452 := by decide +kernel
private theorem endpoint_15_58_w0 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 2 252899572409724452 = some 255744820407995772 := by decide +kernel
private theorem endpoint_15_58_w2 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 2 2 255744820407995772 = some 255744820407995772 := by decide +kernel
private theorem endpoint_15_58_p4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 4 252899572409724452 = some 255744820407995772 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 2 2 252899572409724452 255744820407995772 255744820407995772 endpoint_15_58_w0 endpoint_15_58_w2
private theorem endpoint_15_58_w4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 4 2 255744820407995772 = some 255744820407995772 := by decide +kernel
private theorem endpoint_15_58_p6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 6 252899572409724452 = some 255744820407995772 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 4 2 252899572409724452 255744820407995772 255744820407995772 endpoint_15_58_p4 endpoint_15_58_w4
private theorem endpoint_15_58_w6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 6 2 255744820407995772 = some 255744820407995772 := by decide +kernel
private theorem endpoint_15_58_p8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 8 252899572409724452 = some 255744820407995772 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 6 2 252899572409724452 255744820407995772 255744820407995772 endpoint_15_58_p6 endpoint_15_58_w6
private theorem endpoint_15_58_w8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 8 2 255744820407995772 = some 255744820407995772 := by decide +kernel
private theorem endpoint_15_58_p10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 10 252899572409724452 = some 255744820407995772 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 8 2 252899572409724452 255744820407995772 255744820407995772 endpoint_15_58_p8 endpoint_15_58_w8
private theorem endpoint_15_58_w10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 10 2 255744820407995772 = some 255744820407995772 := by decide +kernel
private theorem endpoint_15_58_p12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 12 252899572409724452 = some 255744820407995772 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 10 2 252899572409724452 255744820407995772 255744820407995772 endpoint_15_58_p10 endpoint_15_58_w10
private theorem endpoint_15_58_w12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 12 2 255744820407995772 = some 255744820407995772 := by decide +kernel
private theorem endpoint_15_58_p14 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 14 252899572409724452 = some 255744820407995772 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 12 2 252899572409724452 255744820407995772 255744820407995772 endpoint_15_58_p12 endpoint_15_58_w12
def endpoint_15_58 : CertifiedEndpoint :=
  ⟨⟨15, 58, 2520⟩, 255744820407995772, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_58_flag endpoint_15_58_sources 14 252899572409724452 255744820407995772 rfl endpoint_15_58_base endpoint_15_58_p14) (by decide)⟩
private def endpoint_15_59_flag : Flag := ⟨15, 59, 2458⟩
private def endpoint_15_59_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_15_59_base : receiptBase endpoint_15_59_flag endpoint_15_59_sources = some 250465355873601135 := by decide +kernel
private theorem endpoint_15_59_w0 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 2 250465355873601135 = some 262381164111731183 := by decide +kernel
private theorem endpoint_15_59_w2 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 2 2 262381164111731183 = some 262381164111731183 := by decide +kernel
private theorem endpoint_15_59_p4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 4 250465355873601135 = some 262381164111731183 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 2 2 250465355873601135 262381164111731183 262381164111731183 endpoint_15_59_w0 endpoint_15_59_w2
private theorem endpoint_15_59_w4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 4 2 262381164111731183 = some 262381164111731183 := by decide +kernel
private theorem endpoint_15_59_p6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 6 250465355873601135 = some 262381164111731183 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 4 2 250465355873601135 262381164111731183 262381164111731183 endpoint_15_59_p4 endpoint_15_59_w4
private theorem endpoint_15_59_w6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 6 2 262381164111731183 = some 262381164111731183 := by decide +kernel
private theorem endpoint_15_59_p8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 8 250465355873601135 = some 262381164111731183 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 6 2 250465355873601135 262381164111731183 262381164111731183 endpoint_15_59_p6 endpoint_15_59_w6
private theorem endpoint_15_59_w8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 8 2 262381164111731183 = some 262381164111731183 := by decide +kernel
private theorem endpoint_15_59_p10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 10 250465355873601135 = some 262381164111731183 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 8 2 250465355873601135 262381164111731183 262381164111731183 endpoint_15_59_p8 endpoint_15_59_w8
private theorem endpoint_15_59_w10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 10 2 262381164111731183 = some 262381164111731183 := by decide +kernel
private theorem endpoint_15_59_p12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 12 250465355873601135 = some 262381164111731183 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 10 2 250465355873601135 262381164111731183 262381164111731183 endpoint_15_59_p10 endpoint_15_59_w10
private theorem endpoint_15_59_w12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 12 2 262381164111731183 = some 262381164111731183 := by decide +kernel
private theorem endpoint_15_59_p14 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 14 250465355873601135 = some 262381164111731183 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 12 2 250465355873601135 262381164111731183 262381164111731183 endpoint_15_59_p12 endpoint_15_59_w12
def endpoint_15_59 : CertifiedEndpoint :=
  ⟨⟨15, 59, 2458⟩, 262381164111731183, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_15_59_flag endpoint_15_59_sources 14 250465355873601135 262381164111731183 rfl endpoint_15_59_base endpoint_15_59_p14) (by decide)⟩
private def endpoint_15_60_flag : Flag := ⟨15, 60, 2393⟩
private def endpoint_15_60_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_60_base : receiptBase endpoint_15_60_flag endpoint_15_60_sources = some 247713751974171927 := by decide +kernel
private theorem endpoint_15_60_w0 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 2 247713751974171927 = some 258459724812259974 := by decide +kernel
private theorem endpoint_15_60_w2 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 2 2 258459724812259974 = some 258459724812259974 := by decide +kernel
private theorem endpoint_15_60_p4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 4 247713751974171927 = some 258459724812259974 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 2 2 247713751974171927 258459724812259974 258459724812259974 endpoint_15_60_w0 endpoint_15_60_w2
private theorem endpoint_15_60_w4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 4 2 258459724812259974 = some 258459724812259974 := by decide +kernel
private theorem endpoint_15_60_p6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 6 247713751974171927 = some 258459724812259974 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 4 2 247713751974171927 258459724812259974 258459724812259974 endpoint_15_60_p4 endpoint_15_60_w4
private theorem endpoint_15_60_w6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 6 2 258459724812259974 = some 258459724812259974 := by decide +kernel
private theorem endpoint_15_60_p8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 8 247713751974171927 = some 258459724812259974 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 6 2 247713751974171927 258459724812259974 258459724812259974 endpoint_15_60_p6 endpoint_15_60_w6
private theorem endpoint_15_60_w8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 8 2 258459724812259974 = some 258459724812259974 := by decide +kernel
private theorem endpoint_15_60_p10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 10 247713751974171927 = some 258459724812259974 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 8 2 247713751974171927 258459724812259974 258459724812259974 endpoint_15_60_p8 endpoint_15_60_w8
private theorem endpoint_15_60_w10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 10 2 258459724812259974 = some 258459724812259974 := by decide +kernel
private theorem endpoint_15_60_p12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 12 247713751974171927 = some 258459724812259974 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 10 2 247713751974171927 258459724812259974 258459724812259974 endpoint_15_60_p10 endpoint_15_60_w10
private theorem endpoint_15_60_w12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 12 2 258459724812259974 = some 258459724812259974 := by decide +kernel
private theorem endpoint_15_60_p14 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 14 247713751974171927 = some 258459724812259974 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 12 2 247713751974171927 258459724812259974 258459724812259974 endpoint_15_60_p12 endpoint_15_60_w12
def endpoint_15_60 : CertifiedEndpoint :=
  ⟨⟨15, 60, 2393⟩, 258459724812259974, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_60_flag endpoint_15_60_sources 14 247713751974171927 258459724812259974 rfl endpoint_15_60_base endpoint_15_60_p14) (by decide)⟩
private def endpoint_15_61_flag : Flag := ⟨15, 61, 2327⟩
private def endpoint_15_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_61_base : receiptBase endpoint_15_61_flag endpoint_15_61_sources = some 244580818225369451 := by decide +kernel
private theorem endpoint_15_61_w0 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 2 244580818225369451 = some 259445004384926175 := by decide +kernel
private theorem endpoint_15_61_w2 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 2 2 259445004384926175 = some 259445004384926175 := by decide +kernel
private theorem endpoint_15_61_p4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 4 244580818225369451 = some 259445004384926175 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 2 2 244580818225369451 259445004384926175 259445004384926175 endpoint_15_61_w0 endpoint_15_61_w2
private theorem endpoint_15_61_w4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 4 2 259445004384926175 = some 259445004384926175 := by decide +kernel
private theorem endpoint_15_61_p6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 6 244580818225369451 = some 259445004384926175 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 4 2 244580818225369451 259445004384926175 259445004384926175 endpoint_15_61_p4 endpoint_15_61_w4
private theorem endpoint_15_61_w6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 6 2 259445004384926175 = some 259445004384926175 := by decide +kernel
private theorem endpoint_15_61_p8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 8 244580818225369451 = some 259445004384926175 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 6 2 244580818225369451 259445004384926175 259445004384926175 endpoint_15_61_p6 endpoint_15_61_w6
private theorem endpoint_15_61_w8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 8 2 259445004384926175 = some 259445004384926175 := by decide +kernel
private theorem endpoint_15_61_p10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 10 244580818225369451 = some 259445004384926175 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 8 2 244580818225369451 259445004384926175 259445004384926175 endpoint_15_61_p8 endpoint_15_61_w8
private theorem endpoint_15_61_w10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 10 2 259445004384926175 = some 259445004384926175 := by decide +kernel
private theorem endpoint_15_61_p12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 12 244580818225369451 = some 259445004384926175 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 10 2 244580818225369451 259445004384926175 259445004384926175 endpoint_15_61_p10 endpoint_15_61_w10
private theorem endpoint_15_61_w12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 12 2 259445004384926175 = some 259445004384926175 := by decide +kernel
private theorem endpoint_15_61_p14 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 14 244580818225369451 = some 259445004384926175 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 12 2 244580818225369451 259445004384926175 259445004384926175 endpoint_15_61_p12 endpoint_15_61_w12
def endpoint_15_61 : CertifiedEndpoint :=
  ⟨⟨15, 61, 2327⟩, 259445004384926175, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_61_flag endpoint_15_61_sources 14 244580818225369451 259445004384926175 rfl endpoint_15_61_base endpoint_15_61_p14) (by decide)⟩
private def endpoint_15_62_flag : Flag := ⟨15, 62, 2258⟩
private def endpoint_15_62_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_62_base : receiptBase endpoint_15_62_flag endpoint_15_62_sources = some 240939474948922768 := by decide +kernel
private theorem endpoint_15_62_w0 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 2 240939474948922768 = some 260093403953175124 := by decide +kernel
private theorem endpoint_15_62_w2 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 2 2 260093403953175124 = some 260093403953175124 := by decide +kernel
private theorem endpoint_15_62_p4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 4 240939474948922768 = some 260093403953175124 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 2 2 240939474948922768 260093403953175124 260093403953175124 endpoint_15_62_w0 endpoint_15_62_w2
private theorem endpoint_15_62_w4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 4 2 260093403953175124 = some 260093403953175124 := by decide +kernel
private theorem endpoint_15_62_p6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 6 240939474948922768 = some 260093403953175124 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 4 2 240939474948922768 260093403953175124 260093403953175124 endpoint_15_62_p4 endpoint_15_62_w4
private theorem endpoint_15_62_w6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 6 2 260093403953175124 = some 260093403953175124 := by decide +kernel
private theorem endpoint_15_62_p8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 8 240939474948922768 = some 260093403953175124 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 6 2 240939474948922768 260093403953175124 260093403953175124 endpoint_15_62_p6 endpoint_15_62_w6
private theorem endpoint_15_62_w8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 8 2 260093403953175124 = some 260093403953175124 := by decide +kernel
private theorem endpoint_15_62_p10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 10 240939474948922768 = some 260093403953175124 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 8 2 240939474948922768 260093403953175124 260093403953175124 endpoint_15_62_p8 endpoint_15_62_w8
private theorem endpoint_15_62_w10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 10 2 260093403953175124 = some 260093403953175124 := by decide +kernel
private theorem endpoint_15_62_p12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 12 240939474948922768 = some 260093403953175124 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 10 2 240939474948922768 260093403953175124 260093403953175124 endpoint_15_62_p10 endpoint_15_62_w10
private theorem endpoint_15_62_w12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 12 2 260093403953175124 = some 260093403953175124 := by decide +kernel
private theorem endpoint_15_62_p14 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 14 240939474948922768 = some 260093403953175124 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 12 2 240939474948922768 260093403953175124 260093403953175124 endpoint_15_62_p12 endpoint_15_62_w12
def endpoint_15_62 : CertifiedEndpoint :=
  ⟨⟨15, 62, 2258⟩, 260093403953175124, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_62_flag endpoint_15_62_sources 14 240939474948922768 260093403953175124 rfl endpoint_15_62_base endpoint_15_62_p14) (by decide)⟩
private def endpoint_15_63_flag : Flag := ⟨15, 63, 2188⟩
private def endpoint_15_63_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_63_base : receiptBase endpoint_15_63_flag endpoint_15_63_sources = some 238018562599517534 := by decide +kernel
private theorem endpoint_15_63_w0 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 2 238018562599517534 = some 247163578300232412 := by decide +kernel
private theorem endpoint_15_63_w2 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 2 2 247163578300232412 = some 247163578300232412 := by decide +kernel
private theorem endpoint_15_63_p4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 4 238018562599517534 = some 247163578300232412 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 2 2 238018562599517534 247163578300232412 247163578300232412 endpoint_15_63_w0 endpoint_15_63_w2
private theorem endpoint_15_63_w4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 4 2 247163578300232412 = some 247163578300232412 := by decide +kernel
private theorem endpoint_15_63_p6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 6 238018562599517534 = some 247163578300232412 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 4 2 238018562599517534 247163578300232412 247163578300232412 endpoint_15_63_p4 endpoint_15_63_w4
private theorem endpoint_15_63_w6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 6 2 247163578300232412 = some 247163578300232412 := by decide +kernel
private theorem endpoint_15_63_p8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 8 238018562599517534 = some 247163578300232412 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 6 2 238018562599517534 247163578300232412 247163578300232412 endpoint_15_63_p6 endpoint_15_63_w6
private theorem endpoint_15_63_w8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 8 2 247163578300232412 = some 247163578300232412 := by decide +kernel
private theorem endpoint_15_63_p10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 10 238018562599517534 = some 247163578300232412 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 8 2 238018562599517534 247163578300232412 247163578300232412 endpoint_15_63_p8 endpoint_15_63_w8
private theorem endpoint_15_63_w10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 10 2 247163578300232412 = some 247163578300232412 := by decide +kernel
private theorem endpoint_15_63_p12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 12 238018562599517534 = some 247163578300232412 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 10 2 238018562599517534 247163578300232412 247163578300232412 endpoint_15_63_p10 endpoint_15_63_w10
private theorem endpoint_15_63_w12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 12 2 247163578300232412 = some 247163578300232412 := by decide +kernel
private theorem endpoint_15_63_p14 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 14 238018562599517534 = some 247163578300232412 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 12 2 238018562599517534 247163578300232412 247163578300232412 endpoint_15_63_p12 endpoint_15_63_w12
def endpoint_15_63 : CertifiedEndpoint :=
  ⟨⟨15, 63, 2188⟩, 247163578300232412, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_63_flag endpoint_15_63_sources 14 238018562599517534 247163578300232412 rfl endpoint_15_63_base endpoint_15_63_p14) (by decide)⟩
private def endpoint_15_64_flag : Flag := ⟨15, 64, 2115⟩
private def endpoint_15_64_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_64_base : receiptBase endpoint_15_64_flag endpoint_15_64_sources = some 233502396421781295 := by decide +kernel
private theorem endpoint_15_64_w0 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 2 233502396421781295 = some 246992056576063046 := by decide +kernel
private theorem endpoint_15_64_w2 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 2 2 246992056576063046 = some 246992056576063046 := by decide +kernel
private theorem endpoint_15_64_p4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 4 233502396421781295 = some 246992056576063046 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 2 2 233502396421781295 246992056576063046 246992056576063046 endpoint_15_64_w0 endpoint_15_64_w2
private theorem endpoint_15_64_w4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 4 2 246992056576063046 = some 246992056576063046 := by decide +kernel
private theorem endpoint_15_64_p6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 6 233502396421781295 = some 246992056576063046 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 4 2 233502396421781295 246992056576063046 246992056576063046 endpoint_15_64_p4 endpoint_15_64_w4
private theorem endpoint_15_64_w6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 6 2 246992056576063046 = some 246992056576063046 := by decide +kernel
private theorem endpoint_15_64_p8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 8 233502396421781295 = some 246992056576063046 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 6 2 233502396421781295 246992056576063046 246992056576063046 endpoint_15_64_p6 endpoint_15_64_w6
private theorem endpoint_15_64_w8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 8 2 246992056576063046 = some 246992056576063046 := by decide +kernel
private theorem endpoint_15_64_p10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 10 233502396421781295 = some 246992056576063046 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 8 2 233502396421781295 246992056576063046 246992056576063046 endpoint_15_64_p8 endpoint_15_64_w8
private theorem endpoint_15_64_w10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 10 2 246992056576063046 = some 246992056576063046 := by decide +kernel
private theorem endpoint_15_64_p12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 12 233502396421781295 = some 246992056576063046 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 10 2 233502396421781295 246992056576063046 246992056576063046 endpoint_15_64_p10 endpoint_15_64_w10
private theorem endpoint_15_64_w12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 12 2 246992056576063046 = some 246992056576063046 := by decide +kernel
private theorem endpoint_15_64_p14 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 14 233502396421781295 = some 246992056576063046 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 12 2 233502396421781295 246992056576063046 246992056576063046 endpoint_15_64_p12 endpoint_15_64_w12
def endpoint_15_64 : CertifiedEndpoint :=
  ⟨⟨15, 64, 2115⟩, 246992056576063046, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_64_flag endpoint_15_64_sources 14 233502396421781295 246992056576063046 rfl endpoint_15_64_base endpoint_15_64_p14) (by decide)⟩
private def endpoint_15_65_flag : Flag := ⟨15, 65, 2039⟩
private def endpoint_15_65_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_65_base : receiptBase endpoint_15_65_flag endpoint_15_65_sources = some 228439142835366695 := by decide +kernel
private theorem endpoint_15_65_w0 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 2 228439142835366695 = some 246457377575838575 := by decide +kernel
private theorem endpoint_15_65_w2 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 2 2 246457377575838575 = some 246457377575838575 := by decide +kernel
private theorem endpoint_15_65_p4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 4 228439142835366695 = some 246457377575838575 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 2 2 228439142835366695 246457377575838575 246457377575838575 endpoint_15_65_w0 endpoint_15_65_w2
private theorem endpoint_15_65_w4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 4 2 246457377575838575 = some 246457377575838575 := by decide +kernel
private theorem endpoint_15_65_p6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 6 228439142835366695 = some 246457377575838575 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 4 2 228439142835366695 246457377575838575 246457377575838575 endpoint_15_65_p4 endpoint_15_65_w4
private theorem endpoint_15_65_w6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 6 2 246457377575838575 = some 246457377575838575 := by decide +kernel
private theorem endpoint_15_65_p8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 8 228439142835366695 = some 246457377575838575 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 6 2 228439142835366695 246457377575838575 246457377575838575 endpoint_15_65_p6 endpoint_15_65_w6
private theorem endpoint_15_65_w8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 8 2 246457377575838575 = some 246457377575838575 := by decide +kernel
private theorem endpoint_15_65_p10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 10 228439142835366695 = some 246457377575838575 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 8 2 228439142835366695 246457377575838575 246457377575838575 endpoint_15_65_p8 endpoint_15_65_w8
private theorem endpoint_15_65_w10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 10 2 246457377575838575 = some 246457377575838575 := by decide +kernel
private theorem endpoint_15_65_p12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 12 228439142835366695 = some 246457377575838575 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 10 2 228439142835366695 246457377575838575 246457377575838575 endpoint_15_65_p10 endpoint_15_65_w10
private theorem endpoint_15_65_w12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 12 2 246457377575838575 = some 246457377575838575 := by decide +kernel
private theorem endpoint_15_65_p14 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 14 228439142835366695 = some 246457377575838575 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 12 2 228439142835366695 246457377575838575 246457377575838575 endpoint_15_65_p12 endpoint_15_65_w12
def endpoint_15_65 : CertifiedEndpoint :=
  ⟨⟨15, 65, 2039⟩, 246457377575838575, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_65_flag endpoint_15_65_sources 14 228439142835366695 246457377575838575 rfl endpoint_15_65_base endpoint_15_65_p14) (by decide)⟩
private def endpoint_15_66_flag : Flag := ⟨15, 66, 1961⟩
private def endpoint_15_66_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_15_66_base : receiptBase endpoint_15_66_flag endpoint_15_66_sources = some 224149275066019862 := by decide +kernel
private theorem endpoint_15_66_w0 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 2 224149275066019862 = some 238706767221225342 := by decide +kernel
private theorem endpoint_15_66_w2 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 2 2 238706767221225342 = some 238706767221225342 := by decide +kernel
private theorem endpoint_15_66_p4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 4 224149275066019862 = some 238706767221225342 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 2 2 224149275066019862 238706767221225342 238706767221225342 endpoint_15_66_w0 endpoint_15_66_w2
private theorem endpoint_15_66_w4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 4 2 238706767221225342 = some 238706767221225342 := by decide +kernel
private theorem endpoint_15_66_p6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 6 224149275066019862 = some 238706767221225342 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 4 2 224149275066019862 238706767221225342 238706767221225342 endpoint_15_66_p4 endpoint_15_66_w4
private theorem endpoint_15_66_w6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 6 2 238706767221225342 = some 238706767221225342 := by decide +kernel
private theorem endpoint_15_66_p8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 8 224149275066019862 = some 238706767221225342 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 6 2 224149275066019862 238706767221225342 238706767221225342 endpoint_15_66_p6 endpoint_15_66_w6
private theorem endpoint_15_66_w8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 8 2 238706767221225342 = some 238706767221225342 := by decide +kernel
private theorem endpoint_15_66_p10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 10 224149275066019862 = some 238706767221225342 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 8 2 224149275066019862 238706767221225342 238706767221225342 endpoint_15_66_p8 endpoint_15_66_w8
private theorem endpoint_15_66_w10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 10 2 238706767221225342 = some 238706767221225342 := by decide +kernel
private theorem endpoint_15_66_p12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 12 224149275066019862 = some 238706767221225342 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 10 2 224149275066019862 238706767221225342 238706767221225342 endpoint_15_66_p10 endpoint_15_66_w10
private theorem endpoint_15_66_w12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 12 2 238706767221225342 = some 238706767221225342 := by decide +kernel
private theorem endpoint_15_66_p14 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 14 224149275066019862 = some 238706767221225342 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 12 2 224149275066019862 238706767221225342 238706767221225342 endpoint_15_66_p12 endpoint_15_66_w12
def endpoint_15_66 : CertifiedEndpoint :=
  ⟨⟨15, 66, 1961⟩, 238706767221225342, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_15_66_flag endpoint_15_66_sources 14 224149275066019862 238706767221225342 rfl endpoint_15_66_base endpoint_15_66_p14) (by decide)⟩
private def endpoint_15_67_flag : Flag := ⟨15, 67, 1881⟩
private def endpoint_15_67_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_67_base : receiptBase endpoint_15_67_flag endpoint_15_67_sources = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_w0 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 2 220903378256927616 = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_w2 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 2 2 220903378256927616 = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_p4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 4 220903378256927616 = some 220903378256927616 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 2 2 220903378256927616 220903378256927616 220903378256927616 endpoint_15_67_w0 endpoint_15_67_w2
private theorem endpoint_15_67_w4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 4 2 220903378256927616 = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_p6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 6 220903378256927616 = some 220903378256927616 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 4 2 220903378256927616 220903378256927616 220903378256927616 endpoint_15_67_p4 endpoint_15_67_w4
private theorem endpoint_15_67_w6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 6 2 220903378256927616 = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_p8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 8 220903378256927616 = some 220903378256927616 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 6 2 220903378256927616 220903378256927616 220903378256927616 endpoint_15_67_p6 endpoint_15_67_w6
private theorem endpoint_15_67_w8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 8 2 220903378256927616 = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_p10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 10 220903378256927616 = some 220903378256927616 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 8 2 220903378256927616 220903378256927616 220903378256927616 endpoint_15_67_p8 endpoint_15_67_w8
private theorem endpoint_15_67_w10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 10 2 220903378256927616 = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_p12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 12 220903378256927616 = some 220903378256927616 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 10 2 220903378256927616 220903378256927616 220903378256927616 endpoint_15_67_p10 endpoint_15_67_w10
private theorem endpoint_15_67_w12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 12 2 220903378256927616 = some 220903378256927616 := by decide +kernel
private theorem endpoint_15_67_p14 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 14 220903378256927616 = some 220903378256927616 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 12 2 220903378256927616 220903378256927616 220903378256927616 endpoint_15_67_p12 endpoint_15_67_w12
def endpoint_15_67 : CertifiedEndpoint :=
  ⟨⟨15, 67, 1881⟩, 220903378256927616, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_67_flag endpoint_15_67_sources 14 220903378256927616 220903378256927616 rfl endpoint_15_67_base endpoint_15_67_p14) (by decide)⟩
private def endpoint_15_68_flag : Flag := ⟨15, 68, 1798⟩
private def endpoint_15_68_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_68_base : receiptBase endpoint_15_68_flag endpoint_15_68_sources = some 214040125318223425 := by decide +kernel
private theorem endpoint_15_68_w0 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 2 214040125318223425 = some 218525847904330802 := by decide +kernel
private theorem endpoint_15_68_w2 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 2 2 218525847904330802 = some 218525847904330802 := by decide +kernel
private theorem endpoint_15_68_p4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 4 214040125318223425 = some 218525847904330802 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 2 2 214040125318223425 218525847904330802 218525847904330802 endpoint_15_68_w0 endpoint_15_68_w2
private theorem endpoint_15_68_w4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 4 2 218525847904330802 = some 218525847904330802 := by decide +kernel
private theorem endpoint_15_68_p6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 6 214040125318223425 = some 218525847904330802 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 4 2 214040125318223425 218525847904330802 218525847904330802 endpoint_15_68_p4 endpoint_15_68_w4
private theorem endpoint_15_68_w6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 6 2 218525847904330802 = some 218525847904330802 := by decide +kernel
private theorem endpoint_15_68_p8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 8 214040125318223425 = some 218525847904330802 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 6 2 214040125318223425 218525847904330802 218525847904330802 endpoint_15_68_p6 endpoint_15_68_w6
private theorem endpoint_15_68_w8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 8 2 218525847904330802 = some 218525847904330802 := by decide +kernel
private theorem endpoint_15_68_p10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 10 214040125318223425 = some 218525847904330802 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 8 2 214040125318223425 218525847904330802 218525847904330802 endpoint_15_68_p8 endpoint_15_68_w8
private theorem endpoint_15_68_w10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 10 2 218525847904330802 = some 218525847904330802 := by decide +kernel
private theorem endpoint_15_68_p12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 12 214040125318223425 = some 218525847904330802 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 10 2 214040125318223425 218525847904330802 218525847904330802 endpoint_15_68_p10 endpoint_15_68_w10
private theorem endpoint_15_68_w12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 12 2 218525847904330802 = some 218525847904330802 := by decide +kernel
private theorem endpoint_15_68_p14 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 14 214040125318223425 = some 218525847904330802 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 12 2 214040125318223425 218525847904330802 218525847904330802 endpoint_15_68_p12 endpoint_15_68_w12
def endpoint_15_68 : CertifiedEndpoint :=
  ⟨⟨15, 68, 1798⟩, 218525847904330802, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_68_flag endpoint_15_68_sources 14 214040125318223425 218525847904330802 rfl endpoint_15_68_base endpoint_15_68_p14) (by decide)⟩
private def endpoint_15_69_flag : Flag := ⟨15, 69, 1711⟩
private def endpoint_15_69_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_69_base : receiptBase endpoint_15_69_flag endpoint_15_69_sources = some 206440730786111079 := by decide +kernel
private theorem endpoint_15_69_w0 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 2 206440730786111079 = some 216102237624812049 := by decide +kernel
private theorem endpoint_15_69_w2 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 2 2 216102237624812049 = some 216102237624812049 := by decide +kernel
private theorem endpoint_15_69_p4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 4 206440730786111079 = some 216102237624812049 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 2 2 206440730786111079 216102237624812049 216102237624812049 endpoint_15_69_w0 endpoint_15_69_w2
private theorem endpoint_15_69_w4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 4 2 216102237624812049 = some 216102237624812049 := by decide +kernel
private theorem endpoint_15_69_p6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 6 206440730786111079 = some 216102237624812049 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 4 2 206440730786111079 216102237624812049 216102237624812049 endpoint_15_69_p4 endpoint_15_69_w4
private theorem endpoint_15_69_w6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 6 2 216102237624812049 = some 216102237624812049 := by decide +kernel
private theorem endpoint_15_69_p8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 8 206440730786111079 = some 216102237624812049 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 6 2 206440730786111079 216102237624812049 216102237624812049 endpoint_15_69_p6 endpoint_15_69_w6
private theorem endpoint_15_69_w8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 8 2 216102237624812049 = some 216102237624812049 := by decide +kernel
private theorem endpoint_15_69_p10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 10 206440730786111079 = some 216102237624812049 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 8 2 206440730786111079 216102237624812049 216102237624812049 endpoint_15_69_p8 endpoint_15_69_w8
private theorem endpoint_15_69_w10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 10 2 216102237624812049 = some 216102237624812049 := by decide +kernel
private theorem endpoint_15_69_p12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 12 206440730786111079 = some 216102237624812049 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 10 2 206440730786111079 216102237624812049 216102237624812049 endpoint_15_69_p10 endpoint_15_69_w10
private theorem endpoint_15_69_w12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 12 2 216102237624812049 = some 216102237624812049 := by decide +kernel
private theorem endpoint_15_69_p14 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 14 206440730786111079 = some 216102237624812049 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 12 2 206440730786111079 216102237624812049 216102237624812049 endpoint_15_69_p12 endpoint_15_69_w12
def endpoint_15_69 : CertifiedEndpoint :=
  ⟨⟨15, 69, 1711⟩, 216102237624812049, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_69_flag endpoint_15_69_sources 14 206440730786111079 216102237624812049 rfl endpoint_15_69_base endpoint_15_69_p14) (by decide)⟩
private def endpoint_15_70_flag : Flag := ⟨15, 70, 1623⟩
private def endpoint_15_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_15_70_base : receiptBase endpoint_15_70_flag endpoint_15_70_sources = some 197267476417238728 := by decide +kernel
private theorem endpoint_15_70_w0 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 2 197267476417238728 = some 214420154677199350 := by decide +kernel
private theorem endpoint_15_70_w2 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 2 2 214420154677199350 = some 214420154677199350 := by decide +kernel
private theorem endpoint_15_70_p4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 4 197267476417238728 = some 214420154677199350 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 2 2 197267476417238728 214420154677199350 214420154677199350 endpoint_15_70_w0 endpoint_15_70_w2
private theorem endpoint_15_70_w4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 4 2 214420154677199350 = some 214420154677199350 := by decide +kernel
private theorem endpoint_15_70_p6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 6 197267476417238728 = some 214420154677199350 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 4 2 197267476417238728 214420154677199350 214420154677199350 endpoint_15_70_p4 endpoint_15_70_w4
private theorem endpoint_15_70_w6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 6 2 214420154677199350 = some 214420154677199350 := by decide +kernel
private theorem endpoint_15_70_p8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 8 197267476417238728 = some 214420154677199350 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 6 2 197267476417238728 214420154677199350 214420154677199350 endpoint_15_70_p6 endpoint_15_70_w6
private theorem endpoint_15_70_w8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 8 2 214420154677199350 = some 214420154677199350 := by decide +kernel
private theorem endpoint_15_70_p10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 10 197267476417238728 = some 214420154677199350 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 8 2 197267476417238728 214420154677199350 214420154677199350 endpoint_15_70_p8 endpoint_15_70_w8
private theorem endpoint_15_70_w10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 10 2 214420154677199350 = some 214420154677199350 := by decide +kernel
private theorem endpoint_15_70_p12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 12 197267476417238728 = some 214420154677199350 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 10 2 197267476417238728 214420154677199350 214420154677199350 endpoint_15_70_p10 endpoint_15_70_w10
private theorem endpoint_15_70_w12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 12 2 214420154677199350 = some 214420154677199350 := by decide +kernel
private theorem endpoint_15_70_p14 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 14 197267476417238728 = some 214420154677199350 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 12 2 197267476417238728 214420154677199350 214420154677199350 endpoint_15_70_p12 endpoint_15_70_w12
def endpoint_15_70 : CertifiedEndpoint :=
  ⟨⟨15, 70, 1623⟩, 214420154677199350, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_15_70_flag endpoint_15_70_sources 14 197267476417238728 214420154677199350 rfl endpoint_15_70_base endpoint_15_70_p14) (by decide)⟩
private def endpoint_15_71_flag : Flag := ⟨15, 71, 1531⟩
private def endpoint_15_71_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_71_base : receiptBase endpoint_15_71_flag endpoint_15_71_sources = some 191199790207288250 := by decide +kernel
private theorem endpoint_15_71_w0 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 2 191199790207288250 = some 194179235446679470 := by decide +kernel
private theorem endpoint_15_71_w2 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 2 2 194179235446679470 = some 194179235446679470 := by decide +kernel
private theorem endpoint_15_71_p4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 4 191199790207288250 = some 194179235446679470 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 2 2 191199790207288250 194179235446679470 194179235446679470 endpoint_15_71_w0 endpoint_15_71_w2
private theorem endpoint_15_71_w4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 4 2 194179235446679470 = some 194179235446679470 := by decide +kernel
private theorem endpoint_15_71_p6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 6 191199790207288250 = some 194179235446679470 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 4 2 191199790207288250 194179235446679470 194179235446679470 endpoint_15_71_p4 endpoint_15_71_w4
private theorem endpoint_15_71_w6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 6 2 194179235446679470 = some 194179235446679470 := by decide +kernel
private theorem endpoint_15_71_p8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 8 191199790207288250 = some 194179235446679470 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 6 2 191199790207288250 194179235446679470 194179235446679470 endpoint_15_71_p6 endpoint_15_71_w6
private theorem endpoint_15_71_w8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 8 2 194179235446679470 = some 194179235446679470 := by decide +kernel
private theorem endpoint_15_71_p10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 10 191199790207288250 = some 194179235446679470 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 8 2 191199790207288250 194179235446679470 194179235446679470 endpoint_15_71_p8 endpoint_15_71_w8
private theorem endpoint_15_71_w10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 10 2 194179235446679470 = some 194179235446679470 := by decide +kernel
private theorem endpoint_15_71_p12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 12 191199790207288250 = some 194179235446679470 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 10 2 191199790207288250 194179235446679470 194179235446679470 endpoint_15_71_p10 endpoint_15_71_w10
private theorem endpoint_15_71_w12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 12 2 194179235446679470 = some 194179235446679470 := by decide +kernel
private theorem endpoint_15_71_p14 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 14 191199790207288250 = some 194179235446679470 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 12 2 191199790207288250 194179235446679470 194179235446679470 endpoint_15_71_p12 endpoint_15_71_w12
def endpoint_15_71 : CertifiedEndpoint :=
  ⟨⟨15, 71, 1531⟩, 194179235446679470, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_71_flag endpoint_15_71_sources 14 191199790207288250 194179235446679470 rfl endpoint_15_71_base endpoint_15_71_p14) (by decide)⟩
private def endpoint_15_72_flag : Flag := ⟨15, 72, 1436⟩
private def endpoint_15_72_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_72_base : receiptBase endpoint_15_72_flag endpoint_15_72_sources = some 181697296454372911 := by decide +kernel
private theorem endpoint_15_72_w0 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 2 181697296454372911 = some 190308021477127980 := by decide +kernel
private theorem endpoint_15_72_w2 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 2 2 190308021477127980 = some 190308021477127980 := by decide +kernel
private theorem endpoint_15_72_p4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 4 181697296454372911 = some 190308021477127980 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 2 2 181697296454372911 190308021477127980 190308021477127980 endpoint_15_72_w0 endpoint_15_72_w2
private theorem endpoint_15_72_w4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 4 2 190308021477127980 = some 190308021477127980 := by decide +kernel
private theorem endpoint_15_72_p6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 6 181697296454372911 = some 190308021477127980 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 4 2 181697296454372911 190308021477127980 190308021477127980 endpoint_15_72_p4 endpoint_15_72_w4
private theorem endpoint_15_72_w6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 6 2 190308021477127980 = some 190308021477127980 := by decide +kernel
private theorem endpoint_15_72_p8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 8 181697296454372911 = some 190308021477127980 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 6 2 181697296454372911 190308021477127980 190308021477127980 endpoint_15_72_p6 endpoint_15_72_w6
private theorem endpoint_15_72_w8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 8 2 190308021477127980 = some 190308021477127980 := by decide +kernel
private theorem endpoint_15_72_p10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 10 181697296454372911 = some 190308021477127980 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 8 2 181697296454372911 190308021477127980 190308021477127980 endpoint_15_72_p8 endpoint_15_72_w8
private theorem endpoint_15_72_w10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 10 2 190308021477127980 = some 190308021477127980 := by decide +kernel
private theorem endpoint_15_72_p12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 12 181697296454372911 = some 190308021477127980 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 10 2 181697296454372911 190308021477127980 190308021477127980 endpoint_15_72_p10 endpoint_15_72_w10
private theorem endpoint_15_72_w12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 12 2 190308021477127980 = some 190308021477127980 := by decide +kernel
private theorem endpoint_15_72_p14 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 14 181697296454372911 = some 190308021477127980 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 12 2 181697296454372911 190308021477127980 190308021477127980 endpoint_15_72_p12 endpoint_15_72_w12
def endpoint_15_72 : CertifiedEndpoint :=
  ⟨⟨15, 72, 1436⟩, 190308021477127980, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_72_flag endpoint_15_72_sources 14 181697296454372911 190308021477127980 rfl endpoint_15_72_base endpoint_15_72_p14) (by decide)⟩
private def endpoint_15_73_flag : Flag := ⟨15, 73, 1338⟩
private def endpoint_15_73_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_15_73_base : receiptBase endpoint_15_73_flag endpoint_15_73_sources = some 171926127070842979 := by decide +kernel
private theorem endpoint_15_73_w0 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 2 171926127070842979 = some 183110521348855582 := by decide +kernel
private theorem endpoint_15_73_w2 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 2 2 183110521348855582 = some 183110521348855582 := by decide +kernel
private theorem endpoint_15_73_p4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 4 171926127070842979 = some 183110521348855582 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 2 2 171926127070842979 183110521348855582 183110521348855582 endpoint_15_73_w0 endpoint_15_73_w2
private theorem endpoint_15_73_w4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 4 2 183110521348855582 = some 183110521348855582 := by decide +kernel
private theorem endpoint_15_73_p6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 6 171926127070842979 = some 183110521348855582 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 4 2 171926127070842979 183110521348855582 183110521348855582 endpoint_15_73_p4 endpoint_15_73_w4
private theorem endpoint_15_73_w6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 6 2 183110521348855582 = some 183110521348855582 := by decide +kernel
private theorem endpoint_15_73_p8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 8 171926127070842979 = some 183110521348855582 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 6 2 171926127070842979 183110521348855582 183110521348855582 endpoint_15_73_p6 endpoint_15_73_w6
private theorem endpoint_15_73_w8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 8 2 183110521348855582 = some 183110521348855582 := by decide +kernel
private theorem endpoint_15_73_p10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 10 171926127070842979 = some 183110521348855582 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 8 2 171926127070842979 183110521348855582 183110521348855582 endpoint_15_73_p8 endpoint_15_73_w8
private theorem endpoint_15_73_w10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 10 2 183110521348855582 = some 183110521348855582 := by decide +kernel
private theorem endpoint_15_73_p12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 12 171926127070842979 = some 183110521348855582 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 10 2 171926127070842979 183110521348855582 183110521348855582 endpoint_15_73_p10 endpoint_15_73_w10
private theorem endpoint_15_73_w12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 12 2 183110521348855582 = some 183110521348855582 := by decide +kernel
private theorem endpoint_15_73_p14 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 14 171926127070842979 = some 183110521348855582 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 12 2 171926127070842979 183110521348855582 183110521348855582 endpoint_15_73_p12 endpoint_15_73_w12
def endpoint_15_73 : CertifiedEndpoint :=
  ⟨⟨15, 73, 1338⟩, 183110521348855582, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_15_73_flag endpoint_15_73_sources 14 171926127070842979 183110521348855582 rfl endpoint_15_73_base endpoint_15_73_p14) (by decide)⟩
private def endpoint_15_74_flag : Flag := ⟨15, 74, 1238⟩
private def endpoint_15_74_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_15_74_base : receiptBase endpoint_15_74_flag endpoint_15_74_sources = some 162224928340027627 := by decide +kernel
private theorem endpoint_15_74_w0 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 2 162224928340027627 = some 170821038632901632 := by decide +kernel
private theorem endpoint_15_74_w2 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 2 2 170821038632901632 = some 170821038632901632 := by decide +kernel
private theorem endpoint_15_74_p4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 4 162224928340027627 = some 170821038632901632 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 2 2 162224928340027627 170821038632901632 170821038632901632 endpoint_15_74_w0 endpoint_15_74_w2
private theorem endpoint_15_74_w4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 4 2 170821038632901632 = some 170821038632901632 := by decide +kernel
private theorem endpoint_15_74_p6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 6 162224928340027627 = some 170821038632901632 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 4 2 162224928340027627 170821038632901632 170821038632901632 endpoint_15_74_p4 endpoint_15_74_w4
private theorem endpoint_15_74_w6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 6 2 170821038632901632 = some 170821038632901632 := by decide +kernel
private theorem endpoint_15_74_p8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 8 162224928340027627 = some 170821038632901632 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 6 2 162224928340027627 170821038632901632 170821038632901632 endpoint_15_74_p6 endpoint_15_74_w6
private theorem endpoint_15_74_w8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 8 2 170821038632901632 = some 170821038632901632 := by decide +kernel
private theorem endpoint_15_74_p10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 10 162224928340027627 = some 170821038632901632 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 8 2 162224928340027627 170821038632901632 170821038632901632 endpoint_15_74_p8 endpoint_15_74_w8
private theorem endpoint_15_74_w10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 10 2 170821038632901632 = some 170821038632901632 := by decide +kernel
private theorem endpoint_15_74_p12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 12 162224928340027627 = some 170821038632901632 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 10 2 162224928340027627 170821038632901632 170821038632901632 endpoint_15_74_p10 endpoint_15_74_w10
private theorem endpoint_15_74_w12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 12 2 170821038632901632 = some 170821038632901632 := by decide +kernel
private theorem endpoint_15_74_p14 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 14 162224928340027627 = some 170821038632901632 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 12 2 162224928340027627 170821038632901632 170821038632901632 endpoint_15_74_p12 endpoint_15_74_w12
def endpoint_15_74 : CertifiedEndpoint :=
  ⟨⟨15, 74, 1238⟩, 170821038632901632, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_15_74_flag endpoint_15_74_sources 14 162224928340027627 170821038632901632 rfl endpoint_15_74_base endpoint_15_74_p14) (by decide)⟩
private def endpoint_15_75_flag : Flag := ⟨15, 75, 1134⟩
private def endpoint_15_75_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_75_base : receiptBase endpoint_15_75_flag endpoint_15_75_sources = some 151820531513047137 := by decide +kernel
private theorem endpoint_15_75_w0 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 2 151820531513047137 = some 156044784994094841 := by decide +kernel
private theorem endpoint_15_75_w2 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 2 2 156044784994094841 = some 156044784994094841 := by decide +kernel
private theorem endpoint_15_75_p4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 4 151820531513047137 = some 156044784994094841 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 2 2 151820531513047137 156044784994094841 156044784994094841 endpoint_15_75_w0 endpoint_15_75_w2
private theorem endpoint_15_75_w4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 4 2 156044784994094841 = some 156044784994094841 := by decide +kernel
private theorem endpoint_15_75_p6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 6 151820531513047137 = some 156044784994094841 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 4 2 151820531513047137 156044784994094841 156044784994094841 endpoint_15_75_p4 endpoint_15_75_w4
private theorem endpoint_15_75_w6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 6 2 156044784994094841 = some 156044784994094841 := by decide +kernel
private theorem endpoint_15_75_p8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 8 151820531513047137 = some 156044784994094841 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 6 2 151820531513047137 156044784994094841 156044784994094841 endpoint_15_75_p6 endpoint_15_75_w6
private theorem endpoint_15_75_w8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 8 2 156044784994094841 = some 156044784994094841 := by decide +kernel
private theorem endpoint_15_75_p10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 10 151820531513047137 = some 156044784994094841 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 8 2 151820531513047137 156044784994094841 156044784994094841 endpoint_15_75_p8 endpoint_15_75_w8
private theorem endpoint_15_75_w10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 10 2 156044784994094841 = some 156044784994094841 := by decide +kernel
private theorem endpoint_15_75_p12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 12 151820531513047137 = some 156044784994094841 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 10 2 151820531513047137 156044784994094841 156044784994094841 endpoint_15_75_p10 endpoint_15_75_w10
private theorem endpoint_15_75_w12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 12 2 156044784994094841 = some 156044784994094841 := by decide +kernel
private theorem endpoint_15_75_p14 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 14 151820531513047137 = some 156044784994094841 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 12 2 151820531513047137 156044784994094841 156044784994094841 endpoint_15_75_p12 endpoint_15_75_w12
def endpoint_15_75 : CertifiedEndpoint :=
  ⟨⟨15, 75, 1134⟩, 156044784994094841, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_75_flag endpoint_15_75_sources 14 151820531513047137 156044784994094841 rfl endpoint_15_75_base endpoint_15_75_p14) (by decide)⟩
def endpoint_15_76 : CertifiedEndpoint :=
  ⟨⟨15, 76, 1027⟩, 250902211972753727, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_77 : CertifiedEndpoint :=
  ⟨⟨15, 77, 917⟩, 226034312070297642, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_78 : CertifiedEndpoint :=
  ⟨⟨15, 78, 804⟩, 199552159957150584, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_79 : CertifiedEndpoint :=
  ⟨⟨15, 79, 689⟩, 171687973155096794, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_80 : CertifiedEndpoint :=
  ⟨⟨15, 80, 570⟩, 141879938699021690, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_81 : CertifiedEndpoint :=
  ⟨⟨15, 81, 448⟩, 110356528806034663, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_82 : CertifiedEndpoint :=
  ⟨⟨15, 82, 322⟩, 76806874556179622, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_83 : CertifiedEndpoint :=
  ⟨⟨15, 83, 194⟩, 41747845258472949, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_16 : CertifiedEndpoint :=
  ⟨⟨16, 16, 3976⟩, 140368279618647464, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_17 : CertifiedEndpoint :=
  ⟨⟨16, 17, 3948⟩, 144542009178343834, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_18 : CertifiedEndpoint :=
  ⟨⟨16, 18, 3921⟩, 148680175552727563, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_19 : CertifiedEndpoint :=
  ⟨⟨16, 19, 3892⟩, 163082751541399753, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_20 : CertifiedEndpoint :=
  ⟨⟨16, 20, 3864⟩, 177295193237138712, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_21 : CertifiedEndpoint :=
  ⟨⟨16, 21, 3835⟩, 191229417172330968, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_22 : CertifiedEndpoint :=
  ⟨⟨16, 22, 3805⟩, 204873414319964215, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_23 : CertifiedEndpoint :=
  ⟨⟨16, 23, 3775⟩, 218273227918347240, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_24 : CertifiedEndpoint :=
  ⟨⟨16, 24, 3744⟩, 231366802693154848, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_25 : CertifiedEndpoint :=
  ⟨⟨16, 25, 3713⟩, 244208187900704030, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_26 : CertifiedEndpoint :=
  ⟨⟨16, 26, 3682⟩, 256797383540994786, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_16_27_flag : Flag := ⟨16, 27, 3650⟩
private def endpoint_16_27_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_27_base : receiptBase endpoint_16_27_flag endpoint_16_27_sources = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_w0 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 2 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_w2 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 2 2 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_p4 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 4 188464588301652546 = some 188464588301652546 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 2 2 188464588301652546 188464588301652546 188464588301652546 endpoint_16_27_w0 endpoint_16_27_w2
private theorem endpoint_16_27_w4 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 4 2 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_p6 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 6 188464588301652546 = some 188464588301652546 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 4 2 188464588301652546 188464588301652546 188464588301652546 endpoint_16_27_p4 endpoint_16_27_w4
private theorem endpoint_16_27_w6 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 6 2 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_p8 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 8 188464588301652546 = some 188464588301652546 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 6 2 188464588301652546 188464588301652546 188464588301652546 endpoint_16_27_p6 endpoint_16_27_w6
private theorem endpoint_16_27_w8 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 8 2 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_p10 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 10 188464588301652546 = some 188464588301652546 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 8 2 188464588301652546 188464588301652546 188464588301652546 endpoint_16_27_p8 endpoint_16_27_w8
private theorem endpoint_16_27_w10 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 10 2 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_p12 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 12 188464588301652546 = some 188464588301652546 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 10 2 188464588301652546 188464588301652546 188464588301652546 endpoint_16_27_p10 endpoint_16_27_w10
private theorem endpoint_16_27_w12 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 12 2 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_p14 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 14 188464588301652546 = some 188464588301652546 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 12 2 188464588301652546 188464588301652546 188464588301652546 endpoint_16_27_p12 endpoint_16_27_w12
private theorem endpoint_16_27_w14 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 14 1 188464588301652546 = some 188464588301652546 := by decide +kernel
private theorem endpoint_16_27_p15 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 15 188464588301652546 = some 188464588301652546 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 14 1 188464588301652546 188464588301652546 188464588301652546 endpoint_16_27_p14 endpoint_16_27_w14
def endpoint_16_27 : CertifiedEndpoint :=
  ⟨⟨16, 27, 3650⟩, 188464588301652546, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_27_flag endpoint_16_27_sources 15 188464588301652546 188464588301652546 rfl endpoint_16_27_base endpoint_16_27_p15) (by decide)⟩
private def endpoint_16_28_flag : Flag := ⟨16, 28, 3617⟩
private def endpoint_16_28_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_28_base : receiptBase endpoint_16_28_flag endpoint_16_28_sources = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_w0 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 2 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_w2 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 2 2 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_p4 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 4 192417030382090950 = some 192417030382090950 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 2 2 192417030382090950 192417030382090950 192417030382090950 endpoint_16_28_w0 endpoint_16_28_w2
private theorem endpoint_16_28_w4 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 4 2 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_p6 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 6 192417030382090950 = some 192417030382090950 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 4 2 192417030382090950 192417030382090950 192417030382090950 endpoint_16_28_p4 endpoint_16_28_w4
private theorem endpoint_16_28_w6 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 6 2 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_p8 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 8 192417030382090950 = some 192417030382090950 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 6 2 192417030382090950 192417030382090950 192417030382090950 endpoint_16_28_p6 endpoint_16_28_w6
private theorem endpoint_16_28_w8 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 8 2 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_p10 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 10 192417030382090950 = some 192417030382090950 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 8 2 192417030382090950 192417030382090950 192417030382090950 endpoint_16_28_p8 endpoint_16_28_w8
private theorem endpoint_16_28_w10 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 10 2 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_p12 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 12 192417030382090950 = some 192417030382090950 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 10 2 192417030382090950 192417030382090950 192417030382090950 endpoint_16_28_p10 endpoint_16_28_w10
private theorem endpoint_16_28_w12 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 12 2 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_p14 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 14 192417030382090950 = some 192417030382090950 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 12 2 192417030382090950 192417030382090950 192417030382090950 endpoint_16_28_p12 endpoint_16_28_w12
private theorem endpoint_16_28_w14 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 14 1 192417030382090950 = some 192417030382090950 := by decide +kernel
private theorem endpoint_16_28_p15 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 15 192417030382090950 = some 192417030382090950 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 14 1 192417030382090950 192417030382090950 192417030382090950 endpoint_16_28_p14 endpoint_16_28_w14
def endpoint_16_28 : CertifiedEndpoint :=
  ⟨⟨16, 28, 3617⟩, 192417030382090950, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_28_flag endpoint_16_28_sources 15 192417030382090950 192417030382090950 rfl endpoint_16_28_base endpoint_16_28_p15) (by decide)⟩
private def endpoint_16_29_flag : Flag := ⟨16, 29, 3584⟩
private def endpoint_16_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_29_base : receiptBase endpoint_16_29_flag endpoint_16_29_sources = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_w0 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 2 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_w2 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 2 2 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_p4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 4 196267328882265187 = some 196267328882265187 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 2 2 196267328882265187 196267328882265187 196267328882265187 endpoint_16_29_w0 endpoint_16_29_w2
private theorem endpoint_16_29_w4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 4 2 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_p6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 6 196267328882265187 = some 196267328882265187 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 4 2 196267328882265187 196267328882265187 196267328882265187 endpoint_16_29_p4 endpoint_16_29_w4
private theorem endpoint_16_29_w6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 6 2 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_p8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 8 196267328882265187 = some 196267328882265187 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 6 2 196267328882265187 196267328882265187 196267328882265187 endpoint_16_29_p6 endpoint_16_29_w6
private theorem endpoint_16_29_w8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 8 2 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_p10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 10 196267328882265187 = some 196267328882265187 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 8 2 196267328882265187 196267328882265187 196267328882265187 endpoint_16_29_p8 endpoint_16_29_w8
private theorem endpoint_16_29_w10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 10 2 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_p12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 12 196267328882265187 = some 196267328882265187 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 10 2 196267328882265187 196267328882265187 196267328882265187 endpoint_16_29_p10 endpoint_16_29_w10
private theorem endpoint_16_29_w12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 12 2 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_p14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 14 196267328882265187 = some 196267328882265187 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 12 2 196267328882265187 196267328882265187 196267328882265187 endpoint_16_29_p12 endpoint_16_29_w12
private theorem endpoint_16_29_w14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 14 1 196267328882265187 = some 196267328882265187 := by decide +kernel
private theorem endpoint_16_29_p15 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 15 196267328882265187 = some 196267328882265187 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 14 1 196267328882265187 196267328882265187 196267328882265187 endpoint_16_29_p14 endpoint_16_29_w14
def endpoint_16_29 : CertifiedEndpoint :=
  ⟨⟨16, 29, 3584⟩, 196267328882265187, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_29_flag endpoint_16_29_sources 15 196267328882265187 196267328882265187 rfl endpoint_16_29_base endpoint_16_29_p15) (by decide)⟩
private def endpoint_16_30_flag : Flag := ⟨16, 30, 3550⟩
private def endpoint_16_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_30_base : receiptBase endpoint_16_30_flag endpoint_16_30_sources = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_w0 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 2 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_w2 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 2 2 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_p4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 4 199959908914970934 = some 199959908914970934 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 2 2 199959908914970934 199959908914970934 199959908914970934 endpoint_16_30_w0 endpoint_16_30_w2
private theorem endpoint_16_30_w4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 4 2 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_p6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 6 199959908914970934 = some 199959908914970934 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 4 2 199959908914970934 199959908914970934 199959908914970934 endpoint_16_30_p4 endpoint_16_30_w4
private theorem endpoint_16_30_w6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 6 2 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_p8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 8 199959908914970934 = some 199959908914970934 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 6 2 199959908914970934 199959908914970934 199959908914970934 endpoint_16_30_p6 endpoint_16_30_w6
private theorem endpoint_16_30_w8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 8 2 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_p10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 10 199959908914970934 = some 199959908914970934 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 8 2 199959908914970934 199959908914970934 199959908914970934 endpoint_16_30_p8 endpoint_16_30_w8
private theorem endpoint_16_30_w10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 10 2 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_p12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 12 199959908914970934 = some 199959908914970934 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 10 2 199959908914970934 199959908914970934 199959908914970934 endpoint_16_30_p10 endpoint_16_30_w10
private theorem endpoint_16_30_w12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 12 2 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_p14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 14 199959908914970934 = some 199959908914970934 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 12 2 199959908914970934 199959908914970934 199959908914970934 endpoint_16_30_p12 endpoint_16_30_w12
private theorem endpoint_16_30_w14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 14 1 199959908914970934 = some 199959908914970934 := by decide +kernel
private theorem endpoint_16_30_p15 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 15 199959908914970934 = some 199959908914970934 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 14 1 199959908914970934 199959908914970934 199959908914970934 endpoint_16_30_p14 endpoint_16_30_w14
def endpoint_16_30 : CertifiedEndpoint :=
  ⟨⟨16, 30, 3550⟩, 199959908914970934, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_30_flag endpoint_16_30_sources 15 199959908914970934 199959908914970934 rfl endpoint_16_30_base endpoint_16_30_p15) (by decide)⟩
private def endpoint_16_31_flag : Flag := ⟨16, 31, 3515⟩
private def endpoint_16_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_31_base : receiptBase endpoint_16_31_flag endpoint_16_31_sources = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_w0 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 2 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_w2 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 2 2 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_p4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 4 203490197944805005 = some 203490197944805005 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 2 2 203490197944805005 203490197944805005 203490197944805005 endpoint_16_31_w0 endpoint_16_31_w2
private theorem endpoint_16_31_w4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 4 2 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_p6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 6 203490197944805005 = some 203490197944805005 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 4 2 203490197944805005 203490197944805005 203490197944805005 endpoint_16_31_p4 endpoint_16_31_w4
private theorem endpoint_16_31_w6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 6 2 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_p8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 8 203490197944805005 = some 203490197944805005 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 6 2 203490197944805005 203490197944805005 203490197944805005 endpoint_16_31_p6 endpoint_16_31_w6
private theorem endpoint_16_31_w8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 8 2 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_p10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 10 203490197944805005 = some 203490197944805005 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 8 2 203490197944805005 203490197944805005 203490197944805005 endpoint_16_31_p8 endpoint_16_31_w8
private theorem endpoint_16_31_w10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 10 2 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_p12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 12 203490197944805005 = some 203490197944805005 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 10 2 203490197944805005 203490197944805005 203490197944805005 endpoint_16_31_p10 endpoint_16_31_w10
private theorem endpoint_16_31_w12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 12 2 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_p14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 14 203490197944805005 = some 203490197944805005 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 12 2 203490197944805005 203490197944805005 203490197944805005 endpoint_16_31_p12 endpoint_16_31_w12
private theorem endpoint_16_31_w14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 14 1 203490197944805005 = some 203490197944805005 := by decide +kernel
private theorem endpoint_16_31_p15 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 15 203490197944805005 = some 203490197944805005 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 14 1 203490197944805005 203490197944805005 203490197944805005 endpoint_16_31_p14 endpoint_16_31_w14
def endpoint_16_31 : CertifiedEndpoint :=
  ⟨⟨16, 31, 3515⟩, 203490197944805005, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_31_flag endpoint_16_31_sources 15 203490197944805005 203490197944805005 rfl endpoint_16_31_base endpoint_16_31_p15) (by decide)⟩
private def endpoint_16_32_flag : Flag := ⟨16, 32, 3480⟩
private def endpoint_16_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_32_base : receiptBase endpoint_16_32_flag endpoint_16_32_sources = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_w0 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 2 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_w2 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 2 2 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_p4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 4 206912246680503994 = some 206912246680503994 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 2 2 206912246680503994 206912246680503994 206912246680503994 endpoint_16_32_w0 endpoint_16_32_w2
private theorem endpoint_16_32_w4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 4 2 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_p6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 6 206912246680503994 = some 206912246680503994 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 4 2 206912246680503994 206912246680503994 206912246680503994 endpoint_16_32_p4 endpoint_16_32_w4
private theorem endpoint_16_32_w6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 6 2 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_p8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 8 206912246680503994 = some 206912246680503994 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 6 2 206912246680503994 206912246680503994 206912246680503994 endpoint_16_32_p6 endpoint_16_32_w6
private theorem endpoint_16_32_w8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 8 2 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_p10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 10 206912246680503994 = some 206912246680503994 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 8 2 206912246680503994 206912246680503994 206912246680503994 endpoint_16_32_p8 endpoint_16_32_w8
private theorem endpoint_16_32_w10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 10 2 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_p12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 12 206912246680503994 = some 206912246680503994 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 10 2 206912246680503994 206912246680503994 206912246680503994 endpoint_16_32_p10 endpoint_16_32_w10
private theorem endpoint_16_32_w12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 12 2 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_p14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 14 206912246680503994 = some 206912246680503994 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 12 2 206912246680503994 206912246680503994 206912246680503994 endpoint_16_32_p12 endpoint_16_32_w12
private theorem endpoint_16_32_w14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 14 1 206912246680503994 = some 206912246680503994 := by decide +kernel
private theorem endpoint_16_32_p15 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 15 206912246680503994 = some 206912246680503994 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 14 1 206912246680503994 206912246680503994 206912246680503994 endpoint_16_32_p14 endpoint_16_32_w14
def endpoint_16_32 : CertifiedEndpoint :=
  ⟨⟨16, 32, 3480⟩, 206912246680503994, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_32_flag endpoint_16_32_sources 15 206912246680503994 206912246680503994 rfl endpoint_16_32_base endpoint_16_32_p15) (by decide)⟩
private def endpoint_16_33_flag : Flag := ⟨16, 33, 3444⟩
private def endpoint_16_33_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_16_33_base : receiptBase endpoint_16_33_flag endpoint_16_33_sources = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_w0 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 2 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_w2 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 2 2 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_p4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 4 212068515879261557 = some 212068515879261557 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 2 2 212068515879261557 212068515879261557 212068515879261557 endpoint_16_33_w0 endpoint_16_33_w2
private theorem endpoint_16_33_w4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 4 2 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_p6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 6 212068515879261557 = some 212068515879261557 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 4 2 212068515879261557 212068515879261557 212068515879261557 endpoint_16_33_p4 endpoint_16_33_w4
private theorem endpoint_16_33_w6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 6 2 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_p8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 8 212068515879261557 = some 212068515879261557 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 6 2 212068515879261557 212068515879261557 212068515879261557 endpoint_16_33_p6 endpoint_16_33_w6
private theorem endpoint_16_33_w8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 8 2 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_p10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 10 212068515879261557 = some 212068515879261557 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 8 2 212068515879261557 212068515879261557 212068515879261557 endpoint_16_33_p8 endpoint_16_33_w8
private theorem endpoint_16_33_w10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 10 2 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_p12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 12 212068515879261557 = some 212068515879261557 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 10 2 212068515879261557 212068515879261557 212068515879261557 endpoint_16_33_p10 endpoint_16_33_w10
private theorem endpoint_16_33_w12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 12 2 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_p14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 14 212068515879261557 = some 212068515879261557 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 12 2 212068515879261557 212068515879261557 212068515879261557 endpoint_16_33_p12 endpoint_16_33_w12
private theorem endpoint_16_33_w14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 14 1 212068515879261557 = some 212068515879261557 := by decide +kernel
private theorem endpoint_16_33_p15 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 15 212068515879261557 = some 212068515879261557 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 14 1 212068515879261557 212068515879261557 212068515879261557 endpoint_16_33_p14 endpoint_16_33_w14
def endpoint_16_33 : CertifiedEndpoint :=
  ⟨⟨16, 33, 3444⟩, 212068515879261557, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_16_33_flag endpoint_16_33_sources 15 212068515879261557 212068515879261557 rfl endpoint_16_33_base endpoint_16_33_p15) (by decide)⟩
private def endpoint_16_34_flag : Flag := ⟨16, 34, 3407⟩
private def endpoint_16_34_sources : Sources := ⟨contact25, contact03, contact25⟩
private theorem endpoint_16_34_base : receiptBase endpoint_16_34_flag endpoint_16_34_sources = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_w0 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 2 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_w2 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 2 2 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_p4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 4 215361540958361741 = some 215361540958361741 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 2 2 215361540958361741 215361540958361741 215361540958361741 endpoint_16_34_w0 endpoint_16_34_w2
private theorem endpoint_16_34_w4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 4 2 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_p6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 6 215361540958361741 = some 215361540958361741 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 4 2 215361540958361741 215361540958361741 215361540958361741 endpoint_16_34_p4 endpoint_16_34_w4
private theorem endpoint_16_34_w6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 6 2 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_p8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 8 215361540958361741 = some 215361540958361741 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 6 2 215361540958361741 215361540958361741 215361540958361741 endpoint_16_34_p6 endpoint_16_34_w6
private theorem endpoint_16_34_w8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 8 2 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_p10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 10 215361540958361741 = some 215361540958361741 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 8 2 215361540958361741 215361540958361741 215361540958361741 endpoint_16_34_p8 endpoint_16_34_w8
private theorem endpoint_16_34_w10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 10 2 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_p12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 12 215361540958361741 = some 215361540958361741 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 10 2 215361540958361741 215361540958361741 215361540958361741 endpoint_16_34_p10 endpoint_16_34_w10
private theorem endpoint_16_34_w12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 12 2 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_p14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 14 215361540958361741 = some 215361540958361741 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 12 2 215361540958361741 215361540958361741 215361540958361741 endpoint_16_34_p12 endpoint_16_34_w12
private theorem endpoint_16_34_w14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 14 1 215361540958361741 = some 215361540958361741 := by decide +kernel
private theorem endpoint_16_34_p15 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 15 215361540958361741 = some 215361540958361741 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 14 1 215361540958361741 215361540958361741 215361540958361741 endpoint_16_34_p14 endpoint_16_34_w14
def endpoint_16_34 : CertifiedEndpoint :=
  ⟨⟨16, 34, 3407⟩, 215361540958361741, .terminal ⟨contact25, contact03, contact25⟩ (finish_receipt_window endpoint_16_34_flag endpoint_16_34_sources 15 215361540958361741 215361540958361741 rfl endpoint_16_34_base endpoint_16_34_p15) (by decide)⟩
private def endpoint_16_35_flag : Flag := ⟨16, 35, 3369⟩
private def endpoint_16_35_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_35_base : receiptBase endpoint_16_35_flag endpoint_16_35_sources = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_w0 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 2 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_w2 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 2 2 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_p4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 4 219955457314080519 = some 219955457314080519 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 2 2 219955457314080519 219955457314080519 219955457314080519 endpoint_16_35_w0 endpoint_16_35_w2
private theorem endpoint_16_35_w4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 4 2 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_p6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 6 219955457314080519 = some 219955457314080519 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 4 2 219955457314080519 219955457314080519 219955457314080519 endpoint_16_35_p4 endpoint_16_35_w4
private theorem endpoint_16_35_w6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 6 2 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_p8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 8 219955457314080519 = some 219955457314080519 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 6 2 219955457314080519 219955457314080519 219955457314080519 endpoint_16_35_p6 endpoint_16_35_w6
private theorem endpoint_16_35_w8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 8 2 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_p10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 10 219955457314080519 = some 219955457314080519 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 8 2 219955457314080519 219955457314080519 219955457314080519 endpoint_16_35_p8 endpoint_16_35_w8
private theorem endpoint_16_35_w10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 10 2 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_p12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 12 219955457314080519 = some 219955457314080519 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 10 2 219955457314080519 219955457314080519 219955457314080519 endpoint_16_35_p10 endpoint_16_35_w10
private theorem endpoint_16_35_w12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 12 2 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_p14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 14 219955457314080519 = some 219955457314080519 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 12 2 219955457314080519 219955457314080519 219955457314080519 endpoint_16_35_p12 endpoint_16_35_w12
private theorem endpoint_16_35_w14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 14 1 219955457314080519 = some 219955457314080519 := by decide +kernel
private theorem endpoint_16_35_p15 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 15 219955457314080519 = some 219955457314080519 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 14 1 219955457314080519 219955457314080519 219955457314080519 endpoint_16_35_p14 endpoint_16_35_w14
def endpoint_16_35 : CertifiedEndpoint :=
  ⟨⟨16, 35, 3369⟩, 219955457314080519, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_35_flag endpoint_16_35_sources 15 219955457314080519 219955457314080519 rfl endpoint_16_35_base endpoint_16_35_p15) (by decide)⟩
private def endpoint_16_36_flag : Flag := ⟨16, 36, 3331⟩
private def endpoint_16_36_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_36_base : receiptBase endpoint_16_36_flag endpoint_16_36_sources = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_w0 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 2 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_w2 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 2 2 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_p4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 4 222624269294944698 = some 222624269294944698 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 2 2 222624269294944698 222624269294944698 222624269294944698 endpoint_16_36_w0 endpoint_16_36_w2
private theorem endpoint_16_36_w4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 4 2 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_p6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 6 222624269294944698 = some 222624269294944698 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 4 2 222624269294944698 222624269294944698 222624269294944698 endpoint_16_36_p4 endpoint_16_36_w4
private theorem endpoint_16_36_w6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 6 2 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_p8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 8 222624269294944698 = some 222624269294944698 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 6 2 222624269294944698 222624269294944698 222624269294944698 endpoint_16_36_p6 endpoint_16_36_w6
private theorem endpoint_16_36_w8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 8 2 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_p10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 10 222624269294944698 = some 222624269294944698 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 8 2 222624269294944698 222624269294944698 222624269294944698 endpoint_16_36_p8 endpoint_16_36_w8
private theorem endpoint_16_36_w10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 10 2 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_p12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 12 222624269294944698 = some 222624269294944698 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 10 2 222624269294944698 222624269294944698 222624269294944698 endpoint_16_36_p10 endpoint_16_36_w10
private theorem endpoint_16_36_w12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 12 2 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_p14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 14 222624269294944698 = some 222624269294944698 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 12 2 222624269294944698 222624269294944698 222624269294944698 endpoint_16_36_p12 endpoint_16_36_w12
private theorem endpoint_16_36_w14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 14 1 222624269294944698 = some 222624269294944698 := by decide +kernel
private theorem endpoint_16_36_p15 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 15 222624269294944698 = some 222624269294944698 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 14 1 222624269294944698 222624269294944698 222624269294944698 endpoint_16_36_p14 endpoint_16_36_w14
def endpoint_16_36 : CertifiedEndpoint :=
  ⟨⟨16, 36, 3331⟩, 222624269294944698, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_36_flag endpoint_16_36_sources 15 222624269294944698 222624269294944698 rfl endpoint_16_36_base endpoint_16_36_p15) (by decide)⟩

def endpointBlock10 : List CertifiedEndpoint := [
  endpoint_14_56, endpoint_14_57, endpoint_14_58, endpoint_14_59, endpoint_14_60, endpoint_14_61, endpoint_14_62,
  endpoint_14_63, endpoint_14_64, endpoint_14_65, endpoint_14_66, endpoint_14_67, endpoint_14_68, endpoint_14_69,
  endpoint_14_70, endpoint_14_71, endpoint_14_72, endpoint_14_73, endpoint_14_74, endpoint_14_75, endpoint_14_76,
  endpoint_14_77, endpoint_14_78, endpoint_14_79, endpoint_14_80, endpoint_14_81, endpoint_14_82, endpoint_14_83,
  endpoint_14_84, endpoint_14_85, endpoint_15_15, endpoint_15_16, endpoint_15_17, endpoint_15_18, endpoint_15_19,
  endpoint_15_20, endpoint_15_21, endpoint_15_22, endpoint_15_23, endpoint_15_24, endpoint_15_25, endpoint_15_26,
  endpoint_15_27, endpoint_15_28, endpoint_15_29, endpoint_15_30, endpoint_15_31, endpoint_15_32, endpoint_15_33,
  endpoint_15_34, endpoint_15_35, endpoint_15_36, endpoint_15_37, endpoint_15_38, endpoint_15_39, endpoint_15_40,
  endpoint_15_41, endpoint_15_42, endpoint_15_43, endpoint_15_44, endpoint_15_45, endpoint_15_46, endpoint_15_47,
  endpoint_15_48, endpoint_15_49, endpoint_15_50, endpoint_15_51, endpoint_15_52, endpoint_15_53, endpoint_15_54,
  endpoint_15_55, endpoint_15_56, endpoint_15_57, endpoint_15_58, endpoint_15_59, endpoint_15_60, endpoint_15_61,
  endpoint_15_62, endpoint_15_63, endpoint_15_64, endpoint_15_65, endpoint_15_66, endpoint_15_67, endpoint_15_68,
  endpoint_15_69, endpoint_15_70, endpoint_15_71, endpoint_15_72, endpoint_15_73, endpoint_15_74, endpoint_15_75,
  endpoint_15_76, endpoint_15_77, endpoint_15_78, endpoint_15_79, endpoint_15_80, endpoint_15_81, endpoint_15_82,
  endpoint_15_83, endpoint_16_16, endpoint_16_17, endpoint_16_18, endpoint_16_19, endpoint_16_20, endpoint_16_21,
  endpoint_16_22, endpoint_16_23, endpoint_16_24, endpoint_16_25, endpoint_16_26, endpoint_16_27, endpoint_16_28,
  endpoint_16_29, endpoint_16_30, endpoint_16_31, endpoint_16_32, endpoint_16_33, endpoint_16_34, endpoint_16_35,
  endpoint_16_36
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
