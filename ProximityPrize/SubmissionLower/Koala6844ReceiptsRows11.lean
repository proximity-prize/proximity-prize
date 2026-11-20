import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_16_37_flag : Flag := ⟨16, 37, 3292⟩
private def endpoint_16_37_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_37_base : receiptBase endpoint_16_37_flag endpoint_16_37_sources = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_w0 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 2 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_w2 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 2 2 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_p4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 4 225109330208599148 = some 225109330208599148 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 2 2 225109330208599148 225109330208599148 225109330208599148 endpoint_16_37_w0 endpoint_16_37_w2
private theorem endpoint_16_37_w4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 4 2 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_p6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 6 225109330208599148 = some 225109330208599148 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 4 2 225109330208599148 225109330208599148 225109330208599148 endpoint_16_37_p4 endpoint_16_37_w4
private theorem endpoint_16_37_w6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 6 2 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_p8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 8 225109330208599148 = some 225109330208599148 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 6 2 225109330208599148 225109330208599148 225109330208599148 endpoint_16_37_p6 endpoint_16_37_w6
private theorem endpoint_16_37_w8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 8 2 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_p10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 10 225109330208599148 = some 225109330208599148 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 8 2 225109330208599148 225109330208599148 225109330208599148 endpoint_16_37_p8 endpoint_16_37_w8
private theorem endpoint_16_37_w10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 10 2 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_p12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 12 225109330208599148 = some 225109330208599148 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 10 2 225109330208599148 225109330208599148 225109330208599148 endpoint_16_37_p10 endpoint_16_37_w10
private theorem endpoint_16_37_w12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 12 2 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_p14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 14 225109330208599148 = some 225109330208599148 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 12 2 225109330208599148 225109330208599148 225109330208599148 endpoint_16_37_p12 endpoint_16_37_w12
private theorem endpoint_16_37_w14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 14 1 225109330208599148 = some 225109330208599148 := by decide +kernel
private theorem endpoint_16_37_p15 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 15 225109330208599148 = some 225109330208599148 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 14 1 225109330208599148 225109330208599148 225109330208599148 endpoint_16_37_p14 endpoint_16_37_w14
def endpoint_16_37 : CertifiedEndpoint :=
  ⟨⟨16, 37, 3292⟩, 225109330208599148, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_37_flag endpoint_16_37_sources 15 225109330208599148 225109330208599148 rfl endpoint_16_37_base endpoint_16_37_p15) (by decide)⟩
private def endpoint_16_38_flag : Flag := ⟨16, 38, 3252⟩
private def endpoint_16_38_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_38_base : receiptBase endpoint_16_38_flag endpoint_16_38_sources = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_w0 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 2 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_w2 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 2 2 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_p4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 4 227406111424967172 = some 227406111424967172 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 2 2 227406111424967172 227406111424967172 227406111424967172 endpoint_16_38_w0 endpoint_16_38_w2
private theorem endpoint_16_38_w4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 4 2 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_p6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 6 227406111424967172 = some 227406111424967172 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 4 2 227406111424967172 227406111424967172 227406111424967172 endpoint_16_38_p4 endpoint_16_38_w4
private theorem endpoint_16_38_w6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 6 2 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_p8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 8 227406111424967172 = some 227406111424967172 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 6 2 227406111424967172 227406111424967172 227406111424967172 endpoint_16_38_p6 endpoint_16_38_w6
private theorem endpoint_16_38_w8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 8 2 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_p10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 10 227406111424967172 = some 227406111424967172 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 8 2 227406111424967172 227406111424967172 227406111424967172 endpoint_16_38_p8 endpoint_16_38_w8
private theorem endpoint_16_38_w10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 10 2 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_p12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 12 227406111424967172 = some 227406111424967172 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 10 2 227406111424967172 227406111424967172 227406111424967172 endpoint_16_38_p10 endpoint_16_38_w10
private theorem endpoint_16_38_w12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 12 2 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_p14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 14 227406111424967172 = some 227406111424967172 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 12 2 227406111424967172 227406111424967172 227406111424967172 endpoint_16_38_p12 endpoint_16_38_w12
private theorem endpoint_16_38_w14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 14 1 227406111424967172 = some 227406111424967172 := by decide +kernel
private theorem endpoint_16_38_p15 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 15 227406111424967172 = some 227406111424967172 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 14 1 227406111424967172 227406111424967172 227406111424967172 endpoint_16_38_p14 endpoint_16_38_w14
def endpoint_16_38 : CertifiedEndpoint :=
  ⟨⟨16, 38, 3252⟩, 227406111424967172, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_38_flag endpoint_16_38_sources 15 227406111424967172 227406111424967172 rfl endpoint_16_38_base endpoint_16_38_p15) (by decide)⟩
private def endpoint_16_39_flag : Flag := ⟨16, 39, 3211⟩
private def endpoint_16_39_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_39_base : receiptBase endpoint_16_39_flag endpoint_16_39_sources = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_w0 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 2 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_w2 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 2 2 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_p4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 4 230064017996109751 = some 230064017996109751 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 2 2 230064017996109751 230064017996109751 230064017996109751 endpoint_16_39_w0 endpoint_16_39_w2
private theorem endpoint_16_39_w4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 4 2 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_p6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 6 230064017996109751 = some 230064017996109751 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 4 2 230064017996109751 230064017996109751 230064017996109751 endpoint_16_39_p4 endpoint_16_39_w4
private theorem endpoint_16_39_w6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 6 2 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_p8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 8 230064017996109751 = some 230064017996109751 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 6 2 230064017996109751 230064017996109751 230064017996109751 endpoint_16_39_p6 endpoint_16_39_w6
private theorem endpoint_16_39_w8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 8 2 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_p10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 10 230064017996109751 = some 230064017996109751 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 8 2 230064017996109751 230064017996109751 230064017996109751 endpoint_16_39_p8 endpoint_16_39_w8
private theorem endpoint_16_39_w10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 10 2 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_p12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 12 230064017996109751 = some 230064017996109751 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 10 2 230064017996109751 230064017996109751 230064017996109751 endpoint_16_39_p10 endpoint_16_39_w10
private theorem endpoint_16_39_w12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 12 2 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_p14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 14 230064017996109751 = some 230064017996109751 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 12 2 230064017996109751 230064017996109751 230064017996109751 endpoint_16_39_p12 endpoint_16_39_w12
private theorem endpoint_16_39_w14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 14 1 230064017996109751 = some 230064017996109751 := by decide +kernel
private theorem endpoint_16_39_p15 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 15 230064017996109751 = some 230064017996109751 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 14 1 230064017996109751 230064017996109751 230064017996109751 endpoint_16_39_p14 endpoint_16_39_w14
def endpoint_16_39 : CertifiedEndpoint :=
  ⟨⟨16, 39, 3211⟩, 230064017996109751, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_39_flag endpoint_16_39_sources 15 230064017996109751 230064017996109751 rfl endpoint_16_39_base endpoint_16_39_p15) (by decide)⟩
private def endpoint_16_40_flag : Flag := ⟨16, 40, 3170⟩
private def endpoint_16_40_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_40_base : receiptBase endpoint_16_40_flag endpoint_16_40_sources = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_w0 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 2 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_w2 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 2 2 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_p4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 4 232058273031589583 = some 232058273031589583 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 2 2 232058273031589583 232058273031589583 232058273031589583 endpoint_16_40_w0 endpoint_16_40_w2
private theorem endpoint_16_40_w4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 4 2 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_p6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 6 232058273031589583 = some 232058273031589583 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 4 2 232058273031589583 232058273031589583 232058273031589583 endpoint_16_40_p4 endpoint_16_40_w4
private theorem endpoint_16_40_w6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 6 2 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_p8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 8 232058273031589583 = some 232058273031589583 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 6 2 232058273031589583 232058273031589583 232058273031589583 endpoint_16_40_p6 endpoint_16_40_w6
private theorem endpoint_16_40_w8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 8 2 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_p10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 10 232058273031589583 = some 232058273031589583 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 8 2 232058273031589583 232058273031589583 232058273031589583 endpoint_16_40_p8 endpoint_16_40_w8
private theorem endpoint_16_40_w10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 10 2 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_p12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 12 232058273031589583 = some 232058273031589583 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 10 2 232058273031589583 232058273031589583 232058273031589583 endpoint_16_40_p10 endpoint_16_40_w10
private theorem endpoint_16_40_w12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 12 2 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_p14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 14 232058273031589583 = some 232058273031589583 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 12 2 232058273031589583 232058273031589583 232058273031589583 endpoint_16_40_p12 endpoint_16_40_w12
private theorem endpoint_16_40_w14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 14 1 232058273031589583 = some 232058273031589583 := by decide +kernel
private theorem endpoint_16_40_p15 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 15 232058273031589583 = some 232058273031589583 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 14 1 232058273031589583 232058273031589583 232058273031589583 endpoint_16_40_p14 endpoint_16_40_w14
def endpoint_16_40 : CertifiedEndpoint :=
  ⟨⟨16, 40, 3170⟩, 232058273031589583, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_40_flag endpoint_16_40_sources 15 232058273031589583 232058273031589583 rfl endpoint_16_40_base endpoint_16_40_p15) (by decide)⟩
private def endpoint_16_41_flag : Flag := ⟨16, 41, 3127⟩
private def endpoint_16_41_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_41_base : receiptBase endpoint_16_41_flag endpoint_16_41_sources = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_w0 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 2 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_w2 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 2 2 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_p4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 4 233778936612010735 = some 233778936612010735 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 2 2 233778936612010735 233778936612010735 233778936612010735 endpoint_16_41_w0 endpoint_16_41_w2
private theorem endpoint_16_41_w4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 4 2 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_p6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 6 233778936612010735 = some 233778936612010735 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 4 2 233778936612010735 233778936612010735 233778936612010735 endpoint_16_41_p4 endpoint_16_41_w4
private theorem endpoint_16_41_w6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 6 2 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_p8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 8 233778936612010735 = some 233778936612010735 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 6 2 233778936612010735 233778936612010735 233778936612010735 endpoint_16_41_p6 endpoint_16_41_w6
private theorem endpoint_16_41_w8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 8 2 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_p10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 10 233778936612010735 = some 233778936612010735 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 8 2 233778936612010735 233778936612010735 233778936612010735 endpoint_16_41_p8 endpoint_16_41_w8
private theorem endpoint_16_41_w10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 10 2 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_p12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 12 233778936612010735 = some 233778936612010735 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 10 2 233778936612010735 233778936612010735 233778936612010735 endpoint_16_41_p10 endpoint_16_41_w10
private theorem endpoint_16_41_w12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 12 2 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_p14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 14 233778936612010735 = some 233778936612010735 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 12 2 233778936612010735 233778936612010735 233778936612010735 endpoint_16_41_p12 endpoint_16_41_w12
private theorem endpoint_16_41_w14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 14 1 233778936612010735 = some 233778936612010735 := by decide +kernel
private theorem endpoint_16_41_p15 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 15 233778936612010735 = some 233778936612010735 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 14 1 233778936612010735 233778936612010735 233778936612010735 endpoint_16_41_p14 endpoint_16_41_w14
def endpoint_16_41 : CertifiedEndpoint :=
  ⟨⟨16, 41, 3127⟩, 233778936612010735, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_41_flag endpoint_16_41_sources 15 233778936612010735 233778936612010735 rfl endpoint_16_41_base endpoint_16_41_p15) (by decide)⟩
private def endpoint_16_42_flag : Flag := ⟨16, 42, 3084⟩
private def endpoint_16_42_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_42_base : receiptBase endpoint_16_42_flag endpoint_16_42_sources = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_w0 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 2 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_w2 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 2 2 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_p4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 4 235367486856781459 = some 235367486856781459 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 2 2 235367486856781459 235367486856781459 235367486856781459 endpoint_16_42_w0 endpoint_16_42_w2
private theorem endpoint_16_42_w4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 4 2 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_p6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 6 235367486856781459 = some 235367486856781459 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 4 2 235367486856781459 235367486856781459 235367486856781459 endpoint_16_42_p4 endpoint_16_42_w4
private theorem endpoint_16_42_w6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 6 2 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_p8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 8 235367486856781459 = some 235367486856781459 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 6 2 235367486856781459 235367486856781459 235367486856781459 endpoint_16_42_p6 endpoint_16_42_w6
private theorem endpoint_16_42_w8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 8 2 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_p10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 10 235367486856781459 = some 235367486856781459 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 8 2 235367486856781459 235367486856781459 235367486856781459 endpoint_16_42_p8 endpoint_16_42_w8
private theorem endpoint_16_42_w10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 10 2 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_p12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 12 235367486856781459 = some 235367486856781459 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 10 2 235367486856781459 235367486856781459 235367486856781459 endpoint_16_42_p10 endpoint_16_42_w10
private theorem endpoint_16_42_w12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 12 2 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_p14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 14 235367486856781459 = some 235367486856781459 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 12 2 235367486856781459 235367486856781459 235367486856781459 endpoint_16_42_p12 endpoint_16_42_w12
private theorem endpoint_16_42_w14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 14 1 235367486856781459 = some 235367486856781459 := by decide +kernel
private theorem endpoint_16_42_p15 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 15 235367486856781459 = some 235367486856781459 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 14 1 235367486856781459 235367486856781459 235367486856781459 endpoint_16_42_p14 endpoint_16_42_w14
def endpoint_16_42 : CertifiedEndpoint :=
  ⟨⟨16, 42, 3084⟩, 235367486856781459, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_42_flag endpoint_16_42_sources 15 235367486856781459 235367486856781459 rfl endpoint_16_42_base endpoint_16_42_p15) (by decide)⟩
private def endpoint_16_43_flag : Flag := ⟨16, 43, 3039⟩
private def endpoint_16_43_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_43_base : receiptBase endpoint_16_43_flag endpoint_16_43_sources = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_w0 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 2 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_w2 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 2 2 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_p4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 4 237316081118725487 = some 237316081118725487 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 2 2 237316081118725487 237316081118725487 237316081118725487 endpoint_16_43_w0 endpoint_16_43_w2
private theorem endpoint_16_43_w4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 4 2 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_p6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 6 237316081118725487 = some 237316081118725487 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 4 2 237316081118725487 237316081118725487 237316081118725487 endpoint_16_43_p4 endpoint_16_43_w4
private theorem endpoint_16_43_w6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 6 2 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_p8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 8 237316081118725487 = some 237316081118725487 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 6 2 237316081118725487 237316081118725487 237316081118725487 endpoint_16_43_p6 endpoint_16_43_w6
private theorem endpoint_16_43_w8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 8 2 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_p10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 10 237316081118725487 = some 237316081118725487 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 8 2 237316081118725487 237316081118725487 237316081118725487 endpoint_16_43_p8 endpoint_16_43_w8
private theorem endpoint_16_43_w10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 10 2 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_p12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 12 237316081118725487 = some 237316081118725487 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 10 2 237316081118725487 237316081118725487 237316081118725487 endpoint_16_43_p10 endpoint_16_43_w10
private theorem endpoint_16_43_w12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 12 2 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_p14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 14 237316081118725487 = some 237316081118725487 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 12 2 237316081118725487 237316081118725487 237316081118725487 endpoint_16_43_p12 endpoint_16_43_w12
private theorem endpoint_16_43_w14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 14 1 237316081118725487 = some 237316081118725487 := by decide +kernel
private theorem endpoint_16_43_p15 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 15 237316081118725487 = some 237316081118725487 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 14 1 237316081118725487 237316081118725487 237316081118725487 endpoint_16_43_p14 endpoint_16_43_w14
def endpoint_16_43 : CertifiedEndpoint :=
  ⟨⟨16, 43, 3039⟩, 237316081118725487, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_43_flag endpoint_16_43_sources 15 237316081118725487 237316081118725487 rfl endpoint_16_43_base endpoint_16_43_p15) (by decide)⟩
private def endpoint_16_44_flag : Flag := ⟨16, 44, 2994⟩
private def endpoint_16_44_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_44_base : receiptBase endpoint_16_44_flag endpoint_16_44_sources = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_w0 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 2 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_w2 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 2 2 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_p4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 4 238493591376166421 = some 238493591376166421 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 2 2 238493591376166421 238493591376166421 238493591376166421 endpoint_16_44_w0 endpoint_16_44_w2
private theorem endpoint_16_44_w4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 4 2 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_p6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 6 238493591376166421 = some 238493591376166421 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 4 2 238493591376166421 238493591376166421 238493591376166421 endpoint_16_44_p4 endpoint_16_44_w4
private theorem endpoint_16_44_w6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 6 2 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_p8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 8 238493591376166421 = some 238493591376166421 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 6 2 238493591376166421 238493591376166421 238493591376166421 endpoint_16_44_p6 endpoint_16_44_w6
private theorem endpoint_16_44_w8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 8 2 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_p10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 10 238493591376166421 = some 238493591376166421 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 8 2 238493591376166421 238493591376166421 238493591376166421 endpoint_16_44_p8 endpoint_16_44_w8
private theorem endpoint_16_44_w10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 10 2 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_p12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 12 238493591376166421 = some 238493591376166421 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 10 2 238493591376166421 238493591376166421 238493591376166421 endpoint_16_44_p10 endpoint_16_44_w10
private theorem endpoint_16_44_w12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 12 2 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_p14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 14 238493591376166421 = some 238493591376166421 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 12 2 238493591376166421 238493591376166421 238493591376166421 endpoint_16_44_p12 endpoint_16_44_w12
private theorem endpoint_16_44_w14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 14 1 238493591376166421 = some 238493591376166421 := by decide +kernel
private theorem endpoint_16_44_p15 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 15 238493591376166421 = some 238493591376166421 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 14 1 238493591376166421 238493591376166421 238493591376166421 endpoint_16_44_p14 endpoint_16_44_w14
def endpoint_16_44 : CertifiedEndpoint :=
  ⟨⟨16, 44, 2994⟩, 238493591376166421, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_44_flag endpoint_16_44_sources 15 238493591376166421 238493591376166421 rfl endpoint_16_44_base endpoint_16_44_p15) (by decide)⟩
private def endpoint_16_45_flag : Flag := ⟨16, 45, 2947⟩
private def endpoint_16_45_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_45_base : receiptBase endpoint_16_45_flag endpoint_16_45_sources = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_w0 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 2 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_w2 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 2 2 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_p4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 4 239371878909227249 = some 239371878909227249 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 2 2 239371878909227249 239371878909227249 239371878909227249 endpoint_16_45_w0 endpoint_16_45_w2
private theorem endpoint_16_45_w4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 4 2 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_p6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 6 239371878909227249 = some 239371878909227249 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 4 2 239371878909227249 239371878909227249 239371878909227249 endpoint_16_45_p4 endpoint_16_45_w4
private theorem endpoint_16_45_w6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 6 2 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_p8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 8 239371878909227249 = some 239371878909227249 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 6 2 239371878909227249 239371878909227249 239371878909227249 endpoint_16_45_p6 endpoint_16_45_w6
private theorem endpoint_16_45_w8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 8 2 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_p10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 10 239371878909227249 = some 239371878909227249 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 8 2 239371878909227249 239371878909227249 239371878909227249 endpoint_16_45_p8 endpoint_16_45_w8
private theorem endpoint_16_45_w10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 10 2 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_p12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 12 239371878909227249 = some 239371878909227249 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 10 2 239371878909227249 239371878909227249 239371878909227249 endpoint_16_45_p10 endpoint_16_45_w10
private theorem endpoint_16_45_w12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 12 2 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_p14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 14 239371878909227249 = some 239371878909227249 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 12 2 239371878909227249 239371878909227249 239371878909227249 endpoint_16_45_p12 endpoint_16_45_w12
private theorem endpoint_16_45_w14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 14 1 239371878909227249 = some 239371878909227249 := by decide +kernel
private theorem endpoint_16_45_p15 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 15 239371878909227249 = some 239371878909227249 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 14 1 239371878909227249 239371878909227249 239371878909227249 endpoint_16_45_p14 endpoint_16_45_w14
def endpoint_16_45 : CertifiedEndpoint :=
  ⟨⟨16, 45, 2947⟩, 239371878909227249, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_45_flag endpoint_16_45_sources 15 239371878909227249 239371878909227249 rfl endpoint_16_45_base endpoint_16_45_p15) (by decide)⟩
private def endpoint_16_46_flag : Flag := ⟨16, 46, 2900⟩
private def endpoint_16_46_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_46_base : receiptBase endpoint_16_46_flag endpoint_16_46_sources = some 240773119818320497 := by decide +kernel
private theorem endpoint_16_46_w0 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 2 240773119818320497 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_w2 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 2 2 241771067642828104 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_p4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 4 240773119818320497 = some 241771067642828104 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 2 2 240773119818320497 241771067642828104 241771067642828104 endpoint_16_46_w0 endpoint_16_46_w2
private theorem endpoint_16_46_w4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 4 2 241771067642828104 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_p6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 6 240773119818320497 = some 241771067642828104 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 4 2 240773119818320497 241771067642828104 241771067642828104 endpoint_16_46_p4 endpoint_16_46_w4
private theorem endpoint_16_46_w6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 6 2 241771067642828104 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_p8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 8 240773119818320497 = some 241771067642828104 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 6 2 240773119818320497 241771067642828104 241771067642828104 endpoint_16_46_p6 endpoint_16_46_w6
private theorem endpoint_16_46_w8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 8 2 241771067642828104 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_p10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 10 240773119818320497 = some 241771067642828104 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 8 2 240773119818320497 241771067642828104 241771067642828104 endpoint_16_46_p8 endpoint_16_46_w8
private theorem endpoint_16_46_w10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 10 2 241771067642828104 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_p12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 12 240773119818320497 = some 241771067642828104 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 10 2 240773119818320497 241771067642828104 241771067642828104 endpoint_16_46_p10 endpoint_16_46_w10
private theorem endpoint_16_46_w12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 12 2 241771067642828104 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_p14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 14 240773119818320497 = some 241771067642828104 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 12 2 240773119818320497 241771067642828104 241771067642828104 endpoint_16_46_p12 endpoint_16_46_w12
private theorem endpoint_16_46_w14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 14 1 241771067642828104 = some 241771067642828104 := by decide +kernel
private theorem endpoint_16_46_p15 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 15 240773119818320497 = some 241771067642828104 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 14 1 240773119818320497 241771067642828104 241771067642828104 endpoint_16_46_p14 endpoint_16_46_w14
def endpoint_16_46 : CertifiedEndpoint :=
  ⟨⟨16, 46, 2900⟩, 241771067642828104, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_46_flag endpoint_16_46_sources 15 240773119818320497 241771067642828104 rfl endpoint_16_46_base endpoint_16_46_p15) (by decide)⟩
private def endpoint_16_47_flag : Flag := ⟨16, 47, 2851⟩
private def endpoint_16_47_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_47_base : receiptBase endpoint_16_47_flag endpoint_16_47_sources = some 241226142296725942 := by decide +kernel
private theorem endpoint_16_47_w0 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 2 241226142296725942 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_w2 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 2 2 245961538521825860 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_p4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 4 241226142296725942 = some 245961538521825860 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 2 2 241226142296725942 245961538521825860 245961538521825860 endpoint_16_47_w0 endpoint_16_47_w2
private theorem endpoint_16_47_w4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 4 2 245961538521825860 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_p6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 6 241226142296725942 = some 245961538521825860 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 4 2 241226142296725942 245961538521825860 245961538521825860 endpoint_16_47_p4 endpoint_16_47_w4
private theorem endpoint_16_47_w6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 6 2 245961538521825860 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_p8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 8 241226142296725942 = some 245961538521825860 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 6 2 241226142296725942 245961538521825860 245961538521825860 endpoint_16_47_p6 endpoint_16_47_w6
private theorem endpoint_16_47_w8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 8 2 245961538521825860 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_p10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 10 241226142296725942 = some 245961538521825860 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 8 2 241226142296725942 245961538521825860 245961538521825860 endpoint_16_47_p8 endpoint_16_47_w8
private theorem endpoint_16_47_w10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 10 2 245961538521825860 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_p12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 12 241226142296725942 = some 245961538521825860 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 10 2 241226142296725942 245961538521825860 245961538521825860 endpoint_16_47_p10 endpoint_16_47_w10
private theorem endpoint_16_47_w12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 12 2 245961538521825860 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_p14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 14 241226142296725942 = some 245961538521825860 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 12 2 241226142296725942 245961538521825860 245961538521825860 endpoint_16_47_p12 endpoint_16_47_w12
private theorem endpoint_16_47_w14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 14 1 245961538521825860 = some 245961538521825860 := by decide +kernel
private theorem endpoint_16_47_p15 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 15 241226142296725942 = some 245961538521825860 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 14 1 241226142296725942 245961538521825860 245961538521825860 endpoint_16_47_p14 endpoint_16_47_w14
def endpoint_16_47 : CertifiedEndpoint :=
  ⟨⟨16, 47, 2851⟩, 245961538521825860, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_47_flag endpoint_16_47_sources 15 241226142296725942 245961538521825860 rfl endpoint_16_47_base endpoint_16_47_p15) (by decide)⟩
private def endpoint_16_48_flag : Flag := ⟨16, 48, 2802⟩
private def endpoint_16_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_48_base : receiptBase endpoint_16_48_flag endpoint_16_48_sources = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_w0 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 2 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_w2 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 2 2 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_p4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 4 242160383040863655 = some 242160383040863655 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 2 2 242160383040863655 242160383040863655 242160383040863655 endpoint_16_48_w0 endpoint_16_48_w2
private theorem endpoint_16_48_w4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 4 2 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_p6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 6 242160383040863655 = some 242160383040863655 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 4 2 242160383040863655 242160383040863655 242160383040863655 endpoint_16_48_p4 endpoint_16_48_w4
private theorem endpoint_16_48_w6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 6 2 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_p8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 8 242160383040863655 = some 242160383040863655 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 6 2 242160383040863655 242160383040863655 242160383040863655 endpoint_16_48_p6 endpoint_16_48_w6
private theorem endpoint_16_48_w8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 8 2 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_p10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 10 242160383040863655 = some 242160383040863655 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 8 2 242160383040863655 242160383040863655 242160383040863655 endpoint_16_48_p8 endpoint_16_48_w8
private theorem endpoint_16_48_w10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 10 2 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_p12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 12 242160383040863655 = some 242160383040863655 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 10 2 242160383040863655 242160383040863655 242160383040863655 endpoint_16_48_p10 endpoint_16_48_w10
private theorem endpoint_16_48_w12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 12 2 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_p14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 14 242160383040863655 = some 242160383040863655 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 12 2 242160383040863655 242160383040863655 242160383040863655 endpoint_16_48_p12 endpoint_16_48_w12
private theorem endpoint_16_48_w14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 14 1 242160383040863655 = some 242160383040863655 := by decide +kernel
private theorem endpoint_16_48_p15 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 15 242160383040863655 = some 242160383040863655 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 14 1 242160383040863655 242160383040863655 242160383040863655 endpoint_16_48_p14 endpoint_16_48_w14
def endpoint_16_48 : CertifiedEndpoint :=
  ⟨⟨16, 48, 2802⟩, 242160383040863655, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_48_flag endpoint_16_48_sources 15 242160383040863655 242160383040863655 rfl endpoint_16_48_base endpoint_16_48_p15) (by decide)⟩
private def endpoint_16_49_flag : Flag := ⟨16, 49, 2751⟩
private def endpoint_16_49_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_49_base : receiptBase endpoint_16_49_flag endpoint_16_49_sources = some 242119981008475885 := by decide +kernel
private theorem endpoint_16_49_w0 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 2 242119981008475885 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_w2 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 2 2 244856369744750971 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_p4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 4 242119981008475885 = some 244856369744750971 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 2 2 242119981008475885 244856369744750971 244856369744750971 endpoint_16_49_w0 endpoint_16_49_w2
private theorem endpoint_16_49_w4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 4 2 244856369744750971 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_p6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 6 242119981008475885 = some 244856369744750971 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 4 2 242119981008475885 244856369744750971 244856369744750971 endpoint_16_49_p4 endpoint_16_49_w4
private theorem endpoint_16_49_w6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 6 2 244856369744750971 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_p8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 8 242119981008475885 = some 244856369744750971 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 6 2 242119981008475885 244856369744750971 244856369744750971 endpoint_16_49_p6 endpoint_16_49_w6
private theorem endpoint_16_49_w8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 8 2 244856369744750971 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_p10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 10 242119981008475885 = some 244856369744750971 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 8 2 242119981008475885 244856369744750971 244856369744750971 endpoint_16_49_p8 endpoint_16_49_w8
private theorem endpoint_16_49_w10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 10 2 244856369744750971 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_p12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 12 242119981008475885 = some 244856369744750971 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 10 2 242119981008475885 244856369744750971 244856369744750971 endpoint_16_49_p10 endpoint_16_49_w10
private theorem endpoint_16_49_w12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 12 2 244856369744750971 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_p14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 14 242119981008475885 = some 244856369744750971 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 12 2 242119981008475885 244856369744750971 244856369744750971 endpoint_16_49_p12 endpoint_16_49_w12
private theorem endpoint_16_49_w14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 14 1 244856369744750971 = some 244856369744750971 := by decide +kernel
private theorem endpoint_16_49_p15 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 15 242119981008475885 = some 244856369744750971 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 14 1 242119981008475885 244856369744750971 244856369744750971 endpoint_16_49_p14 endpoint_16_49_w14
def endpoint_16_49 : CertifiedEndpoint :=
  ⟨⟨16, 49, 2751⟩, 244856369744750971, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_49_flag endpoint_16_49_sources 15 242119981008475885 244856369744750971 rfl endpoint_16_49_base endpoint_16_49_p15) (by decide)⟩
private def endpoint_16_50_flag : Flag := ⟨16, 50, 2699⟩
private def endpoint_16_50_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_50_base : receiptBase endpoint_16_50_flag endpoint_16_50_sources = some 241832036847544666 := by decide +kernel
private theorem endpoint_16_50_w0 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 2 241832036847544666 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_w2 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 2 2 248297753757557944 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_p4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 4 241832036847544666 = some 248297753757557944 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 2 2 241832036847544666 248297753757557944 248297753757557944 endpoint_16_50_w0 endpoint_16_50_w2
private theorem endpoint_16_50_w4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 4 2 248297753757557944 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_p6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 6 241832036847544666 = some 248297753757557944 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 4 2 241832036847544666 248297753757557944 248297753757557944 endpoint_16_50_p4 endpoint_16_50_w4
private theorem endpoint_16_50_w6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 6 2 248297753757557944 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_p8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 8 241832036847544666 = some 248297753757557944 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 6 2 241832036847544666 248297753757557944 248297753757557944 endpoint_16_50_p6 endpoint_16_50_w6
private theorem endpoint_16_50_w8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 8 2 248297753757557944 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_p10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 10 241832036847544666 = some 248297753757557944 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 8 2 241832036847544666 248297753757557944 248297753757557944 endpoint_16_50_p8 endpoint_16_50_w8
private theorem endpoint_16_50_w10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 10 2 248297753757557944 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_p12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 12 241832036847544666 = some 248297753757557944 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 10 2 241832036847544666 248297753757557944 248297753757557944 endpoint_16_50_p10 endpoint_16_50_w10
private theorem endpoint_16_50_w12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 12 2 248297753757557944 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_p14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 14 241832036847544666 = some 248297753757557944 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 12 2 241832036847544666 248297753757557944 248297753757557944 endpoint_16_50_p12 endpoint_16_50_w12
private theorem endpoint_16_50_w14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 14 1 248297753757557944 = some 248297753757557944 := by decide +kernel
private theorem endpoint_16_50_p15 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 15 241832036847544666 = some 248297753757557944 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 14 1 241832036847544666 248297753757557944 248297753757557944 endpoint_16_50_p14 endpoint_16_50_w14
def endpoint_16_50 : CertifiedEndpoint :=
  ⟨⟨16, 50, 2699⟩, 248297753757557944, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_50_flag endpoint_16_50_sources 15 241832036847544666 248297753757557944 rfl endpoint_16_50_base endpoint_16_50_p15) (by decide)⟩
private def endpoint_16_51_flag : Flag := ⟨16, 51, 2645⟩
private def endpoint_16_51_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_51_base : receiptBase endpoint_16_51_flag endpoint_16_51_sources = some 241202017209993522 := by decide +kernel
private theorem endpoint_16_51_w0 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 2 241202017209993522 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_w2 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 2 2 251505021770077785 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_p4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 4 241202017209993522 = some 251505021770077785 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 2 2 241202017209993522 251505021770077785 251505021770077785 endpoint_16_51_w0 endpoint_16_51_w2
private theorem endpoint_16_51_w4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 4 2 251505021770077785 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_p6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 6 241202017209993522 = some 251505021770077785 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 4 2 241202017209993522 251505021770077785 251505021770077785 endpoint_16_51_p4 endpoint_16_51_w4
private theorem endpoint_16_51_w6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 6 2 251505021770077785 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_p8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 8 241202017209993522 = some 251505021770077785 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 6 2 241202017209993522 251505021770077785 251505021770077785 endpoint_16_51_p6 endpoint_16_51_w6
private theorem endpoint_16_51_w8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 8 2 251505021770077785 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_p10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 10 241202017209993522 = some 251505021770077785 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 8 2 241202017209993522 251505021770077785 251505021770077785 endpoint_16_51_p8 endpoint_16_51_w8
private theorem endpoint_16_51_w10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 10 2 251505021770077785 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_p12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 12 241202017209993522 = some 251505021770077785 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 10 2 241202017209993522 251505021770077785 251505021770077785 endpoint_16_51_p10 endpoint_16_51_w10
private theorem endpoint_16_51_w12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 12 2 251505021770077785 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_p14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 14 241202017209993522 = some 251505021770077785 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 12 2 241202017209993522 251505021770077785 251505021770077785 endpoint_16_51_p12 endpoint_16_51_w12
private theorem endpoint_16_51_w14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 14 1 251505021770077785 = some 251505021770077785 := by decide +kernel
private theorem endpoint_16_51_p15 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 15 241202017209993522 = some 251505021770077785 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 14 1 241202017209993522 251505021770077785 251505021770077785 endpoint_16_51_p14 endpoint_16_51_w14
def endpoint_16_51 : CertifiedEndpoint :=
  ⟨⟨16, 51, 2645⟩, 251505021770077785, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_51_flag endpoint_16_51_sources 15 241202017209993522 251505021770077785 rfl endpoint_16_51_base endpoint_16_51_p15) (by decide)⟩
private def endpoint_16_52_flag : Flag := ⟨16, 52, 2591⟩
private def endpoint_16_52_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_52_base : receiptBase endpoint_16_52_flag endpoint_16_52_sources = some 240403533359605001 := by decide +kernel
private theorem endpoint_16_52_w0 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 2 240403533359605001 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_w2 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 2 2 254575878194378916 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_p4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 4 240403533359605001 = some 254575878194378916 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 2 2 240403533359605001 254575878194378916 254575878194378916 endpoint_16_52_w0 endpoint_16_52_w2
private theorem endpoint_16_52_w4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 4 2 254575878194378916 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_p6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 6 240403533359605001 = some 254575878194378916 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 4 2 240403533359605001 254575878194378916 254575878194378916 endpoint_16_52_p4 endpoint_16_52_w4
private theorem endpoint_16_52_w6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 6 2 254575878194378916 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_p8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 8 240403533359605001 = some 254575878194378916 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 6 2 240403533359605001 254575878194378916 254575878194378916 endpoint_16_52_p6 endpoint_16_52_w6
private theorem endpoint_16_52_w8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 8 2 254575878194378916 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_p10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 10 240403533359605001 = some 254575878194378916 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 8 2 240403533359605001 254575878194378916 254575878194378916 endpoint_16_52_p8 endpoint_16_52_w8
private theorem endpoint_16_52_w10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 10 2 254575878194378916 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_p12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 12 240403533359605001 = some 254575878194378916 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 10 2 240403533359605001 254575878194378916 254575878194378916 endpoint_16_52_p10 endpoint_16_52_w10
private theorem endpoint_16_52_w12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 12 2 254575878194378916 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_p14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 14 240403533359605001 = some 254575878194378916 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 12 2 240403533359605001 254575878194378916 254575878194378916 endpoint_16_52_p12 endpoint_16_52_w12
private theorem endpoint_16_52_w14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 14 1 254575878194378916 = some 254575878194378916 := by decide +kernel
private theorem endpoint_16_52_p15 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 15 240403533359605001 = some 254575878194378916 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 14 1 240403533359605001 254575878194378916 254575878194378916 endpoint_16_52_p14 endpoint_16_52_w14
def endpoint_16_52 : CertifiedEndpoint :=
  ⟨⟨16, 52, 2591⟩, 254575878194378916, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_52_flag endpoint_16_52_sources 15 240403533359605001 254575878194378916 rfl endpoint_16_52_base endpoint_16_52_p15) (by decide)⟩
private def endpoint_16_53_flag : Flag := ⟨16, 53, 2535⟩
private def endpoint_16_53_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_53_base : receiptBase endpoint_16_53_flag endpoint_16_53_sources = some 239250609686700234 := by decide +kernel
private theorem endpoint_16_53_w0 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 2 239250609686700234 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_w2 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 2 2 257402791486278555 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_p4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 4 239250609686700234 = some 257402791486278555 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 2 2 239250609686700234 257402791486278555 257402791486278555 endpoint_16_53_w0 endpoint_16_53_w2
private theorem endpoint_16_53_w4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 4 2 257402791486278555 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_p6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 6 239250609686700234 = some 257402791486278555 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 4 2 239250609686700234 257402791486278555 257402791486278555 endpoint_16_53_p4 endpoint_16_53_w4
private theorem endpoint_16_53_w6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 6 2 257402791486278555 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_p8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 8 239250609686700234 = some 257402791486278555 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 6 2 239250609686700234 257402791486278555 257402791486278555 endpoint_16_53_p6 endpoint_16_53_w6
private theorem endpoint_16_53_w8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 8 2 257402791486278555 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_p10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 10 239250609686700234 = some 257402791486278555 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 8 2 239250609686700234 257402791486278555 257402791486278555 endpoint_16_53_p8 endpoint_16_53_w8
private theorem endpoint_16_53_w10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 10 2 257402791486278555 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_p12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 12 239250609686700234 = some 257402791486278555 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 10 2 239250609686700234 257402791486278555 257402791486278555 endpoint_16_53_p10 endpoint_16_53_w10
private theorem endpoint_16_53_w12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 12 2 257402791486278555 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_p14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 14 239250609686700234 = some 257402791486278555 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 12 2 239250609686700234 257402791486278555 257402791486278555 endpoint_16_53_p12 endpoint_16_53_w12
private theorem endpoint_16_53_w14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 14 1 257402791486278555 = some 257402791486278555 := by decide +kernel
private theorem endpoint_16_53_p15 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 15 239250609686700234 = some 257402791486278555 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 14 1 239250609686700234 257402791486278555 257402791486278555 endpoint_16_53_p14 endpoint_16_53_w14
def endpoint_16_53 : CertifiedEndpoint :=
  ⟨⟨16, 53, 2535⟩, 257402791486278555, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_53_flag endpoint_16_53_sources 15 239250609686700234 257402791486278555 rfl endpoint_16_53_base endpoint_16_53_p15) (by decide)⟩
private def endpoint_16_54_flag : Flag := ⟨16, 54, 2477⟩
private def endpoint_16_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_54_base : receiptBase endpoint_16_54_flag endpoint_16_54_sources = some 237733972931856980 := by decide +kernel
private theorem endpoint_16_54_w0 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 2 237733972931856980 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_w2 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 2 2 259978391296690932 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_p4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 4 237733972931856980 = some 259978391296690932 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 2 2 237733972931856980 259978391296690932 259978391296690932 endpoint_16_54_w0 endpoint_16_54_w2
private theorem endpoint_16_54_w4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 4 2 259978391296690932 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_p6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 6 237733972931856980 = some 259978391296690932 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 4 2 237733972931856980 259978391296690932 259978391296690932 endpoint_16_54_p4 endpoint_16_54_w4
private theorem endpoint_16_54_w6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 6 2 259978391296690932 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_p8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 8 237733972931856980 = some 259978391296690932 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 6 2 237733972931856980 259978391296690932 259978391296690932 endpoint_16_54_p6 endpoint_16_54_w6
private theorem endpoint_16_54_w8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 8 2 259978391296690932 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_p10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 10 237733972931856980 = some 259978391296690932 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 8 2 237733972931856980 259978391296690932 259978391296690932 endpoint_16_54_p8 endpoint_16_54_w8
private theorem endpoint_16_54_w10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 10 2 259978391296690932 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_p12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 12 237733972931856980 = some 259978391296690932 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 10 2 237733972931856980 259978391296690932 259978391296690932 endpoint_16_54_p10 endpoint_16_54_w10
private theorem endpoint_16_54_w12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 12 2 259978391296690932 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_p14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 14 237733972931856980 = some 259978391296690932 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 12 2 237733972931856980 259978391296690932 259978391296690932 endpoint_16_54_p12 endpoint_16_54_w12
private theorem endpoint_16_54_w14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 14 1 259978391296690932 = some 259978391296690932 := by decide +kernel
private theorem endpoint_16_54_p15 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 15 237733972931856980 = some 259978391296690932 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 14 1 237733972931856980 259978391296690932 259978391296690932 endpoint_16_54_p14 endpoint_16_54_w14
def endpoint_16_54 : CertifiedEndpoint :=
  ⟨⟨16, 54, 2477⟩, 259978391296690932, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_54_flag endpoint_16_54_sources 15 237733972931856980 259978391296690932 rfl endpoint_16_54_base endpoint_16_54_p15) (by decide)⟩
private def endpoint_16_55_flag : Flag := ⟨16, 55, 2418⟩
private def endpoint_16_55_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_55_base : receiptBase endpoint_16_55_flag endpoint_16_55_sources = some 241848903989106502 := by decide +kernel
private theorem endpoint_16_55_w0 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 2 241848903989106502 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_w2 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 2 2 254785197724366893 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_p4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 4 241848903989106502 = some 254785197724366893 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 2 2 241848903989106502 254785197724366893 254785197724366893 endpoint_16_55_w0 endpoint_16_55_w2
private theorem endpoint_16_55_w4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 4 2 254785197724366893 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_p6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 6 241848903989106502 = some 254785197724366893 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 4 2 241848903989106502 254785197724366893 254785197724366893 endpoint_16_55_p4 endpoint_16_55_w4
private theorem endpoint_16_55_w6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 6 2 254785197724366893 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_p8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 8 241848903989106502 = some 254785197724366893 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 6 2 241848903989106502 254785197724366893 254785197724366893 endpoint_16_55_p6 endpoint_16_55_w6
private theorem endpoint_16_55_w8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 8 2 254785197724366893 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_p10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 10 241848903989106502 = some 254785197724366893 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 8 2 241848903989106502 254785197724366893 254785197724366893 endpoint_16_55_p8 endpoint_16_55_w8
private theorem endpoint_16_55_w10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 10 2 254785197724366893 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_p12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 12 241848903989106502 = some 254785197724366893 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 10 2 241848903989106502 254785197724366893 254785197724366893 endpoint_16_55_p10 endpoint_16_55_w10
private theorem endpoint_16_55_w12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 12 2 254785197724366893 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_p14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 14 241848903989106502 = some 254785197724366893 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 12 2 241848903989106502 254785197724366893 254785197724366893 endpoint_16_55_p12 endpoint_16_55_w12
private theorem endpoint_16_55_w14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 14 1 254785197724366893 = some 254785197724366893 := by decide +kernel
private theorem endpoint_16_55_p15 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 15 241848903989106502 = some 254785197724366893 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 14 1 241848903989106502 254785197724366893 254785197724366893 endpoint_16_55_p14 endpoint_16_55_w14
def endpoint_16_55 : CertifiedEndpoint :=
  ⟨⟨16, 55, 2418⟩, 254785197724366893, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_55_flag endpoint_16_55_sources 15 241848903989106502 254785197724366893 rfl endpoint_16_55_base endpoint_16_55_p15) (by decide)⟩
private def endpoint_16_56_flag : Flag := ⟨16, 56, 2358⟩
private def endpoint_16_56_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_56_base : receiptBase endpoint_16_56_flag endpoint_16_56_sources = some 239800788207832916 := by decide +kernel
private theorem endpoint_16_56_w0 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 2 239800788207832916 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_w2 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 2 2 256788590453894208 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_p4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 4 239800788207832916 = some 256788590453894208 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 2 2 239800788207832916 256788590453894208 256788590453894208 endpoint_16_56_w0 endpoint_16_56_w2
private theorem endpoint_16_56_w4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 4 2 256788590453894208 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_p6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 6 239800788207832916 = some 256788590453894208 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 4 2 239800788207832916 256788590453894208 256788590453894208 endpoint_16_56_p4 endpoint_16_56_w4
private theorem endpoint_16_56_w6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 6 2 256788590453894208 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_p8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 8 239800788207832916 = some 256788590453894208 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 6 2 239800788207832916 256788590453894208 256788590453894208 endpoint_16_56_p6 endpoint_16_56_w6
private theorem endpoint_16_56_w8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 8 2 256788590453894208 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_p10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 10 239800788207832916 = some 256788590453894208 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 8 2 239800788207832916 256788590453894208 256788590453894208 endpoint_16_56_p8 endpoint_16_56_w8
private theorem endpoint_16_56_w10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 10 2 256788590453894208 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_p12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 12 239800788207832916 = some 256788590453894208 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 10 2 239800788207832916 256788590453894208 256788590453894208 endpoint_16_56_p10 endpoint_16_56_w10
private theorem endpoint_16_56_w12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 12 2 256788590453894208 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_p14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 14 239800788207832916 = some 256788590453894208 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 12 2 239800788207832916 256788590453894208 256788590453894208 endpoint_16_56_p12 endpoint_16_56_w12
private theorem endpoint_16_56_w14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 14 1 256788590453894208 = some 256788590453894208 := by decide +kernel
private theorem endpoint_16_56_p15 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 15 239800788207832916 = some 256788590453894208 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 14 1 239800788207832916 256788590453894208 256788590453894208 endpoint_16_56_p14 endpoint_16_56_w14
def endpoint_16_56 : CertifiedEndpoint :=
  ⟨⟨16, 56, 2358⟩, 256788590453894208, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_56_flag endpoint_16_56_sources 15 239800788207832916 256788590453894208 rfl endpoint_16_56_base endpoint_16_56_p15) (by decide)⟩
private def endpoint_16_57_flag : Flag := ⟨16, 57, 2296⟩
private def endpoint_16_57_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_57_base : receiptBase endpoint_16_57_flag endpoint_16_57_sources = some 238445534633884776 := by decide +kernel
private theorem endpoint_16_57_w0 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 2 238445534633884776 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_w2 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 2 2 240671948678136274 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_p4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 4 238445534633884776 = some 240671948678136274 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 2 2 238445534633884776 240671948678136274 240671948678136274 endpoint_16_57_w0 endpoint_16_57_w2
private theorem endpoint_16_57_w4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 4 2 240671948678136274 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_p6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 6 238445534633884776 = some 240671948678136274 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 4 2 238445534633884776 240671948678136274 240671948678136274 endpoint_16_57_p4 endpoint_16_57_w4
private theorem endpoint_16_57_w6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 6 2 240671948678136274 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_p8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 8 238445534633884776 = some 240671948678136274 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 6 2 238445534633884776 240671948678136274 240671948678136274 endpoint_16_57_p6 endpoint_16_57_w6
private theorem endpoint_16_57_w8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 8 2 240671948678136274 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_p10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 10 238445534633884776 = some 240671948678136274 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 8 2 238445534633884776 240671948678136274 240671948678136274 endpoint_16_57_p8 endpoint_16_57_w8
private theorem endpoint_16_57_w10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 10 2 240671948678136274 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_p12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 12 238445534633884776 = some 240671948678136274 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 10 2 238445534633884776 240671948678136274 240671948678136274 endpoint_16_57_p10 endpoint_16_57_w10
private theorem endpoint_16_57_w12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 12 2 240671948678136274 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_p14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 14 238445534633884776 = some 240671948678136274 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 12 2 238445534633884776 240671948678136274 240671948678136274 endpoint_16_57_p12 endpoint_16_57_w12
private theorem endpoint_16_57_w14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 14 1 240671948678136274 = some 240671948678136274 := by decide +kernel
private theorem endpoint_16_57_p15 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 15 238445534633884776 = some 240671948678136274 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 14 1 238445534633884776 240671948678136274 240671948678136274 endpoint_16_57_p14 endpoint_16_57_w14
def endpoint_16_57 : CertifiedEndpoint :=
  ⟨⟨16, 57, 2296⟩, 240671948678136274, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_57_flag endpoint_16_57_sources 15 238445534633884776 240671948678136274 rfl endpoint_16_57_base endpoint_16_57_p15) (by decide)⟩
private def endpoint_16_58_flag : Flag := ⟨16, 58, 2233⟩
private def endpoint_16_58_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_58_base : receiptBase endpoint_16_58_flag endpoint_16_58_sources = some 235635805575233436 := by decide +kernel
private theorem endpoint_16_58_w0 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 2 235635805575233436 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_w2 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 2 2 241820870628264316 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_p4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 4 235635805575233436 = some 241820870628264316 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 2 2 235635805575233436 241820870628264316 241820870628264316 endpoint_16_58_w0 endpoint_16_58_w2
private theorem endpoint_16_58_w4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 4 2 241820870628264316 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_p6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 6 235635805575233436 = some 241820870628264316 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 4 2 235635805575233436 241820870628264316 241820870628264316 endpoint_16_58_p4 endpoint_16_58_w4
private theorem endpoint_16_58_w6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 6 2 241820870628264316 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_p8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 8 235635805575233436 = some 241820870628264316 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 6 2 235635805575233436 241820870628264316 241820870628264316 endpoint_16_58_p6 endpoint_16_58_w6
private theorem endpoint_16_58_w8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 8 2 241820870628264316 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_p10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 10 235635805575233436 = some 241820870628264316 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 8 2 235635805575233436 241820870628264316 241820870628264316 endpoint_16_58_p8 endpoint_16_58_w8
private theorem endpoint_16_58_w10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 10 2 241820870628264316 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_p12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 12 235635805575233436 = some 241820870628264316 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 10 2 235635805575233436 241820870628264316 241820870628264316 endpoint_16_58_p10 endpoint_16_58_w10
private theorem endpoint_16_58_w12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 12 2 241820870628264316 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_p14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 14 235635805575233436 = some 241820870628264316 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 12 2 235635805575233436 241820870628264316 241820870628264316 endpoint_16_58_p12 endpoint_16_58_w12
private theorem endpoint_16_58_w14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 14 1 241820870628264316 = some 241820870628264316 := by decide +kernel
private theorem endpoint_16_58_p15 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 15 235635805575233436 = some 241820870628264316 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 14 1 235635805575233436 241820870628264316 241820870628264316 endpoint_16_58_p14 endpoint_16_58_w14
def endpoint_16_58 : CertifiedEndpoint :=
  ⟨⟨16, 58, 2233⟩, 241820870628264316, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_58_flag endpoint_16_58_sources 15 235635805575233436 241820870628264316 rfl endpoint_16_58_base endpoint_16_58_p15) (by decide)⟩
private def endpoint_16_59_flag : Flag := ⟨16, 59, 2167⟩
private def endpoint_16_59_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_59_base : receiptBase endpoint_16_59_flag endpoint_16_59_sources = some 232313985706354047 := by decide +kernel
private theorem endpoint_16_59_w0 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 2 232313985706354047 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_w2 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 2 2 242627861579384855 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_p4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 4 232313985706354047 = some 242627861579384855 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 2 2 232313985706354047 242627861579384855 242627861579384855 endpoint_16_59_w0 endpoint_16_59_w2
private theorem endpoint_16_59_w4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 4 2 242627861579384855 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_p6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 6 232313985706354047 = some 242627861579384855 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 4 2 232313985706354047 242627861579384855 242627861579384855 endpoint_16_59_p4 endpoint_16_59_w4
private theorem endpoint_16_59_w6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 6 2 242627861579384855 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_p8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 8 232313985706354047 = some 242627861579384855 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 6 2 232313985706354047 242627861579384855 242627861579384855 endpoint_16_59_p6 endpoint_16_59_w6
private theorem endpoint_16_59_w8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 8 2 242627861579384855 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_p10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 10 232313985706354047 = some 242627861579384855 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 8 2 232313985706354047 242627861579384855 242627861579384855 endpoint_16_59_p8 endpoint_16_59_w8
private theorem endpoint_16_59_w10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 10 2 242627861579384855 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_p12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 12 232313985706354047 = some 242627861579384855 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 10 2 232313985706354047 242627861579384855 242627861579384855 endpoint_16_59_p10 endpoint_16_59_w10
private theorem endpoint_16_59_w12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 12 2 242627861579384855 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_p14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 14 232313985706354047 = some 242627861579384855 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 12 2 232313985706354047 242627861579384855 242627861579384855 endpoint_16_59_p12 endpoint_16_59_w12
private theorem endpoint_16_59_w14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 14 1 242627861579384855 = some 242627861579384855 := by decide +kernel
private theorem endpoint_16_59_p15 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 15 232313985706354047 = some 242627861579384855 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 14 1 232313985706354047 242627861579384855 242627861579384855 endpoint_16_59_p14 endpoint_16_59_w14
def endpoint_16_59 : CertifiedEndpoint :=
  ⟨⟨16, 59, 2167⟩, 242627861579384855, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_59_flag endpoint_16_59_sources 15 232313985706354047 242627861579384855 rfl endpoint_16_59_base endpoint_16_59_p15) (by decide)⟩
private def endpoint_16_60_flag : Flag := ⟨16, 60, 2100⟩
private def endpoint_16_60_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_60_base : receiptBase endpoint_16_60_flag endpoint_16_60_sources = some 228678149679267470 := by decide +kernel
private theorem endpoint_16_60_w0 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 2 228678149679267470 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_w2 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 2 2 243206595033252148 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_p4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 4 228678149679267470 = some 243206595033252148 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 2 2 228678149679267470 243206595033252148 243206595033252148 endpoint_16_60_w0 endpoint_16_60_w2
private theorem endpoint_16_60_w4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 4 2 243206595033252148 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_p6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 6 228678149679267470 = some 243206595033252148 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 4 2 228678149679267470 243206595033252148 243206595033252148 endpoint_16_60_p4 endpoint_16_60_w4
private theorem endpoint_16_60_w6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 6 2 243206595033252148 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_p8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 8 228678149679267470 = some 243206595033252148 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 6 2 228678149679267470 243206595033252148 243206595033252148 endpoint_16_60_p6 endpoint_16_60_w6
private theorem endpoint_16_60_w8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 8 2 243206595033252148 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_p10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 10 228678149679267470 = some 243206595033252148 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 8 2 228678149679267470 243206595033252148 243206595033252148 endpoint_16_60_p8 endpoint_16_60_w8
private theorem endpoint_16_60_w10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 10 2 243206595033252148 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_p12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 12 228678149679267470 = some 243206595033252148 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 10 2 228678149679267470 243206595033252148 243206595033252148 endpoint_16_60_p10 endpoint_16_60_w10
private theorem endpoint_16_60_w12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 12 2 243206595033252148 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_p14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 14 228678149679267470 = some 243206595033252148 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 12 2 228678149679267470 243206595033252148 243206595033252148 endpoint_16_60_p12 endpoint_16_60_w12
private theorem endpoint_16_60_w14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 14 1 243206595033252148 = some 243206595033252148 := by decide +kernel
private theorem endpoint_16_60_p15 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 15 228678149679267470 = some 243206595033252148 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 14 1 228678149679267470 243206595033252148 243206595033252148 endpoint_16_60_p14 endpoint_16_60_w14
def endpoint_16_60 : CertifiedEndpoint :=
  ⟨⟨16, 60, 2100⟩, 243206595033252148, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_60_flag endpoint_16_60_sources 15 228678149679267470 243206595033252148 rfl endpoint_16_60_base endpoint_16_60_p15) (by decide)⟩
private def endpoint_16_61_flag : Flag := ⟨16, 61, 2031⟩
private def endpoint_16_61_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_61_base : receiptBase endpoint_16_61_flag endpoint_16_61_sources = some 224615970567427476 := by decide +kernel
private theorem endpoint_16_61_w0 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 2 224615970567427476 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_w2 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 2 2 243489792911117559 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_p4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 4 224615970567427476 = some 243489792911117559 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 2 2 224615970567427476 243489792911117559 243489792911117559 endpoint_16_61_w0 endpoint_16_61_w2
private theorem endpoint_16_61_w4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 4 2 243489792911117559 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_p6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 6 224615970567427476 = some 243489792911117559 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 4 2 224615970567427476 243489792911117559 243489792911117559 endpoint_16_61_p4 endpoint_16_61_w4
private theorem endpoint_16_61_w6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 6 2 243489792911117559 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_p8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 8 224615970567427476 = some 243489792911117559 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 6 2 224615970567427476 243489792911117559 243489792911117559 endpoint_16_61_p6 endpoint_16_61_w6
private theorem endpoint_16_61_w8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 8 2 243489792911117559 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_p10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 10 224615970567427476 = some 243489792911117559 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 8 2 224615970567427476 243489792911117559 243489792911117559 endpoint_16_61_p8 endpoint_16_61_w8
private theorem endpoint_16_61_w10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 10 2 243489792911117559 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_p12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 12 224615970567427476 = some 243489792911117559 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 10 2 224615970567427476 243489792911117559 243489792911117559 endpoint_16_61_p10 endpoint_16_61_w10
private theorem endpoint_16_61_w12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 12 2 243489792911117559 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_p14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 14 224615970567427476 = some 243489792911117559 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 12 2 224615970567427476 243489792911117559 243489792911117559 endpoint_16_61_p12 endpoint_16_61_w12
private theorem endpoint_16_61_w14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 14 1 243489792911117559 = some 243489792911117559 := by decide +kernel
private theorem endpoint_16_61_p15 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 15 224615970567427476 = some 243489792911117559 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 14 1 224615970567427476 243489792911117559 243489792911117559 endpoint_16_61_p14 endpoint_16_61_w14
def endpoint_16_61 : CertifiedEndpoint :=
  ⟨⟨16, 61, 2031⟩, 243489792911117559, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_61_flag endpoint_16_61_sources 15 224615970567427476 243489792911117559 rfl endpoint_16_61_base endpoint_16_61_p15) (by decide)⟩
private def endpoint_16_62_flag : Flag := ⟨16, 62, 1961⟩
private def endpoint_16_62_sources : Sources := ⟨contact15, contact15, contact12⟩
private theorem endpoint_16_62_base : receiptBase endpoint_16_62_flag endpoint_16_62_sources = some 221317668575664027 := by decide +kernel
private theorem endpoint_16_62_w0 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 2 221317668575664027 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_w2 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 2 2 236699707584813358 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_p4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 4 221317668575664027 = some 236699707584813358 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 2 2 221317668575664027 236699707584813358 236699707584813358 endpoint_16_62_w0 endpoint_16_62_w2
private theorem endpoint_16_62_w4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 4 2 236699707584813358 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_p6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 6 221317668575664027 = some 236699707584813358 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 4 2 221317668575664027 236699707584813358 236699707584813358 endpoint_16_62_p4 endpoint_16_62_w4
private theorem endpoint_16_62_w6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 6 2 236699707584813358 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_p8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 8 221317668575664027 = some 236699707584813358 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 6 2 221317668575664027 236699707584813358 236699707584813358 endpoint_16_62_p6 endpoint_16_62_w6
private theorem endpoint_16_62_w8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 8 2 236699707584813358 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_p10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 10 221317668575664027 = some 236699707584813358 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 8 2 221317668575664027 236699707584813358 236699707584813358 endpoint_16_62_p8 endpoint_16_62_w8
private theorem endpoint_16_62_w10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 10 2 236699707584813358 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_p12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 12 221317668575664027 = some 236699707584813358 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 10 2 221317668575664027 236699707584813358 236699707584813358 endpoint_16_62_p10 endpoint_16_62_w10
private theorem endpoint_16_62_w12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 12 2 236699707584813358 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_p14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 14 221317668575664027 = some 236699707584813358 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 12 2 221317668575664027 236699707584813358 236699707584813358 endpoint_16_62_p12 endpoint_16_62_w12
private theorem endpoint_16_62_w14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 14 1 236699707584813358 = some 236699707584813358 := by decide +kernel
private theorem endpoint_16_62_p15 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 15 221317668575664027 = some 236699707584813358 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 14 1 221317668575664027 236699707584813358 236699707584813358 endpoint_16_62_p14 endpoint_16_62_w14
def endpoint_16_62 : CertifiedEndpoint :=
  ⟨⟨16, 62, 1961⟩, 236699707584813358, .terminal ⟨contact15, contact15, contact12⟩ (finish_receipt_window endpoint_16_62_flag endpoint_16_62_sources 15 221317668575664027 236699707584813358 rfl endpoint_16_62_base endpoint_16_62_p15) (by decide)⟩
private def endpoint_16_63_flag : Flag := ⟨16, 63, 1888⟩
private def endpoint_16_63_sources : Sources := ⟨contact29, contact16, contact13⟩
private theorem endpoint_16_63_base : receiptBase endpoint_16_63_flag endpoint_16_63_sources = some 217037811039487977 := by decide +kernel
private theorem endpoint_16_63_w0 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 2 217037811039487977 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_w2 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 2 2 234740644522843814 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_p4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 4 217037811039487977 = some 234740644522843814 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 2 2 217037811039487977 234740644522843814 234740644522843814 endpoint_16_63_w0 endpoint_16_63_w2
private theorem endpoint_16_63_w4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 4 2 234740644522843814 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_p6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 6 217037811039487977 = some 234740644522843814 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 4 2 217037811039487977 234740644522843814 234740644522843814 endpoint_16_63_p4 endpoint_16_63_w4
private theorem endpoint_16_63_w6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 6 2 234740644522843814 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_p8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 8 217037811039487977 = some 234740644522843814 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 6 2 217037811039487977 234740644522843814 234740644522843814 endpoint_16_63_p6 endpoint_16_63_w6
private theorem endpoint_16_63_w8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 8 2 234740644522843814 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_p10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 10 217037811039487977 = some 234740644522843814 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 8 2 217037811039487977 234740644522843814 234740644522843814 endpoint_16_63_p8 endpoint_16_63_w8
private theorem endpoint_16_63_w10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 10 2 234740644522843814 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_p12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 12 217037811039487977 = some 234740644522843814 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 10 2 217037811039487977 234740644522843814 234740644522843814 endpoint_16_63_p10 endpoint_16_63_w10
private theorem endpoint_16_63_w12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 12 2 234740644522843814 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_p14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 14 217037811039487977 = some 234740644522843814 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 12 2 217037811039487977 234740644522843814 234740644522843814 endpoint_16_63_p12 endpoint_16_63_w12
private theorem endpoint_16_63_w14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 14 1 234740644522843814 = some 234740644522843814 := by decide +kernel
private theorem endpoint_16_63_p15 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 15 217037811039487977 = some 234740644522843814 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 14 1 217037811039487977 234740644522843814 234740644522843814 endpoint_16_63_p14 endpoint_16_63_w14
def endpoint_16_63 : CertifiedEndpoint :=
  ⟨⟨16, 63, 1888⟩, 234740644522843814, .terminal ⟨contact29, contact16, contact13⟩ (finish_receipt_window endpoint_16_63_flag endpoint_16_63_sources 15 217037811039487977 234740644522843814 rfl endpoint_16_63_base endpoint_16_63_p15) (by decide)⟩
private def endpoint_16_64_flag : Flag := ⟨16, 64, 1813⟩
private def endpoint_16_64_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_64_base : receiptBase endpoint_16_64_flag endpoint_16_64_sources = some 213318448224118568 := by decide +kernel
private theorem endpoint_16_64_w0 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 2 213318448224118568 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_w2 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 2 2 218363772641513452 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_p4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 4 213318448224118568 = some 218363772641513452 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 2 2 213318448224118568 218363772641513452 218363772641513452 endpoint_16_64_w0 endpoint_16_64_w2
private theorem endpoint_16_64_w4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 4 2 218363772641513452 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_p6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 6 213318448224118568 = some 218363772641513452 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 4 2 213318448224118568 218363772641513452 218363772641513452 endpoint_16_64_p4 endpoint_16_64_w4
private theorem endpoint_16_64_w6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 6 2 218363772641513452 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_p8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 8 213318448224118568 = some 218363772641513452 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 6 2 213318448224118568 218363772641513452 218363772641513452 endpoint_16_64_p6 endpoint_16_64_w6
private theorem endpoint_16_64_w8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 8 2 218363772641513452 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_p10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 10 213318448224118568 = some 218363772641513452 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 8 2 213318448224118568 218363772641513452 218363772641513452 endpoint_16_64_p8 endpoint_16_64_w8
private theorem endpoint_16_64_w10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 10 2 218363772641513452 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_p12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 12 213318448224118568 = some 218363772641513452 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 10 2 213318448224118568 218363772641513452 218363772641513452 endpoint_16_64_p10 endpoint_16_64_w10
private theorem endpoint_16_64_w12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 12 2 218363772641513452 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_p14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 14 213318448224118568 = some 218363772641513452 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 12 2 213318448224118568 218363772641513452 218363772641513452 endpoint_16_64_p12 endpoint_16_64_w12
private theorem endpoint_16_64_w14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 14 1 218363772641513452 = some 218363772641513452 := by decide +kernel
private theorem endpoint_16_64_p15 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 15 213318448224118568 = some 218363772641513452 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 14 1 213318448224118568 218363772641513452 218363772641513452 endpoint_16_64_p14 endpoint_16_64_w14
def endpoint_16_64 : CertifiedEndpoint :=
  ⟨⟨16, 64, 1813⟩, 218363772641513452, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_64_flag endpoint_16_64_sources 15 213318448224118568 218363772641513452 rfl endpoint_16_64_base endpoint_16_64_p15) (by decide)⟩
private def endpoint_16_65_flag : Flag := ⟨16, 65, 1736⟩
private def endpoint_16_65_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_65_base : receiptBase endpoint_16_65_flag endpoint_16_65_sources = some 207176239553223194 := by decide +kernel
private theorem endpoint_16_65_w0 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 2 207176239553223194 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_w2 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 2 2 216954410226091360 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_p4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 4 207176239553223194 = some 216954410226091360 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 2 2 207176239553223194 216954410226091360 216954410226091360 endpoint_16_65_w0 endpoint_16_65_w2
private theorem endpoint_16_65_w4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 4 2 216954410226091360 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_p6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 6 207176239553223194 = some 216954410226091360 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 4 2 207176239553223194 216954410226091360 216954410226091360 endpoint_16_65_p4 endpoint_16_65_w4
private theorem endpoint_16_65_w6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 6 2 216954410226091360 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_p8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 8 207176239553223194 = some 216954410226091360 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 6 2 207176239553223194 216954410226091360 216954410226091360 endpoint_16_65_p6 endpoint_16_65_w6
private theorem endpoint_16_65_w8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 8 2 216954410226091360 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_p10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 10 207176239553223194 = some 216954410226091360 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 8 2 207176239553223194 216954410226091360 216954410226091360 endpoint_16_65_p8 endpoint_16_65_w8
private theorem endpoint_16_65_w10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 10 2 216954410226091360 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_p12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 12 207176239553223194 = some 216954410226091360 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 10 2 207176239553223194 216954410226091360 216954410226091360 endpoint_16_65_p10 endpoint_16_65_w10
private theorem endpoint_16_65_w12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 12 2 216954410226091360 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_p14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 14 207176239553223194 = some 216954410226091360 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 12 2 207176239553223194 216954410226091360 216954410226091360 endpoint_16_65_p12 endpoint_16_65_w12
private theorem endpoint_16_65_w14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 14 1 216954410226091360 = some 216954410226091360 := by decide +kernel
private theorem endpoint_16_65_p15 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 15 207176239553223194 = some 216954410226091360 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 14 1 207176239553223194 216954410226091360 216954410226091360 endpoint_16_65_p14 endpoint_16_65_w14
def endpoint_16_65 : CertifiedEndpoint :=
  ⟨⟨16, 65, 1736⟩, 216954410226091360, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_65_flag endpoint_16_65_sources 15 207176239553223194 216954410226091360 rfl endpoint_16_65_base endpoint_16_65_p15) (by decide)⟩
private def endpoint_16_66_flag : Flag := ⟨16, 66, 1657⟩
private def endpoint_16_66_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_66_base : receiptBase endpoint_16_66_flag endpoint_16_66_sources = some 200544047845822236 := by decide +kernel
private theorem endpoint_16_66_w0 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 2 200544047845822236 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_w2 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 2 2 215212660489238536 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_p4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 4 200544047845822236 = some 215212660489238536 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 2 2 200544047845822236 215212660489238536 215212660489238536 endpoint_16_66_w0 endpoint_16_66_w2
private theorem endpoint_16_66_w4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 4 2 215212660489238536 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_p6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 6 200544047845822236 = some 215212660489238536 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 4 2 200544047845822236 215212660489238536 215212660489238536 endpoint_16_66_p4 endpoint_16_66_w4
private theorem endpoint_16_66_w6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 6 2 215212660489238536 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_p8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 8 200544047845822236 = some 215212660489238536 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 6 2 200544047845822236 215212660489238536 215212660489238536 endpoint_16_66_p6 endpoint_16_66_w6
private theorem endpoint_16_66_w8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 8 2 215212660489238536 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_p10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 10 200544047845822236 = some 215212660489238536 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 8 2 200544047845822236 215212660489238536 215212660489238536 endpoint_16_66_p8 endpoint_16_66_w8
private theorem endpoint_16_66_w10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 10 2 215212660489238536 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_p12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 12 200544047845822236 = some 215212660489238536 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 10 2 200544047845822236 215212660489238536 215212660489238536 endpoint_16_66_p10 endpoint_16_66_w10
private theorem endpoint_16_66_w12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 12 2 215212660489238536 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_p14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 14 200544047845822236 = some 215212660489238536 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 12 2 200544047845822236 215212660489238536 215212660489238536 endpoint_16_66_p12 endpoint_16_66_w12
private theorem endpoint_16_66_w14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 14 1 215212660489238536 = some 215212660489238536 := by decide +kernel
private theorem endpoint_16_66_p15 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 15 200544047845822236 = some 215212660489238536 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 14 1 200544047845822236 215212660489238536 215212660489238536 endpoint_16_66_p14 endpoint_16_66_w14
def endpoint_16_66 : CertifiedEndpoint :=
  ⟨⟨16, 66, 1657⟩, 215212660489238536, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_66_flag endpoint_16_66_sources 15 200544047845822236 215212660489238536 rfl endpoint_16_66_base endpoint_16_66_p15) (by decide)⟩
private def endpoint_16_67_flag : Flag := ⟨16, 67, 1575⟩
private def endpoint_16_67_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_67_base : receiptBase endpoint_16_67_flag endpoint_16_67_sources = some 194846603861134785 := by decide +kernel
private theorem endpoint_16_67_w0 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 2 194846603861134785 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_w2 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 2 2 197079910496204260 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_p4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 4 194846603861134785 = some 197079910496204260 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 2 2 194846603861134785 197079910496204260 197079910496204260 endpoint_16_67_w0 endpoint_16_67_w2
private theorem endpoint_16_67_w4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 4 2 197079910496204260 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_p6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 6 194846603861134785 = some 197079910496204260 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 4 2 194846603861134785 197079910496204260 197079910496204260 endpoint_16_67_p4 endpoint_16_67_w4
private theorem endpoint_16_67_w6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 6 2 197079910496204260 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_p8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 8 194846603861134785 = some 197079910496204260 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 6 2 194846603861134785 197079910496204260 197079910496204260 endpoint_16_67_p6 endpoint_16_67_w6
private theorem endpoint_16_67_w8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 8 2 197079910496204260 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_p10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 10 194846603861134785 = some 197079910496204260 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 8 2 194846603861134785 197079910496204260 197079910496204260 endpoint_16_67_p8 endpoint_16_67_w8
private theorem endpoint_16_67_w10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 10 2 197079910496204260 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_p12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 12 194846603861134785 = some 197079910496204260 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 10 2 194846603861134785 197079910496204260 197079910496204260 endpoint_16_67_p10 endpoint_16_67_w10
private theorem endpoint_16_67_w12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 12 2 197079910496204260 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_p14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 14 194846603861134785 = some 197079910496204260 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 12 2 194846603861134785 197079910496204260 197079910496204260 endpoint_16_67_p12 endpoint_16_67_w12
private theorem endpoint_16_67_w14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 14 1 197079910496204260 = some 197079910496204260 := by decide +kernel
private theorem endpoint_16_67_p15 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 15 194846603861134785 = some 197079910496204260 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 14 1 194846603861134785 197079910496204260 197079910496204260 endpoint_16_67_p14 endpoint_16_67_w14
def endpoint_16_67 : CertifiedEndpoint :=
  ⟨⟨16, 67, 1575⟩, 197079910496204260, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_67_flag endpoint_16_67_sources 15 194846603861134785 197079910496204260 rfl endpoint_16_67_base endpoint_16_67_p15) (by decide)⟩
private def endpoint_16_68_flag : Flag := ⟨16, 68, 1491⟩
private def endpoint_16_68_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_68_base : receiptBase endpoint_16_68_flag endpoint_16_68_sources = some 187004418602681224 := by decide +kernel
private theorem endpoint_16_68_w0 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 2 187004418602681224 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_w2 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 2 2 194303511498412056 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_p4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 4 187004418602681224 = some 194303511498412056 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 2 2 187004418602681224 194303511498412056 194303511498412056 endpoint_16_68_w0 endpoint_16_68_w2
private theorem endpoint_16_68_w4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 4 2 194303511498412056 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_p6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 6 187004418602681224 = some 194303511498412056 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 4 2 187004418602681224 194303511498412056 194303511498412056 endpoint_16_68_p4 endpoint_16_68_w4
private theorem endpoint_16_68_w6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 6 2 194303511498412056 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_p8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 8 187004418602681224 = some 194303511498412056 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 6 2 187004418602681224 194303511498412056 194303511498412056 endpoint_16_68_p6 endpoint_16_68_w6
private theorem endpoint_16_68_w8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 8 2 194303511498412056 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_p10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 10 187004418602681224 = some 194303511498412056 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 8 2 187004418602681224 194303511498412056 194303511498412056 endpoint_16_68_p8 endpoint_16_68_w8
private theorem endpoint_16_68_w10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 10 2 194303511498412056 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_p12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 12 187004418602681224 = some 194303511498412056 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 10 2 187004418602681224 194303511498412056 194303511498412056 endpoint_16_68_p10 endpoint_16_68_w10
private theorem endpoint_16_68_w12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 12 2 194303511498412056 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_p14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 14 187004418602681224 = some 194303511498412056 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 12 2 187004418602681224 194303511498412056 194303511498412056 endpoint_16_68_p12 endpoint_16_68_w12
private theorem endpoint_16_68_w14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 14 1 194303511498412056 = some 194303511498412056 := by decide +kernel
private theorem endpoint_16_68_p15 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 15 187004418602681224 = some 194303511498412056 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 14 1 187004418602681224 194303511498412056 194303511498412056 endpoint_16_68_p14 endpoint_16_68_w14
def endpoint_16_68 : CertifiedEndpoint :=
  ⟨⟨16, 68, 1491⟩, 194303511498412056, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_68_flag endpoint_16_68_sources 15 187004418602681224 194303511498412056 rfl endpoint_16_68_base endpoint_16_68_p15) (by decide)⟩
private def endpoint_16_69_flag : Flag := ⟨16, 69, 1405⟩
private def endpoint_16_69_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_69_base : receiptBase endpoint_16_69_flag endpoint_16_69_sources = some 178636444411969175 := by decide +kernel
private theorem endpoint_16_69_w0 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 2 178636444411969175 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_w2 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 2 2 191170157348903220 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_p4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 4 178636444411969175 = some 191170157348903220 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 2 2 178636444411969175 191170157348903220 191170157348903220 endpoint_16_69_w0 endpoint_16_69_w2
private theorem endpoint_16_69_w4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 4 2 191170157348903220 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_p6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 6 178636444411969175 = some 191170157348903220 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 4 2 178636444411969175 191170157348903220 191170157348903220 endpoint_16_69_p4 endpoint_16_69_w4
private theorem endpoint_16_69_w6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 6 2 191170157348903220 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_p8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 8 178636444411969175 = some 191170157348903220 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 6 2 178636444411969175 191170157348903220 191170157348903220 endpoint_16_69_p6 endpoint_16_69_w6
private theorem endpoint_16_69_w8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 8 2 191170157348903220 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_p10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 10 178636444411969175 = some 191170157348903220 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 8 2 178636444411969175 191170157348903220 191170157348903220 endpoint_16_69_p8 endpoint_16_69_w8
private theorem endpoint_16_69_w10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 10 2 191170157348903220 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_p12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 12 178636444411969175 = some 191170157348903220 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 10 2 178636444411969175 191170157348903220 191170157348903220 endpoint_16_69_p10 endpoint_16_69_w10
private theorem endpoint_16_69_w12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 12 2 191170157348903220 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_p14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 14 178636444411969175 = some 191170157348903220 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 12 2 178636444411969175 191170157348903220 191170157348903220 endpoint_16_69_p12 endpoint_16_69_w12
private theorem endpoint_16_69_w14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 14 1 191170157348903220 = some 191170157348903220 := by decide +kernel
private theorem endpoint_16_69_p15 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 15 178636444411969175 = some 191170157348903220 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 14 1 178636444411969175 191170157348903220 191170157348903220 endpoint_16_69_p14 endpoint_16_69_w14
def endpoint_16_69 : CertifiedEndpoint :=
  ⟨⟨16, 69, 1405⟩, 191170157348903220, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_69_flag endpoint_16_69_sources 15 178636444411969175 191170157348903220 rfl endpoint_16_69_base endpoint_16_69_p15) (by decide)⟩
private def endpoint_16_70_flag : Flag := ⟨16, 70, 1316⟩
private def endpoint_16_70_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_16_70_base : receiptBase endpoint_16_70_flag endpoint_16_70_sources = some 170012454527372607 := by decide +kernel
private theorem endpoint_16_70_w0 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 2 170012454527372607 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_w2 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 2 2 184668811942485802 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_p4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 4 170012454527372607 = some 184668811942485802 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 2 2 170012454527372607 184668811942485802 184668811942485802 endpoint_16_70_w0 endpoint_16_70_w2
private theorem endpoint_16_70_w4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 4 2 184668811942485802 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_p6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 6 170012454527372607 = some 184668811942485802 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 4 2 170012454527372607 184668811942485802 184668811942485802 endpoint_16_70_p4 endpoint_16_70_w4
private theorem endpoint_16_70_w6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 6 2 184668811942485802 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_p8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 8 170012454527372607 = some 184668811942485802 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 6 2 170012454527372607 184668811942485802 184668811942485802 endpoint_16_70_p6 endpoint_16_70_w6
private theorem endpoint_16_70_w8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 8 2 184668811942485802 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_p10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 10 170012454527372607 = some 184668811942485802 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 8 2 170012454527372607 184668811942485802 184668811942485802 endpoint_16_70_p8 endpoint_16_70_w8
private theorem endpoint_16_70_w10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 10 2 184668811942485802 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_p12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 12 170012454527372607 = some 184668811942485802 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 10 2 170012454527372607 184668811942485802 184668811942485802 endpoint_16_70_p10 endpoint_16_70_w10
private theorem endpoint_16_70_w12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 12 2 184668811942485802 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_p14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 14 170012454527372607 = some 184668811942485802 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 12 2 170012454527372607 184668811942485802 184668811942485802 endpoint_16_70_p12 endpoint_16_70_w12
private theorem endpoint_16_70_w14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 14 1 184668811942485802 = some 184668811942485802 := by decide +kernel
private theorem endpoint_16_70_p15 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 15 170012454527372607 = some 184668811942485802 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 14 1 170012454527372607 184668811942485802 184668811942485802 endpoint_16_70_p14 endpoint_16_70_w14
def endpoint_16_70 : CertifiedEndpoint :=
  ⟨⟨16, 70, 1316⟩, 184668811942485802, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_16_70_flag endpoint_16_70_sources 15 170012454527372607 184668811942485802 rfl endpoint_16_70_base endpoint_16_70_p15) (by decide)⟩
private def endpoint_16_71_flag : Flag := ⟨16, 71, 1223⟩
private def endpoint_16_71_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_16_71_base : receiptBase endpoint_16_71_flag endpoint_16_71_sources = some 161266993615272031 := by decide +kernel
private theorem endpoint_16_71_w0 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 2 161266993615272031 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_w2 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 2 2 172845645967002100 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_p4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 4 161266993615272031 = some 172845645967002100 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 2 2 161266993615272031 172845645967002100 172845645967002100 endpoint_16_71_w0 endpoint_16_71_w2
private theorem endpoint_16_71_w4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 4 2 172845645967002100 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_p6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 6 161266993615272031 = some 172845645967002100 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 4 2 161266993615272031 172845645967002100 172845645967002100 endpoint_16_71_p4 endpoint_16_71_w4
private theorem endpoint_16_71_w6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 6 2 172845645967002100 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_p8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 8 161266993615272031 = some 172845645967002100 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 6 2 161266993615272031 172845645967002100 172845645967002100 endpoint_16_71_p6 endpoint_16_71_w6
private theorem endpoint_16_71_w8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 8 2 172845645967002100 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_p10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 10 161266993615272031 = some 172845645967002100 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 8 2 161266993615272031 172845645967002100 172845645967002100 endpoint_16_71_p8 endpoint_16_71_w8
private theorem endpoint_16_71_w10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 10 2 172845645967002100 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_p12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 12 161266993615272031 = some 172845645967002100 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 10 2 161266993615272031 172845645967002100 172845645967002100 endpoint_16_71_p10 endpoint_16_71_w10
private theorem endpoint_16_71_w12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 12 2 172845645967002100 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_p14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 14 161266993615272031 = some 172845645967002100 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 12 2 161266993615272031 172845645967002100 172845645967002100 endpoint_16_71_p12 endpoint_16_71_w12
private theorem endpoint_16_71_w14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 14 1 172845645967002100 = some 172845645967002100 := by decide +kernel
private theorem endpoint_16_71_p15 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 15 161266993615272031 = some 172845645967002100 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 14 1 161266993615272031 172845645967002100 172845645967002100 endpoint_16_71_p14 endpoint_16_71_w14
def endpoint_16_71 : CertifiedEndpoint :=
  ⟨⟨16, 71, 1223⟩, 172845645967002100, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_16_71_flag endpoint_16_71_sources 15 161266993615272031 172845645967002100 rfl endpoint_16_71_base endpoint_16_71_p15) (by decide)⟩
private def endpoint_16_72_flag : Flag := ⟨16, 72, 1128⟩
private def endpoint_16_72_sources : Sources := ⟨contact31, contact21, contact22⟩
private theorem endpoint_16_72_base : receiptBase endpoint_16_72_flag endpoint_16_72_sources = some 151434130638864336 := by decide +kernel
private theorem endpoint_16_72_w0 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 2 151434130638864336 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_w2 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 2 2 166597898643542280 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_p4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 4 151434130638864336 = some 166597898643542280 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 2 2 151434130638864336 166597898643542280 166597898643542280 endpoint_16_72_w0 endpoint_16_72_w2
private theorem endpoint_16_72_w4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 4 2 166597898643542280 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_p6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 6 151434130638864336 = some 166597898643542280 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 4 2 151434130638864336 166597898643542280 166597898643542280 endpoint_16_72_p4 endpoint_16_72_w4
private theorem endpoint_16_72_w6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 6 2 166597898643542280 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_p8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 8 151434130638864336 = some 166597898643542280 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 6 2 151434130638864336 166597898643542280 166597898643542280 endpoint_16_72_p6 endpoint_16_72_w6
private theorem endpoint_16_72_w8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 8 2 166597898643542280 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_p10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 10 151434130638864336 = some 166597898643542280 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 8 2 151434130638864336 166597898643542280 166597898643542280 endpoint_16_72_p8 endpoint_16_72_w8
private theorem endpoint_16_72_w10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 10 2 166597898643542280 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_p12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 12 151434130638864336 = some 166597898643542280 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 10 2 151434130638864336 166597898643542280 166597898643542280 endpoint_16_72_p10 endpoint_16_72_w10
private theorem endpoint_16_72_w12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 12 2 166597898643542280 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_p14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 14 151434130638864336 = some 166597898643542280 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 12 2 151434130638864336 166597898643542280 166597898643542280 endpoint_16_72_p12 endpoint_16_72_w12
private theorem endpoint_16_72_w14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 14 1 166597898643542280 = some 166597898643542280 := by decide +kernel
private theorem endpoint_16_72_p15 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 15 151434130638864336 = some 166597898643542280 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 14 1 151434130638864336 166597898643542280 166597898643542280 endpoint_16_72_p14 endpoint_16_72_w14
def endpoint_16_72 : CertifiedEndpoint :=
  ⟨⟨16, 72, 1128⟩, 166597898643542280, .terminal ⟨contact31, contact21, contact22⟩ (finish_receipt_window endpoint_16_72_flag endpoint_16_72_sources 15 151434130638864336 166597898643542280 rfl endpoint_16_72_base endpoint_16_72_p15) (by decide)⟩
def endpoint_16_73 : CertifiedEndpoint :=
  ⟨⟨16, 73, 1030⟩, 255467501713355155, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_74 : CertifiedEndpoint :=
  ⟨⟨16, 74, 929⟩, 232813601648218923, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_75 : CertifiedEndpoint :=
  ⟨⟨16, 75, 825⟩, 208548464554646794, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_76 : CertifiedEndpoint :=
  ⟨⟨16, 76, 718⟩, 182636063351601850, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_77 : CertifiedEndpoint :=
  ⟨⟨16, 77, 607⟩, 154766156206504572, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_78 : CertifiedEndpoint :=
  ⟨⟨16, 78, 494⟩, 125447142532399142, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_79 : CertifiedEndpoint :=
  ⟨⟨16, 79, 377⟩, 94090562736159338, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_80 : CertifiedEndpoint :=
  ⟨⟨16, 80, 258⟩, 61220828266845750, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_81 : CertifiedEndpoint :=
  ⟨⟨16, 81, 135⟩, 26233467495315748, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_17 : CertifiedEndpoint :=
  ⟨⟨17, 17, 3753⟩, 148932224517228438, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_18 : CertifiedEndpoint :=
  ⟨⟨17, 18, 3722⟩, 152882867536661596, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_19 : CertifiedEndpoint :=
  ⟨⟨17, 19, 3691⟩, 156746698503266048, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_20 : CertifiedEndpoint :=
  ⟨⟨17, 20, 3660⟩, 170936736495031248, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_21 : CertifiedEndpoint :=
  ⟨⟨17, 21, 3628⟩, 184807212349215211, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_22 : CertifiedEndpoint :=
  ⟨⟨17, 22, 3595⟩, 198345343925817875, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_23 : CertifiedEndpoint :=
  ⟨⟨17, 23, 3562⟩, 211598007709085821, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_24 : CertifiedEndpoint :=
  ⟨⟨17, 24, 3528⟩, 224501284361439052, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_25 : CertifiedEndpoint :=
  ⟨⟨17, 25, 3494⟩, 237110571793790857, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_26 : CertifiedEndpoint :=
  ⟨⟨17, 26, 3459⟩, 249353429241894531, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_27 : CertifiedEndpoint :=
  ⟨⟨17, 27, 3423⟩, 261217074565750012, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_17_28_flag : Flag := ⟨17, 28, 3387⟩
private def endpoint_17_28_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_28_base : receiptBase endpoint_17_28_flag endpoint_17_28_sources = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_w0 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_w2 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 2 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_p4 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 4 192177227299111223 = some 192177227299111223 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 2 2 192177227299111223 192177227299111223 192177227299111223 endpoint_17_28_w0 endpoint_17_28_w2
private theorem endpoint_17_28_w4 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 4 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_p6 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 6 192177227299111223 = some 192177227299111223 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 4 2 192177227299111223 192177227299111223 192177227299111223 endpoint_17_28_p4 endpoint_17_28_w4
private theorem endpoint_17_28_w6 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 6 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_p8 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 8 192177227299111223 = some 192177227299111223 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 6 2 192177227299111223 192177227299111223 192177227299111223 endpoint_17_28_p6 endpoint_17_28_w6
private theorem endpoint_17_28_w8 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 8 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_p10 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 10 192177227299111223 = some 192177227299111223 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 8 2 192177227299111223 192177227299111223 192177227299111223 endpoint_17_28_p8 endpoint_17_28_w8
private theorem endpoint_17_28_w10 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 10 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_p12 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 12 192177227299111223 = some 192177227299111223 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 10 2 192177227299111223 192177227299111223 192177227299111223 endpoint_17_28_p10 endpoint_17_28_w10
private theorem endpoint_17_28_w12 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 12 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_p14 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 14 192177227299111223 = some 192177227299111223 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 12 2 192177227299111223 192177227299111223 192177227299111223 endpoint_17_28_p12 endpoint_17_28_w12
private theorem endpoint_17_28_w14 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 14 2 192177227299111223 = some 192177227299111223 := by decide +kernel
private theorem endpoint_17_28_p16 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 16 192177227299111223 = some 192177227299111223 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 14 2 192177227299111223 192177227299111223 192177227299111223 endpoint_17_28_p14 endpoint_17_28_w14
def endpoint_17_28 : CertifiedEndpoint :=
  ⟨⟨17, 28, 3387⟩, 192177227299111223, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_28_flag endpoint_17_28_sources 16 192177227299111223 192177227299111223 rfl endpoint_17_28_base endpoint_17_28_p16) (by decide)⟩
private def endpoint_17_29_flag : Flag := ⟨17, 29, 3350⟩
private def endpoint_17_29_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_29_base : receiptBase endpoint_17_29_flag endpoint_17_29_sources = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_w0 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_w2 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 2 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_p4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 4 195599643035466553 = some 195599643035466553 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 2 2 195599643035466553 195599643035466553 195599643035466553 endpoint_17_29_w0 endpoint_17_29_w2
private theorem endpoint_17_29_w4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 4 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_p6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 6 195599643035466553 = some 195599643035466553 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 4 2 195599643035466553 195599643035466553 195599643035466553 endpoint_17_29_p4 endpoint_17_29_w4
private theorem endpoint_17_29_w6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 6 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_p8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 8 195599643035466553 = some 195599643035466553 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 6 2 195599643035466553 195599643035466553 195599643035466553 endpoint_17_29_p6 endpoint_17_29_w6
private theorem endpoint_17_29_w8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 8 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_p10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 10 195599643035466553 = some 195599643035466553 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 8 2 195599643035466553 195599643035466553 195599643035466553 endpoint_17_29_p8 endpoint_17_29_w8
private theorem endpoint_17_29_w10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 10 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_p12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 12 195599643035466553 = some 195599643035466553 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 10 2 195599643035466553 195599643035466553 195599643035466553 endpoint_17_29_p10 endpoint_17_29_w10
private theorem endpoint_17_29_w12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 12 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_p14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 14 195599643035466553 = some 195599643035466553 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 12 2 195599643035466553 195599643035466553 195599643035466553 endpoint_17_29_p12 endpoint_17_29_w12
private theorem endpoint_17_29_w14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 14 2 195599643035466553 = some 195599643035466553 := by decide +kernel
private theorem endpoint_17_29_p16 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 16 195599643035466553 = some 195599643035466553 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 14 2 195599643035466553 195599643035466553 195599643035466553 endpoint_17_29_p14 endpoint_17_29_w14
def endpoint_17_29 : CertifiedEndpoint :=
  ⟨⟨17, 29, 3350⟩, 195599643035466553, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_29_flag endpoint_17_29_sources 16 195599643035466553 195599643035466553 rfl endpoint_17_29_base endpoint_17_29_p16) (by decide)⟩
private def endpoint_17_30_flag : Flag := ⟨17, 30, 3313⟩
private def endpoint_17_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_30_base : receiptBase endpoint_17_30_flag endpoint_17_30_sources = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_w0 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_w2 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 2 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_p4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 4 198901117803755214 = some 198901117803755214 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 2 2 198901117803755214 198901117803755214 198901117803755214 endpoint_17_30_w0 endpoint_17_30_w2
private theorem endpoint_17_30_w4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 4 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_p6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 6 198901117803755214 = some 198901117803755214 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 4 2 198901117803755214 198901117803755214 198901117803755214 endpoint_17_30_p4 endpoint_17_30_w4
private theorem endpoint_17_30_w6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 6 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_p8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 8 198901117803755214 = some 198901117803755214 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 6 2 198901117803755214 198901117803755214 198901117803755214 endpoint_17_30_p6 endpoint_17_30_w6
private theorem endpoint_17_30_w8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 8 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_p10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 10 198901117803755214 = some 198901117803755214 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 8 2 198901117803755214 198901117803755214 198901117803755214 endpoint_17_30_p8 endpoint_17_30_w8
private theorem endpoint_17_30_w10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 10 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_p12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 12 198901117803755214 = some 198901117803755214 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 10 2 198901117803755214 198901117803755214 198901117803755214 endpoint_17_30_p10 endpoint_17_30_w10
private theorem endpoint_17_30_w12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 12 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_p14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 14 198901117803755214 = some 198901117803755214 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 12 2 198901117803755214 198901117803755214 198901117803755214 endpoint_17_30_p12 endpoint_17_30_w12
private theorem endpoint_17_30_w14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 14 2 198901117803755214 = some 198901117803755214 := by decide +kernel
private theorem endpoint_17_30_p16 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 16 198901117803755214 = some 198901117803755214 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 14 2 198901117803755214 198901117803755214 198901117803755214 endpoint_17_30_p14 endpoint_17_30_w14
def endpoint_17_30 : CertifiedEndpoint :=
  ⟨⟨17, 30, 3313⟩, 198901117803755214, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_30_flag endpoint_17_30_sources 16 198901117803755214 198901117803755214 rfl endpoint_17_30_base endpoint_17_30_p16) (by decide)⟩
private def endpoint_17_31_flag : Flag := ⟨17, 31, 3275⟩
private def endpoint_17_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_31_base : receiptBase endpoint_17_31_flag endpoint_17_31_sources = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_w0 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_w2 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 2 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_p4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 4 202020644834529633 = some 202020644834529633 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 2 2 202020644834529633 202020644834529633 202020644834529633 endpoint_17_31_w0 endpoint_17_31_w2
private theorem endpoint_17_31_w4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 4 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_p6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 6 202020644834529633 = some 202020644834529633 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 4 2 202020644834529633 202020644834529633 202020644834529633 endpoint_17_31_p4 endpoint_17_31_w4
private theorem endpoint_17_31_w6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 6 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_p8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 8 202020644834529633 = some 202020644834529633 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 6 2 202020644834529633 202020644834529633 202020644834529633 endpoint_17_31_p6 endpoint_17_31_w6
private theorem endpoint_17_31_w8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 8 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_p10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 10 202020644834529633 = some 202020644834529633 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 8 2 202020644834529633 202020644834529633 202020644834529633 endpoint_17_31_p8 endpoint_17_31_w8
private theorem endpoint_17_31_w10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 10 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_p12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 12 202020644834529633 = some 202020644834529633 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 10 2 202020644834529633 202020644834529633 202020644834529633 endpoint_17_31_p10 endpoint_17_31_w10
private theorem endpoint_17_31_w12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 12 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_p14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 14 202020644834529633 = some 202020644834529633 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 12 2 202020644834529633 202020644834529633 202020644834529633 endpoint_17_31_p12 endpoint_17_31_w12
private theorem endpoint_17_31_w14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 14 2 202020644834529633 = some 202020644834529633 := by decide +kernel
private theorem endpoint_17_31_p16 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 16 202020644834529633 = some 202020644834529633 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 14 2 202020644834529633 202020644834529633 202020644834529633 endpoint_17_31_p14 endpoint_17_31_w14
def endpoint_17_31 : CertifiedEndpoint :=
  ⟨⟨17, 31, 3275⟩, 202020644834529633, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_31_flag endpoint_17_31_sources 16 202020644834529633 202020644834529633 rfl endpoint_17_31_base endpoint_17_31_p16) (by decide)⟩
private def endpoint_17_32_flag : Flag := ⟨17, 32, 3236⟩
private def endpoint_17_32_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_32_base : receiptBase endpoint_17_32_flag endpoint_17_32_sources = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_w0 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_w2 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 2 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_p4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 4 204953386777041863 = some 204953386777041863 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 2 2 204953386777041863 204953386777041863 204953386777041863 endpoint_17_32_w0 endpoint_17_32_w2
private theorem endpoint_17_32_w4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 4 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_p6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 6 204953386777041863 = some 204953386777041863 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 4 2 204953386777041863 204953386777041863 204953386777041863 endpoint_17_32_p4 endpoint_17_32_w4
private theorem endpoint_17_32_w6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 6 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_p8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 8 204953386777041863 = some 204953386777041863 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 6 2 204953386777041863 204953386777041863 204953386777041863 endpoint_17_32_p6 endpoint_17_32_w6
private theorem endpoint_17_32_w8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 8 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_p10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 10 204953386777041863 = some 204953386777041863 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 8 2 204953386777041863 204953386777041863 204953386777041863 endpoint_17_32_p8 endpoint_17_32_w8
private theorem endpoint_17_32_w10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 10 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_p12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 12 204953386777041863 = some 204953386777041863 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 10 2 204953386777041863 204953386777041863 204953386777041863 endpoint_17_32_p10 endpoint_17_32_w10
private theorem endpoint_17_32_w12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 12 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_p14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 14 204953386777041863 = some 204953386777041863 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 12 2 204953386777041863 204953386777041863 204953386777041863 endpoint_17_32_p12 endpoint_17_32_w12
private theorem endpoint_17_32_w14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 14 2 204953386777041863 = some 204953386777041863 := by decide +kernel
private theorem endpoint_17_32_p16 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 16 204953386777041863 = some 204953386777041863 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 14 2 204953386777041863 204953386777041863 204953386777041863 endpoint_17_32_p14 endpoint_17_32_w14
def endpoint_17_32 : CertifiedEndpoint :=
  ⟨⟨17, 32, 3236⟩, 204953386777041863, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_32_flag endpoint_17_32_sources 16 204953386777041863 204953386777041863 rfl endpoint_17_32_base endpoint_17_32_p16) (by decide)⟩
private def endpoint_17_33_flag : Flag := ⟨17, 33, 3196⟩
private def endpoint_17_33_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_33_base : receiptBase endpoint_17_33_flag endpoint_17_33_sources = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_w0 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_w2 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 2 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_p4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 4 207694506280543959 = some 207694506280543959 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 2 2 207694506280543959 207694506280543959 207694506280543959 endpoint_17_33_w0 endpoint_17_33_w2
private theorem endpoint_17_33_w4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 4 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_p6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 6 207694506280543959 = some 207694506280543959 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 4 2 207694506280543959 207694506280543959 207694506280543959 endpoint_17_33_p4 endpoint_17_33_w4
private theorem endpoint_17_33_w6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 6 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_p8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 8 207694506280543959 = some 207694506280543959 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 6 2 207694506280543959 207694506280543959 207694506280543959 endpoint_17_33_p6 endpoint_17_33_w6
private theorem endpoint_17_33_w8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 8 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_p10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 10 207694506280543959 = some 207694506280543959 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 8 2 207694506280543959 207694506280543959 207694506280543959 endpoint_17_33_p8 endpoint_17_33_w8
private theorem endpoint_17_33_w10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 10 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_p12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 12 207694506280543959 = some 207694506280543959 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 10 2 207694506280543959 207694506280543959 207694506280543959 endpoint_17_33_p10 endpoint_17_33_w10
private theorem endpoint_17_33_w12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 12 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_p14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 14 207694506280543959 = some 207694506280543959 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 12 2 207694506280543959 207694506280543959 207694506280543959 endpoint_17_33_p12 endpoint_17_33_w12
private theorem endpoint_17_33_w14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 14 2 207694506280543959 = some 207694506280543959 := by decide +kernel
private theorem endpoint_17_33_p16 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 16 207694506280543959 = some 207694506280543959 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 14 2 207694506280543959 207694506280543959 207694506280543959 endpoint_17_33_p14 endpoint_17_33_w14
def endpoint_17_33 : CertifiedEndpoint :=
  ⟨⟨17, 33, 3196⟩, 207694506280543959, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_33_flag endpoint_17_33_sources 16 207694506280543959 207694506280543959 rfl endpoint_17_33_base endpoint_17_33_p16) (by decide)⟩
private def endpoint_17_34_flag : Flag := ⟨17, 34, 3156⟩
private def endpoint_17_34_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_17_34_base : receiptBase endpoint_17_34_flag endpoint_17_34_sources = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_w0 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_w2 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 2 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_p4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 4 209833821383492525 = some 209833821383492525 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 2 2 209833821383492525 209833821383492525 209833821383492525 endpoint_17_34_w0 endpoint_17_34_w2
private theorem endpoint_17_34_w4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 4 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_p6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 6 209833821383492525 = some 209833821383492525 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 4 2 209833821383492525 209833821383492525 209833821383492525 endpoint_17_34_p4 endpoint_17_34_w4
private theorem endpoint_17_34_w6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 6 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_p8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 8 209833821383492525 = some 209833821383492525 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 6 2 209833821383492525 209833821383492525 209833821383492525 endpoint_17_34_p6 endpoint_17_34_w6
private theorem endpoint_17_34_w8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 8 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_p10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 10 209833821383492525 = some 209833821383492525 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 8 2 209833821383492525 209833821383492525 209833821383492525 endpoint_17_34_p8 endpoint_17_34_w8
private theorem endpoint_17_34_w10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 10 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_p12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 12 209833821383492525 = some 209833821383492525 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 10 2 209833821383492525 209833821383492525 209833821383492525 endpoint_17_34_p10 endpoint_17_34_w10
private theorem endpoint_17_34_w12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 12 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_p14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 14 209833821383492525 = some 209833821383492525 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 12 2 209833821383492525 209833821383492525 209833821383492525 endpoint_17_34_p12 endpoint_17_34_w12
private theorem endpoint_17_34_w14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 14 2 209833821383492525 = some 209833821383492525 := by decide +kernel
private theorem endpoint_17_34_p16 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 16 209833821383492525 = some 209833821383492525 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 14 2 209833821383492525 209833821383492525 209833821383492525 endpoint_17_34_p14 endpoint_17_34_w14
def endpoint_17_34 : CertifiedEndpoint :=
  ⟨⟨17, 34, 3156⟩, 209833821383492525, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_17_34_flag endpoint_17_34_sources 16 209833821383492525 209833821383492525 rfl endpoint_17_34_base endpoint_17_34_p16) (by decide)⟩
private def endpoint_17_35_flag : Flag := ⟨17, 35, 3115⟩
private def endpoint_17_35_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_35_base : receiptBase endpoint_17_35_flag endpoint_17_35_sources = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_w0 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_w2 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 2 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_p4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 4 212717441708415637 = some 212717441708415637 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 2 2 212717441708415637 212717441708415637 212717441708415637 endpoint_17_35_w0 endpoint_17_35_w2
private theorem endpoint_17_35_w4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 4 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_p6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 6 212717441708415637 = some 212717441708415637 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 4 2 212717441708415637 212717441708415637 212717441708415637 endpoint_17_35_p4 endpoint_17_35_w4
private theorem endpoint_17_35_w6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 6 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_p8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 8 212717441708415637 = some 212717441708415637 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 6 2 212717441708415637 212717441708415637 212717441708415637 endpoint_17_35_p6 endpoint_17_35_w6
private theorem endpoint_17_35_w8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 8 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_p10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 10 212717441708415637 = some 212717441708415637 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 8 2 212717441708415637 212717441708415637 212717441708415637 endpoint_17_35_p8 endpoint_17_35_w8
private theorem endpoint_17_35_w10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 10 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_p12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 12 212717441708415637 = some 212717441708415637 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 10 2 212717441708415637 212717441708415637 212717441708415637 endpoint_17_35_p10 endpoint_17_35_w10
private theorem endpoint_17_35_w12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 12 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_p14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 14 212717441708415637 = some 212717441708415637 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 12 2 212717441708415637 212717441708415637 212717441708415637 endpoint_17_35_p12 endpoint_17_35_w12
private theorem endpoint_17_35_w14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 14 2 212717441708415637 = some 212717441708415637 := by decide +kernel
private theorem endpoint_17_35_p16 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 16 212717441708415637 = some 212717441708415637 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 14 2 212717441708415637 212717441708415637 212717441708415637 endpoint_17_35_p14 endpoint_17_35_w14
def endpoint_17_35 : CertifiedEndpoint :=
  ⟨⟨17, 35, 3115⟩, 212717441708415637, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_35_flag endpoint_17_35_sources 16 212717441708415637 212717441708415637 rfl endpoint_17_35_base endpoint_17_35_p16) (by decide)⟩
private def endpoint_17_36_flag : Flag := ⟨17, 36, 3073⟩
private def endpoint_17_36_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_36_base : receiptBase endpoint_17_36_flag endpoint_17_36_sources = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_w0 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_w2 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 2 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_p4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 4 214926963711592438 = some 214926963711592438 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 2 2 214926963711592438 214926963711592438 214926963711592438 endpoint_17_36_w0 endpoint_17_36_w2
private theorem endpoint_17_36_w4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 4 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_p6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 6 214926963711592438 = some 214926963711592438 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 4 2 214926963711592438 214926963711592438 214926963711592438 endpoint_17_36_p4 endpoint_17_36_w4
private theorem endpoint_17_36_w6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 6 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_p8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 8 214926963711592438 = some 214926963711592438 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 6 2 214926963711592438 214926963711592438 214926963711592438 endpoint_17_36_p6 endpoint_17_36_w6
private theorem endpoint_17_36_w8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 8 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_p10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 10 214926963711592438 = some 214926963711592438 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 8 2 214926963711592438 214926963711592438 214926963711592438 endpoint_17_36_p8 endpoint_17_36_w8
private theorem endpoint_17_36_w10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 10 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_p12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 12 214926963711592438 = some 214926963711592438 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 10 2 214926963711592438 214926963711592438 214926963711592438 endpoint_17_36_p10 endpoint_17_36_w10
private theorem endpoint_17_36_w12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 12 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_p14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 14 214926963711592438 = some 214926963711592438 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 12 2 214926963711592438 214926963711592438 214926963711592438 endpoint_17_36_p12 endpoint_17_36_w12
private theorem endpoint_17_36_w14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 14 2 214926963711592438 = some 214926963711592438 := by decide +kernel
private theorem endpoint_17_36_p16 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 16 214926963711592438 = some 214926963711592438 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 14 2 214926963711592438 214926963711592438 214926963711592438 endpoint_17_36_p14 endpoint_17_36_w14
def endpoint_17_36 : CertifiedEndpoint :=
  ⟨⟨17, 36, 3073⟩, 214926963711592438, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_36_flag endpoint_17_36_sources 16 214926963711592438 214926963711592438 rfl endpoint_17_36_base endpoint_17_36_p16) (by decide)⟩
private def endpoint_17_37_flag : Flag := ⟨17, 37, 3031⟩
private def endpoint_17_37_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_37_base : receiptBase endpoint_17_37_flag endpoint_17_37_sources = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_w0 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_w2 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 2 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_p4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 4 216999420244209419 = some 216999420244209419 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 2 2 216999420244209419 216999420244209419 216999420244209419 endpoint_17_37_w0 endpoint_17_37_w2
private theorem endpoint_17_37_w4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 4 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_p6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 6 216999420244209419 = some 216999420244209419 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 4 2 216999420244209419 216999420244209419 216999420244209419 endpoint_17_37_p4 endpoint_17_37_w4
private theorem endpoint_17_37_w6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 6 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_p8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 8 216999420244209419 = some 216999420244209419 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 6 2 216999420244209419 216999420244209419 216999420244209419 endpoint_17_37_p6 endpoint_17_37_w6
private theorem endpoint_17_37_w8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 8 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_p10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 10 216999420244209419 = some 216999420244209419 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 8 2 216999420244209419 216999420244209419 216999420244209419 endpoint_17_37_p8 endpoint_17_37_w8
private theorem endpoint_17_37_w10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 10 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_p12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 12 216999420244209419 = some 216999420244209419 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 10 2 216999420244209419 216999420244209419 216999420244209419 endpoint_17_37_p10 endpoint_17_37_w10
private theorem endpoint_17_37_w12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 12 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_p14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 14 216999420244209419 = some 216999420244209419 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 12 2 216999420244209419 216999420244209419 216999420244209419 endpoint_17_37_p12 endpoint_17_37_w12
private theorem endpoint_17_37_w14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 14 2 216999420244209419 = some 216999420244209419 := by decide +kernel
private theorem endpoint_17_37_p16 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 16 216999420244209419 = some 216999420244209419 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 14 2 216999420244209419 216999420244209419 216999420244209419 endpoint_17_37_p14 endpoint_17_37_w14
def endpoint_17_37 : CertifiedEndpoint :=
  ⟨⟨17, 37, 3031⟩, 216999420244209419, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_37_flag endpoint_17_37_sources 16 216999420244209419 216999420244209419 rfl endpoint_17_37_base endpoint_17_37_p16) (by decide)⟩
private def endpoint_17_38_flag : Flag := ⟨17, 38, 2987⟩
private def endpoint_17_38_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_38_base : receiptBase endpoint_17_38_flag endpoint_17_38_sources = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_w0 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_w2 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 2 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_p4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 4 218790223463881017 = some 218790223463881017 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 2 2 218790223463881017 218790223463881017 218790223463881017 endpoint_17_38_w0 endpoint_17_38_w2
private theorem endpoint_17_38_w4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 4 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_p6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 6 218790223463881017 = some 218790223463881017 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 4 2 218790223463881017 218790223463881017 218790223463881017 endpoint_17_38_p4 endpoint_17_38_w4
private theorem endpoint_17_38_w6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 6 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_p8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 8 218790223463881017 = some 218790223463881017 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 6 2 218790223463881017 218790223463881017 218790223463881017 endpoint_17_38_p6 endpoint_17_38_w6
private theorem endpoint_17_38_w8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 8 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_p10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 10 218790223463881017 = some 218790223463881017 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 8 2 218790223463881017 218790223463881017 218790223463881017 endpoint_17_38_p8 endpoint_17_38_w8
private theorem endpoint_17_38_w10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 10 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_p12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 12 218790223463881017 = some 218790223463881017 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 10 2 218790223463881017 218790223463881017 218790223463881017 endpoint_17_38_p10 endpoint_17_38_w10
private theorem endpoint_17_38_w12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 12 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_p14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 14 218790223463881017 = some 218790223463881017 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 12 2 218790223463881017 218790223463881017 218790223463881017 endpoint_17_38_p12 endpoint_17_38_w12
private theorem endpoint_17_38_w14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 14 2 218790223463881017 = some 218790223463881017 := by decide +kernel
private theorem endpoint_17_38_p16 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 16 218790223463881017 = some 218790223463881017 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 14 2 218790223463881017 218790223463881017 218790223463881017 endpoint_17_38_p14 endpoint_17_38_w14
def endpoint_17_38 : CertifiedEndpoint :=
  ⟨⟨17, 38, 2987⟩, 218790223463881017, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_38_flag endpoint_17_38_sources 16 218790223463881017 218790223463881017 rfl endpoint_17_38_base endpoint_17_38_p16) (by decide)⟩
private def endpoint_17_39_flag : Flag := ⟨17, 39, 2943⟩
private def endpoint_17_39_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_39_base : receiptBase endpoint_17_39_flag endpoint_17_39_sources = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_w0 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_w2 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 2 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_p4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 4 220437511411995534 = some 220437511411995534 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 2 2 220437511411995534 220437511411995534 220437511411995534 endpoint_17_39_w0 endpoint_17_39_w2
private theorem endpoint_17_39_w4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 4 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_p6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 6 220437511411995534 = some 220437511411995534 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 4 2 220437511411995534 220437511411995534 220437511411995534 endpoint_17_39_p4 endpoint_17_39_w4
private theorem endpoint_17_39_w6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 6 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_p8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 8 220437511411995534 = some 220437511411995534 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 6 2 220437511411995534 220437511411995534 220437511411995534 endpoint_17_39_p6 endpoint_17_39_w6
private theorem endpoint_17_39_w8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 8 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_p10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 10 220437511411995534 = some 220437511411995534 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 8 2 220437511411995534 220437511411995534 220437511411995534 endpoint_17_39_p8 endpoint_17_39_w8
private theorem endpoint_17_39_w10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 10 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_p12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 12 220437511411995534 = some 220437511411995534 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 10 2 220437511411995534 220437511411995534 220437511411995534 endpoint_17_39_p10 endpoint_17_39_w10
private theorem endpoint_17_39_w12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 12 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_p14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 14 220437511411995534 = some 220437511411995534 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 12 2 220437511411995534 220437511411995534 220437511411995534 endpoint_17_39_p12 endpoint_17_39_w12
private theorem endpoint_17_39_w14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 14 2 220437511411995534 = some 220437511411995534 := by decide +kernel
private theorem endpoint_17_39_p16 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 16 220437511411995534 = some 220437511411995534 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 14 2 220437511411995534 220437511411995534 220437511411995534 endpoint_17_39_p14 endpoint_17_39_w14
def endpoint_17_39 : CertifiedEndpoint :=
  ⟨⟨17, 39, 2943⟩, 220437511411995534, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_39_flag endpoint_17_39_sources 16 220437511411995534 220437511411995534 rfl endpoint_17_39_base endpoint_17_39_p16) (by decide)⟩
private def endpoint_17_40_flag : Flag := ⟨17, 40, 2898⟩
private def endpoint_17_40_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_40_base : receiptBase endpoint_17_40_flag endpoint_17_40_sources = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_w0 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_w2 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 2 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_p4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 4 221865765266861558 = some 221865765266861558 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 2 2 221865765266861558 221865765266861558 221865765266861558 endpoint_17_40_w0 endpoint_17_40_w2
private theorem endpoint_17_40_w4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 4 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_p6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 6 221865765266861558 = some 221865765266861558 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 4 2 221865765266861558 221865765266861558 221865765266861558 endpoint_17_40_p4 endpoint_17_40_w4
private theorem endpoint_17_40_w6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 6 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_p8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 8 221865765266861558 = some 221865765266861558 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 6 2 221865765266861558 221865765266861558 221865765266861558 endpoint_17_40_p6 endpoint_17_40_w6
private theorem endpoint_17_40_w8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 8 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_p10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 10 221865765266861558 = some 221865765266861558 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 8 2 221865765266861558 221865765266861558 221865765266861558 endpoint_17_40_p8 endpoint_17_40_w8
private theorem endpoint_17_40_w10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 10 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_p12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 12 221865765266861558 = some 221865765266861558 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 10 2 221865765266861558 221865765266861558 221865765266861558 endpoint_17_40_p10 endpoint_17_40_w10
private theorem endpoint_17_40_w12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 12 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_p14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 14 221865765266861558 = some 221865765266861558 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 12 2 221865765266861558 221865765266861558 221865765266861558 endpoint_17_40_p12 endpoint_17_40_w12
private theorem endpoint_17_40_w14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 14 2 221865765266861558 = some 221865765266861558 := by decide +kernel
private theorem endpoint_17_40_p16 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 16 221865765266861558 = some 221865765266861558 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 14 2 221865765266861558 221865765266861558 221865765266861558 endpoint_17_40_p14 endpoint_17_40_w14
def endpoint_17_40 : CertifiedEndpoint :=
  ⟨⟨17, 40, 2898⟩, 221865765266861558, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_40_flag endpoint_17_40_sources 16 221865765266861558 221865765266861558 rfl endpoint_17_40_base endpoint_17_40_p16) (by decide)⟩
private def endpoint_17_41_flag : Flag := ⟨17, 41, 2852⟩
private def endpoint_17_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_41_base : receiptBase endpoint_17_41_flag endpoint_17_41_sources = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_w0 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_w2 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 2 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_p4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 4 223751319964703265 = some 223751319964703265 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 2 2 223751319964703265 223751319964703265 223751319964703265 endpoint_17_41_w0 endpoint_17_41_w2
private theorem endpoint_17_41_w4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 4 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_p6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 6 223751319964703265 = some 223751319964703265 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 4 2 223751319964703265 223751319964703265 223751319964703265 endpoint_17_41_p4 endpoint_17_41_w4
private theorem endpoint_17_41_w6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 6 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_p8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 8 223751319964703265 = some 223751319964703265 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 6 2 223751319964703265 223751319964703265 223751319964703265 endpoint_17_41_p6 endpoint_17_41_w6
private theorem endpoint_17_41_w8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 8 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_p10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 10 223751319964703265 = some 223751319964703265 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 8 2 223751319964703265 223751319964703265 223751319964703265 endpoint_17_41_p8 endpoint_17_41_w8
private theorem endpoint_17_41_w10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 10 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_p12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 12 223751319964703265 = some 223751319964703265 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 10 2 223751319964703265 223751319964703265 223751319964703265 endpoint_17_41_p10 endpoint_17_41_w10
private theorem endpoint_17_41_w12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 12 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_p14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 14 223751319964703265 = some 223751319964703265 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 12 2 223751319964703265 223751319964703265 223751319964703265 endpoint_17_41_p12 endpoint_17_41_w12
private theorem endpoint_17_41_w14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 14 2 223751319964703265 = some 223751319964703265 := by decide +kernel
private theorem endpoint_17_41_p16 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 16 223751319964703265 = some 223751319964703265 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 14 2 223751319964703265 223751319964703265 223751319964703265 endpoint_17_41_p14 endpoint_17_41_w14
def endpoint_17_41 : CertifiedEndpoint :=
  ⟨⟨17, 41, 2852⟩, 223751319964703265, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_41_flag endpoint_17_41_sources 16 223751319964703265 223751319964703265 rfl endpoint_17_41_base endpoint_17_41_p16) (by decide)⟩
private def endpoint_17_42_flag : Flag := ⟨17, 42, 2805⟩
private def endpoint_17_42_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_42_base : receiptBase endpoint_17_42_flag endpoint_17_42_sources = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_w0 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_w2 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 2 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_p4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 4 224713147772915718 = some 224713147772915718 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 2 2 224713147772915718 224713147772915718 224713147772915718 endpoint_17_42_w0 endpoint_17_42_w2
private theorem endpoint_17_42_w4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 4 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_p6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 6 224713147772915718 = some 224713147772915718 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 4 2 224713147772915718 224713147772915718 224713147772915718 endpoint_17_42_p4 endpoint_17_42_w4
private theorem endpoint_17_42_w6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 6 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_p8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 8 224713147772915718 = some 224713147772915718 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 6 2 224713147772915718 224713147772915718 224713147772915718 endpoint_17_42_p6 endpoint_17_42_w6
private theorem endpoint_17_42_w8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 8 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_p10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 10 224713147772915718 = some 224713147772915718 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 8 2 224713147772915718 224713147772915718 224713147772915718 endpoint_17_42_p8 endpoint_17_42_w8
private theorem endpoint_17_42_w10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 10 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_p12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 12 224713147772915718 = some 224713147772915718 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 10 2 224713147772915718 224713147772915718 224713147772915718 endpoint_17_42_p10 endpoint_17_42_w10
private theorem endpoint_17_42_w12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 12 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_p14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 14 224713147772915718 = some 224713147772915718 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 12 2 224713147772915718 224713147772915718 224713147772915718 endpoint_17_42_p12 endpoint_17_42_w12
private theorem endpoint_17_42_w14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 14 2 224713147772915718 = some 224713147772915718 := by decide +kernel
private theorem endpoint_17_42_p16 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 16 224713147772915718 = some 224713147772915718 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 14 2 224713147772915718 224713147772915718 224713147772915718 endpoint_17_42_p14 endpoint_17_42_w14
def endpoint_17_42 : CertifiedEndpoint :=
  ⟨⟨17, 42, 2805⟩, 224713147772915718, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_42_flag endpoint_17_42_sources 16 224713147772915718 224713147772915718 rfl endpoint_17_42_base endpoint_17_42_p16) (by decide)⟩
private def endpoint_17_43_flag : Flag := ⟨17, 43, 2757⟩
private def endpoint_17_43_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_43_base : receiptBase endpoint_17_43_flag endpoint_17_43_sources = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_w0 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_w2 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 2 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_p4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 4 225440974941862807 = some 225440974941862807 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 2 2 225440974941862807 225440974941862807 225440974941862807 endpoint_17_43_w0 endpoint_17_43_w2
private theorem endpoint_17_43_w4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 4 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_p6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 6 225440974941862807 = some 225440974941862807 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 4 2 225440974941862807 225440974941862807 225440974941862807 endpoint_17_43_p4 endpoint_17_43_w4
private theorem endpoint_17_43_w6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 6 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_p8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 8 225440974941862807 = some 225440974941862807 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 6 2 225440974941862807 225440974941862807 225440974941862807 endpoint_17_43_p6 endpoint_17_43_w6
private theorem endpoint_17_43_w8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 8 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_p10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 10 225440974941862807 = some 225440974941862807 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 8 2 225440974941862807 225440974941862807 225440974941862807 endpoint_17_43_p8 endpoint_17_43_w8
private theorem endpoint_17_43_w10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 10 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_p12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 12 225440974941862807 = some 225440974941862807 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 10 2 225440974941862807 225440974941862807 225440974941862807 endpoint_17_43_p10 endpoint_17_43_w10
private theorem endpoint_17_43_w12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 12 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_p14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 14 225440974941862807 = some 225440974941862807 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 12 2 225440974941862807 225440974941862807 225440974941862807 endpoint_17_43_p12 endpoint_17_43_w12
private theorem endpoint_17_43_w14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 14 2 225440974941862807 = some 225440974941862807 := by decide +kernel
private theorem endpoint_17_43_p16 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 16 225440974941862807 = some 225440974941862807 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 14 2 225440974941862807 225440974941862807 225440974941862807 endpoint_17_43_p14 endpoint_17_43_w14
def endpoint_17_43 : CertifiedEndpoint :=
  ⟨⟨17, 43, 2757⟩, 225440974941862807, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_43_flag endpoint_17_43_sources 16 225440974941862807 225440974941862807 rfl endpoint_17_43_base endpoint_17_43_p16) (by decide)⟩
private def endpoint_17_44_flag : Flag := ⟨17, 44, 2708⟩
private def endpoint_17_44_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_44_base : receiptBase endpoint_17_44_flag endpoint_17_44_sources = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_w0 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_w2 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 2 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_p4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 4 225929958680257477 = some 225929958680257477 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 2 2 225929958680257477 225929958680257477 225929958680257477 endpoint_17_44_w0 endpoint_17_44_w2
private theorem endpoint_17_44_w4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 4 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_p6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 6 225929958680257477 = some 225929958680257477 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 4 2 225929958680257477 225929958680257477 225929958680257477 endpoint_17_44_p4 endpoint_17_44_w4
private theorem endpoint_17_44_w6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 6 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_p8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 8 225929958680257477 = some 225929958680257477 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 6 2 225929958680257477 225929958680257477 225929958680257477 endpoint_17_44_p6 endpoint_17_44_w6
private theorem endpoint_17_44_w8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 8 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_p10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 10 225929958680257477 = some 225929958680257477 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 8 2 225929958680257477 225929958680257477 225929958680257477 endpoint_17_44_p8 endpoint_17_44_w8
private theorem endpoint_17_44_w10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 10 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_p12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 12 225929958680257477 = some 225929958680257477 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 10 2 225929958680257477 225929958680257477 225929958680257477 endpoint_17_44_p10 endpoint_17_44_w10
private theorem endpoint_17_44_w12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 12 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_p14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 14 225929958680257477 = some 225929958680257477 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 12 2 225929958680257477 225929958680257477 225929958680257477 endpoint_17_44_p12 endpoint_17_44_w12
private theorem endpoint_17_44_w14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 14 2 225929958680257477 = some 225929958680257477 := by decide +kernel
private theorem endpoint_17_44_p16 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 16 225929958680257477 = some 225929958680257477 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 14 2 225929958680257477 225929958680257477 225929958680257477 endpoint_17_44_p14 endpoint_17_44_w14
def endpoint_17_44 : CertifiedEndpoint :=
  ⟨⟨17, 44, 2708⟩, 225929958680257477, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_44_flag endpoint_17_44_sources 16 225929958680257477 225929958680257477 rfl endpoint_17_44_base endpoint_17_44_p16) (by decide)⟩
private def endpoint_17_45_flag : Flag := ⟨17, 45, 2658⟩
private def endpoint_17_45_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_45_base : receiptBase endpoint_17_45_flag endpoint_17_45_sources = some 226175256196812670 := by decide +kernel
private theorem endpoint_17_45_w0 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 2 226175256196812670 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_w2 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 2 2 228250257654361744 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_p4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 4 226175256196812670 = some 228250257654361744 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 2 2 226175256196812670 228250257654361744 228250257654361744 endpoint_17_45_w0 endpoint_17_45_w2
private theorem endpoint_17_45_w4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 4 2 228250257654361744 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_p6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 6 226175256196812670 = some 228250257654361744 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 4 2 226175256196812670 228250257654361744 228250257654361744 endpoint_17_45_p4 endpoint_17_45_w4
private theorem endpoint_17_45_w6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 6 2 228250257654361744 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_p8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 8 226175256196812670 = some 228250257654361744 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 6 2 226175256196812670 228250257654361744 228250257654361744 endpoint_17_45_p6 endpoint_17_45_w6
private theorem endpoint_17_45_w8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 8 2 228250257654361744 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_p10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 10 226175256196812670 = some 228250257654361744 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 8 2 226175256196812670 228250257654361744 228250257654361744 endpoint_17_45_p8 endpoint_17_45_w8
private theorem endpoint_17_45_w10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 10 2 228250257654361744 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_p12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 12 226175256196812670 = some 228250257654361744 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 10 2 226175256196812670 228250257654361744 228250257654361744 endpoint_17_45_p10 endpoint_17_45_w10
private theorem endpoint_17_45_w12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 12 2 228250257654361744 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_p14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 14 226175256196812670 = some 228250257654361744 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 12 2 226175256196812670 228250257654361744 228250257654361744 endpoint_17_45_p12 endpoint_17_45_w12
private theorem endpoint_17_45_w14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 14 2 228250257654361744 = some 228250257654361744 := by decide +kernel
private theorem endpoint_17_45_p16 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 16 226175256196812670 = some 228250257654361744 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 14 2 226175256196812670 228250257654361744 228250257654361744 endpoint_17_45_p14 endpoint_17_45_w14
def endpoint_17_45 : CertifiedEndpoint :=
  ⟨⟨17, 45, 2658⟩, 228250257654361744, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_45_flag endpoint_17_45_sources 16 226175256196812670 228250257654361744 rfl endpoint_17_45_base endpoint_17_45_p16) (by decide)⟩
private def endpoint_17_46_flag : Flag := ⟨17, 46, 2607⟩
private def endpoint_17_46_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_46_base : receiptBase endpoint_17_46_flag endpoint_17_46_sources = some 226172024700241331 := by decide +kernel
private theorem endpoint_17_46_w0 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 2 226172024700241331 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_w2 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 2 2 232176821719120134 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_p4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 4 226172024700241331 = some 232176821719120134 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 2 2 226172024700241331 232176821719120134 232176821719120134 endpoint_17_46_w0 endpoint_17_46_w2
private theorem endpoint_17_46_w4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 4 2 232176821719120134 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_p6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 6 226172024700241331 = some 232176821719120134 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 4 2 226172024700241331 232176821719120134 232176821719120134 endpoint_17_46_p4 endpoint_17_46_w4
private theorem endpoint_17_46_w6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 6 2 232176821719120134 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_p8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 8 226172024700241331 = some 232176821719120134 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 6 2 226172024700241331 232176821719120134 232176821719120134 endpoint_17_46_p6 endpoint_17_46_w6
private theorem endpoint_17_46_w8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 8 2 232176821719120134 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_p10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 10 226172024700241331 = some 232176821719120134 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 8 2 226172024700241331 232176821719120134 232176821719120134 endpoint_17_46_p8 endpoint_17_46_w8
private theorem endpoint_17_46_w10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 10 2 232176821719120134 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_p12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 12 226172024700241331 = some 232176821719120134 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 10 2 226172024700241331 232176821719120134 232176821719120134 endpoint_17_46_p10 endpoint_17_46_w10
private theorem endpoint_17_46_w12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 12 2 232176821719120134 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_p14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 14 226172024700241331 = some 232176821719120134 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 12 2 226172024700241331 232176821719120134 232176821719120134 endpoint_17_46_p12 endpoint_17_46_w12
private theorem endpoint_17_46_w14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 14 2 232176821719120134 = some 232176821719120134 := by decide +kernel
private theorem endpoint_17_46_p16 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 16 226172024700241331 = some 232176821719120134 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 14 2 226172024700241331 232176821719120134 232176821719120134 endpoint_17_46_p14 endpoint_17_46_w14
def endpoint_17_46 : CertifiedEndpoint :=
  ⟨⟨17, 46, 2607⟩, 232176821719120134, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_46_flag endpoint_17_46_sources 16 226172024700241331 232176821719120134 rfl endpoint_17_46_base endpoint_17_46_p16) (by decide)⟩
private def endpoint_17_47_flag : Flag := ⟨17, 47, 2555⟩
private def endpoint_17_47_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_47_base : receiptBase endpoint_17_47_flag endpoint_17_47_sources = some 225915421399256402 := by decide +kernel
private theorem endpoint_17_47_w0 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 2 225915421399256402 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_w2 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 2 2 235916343835809375 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_p4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 4 225915421399256402 = some 235916343835809375 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 2 2 225915421399256402 235916343835809375 235916343835809375 endpoint_17_47_w0 endpoint_17_47_w2
private theorem endpoint_17_47_w4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 4 2 235916343835809375 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_p6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 6 225915421399256402 = some 235916343835809375 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 4 2 225915421399256402 235916343835809375 235916343835809375 endpoint_17_47_p4 endpoint_17_47_w4
private theorem endpoint_17_47_w6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 6 2 235916343835809375 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_p8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 8 225915421399256402 = some 235916343835809375 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 6 2 225915421399256402 235916343835809375 235916343835809375 endpoint_17_47_p6 endpoint_17_47_w6
private theorem endpoint_17_47_w8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 8 2 235916343835809375 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_p10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 10 225915421399256402 = some 235916343835809375 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 8 2 225915421399256402 235916343835809375 235916343835809375 endpoint_17_47_p8 endpoint_17_47_w8
private theorem endpoint_17_47_w10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 10 2 235916343835809375 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_p12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 12 225915421399256402 = some 235916343835809375 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 10 2 225915421399256402 235916343835809375 235916343835809375 endpoint_17_47_p10 endpoint_17_47_w10
private theorem endpoint_17_47_w12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 12 2 235916343835809375 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_p14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 14 225915421399256402 = some 235916343835809375 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 12 2 225915421399256402 235916343835809375 235916343835809375 endpoint_17_47_p12 endpoint_17_47_w12
private theorem endpoint_17_47_w14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 14 2 235916343835809375 = some 235916343835809375 := by decide +kernel
private theorem endpoint_17_47_p16 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 16 225915421399256402 = some 235916343835809375 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 14 2 225915421399256402 235916343835809375 235916343835809375 endpoint_17_47_p14 endpoint_17_47_w14
def endpoint_17_47 : CertifiedEndpoint :=
  ⟨⟨17, 47, 2555⟩, 235916343835809375, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_47_flag endpoint_17_47_sources 16 225915421399256402 235916343835809375 rfl endpoint_17_47_base endpoint_17_47_p16) (by decide)⟩
private def endpoint_17_48_flag : Flag := ⟨17, 48, 2502⟩
private def endpoint_17_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_48_base : receiptBase endpoint_17_48_flag endpoint_17_48_sources = some 225400603502570827 := by decide +kernel
private theorem endpoint_17_48_w0 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 2 225400603502570827 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_w2 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 2 2 239464881125557330 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_p4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 4 225400603502570827 = some 239464881125557330 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 2 2 225400603502570827 239464881125557330 239464881125557330 endpoint_17_48_w0 endpoint_17_48_w2
private theorem endpoint_17_48_w4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 4 2 239464881125557330 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_p6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 6 225400603502570827 = some 239464881125557330 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 4 2 225400603502570827 239464881125557330 239464881125557330 endpoint_17_48_p4 endpoint_17_48_w4
private theorem endpoint_17_48_w6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 6 2 239464881125557330 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_p8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 8 225400603502570827 = some 239464881125557330 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 6 2 225400603502570827 239464881125557330 239464881125557330 endpoint_17_48_p6 endpoint_17_48_w6
private theorem endpoint_17_48_w8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 8 2 239464881125557330 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_p10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 10 225400603502570827 = some 239464881125557330 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 8 2 225400603502570827 239464881125557330 239464881125557330 endpoint_17_48_p8 endpoint_17_48_w8
private theorem endpoint_17_48_w10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 10 2 239464881125557330 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_p12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 12 225400603502570827 = some 239464881125557330 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 10 2 225400603502570827 239464881125557330 239464881125557330 endpoint_17_48_p10 endpoint_17_48_w10
private theorem endpoint_17_48_w12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 12 2 239464881125557330 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_p14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 14 225400603502570827 = some 239464881125557330 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 12 2 225400603502570827 239464881125557330 239464881125557330 endpoint_17_48_p12 endpoint_17_48_w12
private theorem endpoint_17_48_w14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 14 2 239464881125557330 = some 239464881125557330 := by decide +kernel
private theorem endpoint_17_48_p16 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 16 225400603502570827 = some 239464881125557330 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 14 2 225400603502570827 239464881125557330 239464881125557330 endpoint_17_48_p14 endpoint_17_48_w14
def endpoint_17_48 : CertifiedEndpoint :=
  ⟨⟨17, 48, 2502⟩, 239464881125557330, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_48_flag endpoint_17_48_sources 16 225400603502570827 239464881125557330 rfl endpoint_17_48_base endpoint_17_48_p16) (by decide)⟩
private def endpoint_17_49_flag : Flag := ⟨17, 49, 2448⟩
private def endpoint_17_49_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_17_49_base : receiptBase endpoint_17_49_flag endpoint_17_49_sources = some 230207004583817173 := by decide +kernel
private theorem endpoint_17_49_w0 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 2 230207004583817173 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_w2 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 2 2 235873054512269157 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_p4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 4 230207004583817173 = some 235873054512269157 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 2 2 230207004583817173 235873054512269157 235873054512269157 endpoint_17_49_w0 endpoint_17_49_w2
private theorem endpoint_17_49_w4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 4 2 235873054512269157 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_p6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 6 230207004583817173 = some 235873054512269157 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 4 2 230207004583817173 235873054512269157 235873054512269157 endpoint_17_49_p4 endpoint_17_49_w4
private theorem endpoint_17_49_w6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 6 2 235873054512269157 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_p8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 8 230207004583817173 = some 235873054512269157 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 6 2 230207004583817173 235873054512269157 235873054512269157 endpoint_17_49_p6 endpoint_17_49_w6
private theorem endpoint_17_49_w8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 8 2 235873054512269157 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_p10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 10 230207004583817173 = some 235873054512269157 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 8 2 230207004583817173 235873054512269157 235873054512269157 endpoint_17_49_p8 endpoint_17_49_w8
private theorem endpoint_17_49_w10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 10 2 235873054512269157 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_p12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 12 230207004583817173 = some 235873054512269157 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 10 2 230207004583817173 235873054512269157 235873054512269157 endpoint_17_49_p10 endpoint_17_49_w10
private theorem endpoint_17_49_w12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 12 2 235873054512269157 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_p14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 14 230207004583817173 = some 235873054512269157 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 12 2 230207004583817173 235873054512269157 235873054512269157 endpoint_17_49_p12 endpoint_17_49_w12
private theorem endpoint_17_49_w14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 14 2 235873054512269157 = some 235873054512269157 := by decide +kernel
private theorem endpoint_17_49_p16 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 16 230207004583817173 = some 235873054512269157 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 14 2 230207004583817173 235873054512269157 235873054512269157 endpoint_17_49_p14 endpoint_17_49_w14
def endpoint_17_49 : CertifiedEndpoint :=
  ⟨⟨17, 49, 2448⟩, 235873054512269157, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_17_49_flag endpoint_17_49_sources 16 230207004583817173 235873054512269157 rfl endpoint_17_49_base endpoint_17_49_p16) (by decide)⟩
private def endpoint_17_50_flag : Flag := ⟨17, 50, 2392⟩
private def endpoint_17_50_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_50_base : receiptBase endpoint_17_50_flag endpoint_17_50_sources = some 229439055293515864 := by decide +kernel
private theorem endpoint_17_50_w0 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 2 229439055293515864 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_w2 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 2 2 234089815065563268 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_p4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 4 229439055293515864 = some 234089815065563268 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 2 2 229439055293515864 234089815065563268 234089815065563268 endpoint_17_50_w0 endpoint_17_50_w2
private theorem endpoint_17_50_w4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 4 2 234089815065563268 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_p6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 6 229439055293515864 = some 234089815065563268 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 4 2 229439055293515864 234089815065563268 234089815065563268 endpoint_17_50_p4 endpoint_17_50_w4
private theorem endpoint_17_50_w6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 6 2 234089815065563268 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_p8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 8 229439055293515864 = some 234089815065563268 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 6 2 229439055293515864 234089815065563268 234089815065563268 endpoint_17_50_p6 endpoint_17_50_w6
private theorem endpoint_17_50_w8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 8 2 234089815065563268 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_p10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 10 229439055293515864 = some 234089815065563268 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 8 2 229439055293515864 234089815065563268 234089815065563268 endpoint_17_50_p8 endpoint_17_50_w8
private theorem endpoint_17_50_w10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 10 2 234089815065563268 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_p12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 12 229439055293515864 = some 234089815065563268 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 10 2 229439055293515864 234089815065563268 234089815065563268 endpoint_17_50_p10 endpoint_17_50_w10
private theorem endpoint_17_50_w12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 12 2 234089815065563268 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_p14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 14 229439055293515864 = some 234089815065563268 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 12 2 229439055293515864 234089815065563268 234089815065563268 endpoint_17_50_p12 endpoint_17_50_w12
private theorem endpoint_17_50_w14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 14 2 234089815065563268 = some 234089815065563268 := by decide +kernel
private theorem endpoint_17_50_p16 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 16 229439055293515864 = some 234089815065563268 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 14 2 229439055293515864 234089815065563268 234089815065563268 endpoint_17_50_p14 endpoint_17_50_w14
def endpoint_17_50 : CertifiedEndpoint :=
  ⟨⟨17, 50, 2392⟩, 234089815065563268, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_50_flag endpoint_17_50_sources 16 229439055293515864 234089815065563268 rfl endpoint_17_50_base endpoint_17_50_p16) (by decide)⟩
private def endpoint_17_51_flag : Flag := ⟨17, 51, 2336⟩
private def endpoint_17_51_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_51_base : receiptBase endpoint_17_51_flag endpoint_17_51_sources = some 228129518240472902 := by decide +kernel
private theorem endpoint_17_51_w0 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 2 228129518240472902 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_w2 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 2 2 236750044975251080 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_p4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 4 228129518240472902 = some 236750044975251080 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 2 2 228129518240472902 236750044975251080 236750044975251080 endpoint_17_51_w0 endpoint_17_51_w2
private theorem endpoint_17_51_w4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 4 2 236750044975251080 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_p6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 6 228129518240472902 = some 236750044975251080 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 4 2 228129518240472902 236750044975251080 236750044975251080 endpoint_17_51_p4 endpoint_17_51_w4
private theorem endpoint_17_51_w6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 6 2 236750044975251080 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_p8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 8 228129518240472902 = some 236750044975251080 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 6 2 228129518240472902 236750044975251080 236750044975251080 endpoint_17_51_p6 endpoint_17_51_w6
private theorem endpoint_17_51_w8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 8 2 236750044975251080 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_p10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 10 228129518240472902 = some 236750044975251080 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 8 2 228129518240472902 236750044975251080 236750044975251080 endpoint_17_51_p8 endpoint_17_51_w8
private theorem endpoint_17_51_w10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 10 2 236750044975251080 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_p12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 12 228129518240472902 = some 236750044975251080 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 10 2 228129518240472902 236750044975251080 236750044975251080 endpoint_17_51_p10 endpoint_17_51_w10
private theorem endpoint_17_51_w12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 12 2 236750044975251080 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_p14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 14 228129518240472902 = some 236750044975251080 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 12 2 228129518240472902 236750044975251080 236750044975251080 endpoint_17_51_p12 endpoint_17_51_w12
private theorem endpoint_17_51_w14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 14 2 236750044975251080 = some 236750044975251080 := by decide +kernel
private theorem endpoint_17_51_p16 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 16 228129518240472902 = some 236750044975251080 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 14 2 228129518240472902 236750044975251080 236750044975251080 endpoint_17_51_p14 endpoint_17_51_w14
def endpoint_17_51 : CertifiedEndpoint :=
  ⟨⟨17, 51, 2336⟩, 236750044975251080, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_51_flag endpoint_17_51_sources 16 228129518240472902 236750044975251080 rfl endpoint_17_51_base endpoint_17_51_p16) (by decide)⟩
private def endpoint_17_52_flag : Flag := ⟨17, 52, 2278⟩
private def endpoint_17_52_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_52_base : receiptBase endpoint_17_52_flag endpoint_17_52_sources = some 227190975400957858 := by decide +kernel
private theorem endpoint_17_52_w0 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 2 227190975400957858 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_w2 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 2 2 227196388698175870 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_p4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 4 227190975400957858 = some 227196388698175870 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 2 2 227190975400957858 227196388698175870 227196388698175870 endpoint_17_52_w0 endpoint_17_52_w2
private theorem endpoint_17_52_w4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 4 2 227196388698175870 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_p6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 6 227190975400957858 = some 227196388698175870 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 4 2 227190975400957858 227196388698175870 227196388698175870 endpoint_17_52_p4 endpoint_17_52_w4
private theorem endpoint_17_52_w6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 6 2 227196388698175870 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_p8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 8 227190975400957858 = some 227196388698175870 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 6 2 227190975400957858 227196388698175870 227196388698175870 endpoint_17_52_p6 endpoint_17_52_w6
private theorem endpoint_17_52_w8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 8 2 227196388698175870 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_p10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 10 227190975400957858 = some 227196388698175870 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 8 2 227190975400957858 227196388698175870 227196388698175870 endpoint_17_52_p8 endpoint_17_52_w8
private theorem endpoint_17_52_w10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 10 2 227196388698175870 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_p12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 12 227190975400957858 = some 227196388698175870 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 10 2 227190975400957858 227196388698175870 227196388698175870 endpoint_17_52_p10 endpoint_17_52_w10
private theorem endpoint_17_52_w12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 12 2 227196388698175870 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_p14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 14 227190975400957858 = some 227196388698175870 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 12 2 227190975400957858 227196388698175870 227196388698175870 endpoint_17_52_p12 endpoint_17_52_w12
private theorem endpoint_17_52_w14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 14 2 227196388698175870 = some 227196388698175870 := by decide +kernel
private theorem endpoint_17_52_p16 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 16 227190975400957858 = some 227196388698175870 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 14 2 227190975400957858 227196388698175870 227196388698175870 endpoint_17_52_p14 endpoint_17_52_w14
def endpoint_17_52 : CertifiedEndpoint :=
  ⟨⟨17, 52, 2278⟩, 227196388698175870, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_52_flag endpoint_17_52_sources 16 227190975400957858 227196388698175870 rfl endpoint_17_52_base endpoint_17_52_p16) (by decide)⟩
private def endpoint_17_53_flag : Flag := ⟨17, 53, 2219⟩
private def endpoint_17_53_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_53_base : receiptBase endpoint_17_53_flag endpoint_17_53_sources = some 225206717089688984 := by decide +kernel
private theorem endpoint_17_53_w0 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 2 225206717089688984 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_w2 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 2 2 229101355467158643 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_p4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 4 225206717089688984 = some 229101355467158643 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 2 2 225206717089688984 229101355467158643 229101355467158643 endpoint_17_53_w0 endpoint_17_53_w2
private theorem endpoint_17_53_w4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 4 2 229101355467158643 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_p6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 6 225206717089688984 = some 229101355467158643 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 4 2 225206717089688984 229101355467158643 229101355467158643 endpoint_17_53_p4 endpoint_17_53_w4
private theorem endpoint_17_53_w6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 6 2 229101355467158643 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_p8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 8 225206717089688984 = some 229101355467158643 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 6 2 225206717089688984 229101355467158643 229101355467158643 endpoint_17_53_p6 endpoint_17_53_w6
private theorem endpoint_17_53_w8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 8 2 229101355467158643 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_p10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 10 225206717089688984 = some 229101355467158643 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 8 2 225206717089688984 229101355467158643 229101355467158643 endpoint_17_53_p8 endpoint_17_53_w8
private theorem endpoint_17_53_w10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 10 2 229101355467158643 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_p12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 12 225206717089688984 = some 229101355467158643 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 10 2 225206717089688984 229101355467158643 229101355467158643 endpoint_17_53_p10 endpoint_17_53_w10
private theorem endpoint_17_53_w12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 12 2 229101355467158643 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_p14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 14 225206717089688984 = some 229101355467158643 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 12 2 225206717089688984 229101355467158643 229101355467158643 endpoint_17_53_p12 endpoint_17_53_w12
private theorem endpoint_17_53_w14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 14 2 229101355467158643 = some 229101355467158643 := by decide +kernel
private theorem endpoint_17_53_p16 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 16 225206717089688984 = some 229101355467158643 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 14 2 225206717089688984 229101355467158643 229101355467158643 endpoint_17_53_p14 endpoint_17_53_w14
def endpoint_17_53 : CertifiedEndpoint :=
  ⟨⟨17, 53, 2219⟩, 229101355467158643, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_53_flag endpoint_17_53_sources 16 225206717089688984 229101355467158643 rfl endpoint_17_53_base endpoint_17_53_p16) (by decide)⟩
private def endpoint_17_54_flag : Flag := ⟨17, 54, 2158⟩
private def endpoint_17_54_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_54_base : receiptBase endpoint_17_54_flag endpoint_17_54_sources = some 222861621507854550 := by decide +kernel
private theorem endpoint_17_54_w0 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 2 222861621507854550 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_w2 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 2 2 230730870441938508 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_p4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 4 222861621507854550 = some 230730870441938508 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 2 2 222861621507854550 230730870441938508 230730870441938508 endpoint_17_54_w0 endpoint_17_54_w2
private theorem endpoint_17_54_w4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 4 2 230730870441938508 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_p6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 6 222861621507854550 = some 230730870441938508 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 4 2 222861621507854550 230730870441938508 230730870441938508 endpoint_17_54_p4 endpoint_17_54_w4
private theorem endpoint_17_54_w6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 6 2 230730870441938508 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_p8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 8 222861621507854550 = some 230730870441938508 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 6 2 222861621507854550 230730870441938508 230730870441938508 endpoint_17_54_p6 endpoint_17_54_w6
private theorem endpoint_17_54_w8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 8 2 230730870441938508 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_p10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 10 222861621507854550 = some 230730870441938508 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 8 2 222861621507854550 230730870441938508 230730870441938508 endpoint_17_54_p8 endpoint_17_54_w8
private theorem endpoint_17_54_w10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 10 2 230730870441938508 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_p12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 12 222861621507854550 = some 230730870441938508 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 10 2 222861621507854550 230730870441938508 230730870441938508 endpoint_17_54_p10 endpoint_17_54_w10
private theorem endpoint_17_54_w12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 12 2 230730870441938508 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_p14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 14 222861621507854550 = some 230730870441938508 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 12 2 222861621507854550 230730870441938508 230730870441938508 endpoint_17_54_p12 endpoint_17_54_w12
private theorem endpoint_17_54_w14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 14 2 230730870441938508 = some 230730870441938508 := by decide +kernel
private theorem endpoint_17_54_p16 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 16 222861621507854550 = some 230730870441938508 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 14 2 222861621507854550 230730870441938508 230730870441938508 endpoint_17_54_p14 endpoint_17_54_w14
def endpoint_17_54 : CertifiedEndpoint :=
  ⟨⟨17, 54, 2158⟩, 230730870441938508, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_54_flag endpoint_17_54_sources 16 222861621507854550 230730870441938508 rfl endpoint_17_54_base endpoint_17_54_p16) (by decide)⟩
private def endpoint_17_55_flag : Flag := ⟨17, 55, 2096⟩
private def endpoint_17_55_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_55_base : receiptBase endpoint_17_55_flag endpoint_17_55_sources = some 220141402250812440 := by decide +kernel
private theorem endpoint_17_55_w0 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 2 220141402250812440 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_w2 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 2 2 232136543265842612 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_p4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 4 220141402250812440 = some 232136543265842612 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 2 2 220141402250812440 232136543265842612 232136543265842612 endpoint_17_55_w0 endpoint_17_55_w2
private theorem endpoint_17_55_w4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 4 2 232136543265842612 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_p6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 6 220141402250812440 = some 232136543265842612 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 4 2 220141402250812440 232136543265842612 232136543265842612 endpoint_17_55_p4 endpoint_17_55_w4
private theorem endpoint_17_55_w6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 6 2 232136543265842612 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_p8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 8 220141402250812440 = some 232136543265842612 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 6 2 220141402250812440 232136543265842612 232136543265842612 endpoint_17_55_p6 endpoint_17_55_w6
private theorem endpoint_17_55_w8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 8 2 232136543265842612 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_p10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 10 220141402250812440 = some 232136543265842612 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 8 2 220141402250812440 232136543265842612 232136543265842612 endpoint_17_55_p8 endpoint_17_55_w8
private theorem endpoint_17_55_w10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 10 2 232136543265842612 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_p12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 12 220141402250812440 = some 232136543265842612 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 10 2 220141402250812440 232136543265842612 232136543265842612 endpoint_17_55_p10 endpoint_17_55_w10
private theorem endpoint_17_55_w12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 12 2 232136543265842612 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_p14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 14 220141402250812440 = some 232136543265842612 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 12 2 220141402250812440 232136543265842612 232136543265842612 endpoint_17_55_p12 endpoint_17_55_w12
private theorem endpoint_17_55_w14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 14 2 232136543265842612 = some 232136543265842612 := by decide +kernel
private theorem endpoint_17_55_p16 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 16 220141402250812440 = some 232136543265842612 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 14 2 220141402250812440 232136543265842612 232136543265842612 endpoint_17_55_p14 endpoint_17_55_w14
def endpoint_17_55 : CertifiedEndpoint :=
  ⟨⟨17, 55, 2096⟩, 232136543265842612, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_55_flag endpoint_17_55_sources 16 220141402250812440 232136543265842612 rfl endpoint_17_55_base endpoint_17_55_p16) (by decide)⟩
private def endpoint_17_56_flag : Flag := ⟨17, 56, 2033⟩
private def endpoint_17_56_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_56_base : receiptBase endpoint_17_56_flag endpoint_17_56_sources = some 218080046114302105 := by decide +kernel
private theorem endpoint_17_56_w0 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 2 218080046114302105 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_w2 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 2 2 226905063338113200 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_p4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 4 218080046114302105 = some 226905063338113200 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 2 2 218080046114302105 226905063338113200 226905063338113200 endpoint_17_56_w0 endpoint_17_56_w2
private theorem endpoint_17_56_w4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 4 2 226905063338113200 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_p6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 6 218080046114302105 = some 226905063338113200 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 4 2 218080046114302105 226905063338113200 226905063338113200 endpoint_17_56_p4 endpoint_17_56_w4
private theorem endpoint_17_56_w6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 6 2 226905063338113200 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_p8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 8 218080046114302105 = some 226905063338113200 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 6 2 218080046114302105 226905063338113200 226905063338113200 endpoint_17_56_p6 endpoint_17_56_w6
private theorem endpoint_17_56_w8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 8 2 226905063338113200 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_p10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 10 218080046114302105 = some 226905063338113200 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 8 2 218080046114302105 226905063338113200 226905063338113200 endpoint_17_56_p8 endpoint_17_56_w8
private theorem endpoint_17_56_w10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 10 2 226905063338113200 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_p12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 12 218080046114302105 = some 226905063338113200 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 10 2 218080046114302105 226905063338113200 226905063338113200 endpoint_17_56_p10 endpoint_17_56_w10
private theorem endpoint_17_56_w12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 12 2 226905063338113200 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_p14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 14 218080046114302105 = some 226905063338113200 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 12 2 218080046114302105 226905063338113200 226905063338113200 endpoint_17_56_p12 endpoint_17_56_w12
private theorem endpoint_17_56_w14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 14 2 226905063338113200 = some 226905063338113200 := by decide +kernel
private theorem endpoint_17_56_p16 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 16 218080046114302105 = some 226905063338113200 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 14 2 218080046114302105 226905063338113200 226905063338113200 endpoint_17_56_p14 endpoint_17_56_w14
def endpoint_17_56 : CertifiedEndpoint :=
  ⟨⟨17, 56, 2033⟩, 226905063338113200, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_56_flag endpoint_17_56_sources 16 218080046114302105 226905063338113200 rfl endpoint_17_56_base endpoint_17_56_p16) (by decide)⟩
private def endpoint_17_57_flag : Flag := ⟨17, 57, 1968⟩
private def endpoint_17_57_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_57_base : receiptBase endpoint_17_57_flag endpoint_17_57_sources = some 214597502713514641 := by decide +kernel
private theorem endpoint_17_57_w0 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 2 214597502713514641 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_w2 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 2 2 227651974718280319 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_p4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 4 214597502713514641 = some 227651974718280319 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 2 2 214597502713514641 227651974718280319 227651974718280319 endpoint_17_57_w0 endpoint_17_57_w2
private theorem endpoint_17_57_w4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 4 2 227651974718280319 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_p6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 6 214597502713514641 = some 227651974718280319 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 4 2 214597502713514641 227651974718280319 227651974718280319 endpoint_17_57_p4 endpoint_17_57_w4
private theorem endpoint_17_57_w6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 6 2 227651974718280319 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_p8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 8 214597502713514641 = some 227651974718280319 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 6 2 214597502713514641 227651974718280319 227651974718280319 endpoint_17_57_p6 endpoint_17_57_w6
private theorem endpoint_17_57_w8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 8 2 227651974718280319 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_p10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 10 214597502713514641 = some 227651974718280319 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 8 2 214597502713514641 227651974718280319 227651974718280319 endpoint_17_57_p8 endpoint_17_57_w8
private theorem endpoint_17_57_w10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 10 2 227651974718280319 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_p12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 12 214597502713514641 = some 227651974718280319 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 10 2 214597502713514641 227651974718280319 227651974718280319 endpoint_17_57_p10 endpoint_17_57_w10
private theorem endpoint_17_57_w12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 12 2 227651974718280319 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_p14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 14 214597502713514641 = some 227651974718280319 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 12 2 214597502713514641 227651974718280319 227651974718280319 endpoint_17_57_p12 endpoint_17_57_w12
private theorem endpoint_17_57_w14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 14 2 227651974718280319 = some 227651974718280319 := by decide +kernel
private theorem endpoint_17_57_p16 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 16 214597502713514641 = some 227651974718280319 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 14 2 214597502713514641 227651974718280319 227651974718280319 endpoint_17_57_p14 endpoint_17_57_w14
def endpoint_17_57 : CertifiedEndpoint :=
  ⟨⟨17, 57, 1968⟩, 227651974718280319, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_57_flag endpoint_17_57_sources 16 214597502713514641 227651974718280319 rfl endpoint_17_57_base endpoint_17_57_p16) (by decide)⟩
private def endpoint_17_58_flag : Flag := ⟨17, 58, 1902⟩
private def endpoint_17_58_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_58_base : receiptBase endpoint_17_58_flag endpoint_17_58_sources = some 210789928942251725 := by decide +kernel
private theorem endpoint_17_58_w0 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 2 210789928942251725 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_w2 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 2 2 228160586725040508 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_p4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 4 210789928942251725 = some 228160586725040508 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 2 2 210789928942251725 228160586725040508 228160586725040508 endpoint_17_58_w0 endpoint_17_58_w2
private theorem endpoint_17_58_w4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 4 2 228160586725040508 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_p6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 6 210789928942251725 = some 228160586725040508 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 4 2 210789928942251725 228160586725040508 228160586725040508 endpoint_17_58_p4 endpoint_17_58_w4
private theorem endpoint_17_58_w6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 6 2 228160586725040508 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_p8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 8 210789928942251725 = some 228160586725040508 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 6 2 210789928942251725 228160586725040508 228160586725040508 endpoint_17_58_p6 endpoint_17_58_w6
private theorem endpoint_17_58_w8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 8 2 228160586725040508 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_p10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 10 210789928942251725 = some 228160586725040508 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 8 2 210789928942251725 228160586725040508 228160586725040508 endpoint_17_58_p8 endpoint_17_58_w8
private theorem endpoint_17_58_w10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 10 2 228160586725040508 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_p12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 12 210789928942251725 = some 228160586725040508 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 10 2 210789928942251725 228160586725040508 228160586725040508 endpoint_17_58_p10 endpoint_17_58_w10
private theorem endpoint_17_58_w12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 12 2 228160586725040508 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_p14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 14 210789928942251725 = some 228160586725040508 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 12 2 210789928942251725 228160586725040508 228160586725040508 endpoint_17_58_p12 endpoint_17_58_w12
private theorem endpoint_17_58_w14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 14 2 228160586725040508 = some 228160586725040508 := by decide +kernel
private theorem endpoint_17_58_p16 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 16 210789928942251725 = some 228160586725040508 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 14 2 210789928942251725 228160586725040508 228160586725040508 endpoint_17_58_p14 endpoint_17_58_w14
def endpoint_17_58 : CertifiedEndpoint :=
  ⟨⟨17, 58, 1902⟩, 228160586725040508, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_58_flag endpoint_17_58_sources 16 210789928942251725 228160586725040508 rfl endpoint_17_58_base endpoint_17_58_p16) (by decide)⟩
private def endpoint_17_59_flag : Flag := ⟨17, 59, 1834⟩
private def endpoint_17_59_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_59_base : receiptBase endpoint_17_59_flag endpoint_17_59_sources = some 208944345764657562 := by decide +kernel
private theorem endpoint_17_59_w0 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 2 208944345764657562 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_w2 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 2 2 211912180826714592 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_p4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 4 208944345764657562 = some 211912180826714592 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 2 2 208944345764657562 211912180826714592 211912180826714592 endpoint_17_59_w0 endpoint_17_59_w2
private theorem endpoint_17_59_w4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 4 2 211912180826714592 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_p6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 6 208944345764657562 = some 211912180826714592 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 4 2 208944345764657562 211912180826714592 211912180826714592 endpoint_17_59_p4 endpoint_17_59_w4
private theorem endpoint_17_59_w6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 6 2 211912180826714592 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_p8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 8 208944345764657562 = some 211912180826714592 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 6 2 208944345764657562 211912180826714592 211912180826714592 endpoint_17_59_p6 endpoint_17_59_w6
private theorem endpoint_17_59_w8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 8 2 211912180826714592 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_p10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 10 208944345764657562 = some 211912180826714592 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 8 2 208944345764657562 211912180826714592 211912180826714592 endpoint_17_59_p8 endpoint_17_59_w8
private theorem endpoint_17_59_w10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 10 2 211912180826714592 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_p12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 12 208944345764657562 = some 211912180826714592 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 10 2 208944345764657562 211912180826714592 211912180826714592 endpoint_17_59_p10 endpoint_17_59_w10
private theorem endpoint_17_59_w12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 12 2 211912180826714592 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_p14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 14 208944345764657562 = some 211912180826714592 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 12 2 208944345764657562 211912180826714592 211912180826714592 endpoint_17_59_p12 endpoint_17_59_w12
private theorem endpoint_17_59_w14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 14 2 211912180826714592 = some 211912180826714592 := by decide +kernel
private theorem endpoint_17_59_p16 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 16 208944345764657562 = some 211912180826714592 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 14 2 208944345764657562 211912180826714592 211912180826714592 endpoint_17_59_p14 endpoint_17_59_w14
def endpoint_17_59 : CertifiedEndpoint :=
  ⟨⟨17, 59, 1834⟩, 211912180826714592, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_59_flag endpoint_17_59_sources 16 208944345764657562 211912180826714592 rfl endpoint_17_59_base endpoint_17_59_p16) (by decide)⟩
private def endpoint_17_60_flag : Flag := ⟨17, 60, 1764⟩
private def endpoint_17_60_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_60_base : receiptBase endpoint_17_60_flag endpoint_17_60_sources = some 204057624982045564 := by decide +kernel
private theorem endpoint_17_60_w0 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 2 204057624982045564 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_w2 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 2 2 211468205351623570 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_p4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 4 204057624982045564 = some 211468205351623570 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 2 2 204057624982045564 211468205351623570 211468205351623570 endpoint_17_60_w0 endpoint_17_60_w2
private theorem endpoint_17_60_w4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 4 2 211468205351623570 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_p6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 6 204057624982045564 = some 211468205351623570 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 4 2 204057624982045564 211468205351623570 211468205351623570 endpoint_17_60_p4 endpoint_17_60_w4
private theorem endpoint_17_60_w6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 6 2 211468205351623570 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_p8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 8 204057624982045564 = some 211468205351623570 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 6 2 204057624982045564 211468205351623570 211468205351623570 endpoint_17_60_p6 endpoint_17_60_w6
private theorem endpoint_17_60_w8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 8 2 211468205351623570 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_p10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 10 204057624982045564 = some 211468205351623570 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 8 2 204057624982045564 211468205351623570 211468205351623570 endpoint_17_60_p8 endpoint_17_60_w8
private theorem endpoint_17_60_w10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 10 2 211468205351623570 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_p12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 12 204057624982045564 = some 211468205351623570 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 10 2 204057624982045564 211468205351623570 211468205351623570 endpoint_17_60_p10 endpoint_17_60_w10
private theorem endpoint_17_60_w12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 12 2 211468205351623570 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_p14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 14 204057624982045564 = some 211468205351623570 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 12 2 204057624982045564 211468205351623570 211468205351623570 endpoint_17_60_p12 endpoint_17_60_w12
private theorem endpoint_17_60_w14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 14 2 211468205351623570 = some 211468205351623570 := by decide +kernel
private theorem endpoint_17_60_p16 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 16 204057624982045564 = some 211468205351623570 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 14 2 204057624982045564 211468205351623570 211468205351623570 endpoint_17_60_p14 endpoint_17_60_w14
def endpoint_17_60 : CertifiedEndpoint :=
  ⟨⟨17, 60, 1764⟩, 211468205351623570, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_60_flag endpoint_17_60_sources 16 204057624982045564 211468205351623570 rfl endpoint_17_60_base endpoint_17_60_p16) (by decide)⟩
private def endpoint_17_61_flag : Flag := ⟨17, 61, 1693⟩
private def endpoint_17_61_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_61_base : receiptBase endpoint_17_61_flag endpoint_17_61_sources = some 198817077075378393 := by decide +kernel
private theorem endpoint_17_61_w0 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 2 198817077075378393 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_w2 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 2 2 210768844694679691 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_p4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 4 198817077075378393 = some 210768844694679691 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 2 2 198817077075378393 210768844694679691 210768844694679691 endpoint_17_61_w0 endpoint_17_61_w2
private theorem endpoint_17_61_w4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 4 2 210768844694679691 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_p6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 6 198817077075378393 = some 210768844694679691 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 4 2 198817077075378393 210768844694679691 210768844694679691 endpoint_17_61_p4 endpoint_17_61_w4
private theorem endpoint_17_61_w6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 6 2 210768844694679691 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_p8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 8 198817077075378393 = some 210768844694679691 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 6 2 198817077075378393 210768844694679691 210768844694679691 endpoint_17_61_p6 endpoint_17_61_w6
private theorem endpoint_17_61_w8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 8 2 210768844694679691 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_p10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 10 198817077075378393 = some 210768844694679691 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 8 2 198817077075378393 210768844694679691 210768844694679691 endpoint_17_61_p8 endpoint_17_61_w8
private theorem endpoint_17_61_w10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 10 2 210768844694679691 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_p12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 12 198817077075378393 = some 210768844694679691 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 10 2 198817077075378393 210768844694679691 210768844694679691 endpoint_17_61_p10 endpoint_17_61_w10
private theorem endpoint_17_61_w12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 12 2 210768844694679691 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_p14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 14 198817077075378393 = some 210768844694679691 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 12 2 198817077075378393 210768844694679691 210768844694679691 endpoint_17_61_p12 endpoint_17_61_w12
private theorem endpoint_17_61_w14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 14 2 210768844694679691 = some 210768844694679691 := by decide +kernel
private theorem endpoint_17_61_p16 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 16 198817077075378393 = some 210768844694679691 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 14 2 198817077075378393 210768844694679691 210768844694679691 endpoint_17_61_p14 endpoint_17_61_w14
def endpoint_17_61 : CertifiedEndpoint :=
  ⟨⟨17, 61, 1693⟩, 210768844694679691, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_61_flag endpoint_17_61_sources 16 198817077075378393 210768844694679691 rfl endpoint_17_61_base endpoint_17_61_p16) (by decide)⟩
private def endpoint_17_62_flag : Flag := ⟨17, 62, 1620⟩
private def endpoint_17_62_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_62_base : receiptBase endpoint_17_62_flag endpoint_17_62_sources = some 193100032496454402 := by decide +kernel
private theorem endpoint_17_62_w0 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 2 193100032496454402 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_w2 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 2 2 209741460525237744 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_p4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 4 193100032496454402 = some 209741460525237744 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 2 2 193100032496454402 209741460525237744 209741460525237744 endpoint_17_62_w0 endpoint_17_62_w2
private theorem endpoint_17_62_w4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 4 2 209741460525237744 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_p6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 6 193100032496454402 = some 209741460525237744 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 4 2 193100032496454402 209741460525237744 209741460525237744 endpoint_17_62_p4 endpoint_17_62_w4
private theorem endpoint_17_62_w6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 6 2 209741460525237744 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_p8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 8 193100032496454402 = some 209741460525237744 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 6 2 193100032496454402 209741460525237744 209741460525237744 endpoint_17_62_p6 endpoint_17_62_w6
private theorem endpoint_17_62_w8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 8 2 209741460525237744 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_p10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 10 193100032496454402 = some 209741460525237744 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 8 2 193100032496454402 209741460525237744 209741460525237744 endpoint_17_62_p8 endpoint_17_62_w8
private theorem endpoint_17_62_w10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 10 2 209741460525237744 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_p12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 12 193100032496454402 = some 209741460525237744 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 10 2 193100032496454402 209741460525237744 209741460525237744 endpoint_17_62_p10 endpoint_17_62_w10
private theorem endpoint_17_62_w12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 12 2 209741460525237744 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_p14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 14 193100032496454402 = some 209741460525237744 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 12 2 193100032496454402 209741460525237744 209741460525237744 endpoint_17_62_p12 endpoint_17_62_w12
private theorem endpoint_17_62_w14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 14 2 209741460525237744 = some 209741460525237744 := by decide +kernel
private theorem endpoint_17_62_p16 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 16 193100032496454402 = some 209741460525237744 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 14 2 193100032496454402 209741460525237744 209741460525237744 endpoint_17_62_p14 endpoint_17_62_w14
def endpoint_17_62 : CertifiedEndpoint :=
  ⟨⟨17, 62, 1620⟩, 209741460525237744, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_62_flag endpoint_17_62_sources 16 193100032496454402 209741460525237744 rfl endpoint_17_62_base endpoint_17_62_p16) (by decide)⟩
private def endpoint_17_63_flag : Flag := ⟨17, 63, 1545⟩
private def endpoint_17_63_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_63_base : receiptBase endpoint_17_63_flag endpoint_17_63_sources = some 188425159708908919 := by decide +kernel
private theorem endpoint_17_63_w0 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 2 188425159708908919 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_w2 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 2 2 192628224159834544 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_p4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 4 188425159708908919 = some 192628224159834544 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 2 2 188425159708908919 192628224159834544 192628224159834544 endpoint_17_63_w0 endpoint_17_63_w2
private theorem endpoint_17_63_w4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 4 2 192628224159834544 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_p6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 6 188425159708908919 = some 192628224159834544 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 4 2 188425159708908919 192628224159834544 192628224159834544 endpoint_17_63_p4 endpoint_17_63_w4
private theorem endpoint_17_63_w6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 6 2 192628224159834544 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_p8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 8 188425159708908919 = some 192628224159834544 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 6 2 188425159708908919 192628224159834544 192628224159834544 endpoint_17_63_p6 endpoint_17_63_w6
private theorem endpoint_17_63_w8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 8 2 192628224159834544 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_p10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 10 188425159708908919 = some 192628224159834544 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 8 2 188425159708908919 192628224159834544 192628224159834544 endpoint_17_63_p8 endpoint_17_63_w8
private theorem endpoint_17_63_w10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 10 2 192628224159834544 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_p12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 12 188425159708908919 = some 192628224159834544 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 10 2 188425159708908919 192628224159834544 192628224159834544 endpoint_17_63_p10 endpoint_17_63_w10
private theorem endpoint_17_63_w12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 12 2 192628224159834544 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_p14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 14 188425159708908919 = some 192628224159834544 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 12 2 188425159708908919 192628224159834544 192628224159834544 endpoint_17_63_p12 endpoint_17_63_w12
private theorem endpoint_17_63_w14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 14 2 192628224159834544 = some 192628224159834544 := by decide +kernel
private theorem endpoint_17_63_p16 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 16 188425159708908919 = some 192628224159834544 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 14 2 188425159708908919 192628224159834544 192628224159834544 endpoint_17_63_p14 endpoint_17_63_w14
def endpoint_17_63 : CertifiedEndpoint :=
  ⟨⟨17, 63, 1545⟩, 192628224159834544, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_63_flag endpoint_17_63_sources 16 188425159708908919 192628224159834544 rfl endpoint_17_63_base endpoint_17_63_p16) (by decide)⟩
private def endpoint_17_64_flag : Flag := ⟨17, 64, 1468⟩
private def endpoint_17_64_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_64_base : receiptBase endpoint_17_64_flag endpoint_17_64_sources = some 181655337410133766 := by decide +kernel
private theorem endpoint_17_64_w0 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 2 181655337410133766 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_w2 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 2 2 190628065643070832 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_p4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 4 181655337410133766 = some 190628065643070832 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 2 2 181655337410133766 190628065643070832 190628065643070832 endpoint_17_64_w0 endpoint_17_64_w2
private theorem endpoint_17_64_w4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 4 2 190628065643070832 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_p6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 6 181655337410133766 = some 190628065643070832 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 4 2 181655337410133766 190628065643070832 190628065643070832 endpoint_17_64_p4 endpoint_17_64_w4
private theorem endpoint_17_64_w6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 6 2 190628065643070832 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_p8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 8 181655337410133766 = some 190628065643070832 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 6 2 181655337410133766 190628065643070832 190628065643070832 endpoint_17_64_p6 endpoint_17_64_w6
private theorem endpoint_17_64_w8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 8 2 190628065643070832 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_p10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 10 181655337410133766 = some 190628065643070832 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 8 2 181655337410133766 190628065643070832 190628065643070832 endpoint_17_64_p8 endpoint_17_64_w8
private theorem endpoint_17_64_w10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 10 2 190628065643070832 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_p12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 12 181655337410133766 = some 190628065643070832 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 10 2 181655337410133766 190628065643070832 190628065643070832 endpoint_17_64_p10 endpoint_17_64_w10
private theorem endpoint_17_64_w12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 12 2 190628065643070832 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_p14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 14 181655337410133766 = some 190628065643070832 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 12 2 181655337410133766 190628065643070832 190628065643070832 endpoint_17_64_p12 endpoint_17_64_w12
private theorem endpoint_17_64_w14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 14 2 190628065643070832 = some 190628065643070832 := by decide +kernel
private theorem endpoint_17_64_p16 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 16 181655337410133766 = some 190628065643070832 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 14 2 181655337410133766 190628065643070832 190628065643070832 endpoint_17_64_p14 endpoint_17_64_w14
def endpoint_17_64 : CertifiedEndpoint :=
  ⟨⟨17, 64, 1468⟩, 190628065643070832, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_64_flag endpoint_17_64_sources 16 181655337410133766 190628065643070832 rfl endpoint_17_64_base endpoint_17_64_p16) (by decide)⟩
private def endpoint_17_65_flag : Flag := ⟨17, 65, 1390⟩
private def endpoint_17_65_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_65_base : receiptBase endpoint_17_65_flag endpoint_17_65_sources = some 174499039992287423 := by decide +kernel
private theorem endpoint_17_65_w0 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 2 174499039992287423 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_w2 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 2 2 188348864671221441 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_p4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 4 174499039992287423 = some 188348864671221441 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 2 2 174499039992287423 188348864671221441 188348864671221441 endpoint_17_65_w0 endpoint_17_65_w2
private theorem endpoint_17_65_w4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 4 2 188348864671221441 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_p6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 6 174499039992287423 = some 188348864671221441 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 4 2 174499039992287423 188348864671221441 188348864671221441 endpoint_17_65_p4 endpoint_17_65_w4
private theorem endpoint_17_65_w6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 6 2 188348864671221441 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_p8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 8 174499039992287423 = some 188348864671221441 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 6 2 174499039992287423 188348864671221441 188348864671221441 endpoint_17_65_p6 endpoint_17_65_w6
private theorem endpoint_17_65_w8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 8 2 188348864671221441 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_p10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 10 174499039992287423 = some 188348864671221441 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 8 2 174499039992287423 188348864671221441 188348864671221441 endpoint_17_65_p8 endpoint_17_65_w8
private theorem endpoint_17_65_w10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 10 2 188348864671221441 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_p12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 12 174499039992287423 = some 188348864671221441 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 10 2 174499039992287423 188348864671221441 188348864671221441 endpoint_17_65_p10 endpoint_17_65_w10
private theorem endpoint_17_65_w12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 12 2 188348864671221441 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_p14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 14 174499039992287423 = some 188348864671221441 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 12 2 174499039992287423 188348864671221441 188348864671221441 endpoint_17_65_p12 endpoint_17_65_w12
private theorem endpoint_17_65_w14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 14 2 188348864671221441 = some 188348864671221441 := by decide +kernel
private theorem endpoint_17_65_p16 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 16 174499039992287423 = some 188348864671221441 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 14 2 174499039992287423 188348864671221441 188348864671221441 endpoint_17_65_p14 endpoint_17_65_w14
def endpoint_17_65 : CertifiedEndpoint :=
  ⟨⟨17, 65, 1390⟩, 188348864671221441, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_65_flag endpoint_17_65_sources 16 174499039992287423 188348864671221441 rfl endpoint_17_65_base endpoint_17_65_p16) (by decide)⟩
private def endpoint_17_66_flag : Flag := ⟨17, 66, 1309⟩
private def endpoint_17_66_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_66_base : receiptBase endpoint_17_66_flag endpoint_17_66_sources = some 166700357523998524 := by decide +kernel
private theorem endpoint_17_66_w0 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 2 166700357523998524 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_w2 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 2 2 185638773118209054 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_p4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 4 166700357523998524 = some 185638773118209054 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 2 2 166700357523998524 185638773118209054 185638773118209054 endpoint_17_66_w0 endpoint_17_66_w2
private theorem endpoint_17_66_w4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 4 2 185638773118209054 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_p6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 6 166700357523998524 = some 185638773118209054 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 4 2 166700357523998524 185638773118209054 185638773118209054 endpoint_17_66_p4 endpoint_17_66_w4
private theorem endpoint_17_66_w6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 6 2 185638773118209054 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_p8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 8 166700357523998524 = some 185638773118209054 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 6 2 166700357523998524 185638773118209054 185638773118209054 endpoint_17_66_p6 endpoint_17_66_w6
private theorem endpoint_17_66_w8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 8 2 185638773118209054 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_p10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 10 166700357523998524 = some 185638773118209054 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 8 2 166700357523998524 185638773118209054 185638773118209054 endpoint_17_66_p8 endpoint_17_66_w8
private theorem endpoint_17_66_w10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 10 2 185638773118209054 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_p12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 12 166700357523998524 = some 185638773118209054 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 10 2 166700357523998524 185638773118209054 185638773118209054 endpoint_17_66_p10 endpoint_17_66_w10
private theorem endpoint_17_66_w12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 12 2 185638773118209054 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_p14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 14 166700357523998524 = some 185638773118209054 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 12 2 166700357523998524 185638773118209054 185638773118209054 endpoint_17_66_p12 endpoint_17_66_w12
private theorem endpoint_17_66_w14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 14 2 185638773118209054 = some 185638773118209054 := by decide +kernel
private theorem endpoint_17_66_p16 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 16 166700357523998524 = some 185638773118209054 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 14 2 166700357523998524 185638773118209054 185638773118209054 endpoint_17_66_p14 endpoint_17_66_w14
def endpoint_17_66 : CertifiedEndpoint :=
  ⟨⟨17, 66, 1309⟩, 185638773118209054, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_66_flag endpoint_17_66_sources 16 166700357523998524 185638773118209054 rfl endpoint_17_66_base endpoint_17_66_p16) (by decide)⟩
private def endpoint_17_67_flag : Flag := ⟨17, 67, 1226⟩
private def endpoint_17_67_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_17_67_base : receiptBase endpoint_17_67_flag endpoint_17_67_sources = some 159910545047900262 := by decide +kernel
private theorem endpoint_17_67_w0 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 2 159910545047900262 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_w2 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 2 2 172004246031847601 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_p4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 4 159910545047900262 = some 172004246031847601 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 2 2 159910545047900262 172004246031847601 172004246031847601 endpoint_17_67_w0 endpoint_17_67_w2
private theorem endpoint_17_67_w4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 4 2 172004246031847601 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_p6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 6 159910545047900262 = some 172004246031847601 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 4 2 159910545047900262 172004246031847601 172004246031847601 endpoint_17_67_p4 endpoint_17_67_w4
private theorem endpoint_17_67_w6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 6 2 172004246031847601 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_p8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 8 159910545047900262 = some 172004246031847601 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 6 2 159910545047900262 172004246031847601 172004246031847601 endpoint_17_67_p6 endpoint_17_67_w6
private theorem endpoint_17_67_w8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 8 2 172004246031847601 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_p10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 10 159910545047900262 = some 172004246031847601 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 8 2 159910545047900262 172004246031847601 172004246031847601 endpoint_17_67_p8 endpoint_17_67_w8
private theorem endpoint_17_67_w10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 10 2 172004246031847601 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_p12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 12 159910545047900262 = some 172004246031847601 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 10 2 159910545047900262 172004246031847601 172004246031847601 endpoint_17_67_p10 endpoint_17_67_w10
private theorem endpoint_17_67_w12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 12 2 172004246031847601 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_p14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 14 159910545047900262 = some 172004246031847601 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 12 2 159910545047900262 172004246031847601 172004246031847601 endpoint_17_67_p12 endpoint_17_67_w12
private theorem endpoint_17_67_w14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 14 2 172004246031847601 = some 172004246031847601 := by decide +kernel
private theorem endpoint_17_67_p16 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 16 159910545047900262 = some 172004246031847601 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 14 2 159910545047900262 172004246031847601 172004246031847601 endpoint_17_67_p14 endpoint_17_67_w14
def endpoint_17_67 : CertifiedEndpoint :=
  ⟨⟨17, 67, 1226⟩, 172004246031847601, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_17_67_flag endpoint_17_67_sources 16 159910545047900262 172004246031847601 rfl endpoint_17_67_base endpoint_17_67_p16) (by decide)⟩
private def endpoint_17_68_flag : Flag := ⟨17, 68, 1141⟩
private def endpoint_17_68_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_17_68_base : receiptBase endpoint_17_68_flag endpoint_17_68_sources = some 150990053441160158 := by decide +kernel
private theorem endpoint_17_68_w0 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 2 150990053441160158 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_w2 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 2 2 168368531427474900 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_p4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 4 150990053441160158 = some 168368531427474900 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 2 2 150990053441160158 168368531427474900 168368531427474900 endpoint_17_68_w0 endpoint_17_68_w2
private theorem endpoint_17_68_w4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 4 2 168368531427474900 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_p6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 6 150990053441160158 = some 168368531427474900 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 4 2 150990053441160158 168368531427474900 168368531427474900 endpoint_17_68_p4 endpoint_17_68_w4
private theorem endpoint_17_68_w6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 6 2 168368531427474900 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_p8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 8 150990053441160158 = some 168368531427474900 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 6 2 150990053441160158 168368531427474900 168368531427474900 endpoint_17_68_p6 endpoint_17_68_w6
private theorem endpoint_17_68_w8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 8 2 168368531427474900 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_p10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 10 150990053441160158 = some 168368531427474900 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 8 2 150990053441160158 168368531427474900 168368531427474900 endpoint_17_68_p8 endpoint_17_68_w8
private theorem endpoint_17_68_w10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 10 2 168368531427474900 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_p12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 12 150990053441160158 = some 168368531427474900 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 10 2 150990053441160158 168368531427474900 168368531427474900 endpoint_17_68_p10 endpoint_17_68_w10
private theorem endpoint_17_68_w12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 12 2 168368531427474900 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_p14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 14 150990053441160158 = some 168368531427474900 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 12 2 150990053441160158 168368531427474900 168368531427474900 endpoint_17_68_p12 endpoint_17_68_w12
private theorem endpoint_17_68_w14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 14 2 168368531427474900 = some 168368531427474900 := by decide +kernel
private theorem endpoint_17_68_p16 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 16 150990053441160158 = some 168368531427474900 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 14 2 150990053441160158 168368531427474900 168368531427474900 endpoint_17_68_p14 endpoint_17_68_w14
def endpoint_17_68 : CertifiedEndpoint :=
  ⟨⟨17, 68, 1141⟩, 168368531427474900, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_17_68_flag endpoint_17_68_sources 16 150990053441160158 168368531427474900 rfl endpoint_17_68_base endpoint_17_68_p16) (by decide)⟩
def endpoint_17_69 : CertifiedEndpoint :=
  ⟨⟨17, 69, 1053⟩, 259279282501882522, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_70 : CertifiedEndpoint :=
  ⟨⟨17, 70, 963⟩, 240077600482950891, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_71 : CertifiedEndpoint :=
  ⟨⟨17, 71, 871⟩, 219576383622186916, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_72 : CertifiedEndpoint :=
  ⟨⟨17, 72, 776⟩, 197481634062009484, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_73 : CertifiedEndpoint :=
  ⟨⟨17, 73, 678⟩, 173755005382418409, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_74 : CertifiedEndpoint :=
  ⟨⟨17, 74, 578⟩, 148635106167661202, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_75 : CertifiedEndpoint :=
  ⟨⟨17, 75, 474⟩, 121533940702575637, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_76 : CertifiedEndpoint :=
  ⟨⟨17, 76, 367⟩, 92685856858075871, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_77 : CertifiedEndpoint :=
  ⟨⟨17, 77, 258⟩, 62342245358409477, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_78 : CertifiedEndpoint :=
  ⟨⟨17, 78, 145⟩, 29889546208414105, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_18 : CertifiedEndpoint :=
  ⟨⟨18, 18, 3478⟩, 154118244656062446, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_19 : CertifiedEndpoint :=
  ⟨⟨18, 19, 3444⟩, 157694322462654388, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_20 : CertifiedEndpoint :=
  ⟨⟨18, 20, 3409⟩, 161121893726030011, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_21 : CertifiedEndpoint :=
  ⟨⟨18, 21, 3374⟩, 174613586452649927, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_22 : CertifiedEndpoint :=
  ⟨⟨18, 22, 3338⟩, 187727982664044482, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_23 : CertifiedEndpoint :=
  ⟨⟨18, 23, 3301⟩, 200451527107225858, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_24 : CertifiedEndpoint :=
  ⟨⟨18, 24, 3264⟩, 212836190225711784, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_25 : CertifiedEndpoint :=
  ⟨⟨18, 25, 3227⟩, 224881972019502260, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_26 : CertifiedEndpoint :=
  ⟨⟨18, 26, 3188⟩, 236439747424935768, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_27 : CertifiedEndpoint :=
  ⟨⟨18, 27, 3149⟩, 247640567835023402, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_28 : CertifiedEndpoint :=
  ⟨⟨18, 28, 3110⟩, 258484433249765162, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_18_29_flag : Flag := ⟨18, 29, 3070⟩
private def endpoint_18_29_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_29_base : receiptBase endpoint_18_29_flag endpoint_18_29_sources = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_w0 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_w2 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 2 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p4 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 4 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 2 2 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_w0 endpoint_18_29_w2
private theorem endpoint_18_29_w4 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 4 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p6 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 6 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 4 2 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_p4 endpoint_18_29_w4
private theorem endpoint_18_29_w6 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 6 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p8 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 8 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 6 2 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_p6 endpoint_18_29_w6
private theorem endpoint_18_29_w8 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 8 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p10 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 10 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 8 2 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_p8 endpoint_18_29_w8
private theorem endpoint_18_29_w10 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 10 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p12 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 12 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 10 2 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_p10 endpoint_18_29_w10
private theorem endpoint_18_29_w12 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 12 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p14 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 14 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 12 2 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_p12 endpoint_18_29_w12
private theorem endpoint_18_29_w14 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 14 2 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p16 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 16 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 14 2 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_p14 endpoint_18_29_w14
private theorem endpoint_18_29_w16 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 16 1 185825122316280591 = some 185825122316280591 := by decide +kernel
private theorem endpoint_18_29_p17 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 17 185825122316280591 = some 185825122316280591 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 16 1 185825122316280591 185825122316280591 185825122316280591 endpoint_18_29_p16 endpoint_18_29_w16
def endpoint_18_29 : CertifiedEndpoint :=
  ⟨⟨18, 29, 3070⟩, 185825122316280591, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_29_flag endpoint_18_29_sources 17 185825122316280591 185825122316280591 rfl endpoint_18_29_base endpoint_18_29_p17) (by decide)⟩
private def endpoint_18_30_flag : Flag := ⟨18, 30, 3029⟩
private def endpoint_18_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_30_base : receiptBase endpoint_18_30_flag endpoint_18_30_sources = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_w0 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_w2 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 2 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 4 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 2 2 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_w0 endpoint_18_30_w2
private theorem endpoint_18_30_w4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 4 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 6 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 4 2 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_p4 endpoint_18_30_w4
private theorem endpoint_18_30_w6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 6 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 8 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 6 2 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_p6 endpoint_18_30_w6
private theorem endpoint_18_30_w8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 8 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 10 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 8 2 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_p8 endpoint_18_30_w8
private theorem endpoint_18_30_w10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 10 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 12 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 10 2 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_p10 endpoint_18_30_w10
private theorem endpoint_18_30_w12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 12 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 14 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 12 2 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_p12 endpoint_18_30_w12
private theorem endpoint_18_30_w14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 14 2 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 16 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 14 2 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_p14 endpoint_18_30_w14
private theorem endpoint_18_30_w16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 16 1 188567516655467465 = some 188567516655467465 := by decide +kernel
private theorem endpoint_18_30_p17 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 17 188567516655467465 = some 188567516655467465 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 16 1 188567516655467465 188567516655467465 188567516655467465 endpoint_18_30_p16 endpoint_18_30_w16
def endpoint_18_30 : CertifiedEndpoint :=
  ⟨⟨18, 30, 3029⟩, 188567516655467465, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_30_flag endpoint_18_30_sources 17 188567516655467465 188567516655467465 rfl endpoint_18_30_base endpoint_18_30_p17) (by decide)⟩
private def endpoint_18_31_flag : Flag := ⟨18, 31, 2987⟩
private def endpoint_18_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_31_base : receiptBase endpoint_18_31_flag endpoint_18_31_sources = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_w0 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_w2 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 2 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 4 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 2 2 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_w0 endpoint_18_31_w2
private theorem endpoint_18_31_w4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 4 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 6 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 4 2 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_p4 endpoint_18_31_w4
private theorem endpoint_18_31_w6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 6 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 8 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 6 2 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_p6 endpoint_18_31_w6
private theorem endpoint_18_31_w8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 8 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 10 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 8 2 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_p8 endpoint_18_31_w8
private theorem endpoint_18_31_w10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 10 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 12 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 10 2 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_p10 endpoint_18_31_w10
private theorem endpoint_18_31_w12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 12 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 14 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 12 2 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_p12 endpoint_18_31_w12
private theorem endpoint_18_31_w14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 14 2 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 16 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 14 2 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_p14 endpoint_18_31_w14
private theorem endpoint_18_31_w16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 16 1 191107152639793977 = some 191107152639793977 := by decide +kernel
private theorem endpoint_18_31_p17 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 17 191107152639793977 = some 191107152639793977 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 16 1 191107152639793977 191107152639793977 191107152639793977 endpoint_18_31_p16 endpoint_18_31_w16
def endpoint_18_31 : CertifiedEndpoint :=
  ⟨⟨18, 31, 2987⟩, 191107152639793977, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_31_flag endpoint_18_31_sources 17 191107152639793977 191107152639793977 rfl endpoint_18_31_base endpoint_18_31_p17) (by decide)⟩

def endpointBlock11 : List CertifiedEndpoint := [
  endpoint_16_37, endpoint_16_38, endpoint_16_39, endpoint_16_40, endpoint_16_41, endpoint_16_42, endpoint_16_43,
  endpoint_16_44, endpoint_16_45, endpoint_16_46, endpoint_16_47, endpoint_16_48, endpoint_16_49, endpoint_16_50,
  endpoint_16_51, endpoint_16_52, endpoint_16_53, endpoint_16_54, endpoint_16_55, endpoint_16_56, endpoint_16_57,
  endpoint_16_58, endpoint_16_59, endpoint_16_60, endpoint_16_61, endpoint_16_62, endpoint_16_63, endpoint_16_64,
  endpoint_16_65, endpoint_16_66, endpoint_16_67, endpoint_16_68, endpoint_16_69, endpoint_16_70, endpoint_16_71,
  endpoint_16_72, endpoint_16_73, endpoint_16_74, endpoint_16_75, endpoint_16_76, endpoint_16_77, endpoint_16_78,
  endpoint_16_79, endpoint_16_80, endpoint_16_81, endpoint_17_17, endpoint_17_18, endpoint_17_19, endpoint_17_20,
  endpoint_17_21, endpoint_17_22, endpoint_17_23, endpoint_17_24, endpoint_17_25, endpoint_17_26, endpoint_17_27,
  endpoint_17_28, endpoint_17_29, endpoint_17_30, endpoint_17_31, endpoint_17_32, endpoint_17_33, endpoint_17_34,
  endpoint_17_35, endpoint_17_36, endpoint_17_37, endpoint_17_38, endpoint_17_39, endpoint_17_40, endpoint_17_41,
  endpoint_17_42, endpoint_17_43, endpoint_17_44, endpoint_17_45, endpoint_17_46, endpoint_17_47, endpoint_17_48,
  endpoint_17_49, endpoint_17_50, endpoint_17_51, endpoint_17_52, endpoint_17_53, endpoint_17_54, endpoint_17_55,
  endpoint_17_56, endpoint_17_57, endpoint_17_58, endpoint_17_59, endpoint_17_60, endpoint_17_61, endpoint_17_62,
  endpoint_17_63, endpoint_17_64, endpoint_17_65, endpoint_17_66, endpoint_17_67, endpoint_17_68, endpoint_17_69,
  endpoint_17_70, endpoint_17_71, endpoint_17_72, endpoint_17_73, endpoint_17_74, endpoint_17_75, endpoint_17_76,
  endpoint_17_77, endpoint_17_78, endpoint_18_18, endpoint_18_19, endpoint_18_20, endpoint_18_21, endpoint_18_22,
  endpoint_18_23, endpoint_18_24, endpoint_18_25, endpoint_18_26, endpoint_18_27, endpoint_18_28, endpoint_18_29,
  endpoint_18_30, endpoint_18_31
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
