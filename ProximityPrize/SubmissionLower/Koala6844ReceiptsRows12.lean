import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_18_32_flag : Flag := ⟨18, 32, 2945⟩
private def endpoint_18_32_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_32_base : receiptBase endpoint_18_32_flag endpoint_18_32_sources = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_w0 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_w2 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 2 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 4 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 2 2 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_w0 endpoint_18_32_w2
private theorem endpoint_18_32_w4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 4 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 6 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 4 2 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_p4 endpoint_18_32_w4
private theorem endpoint_18_32_w6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 6 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 8 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 6 2 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_p6 endpoint_18_32_w6
private theorem endpoint_18_32_w8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 8 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 10 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 8 2 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_p8 endpoint_18_32_w8
private theorem endpoint_18_32_w10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 10 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 12 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 10 2 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_p10 endpoint_18_32_w10
private theorem endpoint_18_32_w12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 12 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 14 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 12 2 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_p12 endpoint_18_32_w12
private theorem endpoint_18_32_w14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 14 2 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 16 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 14 2 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_p14 endpoint_18_32_w14
private theorem endpoint_18_32_w16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 16 1 193760814891023837 = some 193760814891023837 := by decide +kernel
private theorem endpoint_18_32_p17 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 17 193760814891023837 = some 193760814891023837 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 16 1 193760814891023837 193760814891023837 193760814891023837 endpoint_18_32_p16 endpoint_18_32_w16
def endpoint_18_32 : CertifiedEndpoint :=
  ⟨⟨18, 32, 2945⟩, 193760814891023837, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_32_flag endpoint_18_32_sources 17 193760814891023837 193760814891023837 rfl endpoint_18_32_base endpoint_18_32_p17) (by decide)⟩
private def endpoint_18_33_flag : Flag := ⟨18, 33, 2902⟩
private def endpoint_18_33_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_33_base : receiptBase endpoint_18_33_flag endpoint_18_33_sources = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_w0 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_w2 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 2 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 4 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 2 2 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_w0 endpoint_18_33_w2
private theorem endpoint_18_33_w4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 4 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 6 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 4 2 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_p4 endpoint_18_33_w4
private theorem endpoint_18_33_w6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 6 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 8 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 6 2 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_p6 endpoint_18_33_w6
private theorem endpoint_18_33_w8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 8 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 10 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 8 2 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_p8 endpoint_18_33_w8
private theorem endpoint_18_33_w10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 10 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 12 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 10 2 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_p10 endpoint_18_33_w10
private theorem endpoint_18_33_w12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 12 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 14 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 12 2 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_p12 endpoint_18_33_w12
private theorem endpoint_18_33_w14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 14 2 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 16 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 14 2 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_p14 endpoint_18_33_w14
private theorem endpoint_18_33_w16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 16 1 195962255405536335 = some 195962255405536335 := by decide +kernel
private theorem endpoint_18_33_p17 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 17 195962255405536335 = some 195962255405536335 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 16 1 195962255405536335 195962255405536335 195962255405536335 endpoint_18_33_p16 endpoint_18_33_w16
def endpoint_18_33 : CertifiedEndpoint :=
  ⟨⟨18, 33, 2902⟩, 195962255405536335, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_33_flag endpoint_18_33_sources 17 195962255405536335 195962255405536335 rfl endpoint_18_33_base endpoint_18_33_p17) (by decide)⟩
private def endpoint_18_34_flag : Flag := ⟨18, 34, 2859⟩
private def endpoint_18_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_34_base : receiptBase endpoint_18_34_flag endpoint_18_34_sources = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_w0 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_w2 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 2 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 4 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 2 2 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_w0 endpoint_18_34_w2
private theorem endpoint_18_34_w4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 4 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 6 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 4 2 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_p4 endpoint_18_34_w4
private theorem endpoint_18_34_w6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 6 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 8 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 6 2 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_p6 endpoint_18_34_w6
private theorem endpoint_18_34_w8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 8 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 10 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 8 2 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_p8 endpoint_18_34_w8
private theorem endpoint_18_34_w10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 10 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 12 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 10 2 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_p10 endpoint_18_34_w10
private theorem endpoint_18_34_w12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 12 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 14 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 12 2 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_p12 endpoint_18_34_w12
private theorem endpoint_18_34_w14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 14 2 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 16 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 14 2 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_p14 endpoint_18_34_w14
private theorem endpoint_18_34_w16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 16 1 198453720213583241 = some 198453720213583241 := by decide +kernel
private theorem endpoint_18_34_p17 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 17 198453720213583241 = some 198453720213583241 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 16 1 198453720213583241 198453720213583241 198453720213583241 endpoint_18_34_p16 endpoint_18_34_w16
def endpoint_18_34 : CertifiedEndpoint :=
  ⟨⟨18, 34, 2859⟩, 198453720213583241, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_34_flag endpoint_18_34_sources 17 198453720213583241 198453720213583241 rfl endpoint_18_34_base endpoint_18_34_p17) (by decide)⟩
private def endpoint_18_35_flag : Flag := ⟨18, 35, 2814⟩
private def endpoint_18_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_35_base : receiptBase endpoint_18_35_flag endpoint_18_35_sources = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_w0 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_w2 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 2 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 4 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 2 2 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_w0 endpoint_18_35_w2
private theorem endpoint_18_35_w4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 4 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 6 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 4 2 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_p4 endpoint_18_35_w4
private theorem endpoint_18_35_w6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 6 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 8 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 6 2 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_p6 endpoint_18_35_w6
private theorem endpoint_18_35_w8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 8 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 10 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 8 2 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_p8 endpoint_18_35_w8
private theorem endpoint_18_35_w10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 10 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 12 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 10 2 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_p10 endpoint_18_35_w10
private theorem endpoint_18_35_w12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 12 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 14 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 12 2 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_p12 endpoint_18_35_w12
private theorem endpoint_18_35_w14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 14 2 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 16 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 14 2 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_p14 endpoint_18_35_w14
private theorem endpoint_18_35_w16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 16 1 200194921513468108 = some 200194921513468108 := by decide +kernel
private theorem endpoint_18_35_p17 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 17 200194921513468108 = some 200194921513468108 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 16 1 200194921513468108 200194921513468108 200194921513468108 endpoint_18_35_p16 endpoint_18_35_w16
def endpoint_18_35 : CertifiedEndpoint :=
  ⟨⟨18, 35, 2814⟩, 200194921513468108, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_35_flag endpoint_18_35_sources 17 200194921513468108 200194921513468108 rfl endpoint_18_35_base endpoint_18_35_p17) (by decide)⟩
private def endpoint_18_36_flag : Flag := ⟨18, 36, 2769⟩
private def endpoint_18_36_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_36_base : receiptBase endpoint_18_36_flag endpoint_18_36_sources = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_w0 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_w2 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 2 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 4 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 2 2 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_w0 endpoint_18_36_w2
private theorem endpoint_18_36_w4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 4 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 6 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 4 2 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_p4 endpoint_18_36_w4
private theorem endpoint_18_36_w6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 6 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 8 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 6 2 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_p6 endpoint_18_36_w6
private theorem endpoint_18_36_w8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 8 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 10 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 8 2 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_p8 endpoint_18_36_w8
private theorem endpoint_18_36_w10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 10 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 12 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 10 2 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_p10 endpoint_18_36_w10
private theorem endpoint_18_36_w12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 12 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 14 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 12 2 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_p12 endpoint_18_36_w12
private theorem endpoint_18_36_w14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 14 2 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 16 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 14 2 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_p14 endpoint_18_36_w14
private theorem endpoint_18_36_w16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 16 1 201782971243175537 = some 201782971243175537 := by decide +kernel
private theorem endpoint_18_36_p17 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 17 201782971243175537 = some 201782971243175537 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 16 1 201782971243175537 201782971243175537 201782971243175537 endpoint_18_36_p16 endpoint_18_36_w16
def endpoint_18_36 : CertifiedEndpoint :=
  ⟨⟨18, 36, 2769⟩, 201782971243175537, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_36_flag endpoint_18_36_sources 17 201782971243175537 201782971243175537 rfl endpoint_18_36_base endpoint_18_36_p17) (by decide)⟩
private def endpoint_18_37_flag : Flag := ⟨18, 37, 2723⟩
private def endpoint_18_37_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_37_base : receiptBase endpoint_18_37_flag endpoint_18_37_sources = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_w0 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_w2 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 2 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 4 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 2 2 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_w0 endpoint_18_37_w2
private theorem endpoint_18_37_w4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 4 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 6 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 4 2 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_p4 endpoint_18_37_w4
private theorem endpoint_18_37_w6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 6 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 8 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 6 2 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_p6 endpoint_18_37_w6
private theorem endpoint_18_37_w8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 8 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 10 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 8 2 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_p8 endpoint_18_37_w8
private theorem endpoint_18_37_w10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 10 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 12 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 10 2 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_p10 endpoint_18_37_w10
private theorem endpoint_18_37_w12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 12 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 14 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 12 2 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_p12 endpoint_18_37_w12
private theorem endpoint_18_37_w14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 14 2 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 16 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 14 2 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_p14 endpoint_18_37_w14
private theorem endpoint_18_37_w16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 16 1 203144277237742041 = some 203144277237742041 := by decide +kernel
private theorem endpoint_18_37_p17 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 17 203144277237742041 = some 203144277237742041 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 16 1 203144277237742041 203144277237742041 203144277237742041 endpoint_18_37_p16 endpoint_18_37_w16
def endpoint_18_37 : CertifiedEndpoint :=
  ⟨⟨18, 37, 2723⟩, 203144277237742041, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_37_flag endpoint_18_37_sources 17 203144277237742041 203144277237742041 rfl endpoint_18_37_base endpoint_18_37_p17) (by decide)⟩
private def endpoint_18_38_flag : Flag := ⟨18, 38, 2676⟩
private def endpoint_18_38_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_38_base : receiptBase endpoint_18_38_flag endpoint_18_38_sources = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_w0 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_w2 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 2 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 4 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 2 2 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_w0 endpoint_18_38_w2
private theorem endpoint_18_38_w4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 4 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 6 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 4 2 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_p4 endpoint_18_38_w4
private theorem endpoint_18_38_w6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 6 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 8 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 6 2 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_p6 endpoint_18_38_w6
private theorem endpoint_18_38_w8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 8 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 10 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 8 2 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_p8 endpoint_18_38_w8
private theorem endpoint_18_38_w10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 10 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 12 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 10 2 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_p10 endpoint_18_38_w10
private theorem endpoint_18_38_w12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 12 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 14 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 12 2 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_p12 endpoint_18_38_w12
private theorem endpoint_18_38_w14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 14 2 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 16 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 14 2 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_p14 endpoint_18_38_w14
private theorem endpoint_18_38_w16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 16 1 204273790544304626 = some 204273790544304626 := by decide +kernel
private theorem endpoint_18_38_p17 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 17 204273790544304626 = some 204273790544304626 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 16 1 204273790544304626 204273790544304626 204273790544304626 endpoint_18_38_p16 endpoint_18_38_w16
def endpoint_18_38 : CertifiedEndpoint :=
  ⟨⟨18, 38, 2676⟩, 204273790544304626, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_38_flag endpoint_18_38_sources 17 204273790544304626 204273790544304626 rfl endpoint_18_38_base endpoint_18_38_p17) (by decide)⟩
private def endpoint_18_39_flag : Flag := ⟨18, 39, 2628⟩
private def endpoint_18_39_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_39_base : receiptBase endpoint_18_39_flag endpoint_18_39_sources = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_w0 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_w2 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 2 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 4 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 2 2 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_w0 endpoint_18_39_w2
private theorem endpoint_18_39_w4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 4 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 6 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 4 2 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_p4 endpoint_18_39_w4
private theorem endpoint_18_39_w6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 6 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 8 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 6 2 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_p6 endpoint_18_39_w6
private theorem endpoint_18_39_w8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 8 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 10 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 8 2 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_p8 endpoint_18_39_w8
private theorem endpoint_18_39_w10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 10 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 12 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 10 2 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_p10 endpoint_18_39_w10
private theorem endpoint_18_39_w12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 12 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 14 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 12 2 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_p12 endpoint_18_39_w12
private theorem endpoint_18_39_w14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 14 2 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 16 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 14 2 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_p14 endpoint_18_39_w14
private theorem endpoint_18_39_w16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 16 1 205166462210000301 = some 205166462210000301 := by decide +kernel
private theorem endpoint_18_39_p17 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 17 205166462210000301 = some 205166462210000301 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 16 1 205166462210000301 205166462210000301 205166462210000301 endpoint_18_39_p16 endpoint_18_39_w16
def endpoint_18_39 : CertifiedEndpoint :=
  ⟨⟨18, 39, 2628⟩, 205166462210000301, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_39_flag endpoint_18_39_sources 17 205166462210000301 205166462210000301 rfl endpoint_18_39_base endpoint_18_39_p17) (by decide)⟩
private def endpoint_18_40_flag : Flag := ⟨18, 40, 2580⟩
private def endpoint_18_40_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_40_base : receiptBase endpoint_18_40_flag endpoint_18_40_sources = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_w0 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_w2 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 2 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 4 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 2 2 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_w0 endpoint_18_40_w2
private theorem endpoint_18_40_w4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 4 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 6 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 4 2 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_p4 endpoint_18_40_w4
private theorem endpoint_18_40_w6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 6 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 8 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 6 2 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_p6 endpoint_18_40_w6
private theorem endpoint_18_40_w8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 8 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 10 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 8 2 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_p8 endpoint_18_40_w8
private theorem endpoint_18_40_w10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 10 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 12 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 10 2 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_p10 endpoint_18_40_w10
private theorem endpoint_18_40_w12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 12 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 14 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 12 2 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_p12 endpoint_18_40_w12
private theorem endpoint_18_40_w14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 14 2 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 16 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 14 2 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_p14 endpoint_18_40_w14
private theorem endpoint_18_40_w16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 16 1 205895884399792553 = some 205895884399792553 := by decide +kernel
private theorem endpoint_18_40_p17 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 17 205895884399792553 = some 205895884399792553 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 16 1 205895884399792553 205895884399792553 205895884399792553 endpoint_18_40_p16 endpoint_18_40_w16
def endpoint_18_40 : CertifiedEndpoint :=
  ⟨⟨18, 40, 2580⟩, 205895884399792553, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_40_flag endpoint_18_40_sources 17 205895884399792553 205895884399792553 rfl endpoint_18_40_base endpoint_18_40_p17) (by decide)⟩
private def endpoint_18_41_flag : Flag := ⟨18, 41, 2530⟩
private def endpoint_18_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_41_base : receiptBase endpoint_18_41_flag endpoint_18_41_sources = some 206301408909453094 := by decide +kernel
private theorem endpoint_18_41_w0 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 2 206301408909453094 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_w2 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 2 2 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 4 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 2 2 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_w0 endpoint_18_41_w2
private theorem endpoint_18_41_w4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 4 2 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 6 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 4 2 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_p4 endpoint_18_41_w4
private theorem endpoint_18_41_w6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 6 2 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 8 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 6 2 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_p6 endpoint_18_41_w6
private theorem endpoint_18_41_w8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 8 2 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 10 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 8 2 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_p8 endpoint_18_41_w8
private theorem endpoint_18_41_w10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 10 2 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 12 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 10 2 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_p10 endpoint_18_41_w10
private theorem endpoint_18_41_w12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 12 2 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 14 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 12 2 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_p12 endpoint_18_41_w12
private theorem endpoint_18_41_w14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 14 2 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 16 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 14 2 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_p14 endpoint_18_41_w14
private theorem endpoint_18_41_w16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 16 1 206899575612138796 = some 206899575612138796 := by decide +kernel
private theorem endpoint_18_41_p17 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 17 206301408909453094 = some 206899575612138796 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 16 1 206301408909453094 206899575612138796 206899575612138796 endpoint_18_41_p16 endpoint_18_41_w16
def endpoint_18_41 : CertifiedEndpoint :=
  ⟨⟨18, 41, 2530⟩, 206899575612138796, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_41_flag endpoint_18_41_sources 17 206301408909453094 206899575612138796 rfl endpoint_18_41_base endpoint_18_41_p17) (by decide)⟩
private def endpoint_18_42_flag : Flag := ⟨18, 42, 2480⟩
private def endpoint_18_42_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_18_42_base : receiptBase endpoint_18_42_flag endpoint_18_42_sources = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_w0 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_w2 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 2 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 4 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 2 2 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_w0 endpoint_18_42_w2
private theorem endpoint_18_42_w4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 4 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 6 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 4 2 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_p4 endpoint_18_42_w4
private theorem endpoint_18_42_w6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 6 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 8 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 6 2 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_p6 endpoint_18_42_w6
private theorem endpoint_18_42_w8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 8 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 10 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 8 2 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_p8 endpoint_18_42_w8
private theorem endpoint_18_42_w10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 10 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 12 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 10 2 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_p10 endpoint_18_42_w10
private theorem endpoint_18_42_w12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 12 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 14 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 12 2 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_p12 endpoint_18_42_w12
private theorem endpoint_18_42_w14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 14 2 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 16 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 14 2 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_p14 endpoint_18_42_w14
private theorem endpoint_18_42_w16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 16 1 211630256225746655 = some 211630256225746655 := by decide +kernel
private theorem endpoint_18_42_p17 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 17 211630256225746655 = some 211630256225746655 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 16 1 211630256225746655 211630256225746655 211630256225746655 endpoint_18_42_p16 endpoint_18_42_w16
def endpoint_18_42 : CertifiedEndpoint :=
  ⟨⟨18, 42, 2480⟩, 211630256225746655, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_18_42_flag endpoint_18_42_sources 17 211630256225746655 211630256225746655 rfl endpoint_18_42_base endpoint_18_42_p17) (by decide)⟩
private def endpoint_18_43_flag : Flag := ⟨18, 43, 2429⟩
private def endpoint_18_43_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_43_base : receiptBase endpoint_18_43_flag endpoint_18_43_sources = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_w0 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_w2 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 2 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 4 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 2 2 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_w0 endpoint_18_43_w2
private theorem endpoint_18_43_w4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 4 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 6 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 4 2 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_p4 endpoint_18_43_w4
private theorem endpoint_18_43_w6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 6 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 8 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 6 2 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_p6 endpoint_18_43_w6
private theorem endpoint_18_43_w8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 8 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 10 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 8 2 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_p8 endpoint_18_43_w8
private theorem endpoint_18_43_w10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 10 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 12 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 10 2 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_p10 endpoint_18_43_w10
private theorem endpoint_18_43_w12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 12 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 14 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 12 2 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_p12 endpoint_18_43_w12
private theorem endpoint_18_43_w14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 14 2 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 16 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 14 2 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_p14 endpoint_18_43_w14
private theorem endpoint_18_43_w16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 16 1 212131998841793018 = some 212131998841793018 := by decide +kernel
private theorem endpoint_18_43_p17 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 17 212131998841793018 = some 212131998841793018 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 16 1 212131998841793018 212131998841793018 212131998841793018 endpoint_18_43_p16 endpoint_18_43_w16
def endpoint_18_43 : CertifiedEndpoint :=
  ⟨⟨18, 43, 2429⟩, 212131998841793018, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_43_flag endpoint_18_43_sources 17 212131998841793018 212131998841793018 rfl endpoint_18_43_base endpoint_18_43_p17) (by decide)⟩
private def endpoint_18_44_flag : Flag := ⟨18, 44, 2377⟩
private def endpoint_18_44_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_44_base : receiptBase endpoint_18_44_flag endpoint_18_44_sources = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_w0 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_w2 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 2 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 4 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 2 2 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_w0 endpoint_18_44_w2
private theorem endpoint_18_44_w4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 4 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 6 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 4 2 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_p4 endpoint_18_44_w4
private theorem endpoint_18_44_w6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 6 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 8 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 6 2 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_p6 endpoint_18_44_w6
private theorem endpoint_18_44_w8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 8 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 10 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 8 2 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_p8 endpoint_18_44_w8
private theorem endpoint_18_44_w10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 10 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 12 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 10 2 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_p10 endpoint_18_44_w10
private theorem endpoint_18_44_w12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 12 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 14 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 12 2 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_p12 endpoint_18_44_w12
private theorem endpoint_18_44_w14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 14 2 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 16 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 14 2 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_p14 endpoint_18_44_w14
private theorem endpoint_18_44_w16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 16 1 211911075118465026 = some 211911075118465026 := by decide +kernel
private theorem endpoint_18_44_p17 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 17 211911075118465026 = some 211911075118465026 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 16 1 211911075118465026 211911075118465026 211911075118465026 endpoint_18_44_p16 endpoint_18_44_w16
def endpoint_18_44 : CertifiedEndpoint :=
  ⟨⟨18, 44, 2377⟩, 211911075118465026, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_44_flag endpoint_18_44_sources 17 211911075118465026 211911075118465026 rfl endpoint_18_44_base endpoint_18_44_p17) (by decide)⟩
private def endpoint_18_45_flag : Flag := ⟨18, 45, 2323⟩
private def endpoint_18_45_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_45_base : receiptBase endpoint_18_45_flag endpoint_18_45_sources = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_w0 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_w2 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 2 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 4 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 2 2 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_w0 endpoint_18_45_w2
private theorem endpoint_18_45_w4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 4 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 6 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 4 2 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_p4 endpoint_18_45_w4
private theorem endpoint_18_45_w6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 6 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 8 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 6 2 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_p6 endpoint_18_45_w6
private theorem endpoint_18_45_w8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 8 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 10 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 8 2 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_p8 endpoint_18_45_w8
private theorem endpoint_18_45_w10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 10 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 12 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 10 2 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_p10 endpoint_18_45_w10
private theorem endpoint_18_45_w12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 12 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 14 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 12 2 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_p12 endpoint_18_45_w12
private theorem endpoint_18_45_w14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 14 2 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 16 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 14 2 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_p14 endpoint_18_45_w14
private theorem endpoint_18_45_w16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 16 1 211908656503995971 = some 211908656503995971 := by decide +kernel
private theorem endpoint_18_45_p17 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 17 211908656503995971 = some 211908656503995971 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 16 1 211908656503995971 211908656503995971 211908656503995971 endpoint_18_45_p16 endpoint_18_45_w16
def endpoint_18_45 : CertifiedEndpoint :=
  ⟨⟨18, 45, 2323⟩, 211908656503995971, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_45_flag endpoint_18_45_sources 17 211908656503995971 211908656503995971 rfl endpoint_18_45_base endpoint_18_45_p17) (by decide)⟩
private def endpoint_18_46_flag : Flag := ⟨18, 46, 2269⟩
private def endpoint_18_46_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_46_base : receiptBase endpoint_18_46_flag endpoint_18_46_sources = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_w0 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_w2 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 2 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 4 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 2 2 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_w0 endpoint_18_46_w2
private theorem endpoint_18_46_w4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 4 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 6 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 4 2 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_p4 endpoint_18_46_w4
private theorem endpoint_18_46_w6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 6 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 8 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 6 2 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_p6 endpoint_18_46_w6
private theorem endpoint_18_46_w8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 8 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 10 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 8 2 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_p8 endpoint_18_46_w8
private theorem endpoint_18_46_w10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 10 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 12 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 10 2 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_p10 endpoint_18_46_w10
private theorem endpoint_18_46_w12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 12 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 14 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 12 2 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_p12 endpoint_18_46_w12
private theorem endpoint_18_46_w14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 14 2 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 16 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 14 2 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_p14 endpoint_18_46_w14
private theorem endpoint_18_46_w16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 16 1 211109552128758409 = some 211109552128758409 := by decide +kernel
private theorem endpoint_18_46_p17 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 17 211109552128758409 = some 211109552128758409 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 16 1 211109552128758409 211109552128758409 211109552128758409 endpoint_18_46_p16 endpoint_18_46_w16
def endpoint_18_46 : CertifiedEndpoint :=
  ⟨⟨18, 46, 2269⟩, 211109552128758409, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_46_flag endpoint_18_46_sources 17 211109552128758409 211109552128758409 rfl endpoint_18_46_base endpoint_18_46_p17) (by decide)⟩
private def endpoint_18_47_flag : Flag := ⟨18, 47, 2214⟩
private def endpoint_18_47_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_47_base : receiptBase endpoint_18_47_flag endpoint_18_47_sources = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_w0 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_w2 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 2 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 4 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 2 2 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_w0 endpoint_18_47_w2
private theorem endpoint_18_47_w4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 4 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 6 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 4 2 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_p4 endpoint_18_47_w4
private theorem endpoint_18_47_w6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 6 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 8 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 6 2 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_p6 endpoint_18_47_w6
private theorem endpoint_18_47_w8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 8 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 10 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 8 2 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_p8 endpoint_18_47_w8
private theorem endpoint_18_47_w10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 10 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 12 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 10 2 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_p10 endpoint_18_47_w10
private theorem endpoint_18_47_w12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 12 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 14 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 12 2 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_p12 endpoint_18_47_w12
private theorem endpoint_18_47_w14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 14 2 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 16 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 14 2 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_p14 endpoint_18_47_w14
private theorem endpoint_18_47_w16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 16 1 210032845103761999 = some 210032845103761999 := by decide +kernel
private theorem endpoint_18_47_p17 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 17 210032845103761999 = some 210032845103761999 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 16 1 210032845103761999 210032845103761999 210032845103761999 endpoint_18_47_p16 endpoint_18_47_w16
def endpoint_18_47 : CertifiedEndpoint :=
  ⟨⟨18, 47, 2214⟩, 210032845103761999, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_47_flag endpoint_18_47_sources 17 210032845103761999 210032845103761999 rfl endpoint_18_47_base endpoint_18_47_p17) (by decide)⟩
private def endpoint_18_48_flag : Flag := ⟨18, 48, 2157⟩
private def endpoint_18_48_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_48_base : receiptBase endpoint_18_48_flag endpoint_18_48_sources = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_w0 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_w2 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 2 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 4 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 2 2 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_w0 endpoint_18_48_w2
private theorem endpoint_18_48_w4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 4 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 6 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 4 2 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_p4 endpoint_18_48_w4
private theorem endpoint_18_48_w6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 6 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 8 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 6 2 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_p6 endpoint_18_48_w6
private theorem endpoint_18_48_w8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 8 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 10 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 8 2 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_p8 endpoint_18_48_w8
private theorem endpoint_18_48_w10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 10 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 12 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 10 2 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_p10 endpoint_18_48_w10
private theorem endpoint_18_48_w12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 12 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 14 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 12 2 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_p12 endpoint_18_48_w12
private theorem endpoint_18_48_w14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 14 2 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 16 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 14 2 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_p14 endpoint_18_48_w14
private theorem endpoint_18_48_w16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 16 1 209371053573032459 = some 209371053573032459 := by decide +kernel
private theorem endpoint_18_48_p17 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 17 209371053573032459 = some 209371053573032459 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 16 1 209371053573032459 209371053573032459 209371053573032459 endpoint_18_48_p16 endpoint_18_48_w16
def endpoint_18_48 : CertifiedEndpoint :=
  ⟨⟨18, 48, 2157⟩, 209371053573032459, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_48_flag endpoint_18_48_sources 17 209371053573032459 209371053573032459 rfl endpoint_18_48_base endpoint_18_48_p17) (by decide)⟩
private def endpoint_18_49_flag : Flag := ⟨18, 49, 2100⟩
private def endpoint_18_49_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_49_base : receiptBase endpoint_18_49_flag endpoint_18_49_sources = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_w0 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_w2 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 2 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 4 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 2 2 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_w0 endpoint_18_49_w2
private theorem endpoint_18_49_w4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 4 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 6 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 4 2 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_p4 endpoint_18_49_w4
private theorem endpoint_18_49_w6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 6 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 8 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 6 2 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_p6 endpoint_18_49_w6
private theorem endpoint_18_49_w8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 8 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 10 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 8 2 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_p8 endpoint_18_49_w8
private theorem endpoint_18_49_w10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 10 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 12 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 10 2 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_p10 endpoint_18_49_w10
private theorem endpoint_18_49_w12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 12 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 14 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 12 2 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_p12 endpoint_18_49_w12
private theorem endpoint_18_49_w14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 14 2 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 16 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 14 2 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_p14 endpoint_18_49_w14
private theorem endpoint_18_49_w16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 16 1 207707417648218777 = some 207707417648218777 := by decide +kernel
private theorem endpoint_18_49_p17 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 17 207707417648218777 = some 207707417648218777 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 16 1 207707417648218777 207707417648218777 207707417648218777 endpoint_18_49_p16 endpoint_18_49_w16
def endpoint_18_49 : CertifiedEndpoint :=
  ⟨⟨18, 49, 2100⟩, 207707417648218777, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_49_flag endpoint_18_49_sources 17 207707417648218777 207707417648218777 rfl endpoint_18_49_base endpoint_18_49_p17) (by decide)⟩
private def endpoint_18_50_flag : Flag := ⟨18, 50, 2041⟩
private def endpoint_18_50_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_50_base : receiptBase endpoint_18_50_flag endpoint_18_50_sources = some 205649367715862359 := by decide +kernel
private theorem endpoint_18_50_w0 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 2 205649367715862359 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_w2 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 2 2 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 4 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 2 2 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_w0 endpoint_18_50_w2
private theorem endpoint_18_50_w4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 4 2 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 6 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 4 2 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_p4 endpoint_18_50_w4
private theorem endpoint_18_50_w6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 6 2 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 8 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 6 2 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_p6 endpoint_18_50_w6
private theorem endpoint_18_50_w8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 8 2 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 10 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 8 2 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_p8 endpoint_18_50_w8
private theorem endpoint_18_50_w10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 10 2 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 12 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 10 2 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_p10 endpoint_18_50_w10
private theorem endpoint_18_50_w12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 12 2 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 14 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 12 2 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_p12 endpoint_18_50_w12
private theorem endpoint_18_50_w14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 14 2 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 16 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 14 2 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_p14 endpoint_18_50_w14
private theorem endpoint_18_50_w16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 16 1 208708875584283854 = some 208708875584283854 := by decide +kernel
private theorem endpoint_18_50_p17 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 17 205649367715862359 = some 208708875584283854 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 16 1 205649367715862359 208708875584283854 208708875584283854 endpoint_18_50_p16 endpoint_18_50_w16
def endpoint_18_50 : CertifiedEndpoint :=
  ⟨⟨18, 50, 2041⟩, 208708875584283854, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_50_flag endpoint_18_50_sources 17 205649367715862359 208708875584283854 rfl endpoint_18_50_base endpoint_18_50_p17) (by decide)⟩
private def endpoint_18_51_flag : Flag := ⟨18, 51, 1982⟩
private def endpoint_18_51_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_18_51_base : receiptBase endpoint_18_51_flag endpoint_18_51_sources = some 203397185008950402 := by decide +kernel
private theorem endpoint_18_51_w0 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 2 203397185008950402 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_w2 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 2 2 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 4 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 2 2 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_w0 endpoint_18_51_w2
private theorem endpoint_18_51_w4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 4 2 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 6 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 4 2 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_p4 endpoint_18_51_w4
private theorem endpoint_18_51_w6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 6 2 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 8 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 6 2 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_p6 endpoint_18_51_w6
private theorem endpoint_18_51_w8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 8 2 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 10 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 8 2 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_p8 endpoint_18_51_w8
private theorem endpoint_18_51_w10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 10 2 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 12 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 10 2 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_p10 endpoint_18_51_w10
private theorem endpoint_18_51_w12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 12 2 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 14 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 12 2 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_p12 endpoint_18_51_w12
private theorem endpoint_18_51_w14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 14 2 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 16 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 14 2 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_p14 endpoint_18_51_w14
private theorem endpoint_18_51_w16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 16 1 210472345293212055 = some 210472345293212055 := by decide +kernel
private theorem endpoint_18_51_p17 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 17 203397185008950402 = some 210472345293212055 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 16 1 203397185008950402 210472345293212055 210472345293212055 endpoint_18_51_p16 endpoint_18_51_w16
def endpoint_18_51 : CertifiedEndpoint :=
  ⟨⟨18, 51, 1982⟩, 210472345293212055, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_18_51_flag endpoint_18_51_sources 17 203397185008950402 210472345293212055 rfl endpoint_18_51_base endpoint_18_51_p17) (by decide)⟩
private def endpoint_18_52_flag : Flag := ⟨18, 52, 1921⟩
private def endpoint_18_52_sources : Sources := ⟨contact29, contact16, contact12⟩
private theorem endpoint_18_52_base : receiptBase endpoint_18_52_flag endpoint_18_52_sources = some 201185599342703968 := by decide +kernel
private theorem endpoint_18_52_w0 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 2 201185599342703968 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_w2 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 2 2 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 4 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 2 2 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_w0 endpoint_18_52_w2
private theorem endpoint_18_52_w4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 4 2 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 6 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 4 2 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_p4 endpoint_18_52_w4
private theorem endpoint_18_52_w6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 6 2 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 8 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 6 2 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_p6 endpoint_18_52_w6
private theorem endpoint_18_52_w8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 8 2 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 10 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 8 2 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_p8 endpoint_18_52_w8
private theorem endpoint_18_52_w10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 10 2 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 12 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 10 2 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_p10 endpoint_18_52_w10
private theorem endpoint_18_52_w12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 12 2 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 14 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 12 2 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_p12 endpoint_18_52_w12
private theorem endpoint_18_52_w14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 14 2 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 16 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 14 2 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_p14 endpoint_18_52_w14
private theorem endpoint_18_52_w16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 16 1 210620437445333884 = some 210620437445333884 := by decide +kernel
private theorem endpoint_18_52_p17 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 17 201185599342703968 = some 210620437445333884 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 16 1 201185599342703968 210620437445333884 210620437445333884 endpoint_18_52_p16 endpoint_18_52_w16
def endpoint_18_52 : CertifiedEndpoint :=
  ⟨⟨18, 52, 1921⟩, 210620437445333884, .terminal ⟨contact29, contact16, contact12⟩ (finish_receipt_window endpoint_18_52_flag endpoint_18_52_sources 17 201185599342703968 210620437445333884 rfl endpoint_18_52_base endpoint_18_52_p17) (by decide)⟩
private def endpoint_18_53_flag : Flag := ⟨18, 53, 1858⟩
private def endpoint_18_53_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_18_53_base : receiptBase endpoint_18_53_flag endpoint_18_53_sources = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_w0 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_w2 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 2 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 4 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 2 2 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_w0 endpoint_18_53_w2
private theorem endpoint_18_53_w4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 4 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 6 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 4 2 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_p4 endpoint_18_53_w4
private theorem endpoint_18_53_w6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 6 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 8 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 6 2 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_p6 endpoint_18_53_w6
private theorem endpoint_18_53_w8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 8 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 10 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 8 2 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_p8 endpoint_18_53_w8
private theorem endpoint_18_53_w10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 10 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 12 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 10 2 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_p10 endpoint_18_53_w10
private theorem endpoint_18_53_w12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 12 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 14 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 12 2 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_p12 endpoint_18_53_w12
private theorem endpoint_18_53_w14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 14 2 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 16 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 14 2 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_p14 endpoint_18_53_w14
private theorem endpoint_18_53_w16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 16 1 199653799400145643 = some 199653799400145643 := by decide +kernel
private theorem endpoint_18_53_p17 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 17 199653799400145643 = some 199653799400145643 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 16 1 199653799400145643 199653799400145643 199653799400145643 endpoint_18_53_p16 endpoint_18_53_w16
def endpoint_18_53 : CertifiedEndpoint :=
  ⟨⟨18, 53, 1858⟩, 199653799400145643, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_18_53_flag endpoint_18_53_sources 17 199653799400145643 199653799400145643 rfl endpoint_18_53_base endpoint_18_53_p17) (by decide)⟩
private def endpoint_18_54_flag : Flag := ⟨18, 54, 1795⟩
private def endpoint_18_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_54_base : receiptBase endpoint_18_54_flag endpoint_18_54_sources = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_w0 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_w2 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 2 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 4 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 2 2 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_w0 endpoint_18_54_w2
private theorem endpoint_18_54_w4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 4 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 6 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 4 2 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_p4 endpoint_18_54_w4
private theorem endpoint_18_54_w6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 6 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 8 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 6 2 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_p6 endpoint_18_54_w6
private theorem endpoint_18_54_w8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 8 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 10 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 8 2 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_p8 endpoint_18_54_w8
private theorem endpoint_18_54_w10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 10 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 12 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 10 2 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_p10 endpoint_18_54_w10
private theorem endpoint_18_54_w12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 12 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 14 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 12 2 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_p12 endpoint_18_54_w12
private theorem endpoint_18_54_w14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 14 2 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 16 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 14 2 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_p14 endpoint_18_54_w14
private theorem endpoint_18_54_w16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 16 1 198177628054836564 = some 198177628054836564 := by decide +kernel
private theorem endpoint_18_54_p17 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 17 198177628054836564 = some 198177628054836564 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 16 1 198177628054836564 198177628054836564 198177628054836564 endpoint_18_54_p16 endpoint_18_54_w16
def endpoint_18_54 : CertifiedEndpoint :=
  ⟨⟨18, 54, 1795⟩, 198177628054836564, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_54_flag endpoint_18_54_sources 17 198177628054836564 198177628054836564 rfl endpoint_18_54_base endpoint_18_54_p17) (by decide)⟩
private def endpoint_18_55_flag : Flag := ⟨18, 55, 1730⟩
private def endpoint_18_55_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_55_base : receiptBase endpoint_18_55_flag endpoint_18_55_sources = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_w0 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_w2 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 2 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 4 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 2 2 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_w0 endpoint_18_55_w2
private theorem endpoint_18_55_w4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 4 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 6 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 4 2 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_p4 endpoint_18_55_w4
private theorem endpoint_18_55_w6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 6 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 8 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 6 2 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_p6 endpoint_18_55_w6
private theorem endpoint_18_55_w8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 8 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 10 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 8 2 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_p8 endpoint_18_55_w8
private theorem endpoint_18_55_w10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 10 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 12 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 10 2 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_p10 endpoint_18_55_w10
private theorem endpoint_18_55_w12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 12 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 14 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 12 2 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_p12 endpoint_18_55_w12
private theorem endpoint_18_55_w14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 14 2 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 16 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 14 2 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_p14 endpoint_18_55_w14
private theorem endpoint_18_55_w16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 16 1 194168562069068636 = some 194168562069068636 := by decide +kernel
private theorem endpoint_18_55_p17 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 17 194168562069068636 = some 194168562069068636 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 16 1 194168562069068636 194168562069068636 194168562069068636 endpoint_18_55_p16 endpoint_18_55_w16
def endpoint_18_55 : CertifiedEndpoint :=
  ⟨⟨18, 55, 1730⟩, 194168562069068636, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_55_flag endpoint_18_55_sources 17 194168562069068636 194168562069068636 rfl endpoint_18_55_base endpoint_18_55_p17) (by decide)⟩
private def endpoint_18_56_flag : Flag := ⟨18, 56, 1664⟩
private def endpoint_18_56_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_56_base : receiptBase endpoint_18_56_flag endpoint_18_56_sources = some 188195084662632579 := by decide +kernel
private theorem endpoint_18_56_w0 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 2 188195084662632579 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_w2 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 2 2 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 4 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 2 2 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_w0 endpoint_18_56_w2
private theorem endpoint_18_56_w4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 4 2 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 6 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 4 2 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_p4 endpoint_18_56_w4
private theorem endpoint_18_56_w6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 6 2 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 8 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 6 2 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_p6 endpoint_18_56_w6
private theorem endpoint_18_56_w8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 8 2 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 10 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 8 2 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_p8 endpoint_18_56_w8
private theorem endpoint_18_56_w10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 10 2 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 12 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 10 2 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_p10 endpoint_18_56_w10
private theorem endpoint_18_56_w12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 12 2 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 14 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 12 2 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_p12 endpoint_18_56_w12
private theorem endpoint_18_56_w14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 14 2 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 16 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 14 2 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_p14 endpoint_18_56_w14
private theorem endpoint_18_56_w16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 16 1 199006307435071004 = some 199006307435071004 := by decide +kernel
private theorem endpoint_18_56_p17 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 17 188195084662632579 = some 199006307435071004 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 16 1 188195084662632579 199006307435071004 199006307435071004 endpoint_18_56_p16 endpoint_18_56_w16
def endpoint_18_56 : CertifiedEndpoint :=
  ⟨⟨18, 56, 1664⟩, 199006307435071004, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_56_flag endpoint_18_56_sources 17 188195084662632579 199006307435071004 rfl endpoint_18_56_base endpoint_18_56_p17) (by decide)⟩
private def endpoint_18_57_flag : Flag := ⟨18, 57, 1596⟩
private def endpoint_18_57_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_57_base : receiptBase endpoint_18_57_flag endpoint_18_57_sources = some 183436626638542458 := by decide +kernel
private theorem endpoint_18_57_w0 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 2 183436626638542458 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_w2 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 2 2 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 4 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 2 2 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_w0 endpoint_18_57_w2
private theorem endpoint_18_57_w4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 4 2 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 6 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 4 2 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_p4 endpoint_18_57_w4
private theorem endpoint_18_57_w6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 6 2 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 8 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 6 2 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_p6 endpoint_18_57_w6
private theorem endpoint_18_57_w8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 8 2 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 10 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 8 2 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_p8 endpoint_18_57_w8
private theorem endpoint_18_57_w10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 10 2 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 12 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 10 2 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_p10 endpoint_18_57_w10
private theorem endpoint_18_57_w12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 12 2 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 14 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 12 2 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_p12 endpoint_18_57_w12
private theorem endpoint_18_57_w14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 14 2 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 16 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 14 2 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_p14 endpoint_18_57_w14
private theorem endpoint_18_57_w16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 16 1 198779482319088708 = some 198779482319088708 := by decide +kernel
private theorem endpoint_18_57_p17 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 17 183436626638542458 = some 198779482319088708 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 16 1 183436626638542458 198779482319088708 198779482319088708 endpoint_18_57_p16 endpoint_18_57_w16
def endpoint_18_57 : CertifiedEndpoint :=
  ⟨⟨18, 57, 1596⟩, 198779482319088708, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_57_flag endpoint_18_57_sources 17 183436626638542458 198779482319088708 rfl endpoint_18_57_base endpoint_18_57_p17) (by decide)⟩
private def endpoint_18_58_flag : Flag := ⟨18, 58, 1527⟩
private def endpoint_18_58_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_58_base : receiptBase endpoint_18_58_flag endpoint_18_58_sources = some 179826368961929647 := by decide +kernel
private theorem endpoint_18_58_w0 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 2 179826368961929647 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_w2 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 2 2 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 4 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 2 2 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_w0 endpoint_18_58_w2
private theorem endpoint_18_58_w4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 4 2 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 6 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 4 2 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_p4 endpoint_18_58_w4
private theorem endpoint_18_58_w6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 6 2 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 8 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 6 2 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_p6 endpoint_18_58_w6
private theorem endpoint_18_58_w8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 8 2 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 10 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 8 2 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_p8 endpoint_18_58_w8
private theorem endpoint_18_58_w10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 10 2 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 12 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 10 2 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_p10 endpoint_18_58_w10
private theorem endpoint_18_58_w12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 12 2 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 14 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 12 2 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_p12 endpoint_18_58_w12
private theorem endpoint_18_58_w14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 14 2 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 16 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 14 2 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_p14 endpoint_18_58_w14
private theorem endpoint_18_58_w16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 16 1 183251815798480458 = some 183251815798480458 := by decide +kernel
private theorem endpoint_18_58_p17 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 17 179826368961929647 = some 183251815798480458 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 16 1 179826368961929647 183251815798480458 183251815798480458 endpoint_18_58_p16 endpoint_18_58_w16
def endpoint_18_58 : CertifiedEndpoint :=
  ⟨⟨18, 58, 1527⟩, 183251815798480458, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_58_flag endpoint_18_58_sources 17 179826368961929647 183251815798480458 rfl endpoint_18_58_base endpoint_18_58_p17) (by decide)⟩
private def endpoint_18_59_flag : Flag := ⟨18, 59, 1456⟩
private def endpoint_18_59_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_59_base : receiptBase endpoint_18_59_flag endpoint_18_59_sources = some 174171899248047760 := by decide +kernel
private theorem endpoint_18_59_w0 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 2 174171899248047760 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_w2 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 2 2 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 4 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 2 2 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_w0 endpoint_18_59_w2
private theorem endpoint_18_59_w4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 4 2 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 6 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 4 2 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_p4 endpoint_18_59_w4
private theorem endpoint_18_59_w6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 6 2 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 8 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 6 2 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_p6 endpoint_18_59_w6
private theorem endpoint_18_59_w8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 8 2 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 10 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 8 2 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_p8 endpoint_18_59_w8
private theorem endpoint_18_59_w10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 10 2 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 12 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 10 2 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_p10 endpoint_18_59_w10
private theorem endpoint_18_59_w12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 12 2 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 14 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 12 2 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_p12 endpoint_18_59_w12
private theorem endpoint_18_59_w14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 14 2 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 16 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 14 2 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_p14 endpoint_18_59_w14
private theorem endpoint_18_59_w16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 16 1 182117570251275049 = some 182117570251275049 := by decide +kernel
private theorem endpoint_18_59_p17 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 17 174171899248047760 = some 182117570251275049 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 16 1 174171899248047760 182117570251275049 182117570251275049 endpoint_18_59_p16 endpoint_18_59_w16
def endpoint_18_59 : CertifiedEndpoint :=
  ⟨⟨18, 59, 1456⟩, 182117570251275049, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_59_flag endpoint_18_59_sources 17 174171899248047760 182117570251275049 rfl endpoint_18_59_base endpoint_18_59_p17) (by decide)⟩
private def endpoint_18_60_flag : Flag := ⟨18, 60, 1384⟩
private def endpoint_18_60_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_60_base : receiptBase endpoint_18_60_flag endpoint_18_60_sources = some 168145591195741923 := by decide +kernel
private theorem endpoint_18_60_w0 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 2 168145591195741923 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_w2 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 2 2 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 4 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 2 2 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_w0 endpoint_18_60_w2
private theorem endpoint_18_60_w4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 4 2 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 6 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 4 2 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_p4 endpoint_18_60_w4
private theorem endpoint_18_60_w6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 6 2 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 8 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 6 2 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_p6 endpoint_18_60_w6
private theorem endpoint_18_60_w8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 8 2 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 10 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 8 2 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_p8 endpoint_18_60_w8
private theorem endpoint_18_60_w10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 10 2 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 12 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 10 2 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_p10 endpoint_18_60_w10
private theorem endpoint_18_60_w12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 12 2 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 14 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 12 2 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_p12 endpoint_18_60_w12
private theorem endpoint_18_60_w14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 14 2 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 16 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 14 2 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_p14 endpoint_18_60_w14
private theorem endpoint_18_60_w16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 16 1 180710553068288448 = some 180710553068288448 := by decide +kernel
private theorem endpoint_18_60_p17 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 17 168145591195741923 = some 180710553068288448 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 16 1 168145591195741923 180710553068288448 180710553068288448 endpoint_18_60_p16 endpoint_18_60_w16
def endpoint_18_60 : CertifiedEndpoint :=
  ⟨⟨18, 60, 1384⟩, 180710553068288448, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_60_flag endpoint_18_60_sources 17 168145591195741923 180710553068288448 rfl endpoint_18_60_base endpoint_18_60_p17) (by decide)⟩
private def endpoint_18_61_flag : Flag := ⟨18, 61, 1310⟩
private def endpoint_18_61_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_18_61_base : receiptBase endpoint_18_61_flag endpoint_18_61_sources = some 161950542564091874 := by decide +kernel
private theorem endpoint_18_61_w0 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 2 161950542564091874 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_w2 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 2 2 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 4 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 2 2 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_w0 endpoint_18_61_w2
private theorem endpoint_18_61_w4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 4 2 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 6 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 4 2 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_p4 endpoint_18_61_w4
private theorem endpoint_18_61_w6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 6 2 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 8 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 6 2 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_p6 endpoint_18_61_w6
private theorem endpoint_18_61_w8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 8 2 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 10 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 8 2 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_p8 endpoint_18_61_w8
private theorem endpoint_18_61_w10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 10 2 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 12 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 10 2 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_p10 endpoint_18_61_w10
private theorem endpoint_18_61_w12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 12 2 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 14 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 12 2 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_p12 endpoint_18_61_w12
private theorem endpoint_18_61_w14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 14 2 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 16 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 14 2 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_p14 endpoint_18_61_w14
private theorem endpoint_18_61_w16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 16 1 176170906215924118 = some 176170906215924118 := by decide +kernel
private theorem endpoint_18_61_p17 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 17 161950542564091874 = some 176170906215924118 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 16 1 161950542564091874 176170906215924118 176170906215924118 endpoint_18_61_p16 endpoint_18_61_w16
def endpoint_18_61 : CertifiedEndpoint :=
  ⟨⟨18, 61, 1310⟩, 176170906215924118, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_18_61_flag endpoint_18_61_sources 17 161950542564091874 176170906215924118 rfl endpoint_18_61_base endpoint_18_61_p17) (by decide)⟩
private def endpoint_18_62_flag : Flag := ⟨18, 62, 1235⟩
private def endpoint_18_62_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_18_62_base : receiptBase endpoint_18_62_flag endpoint_18_62_sources = some 156276432992134547 := by decide +kernel
private theorem endpoint_18_62_w0 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 2 156276432992134547 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_w2 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 2 2 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 4 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 2 2 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_w0 endpoint_18_62_w2
private theorem endpoint_18_62_w4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 4 2 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 6 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 4 2 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_p4 endpoint_18_62_w4
private theorem endpoint_18_62_w6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 6 2 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 8 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 6 2 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_p6 endpoint_18_62_w6
private theorem endpoint_18_62_w8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 8 2 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 10 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 8 2 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_p8 endpoint_18_62_w8
private theorem endpoint_18_62_w10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 10 2 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 12 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 10 2 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_p10 endpoint_18_62_w10
private theorem endpoint_18_62_w12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 12 2 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 14 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 12 2 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_p12 endpoint_18_62_w12
private theorem endpoint_18_62_w14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 14 2 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 16 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 14 2 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_p14 endpoint_18_62_w14
private theorem endpoint_18_62_w16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 16 1 166756075192907894 = some 166756075192907894 := by decide +kernel
private theorem endpoint_18_62_p17 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 17 156276432992134547 = some 166756075192907894 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 16 1 156276432992134547 166756075192907894 166756075192907894 endpoint_18_62_p16 endpoint_18_62_w16
def endpoint_18_62 : CertifiedEndpoint :=
  ⟨⟨18, 62, 1235⟩, 166756075192907894, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_18_62_flag endpoint_18_62_sources 17 156276432992134547 166756075192907894 rfl endpoint_18_62_base endpoint_18_62_p17) (by decide)⟩
private def endpoint_18_63_flag : Flag := ⟨18, 63, 1158⟩
private def endpoint_18_63_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_18_63_base : receiptBase endpoint_18_63_flag endpoint_18_63_sources = some 148767328157460985 := by decide +kernel
private theorem endpoint_18_63_w0 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 2 148767328157460985 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_w2 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 2 2 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 4 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 2 2 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_w0 endpoint_18_63_w2
private theorem endpoint_18_63_w4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 4 2 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 6 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 4 2 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_p4 endpoint_18_63_w4
private theorem endpoint_18_63_w6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 6 2 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 8 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 6 2 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_p6 endpoint_18_63_w6
private theorem endpoint_18_63_w8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 8 2 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 10 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 8 2 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_p8 endpoint_18_63_w8
private theorem endpoint_18_63_w10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 10 2 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 12 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 10 2 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_p10 endpoint_18_63_w10
private theorem endpoint_18_63_w12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 12 2 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 14 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 12 2 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_p12 endpoint_18_63_w12
private theorem endpoint_18_63_w14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 14 2 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 16 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 14 2 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_p14 endpoint_18_63_w14
private theorem endpoint_18_63_w16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 16 1 164160456125564907 = some 164160456125564907 := by decide +kernel
private theorem endpoint_18_63_p17 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 17 148767328157460985 = some 164160456125564907 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 16 1 148767328157460985 164160456125564907 164160456125564907 endpoint_18_63_p16 endpoint_18_63_w16
def endpoint_18_63 : CertifiedEndpoint :=
  ⟨⟨18, 63, 1158⟩, 164160456125564907, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_18_63_flag endpoint_18_63_sources 17 148767328157460985 164160456125564907 rfl endpoint_18_63_base endpoint_18_63_p17) (by decide)⟩
def endpoint_18_64 : CertifiedEndpoint :=
  ⟨⟨18, 64, 1079⟩, 256725034592979989, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_65 : CertifiedEndpoint :=
  ⟨⟨18, 65, 998⟩, 240995722837229943, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_66 : CertifiedEndpoint :=
  ⟨⟨18, 66, 916⟩, 224274609764140120, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_67 : CertifiedEndpoint :=
  ⟨⟨18, 67, 831⟩, 206028504808727492, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_68 : CertifiedEndpoint :=
  ⟨⟨18, 68, 744⟩, 186481078285688816, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_69 : CertifiedEndpoint :=
  ⟨⟨18, 69, 656⟩, 165874074180371273, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_70 : CertifiedEndpoint :=
  ⟨⟨18, 70, 565⟩, 143647191421816199, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_71 : CertifiedEndpoint :=
  ⟨⟨18, 71, 471⟩, 119759764251060140, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_72 : CertifiedEndpoint :=
  ⟨⟨18, 72, 376⟩, 94735946397760912, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_73 : CertifiedEndpoint :=
  ⟨⟨18, 73, 278⟩, 67988326284984215, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_74 : CertifiedEndpoint :=
  ⟨⟨18, 74, 177⟩, 39476238153766595, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_19 : CertifiedEndpoint :=
  ⟨⟨19, 19, 3148⟩, 154837358062505489, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_20 : CertifiedEndpoint :=
  ⟨⟨19, 20, 3110⟩, 157815982039894306, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_21 : CertifiedEndpoint :=
  ⟨⟨19, 21, 3072⟩, 160675134223499167, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_22 : CertifiedEndpoint :=
  ⟨⟨19, 22, 3032⟩, 172951810074936836, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_23 : CertifiedEndpoint :=
  ⟨⟨19, 23, 2993⟩, 184903718274143994, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_24 : CertifiedEndpoint :=
  ⟨⟨19, 24, 2952⟩, 196344564133790680, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_25 : CertifiedEndpoint :=
  ⟨⟨19, 25, 2912⟩, 207460642341206855, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_26 : CertifiedEndpoint :=
  ⟨⟨19, 26, 2870⟩, 218037001477111410, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_27 : CertifiedEndpoint :=
  ⟨⟨19, 27, 2828⟩, 228207390243708035, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_28 : CertifiedEndpoint :=
  ⟨⟨19, 28, 2785⟩, 237885829801927453, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_29 : CertifiedEndpoint :=
  ⟨⟨19, 29, 2742⟩, 247148746746855225, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_30 : CertifiedEndpoint :=
  ⟨⟨19, 30, 2697⟩, 255805078912385365, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_31 : CertifiedEndpoint :=
  ⟨⟨19, 31, 2653⟩, 264127091181701278, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_19_32_flag : Flag := ⟨19, 32, 2607⟩
private def endpoint_19_32_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_32_base : receiptBase endpoint_19_32_flag endpoint_19_32_sources = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_w0 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_w2 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 2 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 4 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 2 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_w0 endpoint_19_32_w2
private theorem endpoint_19_32_w4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 4 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 6 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 4 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_p4 endpoint_19_32_w4
private theorem endpoint_19_32_w6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 6 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 8 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 6 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_p6 endpoint_19_32_w6
private theorem endpoint_19_32_w8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 8 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 10 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 8 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_p8 endpoint_19_32_w8
private theorem endpoint_19_32_w10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 10 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 12 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 10 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_p10 endpoint_19_32_w10
private theorem endpoint_19_32_w12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 12 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 14 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 12 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_p12 endpoint_19_32_w12
private theorem endpoint_19_32_w14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 14 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 16 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 14 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_p14 endpoint_19_32_w14
private theorem endpoint_19_32_w16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 16 2 178070648554775497 = some 178070648554775497 := by decide +kernel
private theorem endpoint_19_32_p18 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 18 178070648554775497 = some 178070648554775497 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 16 2 178070648554775497 178070648554775497 178070648554775497 endpoint_19_32_p16 endpoint_19_32_w16
def endpoint_19_32 : CertifiedEndpoint :=
  ⟨⟨19, 32, 2607⟩, 178070648554775497, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_32_flag endpoint_19_32_sources 18 178070648554775497 178070648554775497 rfl endpoint_19_32_base endpoint_19_32_p18) (by decide)⟩
private def endpoint_19_33_flag : Flag := ⟨19, 33, 2561⟩
private def endpoint_19_33_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_33_base : receiptBase endpoint_19_33_flag endpoint_19_33_sources = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_w0 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_w2 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 2 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 4 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 2 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_w0 endpoint_19_33_w2
private theorem endpoint_19_33_w4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 4 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 6 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 4 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_p4 endpoint_19_33_w4
private theorem endpoint_19_33_w6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 6 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 8 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 6 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_p6 endpoint_19_33_w6
private theorem endpoint_19_33_w8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 8 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 10 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 8 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_p8 endpoint_19_33_w8
private theorem endpoint_19_33_w10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 10 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 12 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 10 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_p10 endpoint_19_33_w10
private theorem endpoint_19_33_w12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 12 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 14 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 12 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_p12 endpoint_19_33_w12
private theorem endpoint_19_33_w14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 14 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 16 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 14 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_p14 endpoint_19_33_w14
private theorem endpoint_19_33_w16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 16 2 179555738795040699 = some 179555738795040699 := by decide +kernel
private theorem endpoint_19_33_p18 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 18 179555738795040699 = some 179555738795040699 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 16 2 179555738795040699 179555738795040699 179555738795040699 endpoint_19_33_p16 endpoint_19_33_w16
def endpoint_19_33 : CertifiedEndpoint :=
  ⟨⟨19, 33, 2561⟩, 179555738795040699, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_33_flag endpoint_19_33_sources 18 179555738795040699 179555738795040699 rfl endpoint_19_33_base endpoint_19_33_p18) (by decide)⟩
private def endpoint_19_34_flag : Flag := ⟨19, 34, 2514⟩
private def endpoint_19_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_34_base : receiptBase endpoint_19_34_flag endpoint_19_34_sources = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_w0 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_w2 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 2 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 4 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 2 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_w0 endpoint_19_34_w2
private theorem endpoint_19_34_w4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 4 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 6 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 4 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_p4 endpoint_19_34_w4
private theorem endpoint_19_34_w6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 6 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 8 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 6 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_p6 endpoint_19_34_w6
private theorem endpoint_19_34_w8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 8 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 10 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 8 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_p8 endpoint_19_34_w8
private theorem endpoint_19_34_w10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 10 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 12 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 10 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_p10 endpoint_19_34_w10
private theorem endpoint_19_34_w12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 12 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 14 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 12 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_p12 endpoint_19_34_w12
private theorem endpoint_19_34_w14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 14 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 16 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 14 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_p14 endpoint_19_34_w14
private theorem endpoint_19_34_w16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 16 2 180807019992004180 = some 180807019992004180 := by decide +kernel
private theorem endpoint_19_34_p18 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 18 180807019992004180 = some 180807019992004180 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 16 2 180807019992004180 180807019992004180 180807019992004180 endpoint_19_34_p16 endpoint_19_34_w16
def endpoint_19_34 : CertifiedEndpoint :=
  ⟨⟨19, 34, 2514⟩, 180807019992004180, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_34_flag endpoint_19_34_sources 18 180807019992004180 180807019992004180 rfl endpoint_19_34_base endpoint_19_34_p18) (by decide)⟩
private def endpoint_19_35_flag : Flag := ⟨19, 35, 2466⟩
private def endpoint_19_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_35_base : receiptBase endpoint_19_35_flag endpoint_19_35_sources = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_w0 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_w2 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 2 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 4 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 2 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_w0 endpoint_19_35_w2
private theorem endpoint_19_35_w4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 4 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 6 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 4 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_p4 endpoint_19_35_w4
private theorem endpoint_19_35_w6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 6 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 8 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 6 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_p6 endpoint_19_35_w6
private theorem endpoint_19_35_w8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 8 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 10 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 8 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_p8 endpoint_19_35_w8
private theorem endpoint_19_35_w10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 10 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 12 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 10 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_p10 endpoint_19_35_w10
private theorem endpoint_19_35_w12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 12 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 14 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 12 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_p12 endpoint_19_35_w12
private theorem endpoint_19_35_w14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 14 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 16 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 14 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_p14 endpoint_19_35_w14
private theorem endpoint_19_35_w16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 16 2 181819237031227011 = some 181819237031227011 := by decide +kernel
private theorem endpoint_19_35_p18 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 18 181819237031227011 = some 181819237031227011 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 16 2 181819237031227011 181819237031227011 181819237031227011 endpoint_19_35_p16 endpoint_19_35_w16
def endpoint_19_35 : CertifiedEndpoint :=
  ⟨⟨19, 35, 2466⟩, 181819237031227011, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_35_flag endpoint_19_35_sources 18 181819237031227011 181819237031227011 rfl endpoint_19_35_base endpoint_19_35_p18) (by decide)⟩
private def endpoint_19_36_flag : Flag := ⟨19, 36, 2418⟩
private def endpoint_19_36_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_36_base : receiptBase endpoint_19_36_flag endpoint_19_36_sources = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_w0 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_w2 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 2 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 4 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 2 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_w0 endpoint_19_36_w2
private theorem endpoint_19_36_w4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 4 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 6 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 4 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_p4 endpoint_19_36_w4
private theorem endpoint_19_36_w6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 6 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 8 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 6 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_p6 endpoint_19_36_w6
private theorem endpoint_19_36_w8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 8 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 10 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 8 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_p8 endpoint_19_36_w8
private theorem endpoint_19_36_w10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 10 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 12 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 10 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_p10 endpoint_19_36_w10
private theorem endpoint_19_36_w12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 12 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 14 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 12 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_p12 endpoint_19_36_w12
private theorem endpoint_19_36_w14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 14 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 16 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 14 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_p14 endpoint_19_36_w14
private theorem endpoint_19_36_w16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 16 2 188325202692623133 = some 188325202692623133 := by decide +kernel
private theorem endpoint_19_36_p18 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 18 188325202692623133 = some 188325202692623133 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 16 2 188325202692623133 188325202692623133 188325202692623133 endpoint_19_36_p16 endpoint_19_36_w16
def endpoint_19_36 : CertifiedEndpoint :=
  ⟨⟨19, 36, 2418⟩, 188325202692623133, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_36_flag endpoint_19_36_sources 18 188325202692623133 188325202692623133 rfl endpoint_19_36_base endpoint_19_36_p18) (by decide)⟩
private def endpoint_19_37_flag : Flag := ⟨19, 37, 2368⟩
private def endpoint_19_37_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_37_base : receiptBase endpoint_19_37_flag endpoint_19_37_sources = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_w0 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_w2 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 2 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 4 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 2 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_w0 endpoint_19_37_w2
private theorem endpoint_19_37_w4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 4 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 6 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 4 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_p4 endpoint_19_37_w4
private theorem endpoint_19_37_w6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 6 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 8 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 6 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_p6 endpoint_19_37_w6
private theorem endpoint_19_37_w8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 8 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 10 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 8 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_p8 endpoint_19_37_w8
private theorem endpoint_19_37_w10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 10 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 12 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 10 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_p10 endpoint_19_37_w10
private theorem endpoint_19_37_w12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 12 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 14 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 12 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_p12 endpoint_19_37_w12
private theorem endpoint_19_37_w14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 14 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 16 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 14 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_p14 endpoint_19_37_w14
private theorem endpoint_19_37_w16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 16 2 188875336113044953 = some 188875336113044953 := by decide +kernel
private theorem endpoint_19_37_p18 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 18 188875336113044953 = some 188875336113044953 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 16 2 188875336113044953 188875336113044953 188875336113044953 endpoint_19_37_p16 endpoint_19_37_w16
def endpoint_19_37 : CertifiedEndpoint :=
  ⟨⟨19, 37, 2368⟩, 188875336113044953, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_37_flag endpoint_19_37_sources 18 188875336113044953 188875336113044953 rfl endpoint_19_37_base endpoint_19_37_p18) (by decide)⟩
private def endpoint_19_38_flag : Flag := ⟨19, 38, 2318⟩
private def endpoint_19_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_38_base : receiptBase endpoint_19_38_flag endpoint_19_38_sources = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_w0 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_w2 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 2 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 4 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 2 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_w0 endpoint_19_38_w2
private theorem endpoint_19_38_w4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 4 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 6 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 4 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_p4 endpoint_19_38_w4
private theorem endpoint_19_38_w6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 6 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 8 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 6 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_p6 endpoint_19_38_w6
private theorem endpoint_19_38_w8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 8 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 10 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 8 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_p8 endpoint_19_38_w8
private theorem endpoint_19_38_w10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 10 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 12 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 10 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_p10 endpoint_19_38_w10
private theorem endpoint_19_38_w12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 12 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 14 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 12 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_p12 endpoint_19_38_w12
private theorem endpoint_19_38_w14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 14 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 16 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 14 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_p14 endpoint_19_38_w14
private theorem endpoint_19_38_w16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 16 2 189792995817332611 = some 189792995817332611 := by decide +kernel
private theorem endpoint_19_38_p18 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 18 189792995817332611 = some 189792995817332611 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 16 2 189792995817332611 189792995817332611 189792995817332611 endpoint_19_38_p16 endpoint_19_38_w16
def endpoint_19_38 : CertifiedEndpoint :=
  ⟨⟨19, 38, 2318⟩, 189792995817332611, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_38_flag endpoint_19_38_sources 18 189792995817332611 189792995817332611 rfl endpoint_19_38_base endpoint_19_38_p18) (by decide)⟩
private def endpoint_19_39_flag : Flag := ⟨19, 39, 2267⟩
private def endpoint_19_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_39_base : receiptBase endpoint_19_39_flag endpoint_19_39_sources = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_w0 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_w2 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 2 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 4 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 2 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_w0 endpoint_19_39_w2
private theorem endpoint_19_39_w4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 4 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 6 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 4 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_p4 endpoint_19_39_w4
private theorem endpoint_19_39_w6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 6 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 8 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 6 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_p6 endpoint_19_39_w6
private theorem endpoint_19_39_w8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 8 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 10 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 8 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_p8 endpoint_19_39_w8
private theorem endpoint_19_39_w10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 10 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 12 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 10 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_p10 endpoint_19_39_w10
private theorem endpoint_19_39_w12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 12 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 14 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 12 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_p12 endpoint_19_39_w12
private theorem endpoint_19_39_w14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 14 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 16 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 14 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_p14 endpoint_19_39_w14
private theorem endpoint_19_39_w16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 16 2 189909815032980773 = some 189909815032980773 := by decide +kernel
private theorem endpoint_19_39_p18 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 18 189909815032980773 = some 189909815032980773 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 16 2 189909815032980773 189909815032980773 189909815032980773 endpoint_19_39_p16 endpoint_19_39_w16
def endpoint_19_39 : CertifiedEndpoint :=
  ⟨⟨19, 39, 2267⟩, 189909815032980773, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_39_flag endpoint_19_39_sources 18 189909815032980773 189909815032980773 rfl endpoint_19_39_base endpoint_19_39_p18) (by decide)⟩
private def endpoint_19_40_flag : Flag := ⟨19, 40, 2215⟩
private def endpoint_19_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_40_base : receiptBase endpoint_19_40_flag endpoint_19_40_sources = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_w0 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_w2 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 2 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 4 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 2 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_w0 endpoint_19_40_w2
private theorem endpoint_19_40_w4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 4 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 6 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 4 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_p4 endpoint_19_40_w4
private theorem endpoint_19_40_w6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 6 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 8 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 6 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_p6 endpoint_19_40_w6
private theorem endpoint_19_40_w8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 8 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 10 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 8 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_p8 endpoint_19_40_w8
private theorem endpoint_19_40_w10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 10 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 12 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 10 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_p10 endpoint_19_40_w10
private theorem endpoint_19_40_w12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 12 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 14 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 12 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_p12 endpoint_19_40_w12
private theorem endpoint_19_40_w14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 14 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 16 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 14 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_p14 endpoint_19_40_w14
private theorem endpoint_19_40_w16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 16 2 189758331667065985 = some 189758331667065985 := by decide +kernel
private theorem endpoint_19_40_p18 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 18 189758331667065985 = some 189758331667065985 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 16 2 189758331667065985 189758331667065985 189758331667065985 endpoint_19_40_p16 endpoint_19_40_w16
def endpoint_19_40 : CertifiedEndpoint :=
  ⟨⟨19, 40, 2215⟩, 189758331667065985, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_40_flag endpoint_19_40_sources 18 189758331667065985 189758331667065985 rfl endpoint_19_40_base endpoint_19_40_p18) (by decide)⟩
private def endpoint_19_41_flag : Flag := ⟨19, 41, 2162⟩
private def endpoint_19_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_41_base : receiptBase endpoint_19_41_flag endpoint_19_41_sources = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_w0 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_w2 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 2 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 4 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 2 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_w0 endpoint_19_41_w2
private theorem endpoint_19_41_w4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 4 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 6 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 4 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_p4 endpoint_19_41_w4
private theorem endpoint_19_41_w6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 6 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 8 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 6 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_p6 endpoint_19_41_w6
private theorem endpoint_19_41_w8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 8 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 10 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 8 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_p8 endpoint_19_41_w8
private theorem endpoint_19_41_w10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 10 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 12 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 10 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_p10 endpoint_19_41_w10
private theorem endpoint_19_41_w12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 12 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 14 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 12 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_p12 endpoint_19_41_w12
private theorem endpoint_19_41_w14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 14 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 16 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 14 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_p14 endpoint_19_41_w14
private theorem endpoint_19_41_w16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 16 2 189333165914276486 = some 189333165914276486 := by decide +kernel
private theorem endpoint_19_41_p18 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 18 189333165914276486 = some 189333165914276486 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 16 2 189333165914276486 189333165914276486 189333165914276486 endpoint_19_41_p16 endpoint_19_41_w16
def endpoint_19_41 : CertifiedEndpoint :=
  ⟨⟨19, 41, 2162⟩, 189333165914276486, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_41_flag endpoint_19_41_sources 18 189333165914276486 189333165914276486 rfl endpoint_19_41_base endpoint_19_41_p18) (by decide)⟩
private def endpoint_19_42_flag : Flag := ⟨19, 42, 2109⟩
private def endpoint_19_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_42_base : receiptBase endpoint_19_42_flag endpoint_19_42_sources = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_w0 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_w2 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 2 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 4 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 2 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_w0 endpoint_19_42_w2
private theorem endpoint_19_42_w4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 4 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 6 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 4 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_p4 endpoint_19_42_w4
private theorem endpoint_19_42_w6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 6 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 8 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 6 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_p6 endpoint_19_42_w6
private theorem endpoint_19_42_w8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 8 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 10 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 8 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_p8 endpoint_19_42_w8
private theorem endpoint_19_42_w10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 10 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 12 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 10 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_p10 endpoint_19_42_w10
private theorem endpoint_19_42_w12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 12 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 14 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 12 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_p12 endpoint_19_42_w12
private theorem endpoint_19_42_w14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 14 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 16 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 14 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_p14 endpoint_19_42_w14
private theorem endpoint_19_42_w16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 16 2 188716128313009586 = some 188716128313009586 := by decide +kernel
private theorem endpoint_19_42_p18 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 18 188716128313009586 = some 188716128313009586 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 16 2 188716128313009586 188716128313009586 188716128313009586 endpoint_19_42_p16 endpoint_19_42_w16
def endpoint_19_42 : CertifiedEndpoint :=
  ⟨⟨19, 42, 2109⟩, 188716128313009586, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_42_flag endpoint_19_42_sources 18 188716128313009586 188716128313009586 rfl endpoint_19_42_base endpoint_19_42_p18) (by decide)⟩
private def endpoint_19_43_flag : Flag := ⟨19, 43, 2054⟩
private def endpoint_19_43_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_43_base : receiptBase endpoint_19_43_flag endpoint_19_43_sources = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_w0 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_w2 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 2 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 4 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 2 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_w0 endpoint_19_43_w2
private theorem endpoint_19_43_w4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 4 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 6 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 4 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_p4 endpoint_19_43_w4
private theorem endpoint_19_43_w6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 6 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 8 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 6 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_p6 endpoint_19_43_w6
private theorem endpoint_19_43_w8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 8 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 10 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 8 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_p8 endpoint_19_43_w8
private theorem endpoint_19_43_w10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 10 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 12 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 10 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_p10 endpoint_19_43_w10
private theorem endpoint_19_43_w12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 12 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 14 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 12 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_p12 endpoint_19_43_w12
private theorem endpoint_19_43_w14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 14 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 16 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 14 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_p14 endpoint_19_43_w14
private theorem endpoint_19_43_w16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 16 2 187729251638972632 = some 187729251638972632 := by decide +kernel
private theorem endpoint_19_43_p18 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 18 187729251638972632 = some 187729251638972632 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 16 2 187729251638972632 187729251638972632 187729251638972632 endpoint_19_43_p16 endpoint_19_43_w16
def endpoint_19_43 : CertifiedEndpoint :=
  ⟨⟨19, 43, 2054⟩, 187729251638972632, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_43_flag endpoint_19_43_sources 18 187729251638972632 187729251638972632 rfl endpoint_19_43_base endpoint_19_43_p18) (by decide)⟩
private def endpoint_19_44_flag : Flag := ⟨19, 44, 1999⟩
private def endpoint_19_44_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_44_base : receiptBase endpoint_19_44_flag endpoint_19_44_sources = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_w0 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_w2 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 2 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 4 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 2 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_w0 endpoint_19_44_w2
private theorem endpoint_19_44_w4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 4 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 6 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 4 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_p4 endpoint_19_44_w4
private theorem endpoint_19_44_w6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 6 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 8 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 6 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_p6 endpoint_19_44_w6
private theorem endpoint_19_44_w8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 8 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 10 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 8 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_p8 endpoint_19_44_w8
private theorem endpoint_19_44_w10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 10 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 12 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 10 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_p10 endpoint_19_44_w10
private theorem endpoint_19_44_w12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 12 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 14 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 12 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_p12 endpoint_19_44_w12
private theorem endpoint_19_44_w14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 14 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 16 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 14 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_p14 endpoint_19_44_w14
private theorem endpoint_19_44_w16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 16 2 186543330042709262 = some 186543330042709262 := by decide +kernel
private theorem endpoint_19_44_p18 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 18 186543330042709262 = some 186543330042709262 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 16 2 186543330042709262 186543330042709262 186543330042709262 endpoint_19_44_p16 endpoint_19_44_w16
def endpoint_19_44 : CertifiedEndpoint :=
  ⟨⟨19, 44, 1999⟩, 186543330042709262, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_44_flag endpoint_19_44_sources 18 186543330042709262 186543330042709262 rfl endpoint_19_44_base endpoint_19_44_p18) (by decide)⟩
private def endpoint_19_45_flag : Flag := ⟨19, 45, 1942⟩
private def endpoint_19_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_45_base : receiptBase endpoint_19_45_flag endpoint_19_45_sources = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_w0 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_w2 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 2 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 4 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 2 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_w0 endpoint_19_45_w2
private theorem endpoint_19_45_w4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 4 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 6 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 4 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_p4 endpoint_19_45_w4
private theorem endpoint_19_45_w6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 6 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 8 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 6 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_p6 endpoint_19_45_w6
private theorem endpoint_19_45_w8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 8 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 10 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 8 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_p8 endpoint_19_45_w8
private theorem endpoint_19_45_w10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 10 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 12 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 10 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_p10 endpoint_19_45_w10
private theorem endpoint_19_45_w12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 12 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 14 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 12 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_p12 endpoint_19_45_w12
private theorem endpoint_19_45_w14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 14 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 16 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 14 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_p14 endpoint_19_45_w14
private theorem endpoint_19_45_w16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 16 2 186950311412877363 = some 186950311412877363 := by decide +kernel
private theorem endpoint_19_45_p18 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 18 186950311412877363 = some 186950311412877363 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 16 2 186950311412877363 186950311412877363 186950311412877363 endpoint_19_45_p16 endpoint_19_45_w16
def endpoint_19_45 : CertifiedEndpoint :=
  ⟨⟨19, 45, 1942⟩, 186950311412877363, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_45_flag endpoint_19_45_sources 18 186950311412877363 186950311412877363 rfl endpoint_19_45_base endpoint_19_45_p18) (by decide)⟩
private def endpoint_19_46_flag : Flag := ⟨19, 46, 1885⟩
private def endpoint_19_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_46_base : receiptBase endpoint_19_46_flag endpoint_19_46_sources = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_w0 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_w2 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 2 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 4 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 2 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_w0 endpoint_19_46_w2
private theorem endpoint_19_46_w4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 4 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 6 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 4 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_p4 endpoint_19_46_w4
private theorem endpoint_19_46_w6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 6 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 8 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 6 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_p6 endpoint_19_46_w6
private theorem endpoint_19_46_w8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 8 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 10 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 8 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_p8 endpoint_19_46_w8
private theorem endpoint_19_46_w10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 10 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 12 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 10 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_p10 endpoint_19_46_w10
private theorem endpoint_19_46_w12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 12 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 14 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 12 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_p12 endpoint_19_46_w12
private theorem endpoint_19_46_w14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 14 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 16 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 14 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_p14 endpoint_19_46_w14
private theorem endpoint_19_46_w16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 16 2 185098505674902487 = some 185098505674902487 := by decide +kernel
private theorem endpoint_19_46_p18 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 18 185098505674902487 = some 185098505674902487 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 16 2 185098505674902487 185098505674902487 185098505674902487 endpoint_19_46_p16 endpoint_19_46_w16
def endpoint_19_46 : CertifiedEndpoint :=
  ⟨⟨19, 46, 1885⟩, 185098505674902487, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_46_flag endpoint_19_46_sources 18 185098505674902487 185098505674902487 rfl endpoint_19_46_base endpoint_19_46_p18) (by decide)⟩
private def endpoint_19_47_flag : Flag := ⟨19, 47, 1826⟩
private def endpoint_19_47_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_47_base : receiptBase endpoint_19_47_flag endpoint_19_47_sources = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_w0 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_w2 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 2 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 4 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 2 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_w0 endpoint_19_47_w2
private theorem endpoint_19_47_w4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 4 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 6 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 4 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_p4 endpoint_19_47_w4
private theorem endpoint_19_47_w6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 6 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 8 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 6 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_p6 endpoint_19_47_w6
private theorem endpoint_19_47_w8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 8 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 10 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 8 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_p8 endpoint_19_47_w8
private theorem endpoint_19_47_w10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 10 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 12 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 10 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_p10 endpoint_19_47_w10
private theorem endpoint_19_47_w12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 12 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 14 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 12 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_p12 endpoint_19_47_w12
private theorem endpoint_19_47_w14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 14 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 16 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 14 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_p14 endpoint_19_47_w14
private theorem endpoint_19_47_w16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 16 2 182841043507916730 = some 182841043507916730 := by decide +kernel
private theorem endpoint_19_47_p18 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 18 182841043507916730 = some 182841043507916730 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 16 2 182841043507916730 182841043507916730 182841043507916730 endpoint_19_47_p16 endpoint_19_47_w16
def endpoint_19_47 : CertifiedEndpoint :=
  ⟨⟨19, 47, 1826⟩, 182841043507916730, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_47_flag endpoint_19_47_sources 18 182841043507916730 182841043507916730 rfl endpoint_19_47_base endpoint_19_47_p18) (by decide)⟩
private def endpoint_19_48_flag : Flag := ⟨19, 48, 1767⟩
private def endpoint_19_48_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_48_base : receiptBase endpoint_19_48_flag endpoint_19_48_sources = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_w0 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_w2 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 2 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 4 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 2 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_w0 endpoint_19_48_w2
private theorem endpoint_19_48_w4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 4 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 6 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 4 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_p4 endpoint_19_48_w4
private theorem endpoint_19_48_w6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 6 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 8 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 6 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_p6 endpoint_19_48_w6
private theorem endpoint_19_48_w8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 8 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 10 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 8 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_p8 endpoint_19_48_w8
private theorem endpoint_19_48_w10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 10 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 12 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 10 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_p10 endpoint_19_48_w10
private theorem endpoint_19_48_w12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 12 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 14 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 12 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_p12 endpoint_19_48_w12
private theorem endpoint_19_48_w14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 14 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 16 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 14 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_p14 endpoint_19_48_w14
private theorem endpoint_19_48_w16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 16 2 180366441648324022 = some 180366441648324022 := by decide +kernel
private theorem endpoint_19_48_p18 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 18 180366441648324022 = some 180366441648324022 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 16 2 180366441648324022 180366441648324022 180366441648324022 endpoint_19_48_p16 endpoint_19_48_w16
def endpoint_19_48 : CertifiedEndpoint :=
  ⟨⟨19, 48, 1767⟩, 180366441648324022, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_48_flag endpoint_19_48_sources 18 180366441648324022 180366441648324022 rfl endpoint_19_48_base endpoint_19_48_p18) (by decide)⟩
private def endpoint_19_49_flag : Flag := ⟨19, 49, 1706⟩
private def endpoint_19_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_49_base : receiptBase endpoint_19_49_flag endpoint_19_49_sources = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_w0 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_w2 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 2 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 4 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 2 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_w0 endpoint_19_49_w2
private theorem endpoint_19_49_w4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 4 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 6 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 4 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_p4 endpoint_19_49_w4
private theorem endpoint_19_49_w6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 6 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 8 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 6 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_p6 endpoint_19_49_w6
private theorem endpoint_19_49_w8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 8 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 10 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 8 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_p8 endpoint_19_49_w8
private theorem endpoint_19_49_w10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 10 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 12 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 10 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_p10 endpoint_19_49_w10
private theorem endpoint_19_49_w12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 12 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 14 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 12 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_p12 endpoint_19_49_w12
private theorem endpoint_19_49_w14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 14 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 16 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 14 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_p14 endpoint_19_49_w14
private theorem endpoint_19_49_w16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 16 2 179392380307259440 = some 179392380307259440 := by decide +kernel
private theorem endpoint_19_49_p18 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 18 179392380307259440 = some 179392380307259440 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 16 2 179392380307259440 179392380307259440 179392380307259440 endpoint_19_49_p16 endpoint_19_49_w16
def endpoint_19_49 : CertifiedEndpoint :=
  ⟨⟨19, 49, 1706⟩, 179392380307259440, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_49_flag endpoint_19_49_sources 18 179392380307259440 179392380307259440 rfl endpoint_19_49_base endpoint_19_49_p18) (by decide)⟩
private def endpoint_19_50_flag : Flag := ⟨19, 50, 1644⟩
private def endpoint_19_50_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_50_base : receiptBase endpoint_19_50_flag endpoint_19_50_sources = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_w0 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_w2 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 2 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 4 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 2 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_w0 endpoint_19_50_w2
private theorem endpoint_19_50_w4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 4 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 6 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 4 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_p4 endpoint_19_50_w4
private theorem endpoint_19_50_w6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 6 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 8 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 6 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_p6 endpoint_19_50_w6
private theorem endpoint_19_50_w8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 8 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 10 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 8 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_p8 endpoint_19_50_w8
private theorem endpoint_19_50_w10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 10 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 12 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 10 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_p10 endpoint_19_50_w10
private theorem endpoint_19_50_w12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 12 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 14 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 12 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_p12 endpoint_19_50_w12
private theorem endpoint_19_50_w14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 14 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 16 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 14 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_p14 endpoint_19_50_w14
private theorem endpoint_19_50_w16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 16 2 176011851760310660 = some 176011851760310660 := by decide +kernel
private theorem endpoint_19_50_p18 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 18 176011851760310660 = some 176011851760310660 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 16 2 176011851760310660 176011851760310660 176011851760310660 endpoint_19_50_p16 endpoint_19_50_w16
def endpoint_19_50 : CertifiedEndpoint :=
  ⟨⟨19, 50, 1644⟩, 176011851760310660, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_50_flag endpoint_19_50_sources 18 176011851760310660 176011851760310660 rfl endpoint_19_50_base endpoint_19_50_p18) (by decide)⟩
private def endpoint_19_51_flag : Flag := ⟨19, 51, 1581⟩
private def endpoint_19_51_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_51_base : receiptBase endpoint_19_51_flag endpoint_19_51_sources = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_w0 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_w2 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 2 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 4 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 2 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_w0 endpoint_19_51_w2
private theorem endpoint_19_51_w4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 4 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 6 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 4 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_p4 endpoint_19_51_w4
private theorem endpoint_19_51_w6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 6 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 8 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 6 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_p6 endpoint_19_51_w6
private theorem endpoint_19_51_w8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 8 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 10 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 8 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_p8 endpoint_19_51_w8
private theorem endpoint_19_51_w10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 10 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 12 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 10 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_p10 endpoint_19_51_w10
private theorem endpoint_19_51_w12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 12 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 14 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 12 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_p12 endpoint_19_51_w12
private theorem endpoint_19_51_w14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 14 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 16 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 14 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_p14 endpoint_19_51_w14
private theorem endpoint_19_51_w16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 16 2 172294853425682938 = some 172294853425682938 := by decide +kernel
private theorem endpoint_19_51_p18 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 18 172294853425682938 = some 172294853425682938 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 16 2 172294853425682938 172294853425682938 172294853425682938 endpoint_19_51_p16 endpoint_19_51_w16
def endpoint_19_51 : CertifiedEndpoint :=
  ⟨⟨19, 51, 1581⟩, 172294853425682938, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_51_flag endpoint_19_51_sources 18 172294853425682938 172294853425682938 rfl endpoint_19_51_base endpoint_19_51_p18) (by decide)⟩
private def endpoint_19_52_flag : Flag := ⟨19, 52, 1517⟩
private def endpoint_19_52_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_52_base : receiptBase endpoint_19_52_flag endpoint_19_52_sources = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_w0 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_w2 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 2 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 4 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 2 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_w0 endpoint_19_52_w2
private theorem endpoint_19_52_w4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 4 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 6 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 4 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_p4 endpoint_19_52_w4
private theorem endpoint_19_52_w6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 6 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 8 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 6 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_p6 endpoint_19_52_w6
private theorem endpoint_19_52_w8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 8 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 10 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 8 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_p8 endpoint_19_52_w8
private theorem endpoint_19_52_w10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 10 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 12 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 10 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_p10 endpoint_19_52_w10
private theorem endpoint_19_52_w12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 12 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 14 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 12 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_p12 endpoint_19_52_w12
private theorem endpoint_19_52_w14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 14 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 16 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 14 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_p14 endpoint_19_52_w14
private theorem endpoint_19_52_w16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 16 2 168235887337862721 = some 168235887337862721 := by decide +kernel
private theorem endpoint_19_52_p18 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 18 168235887337862721 = some 168235887337862721 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 16 2 168235887337862721 168235887337862721 168235887337862721 endpoint_19_52_p16 endpoint_19_52_w16
def endpoint_19_52 : CertifiedEndpoint :=
  ⟨⟨19, 52, 1517⟩, 168235887337862721, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_52_flag endpoint_19_52_sources 18 168235887337862721 168235887337862721 rfl endpoint_19_52_base endpoint_19_52_p18) (by decide)⟩
private def endpoint_19_53_flag : Flag := ⟨19, 53, 1452⟩
private def endpoint_19_53_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_53_base : receiptBase endpoint_19_53_flag endpoint_19_53_sources = some 163829455531336454 := by decide +kernel
private theorem endpoint_19_53_w0 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 2 163829455531336454 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_w2 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 2 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 4 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 2 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_w0 endpoint_19_53_w2
private theorem endpoint_19_53_w4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 4 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 6 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 4 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_p4 endpoint_19_53_w4
private theorem endpoint_19_53_w6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 6 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 8 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 6 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_p6 endpoint_19_53_w6
private theorem endpoint_19_53_w8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 8 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 10 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 8 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_p8 endpoint_19_53_w8
private theorem endpoint_19_53_w10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 10 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 12 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 10 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_p10 endpoint_19_53_w10
private theorem endpoint_19_53_w12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 12 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 14 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 12 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_p12 endpoint_19_53_w12
private theorem endpoint_19_53_w14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 14 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 16 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 14 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_p14 endpoint_19_53_w14
private theorem endpoint_19_53_w16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 16 2 167823801950592363 = some 167823801950592363 := by decide +kernel
private theorem endpoint_19_53_p18 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 18 163829455531336454 = some 167823801950592363 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 16 2 163829455531336454 167823801950592363 167823801950592363 endpoint_19_53_p16 endpoint_19_53_w16
def endpoint_19_53 : CertifiedEndpoint :=
  ⟨⟨19, 53, 1452⟩, 167823801950592363, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_53_flag endpoint_19_53_sources 18 163829455531336454 167823801950592363 rfl endpoint_19_53_base endpoint_19_53_p18) (by decide)⟩
private def endpoint_19_54_flag : Flag := ⟨19, 54, 1386⟩
private def endpoint_19_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_54_base : receiptBase endpoint_19_54_flag endpoint_19_54_sources = some 159070060040590583 := by decide +kernel
private theorem endpoint_19_54_w0 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 2 159070060040590583 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_w2 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 2 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 4 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 2 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_w0 endpoint_19_54_w2
private theorem endpoint_19_54_w4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 4 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 6 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 4 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_p4 endpoint_19_54_w4
private theorem endpoint_19_54_w6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 6 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 8 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 6 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_p6 endpoint_19_54_w6
private theorem endpoint_19_54_w8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 8 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 10 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 8 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_p8 endpoint_19_54_w8
private theorem endpoint_19_54_w10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 10 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 12 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 10 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_p10 endpoint_19_54_w10
private theorem endpoint_19_54_w12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 12 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 14 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 12 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_p12 endpoint_19_54_w12
private theorem endpoint_19_54_w14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 14 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 16 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 14 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_p14 endpoint_19_54_w14
private theorem endpoint_19_54_w16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 16 2 167430877766133696 = some 167430877766133696 := by decide +kernel
private theorem endpoint_19_54_p18 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 18 159070060040590583 = some 167430877766133696 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 16 2 159070060040590583 167430877766133696 167430877766133696 endpoint_19_54_p16 endpoint_19_54_w16
def endpoint_19_54 : CertifiedEndpoint :=
  ⟨⟨19, 54, 1386⟩, 167430877766133696, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_54_flag endpoint_19_54_sources 18 159070060040590583 167430877766133696 rfl endpoint_19_54_base endpoint_19_54_p18) (by decide)⟩
private def endpoint_19_55_flag : Flag := ⟨19, 55, 1318⟩
private def endpoint_19_55_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_55_base : receiptBase endpoint_19_55_flag endpoint_19_55_sources = some 154088987123691845 := by decide +kernel
private theorem endpoint_19_55_w0 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 2 154088987123691845 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_w2 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 2 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 4 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 2 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_w0 endpoint_19_55_w2
private theorem endpoint_19_55_w4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 4 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 6 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 4 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_p4 endpoint_19_55_w4
private theorem endpoint_19_55_w6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 6 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 8 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 6 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_p6 endpoint_19_55_w6
private theorem endpoint_19_55_w8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 8 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 10 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 8 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_p8 endpoint_19_55_w8
private theorem endpoint_19_55_w10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 10 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 12 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 10 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_p10 endpoint_19_55_w10
private theorem endpoint_19_55_w12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 12 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 14 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 12 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_p12 endpoint_19_55_w12
private theorem endpoint_19_55_w14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 14 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 16 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 14 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_p14 endpoint_19_55_w14
private theorem endpoint_19_55_w16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 16 2 164128736486292180 = some 164128736486292180 := by decide +kernel
private theorem endpoint_19_55_p18 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 18 154088987123691845 = some 164128736486292180 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 16 2 154088987123691845 164128736486292180 164128736486292180 endpoint_19_55_p16 endpoint_19_55_w16
def endpoint_19_55 : CertifiedEndpoint :=
  ⟨⟨19, 55, 1318⟩, 164128736486292180, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_55_flag endpoint_19_55_sources 18 154088987123691845 164128736486292180 rfl endpoint_19_55_base endpoint_19_55_p18) (by decide)⟩
private def endpoint_19_56_flag : Flag := ⟨19, 56, 1249⟩
private def endpoint_19_56_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_56_base : receiptBase endpoint_19_56_flag endpoint_19_56_sources = some 149797388596074832 := by decide +kernel
private theorem endpoint_19_56_w0 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 2 149797388596074832 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_w2 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 2 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 4 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 2 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_w0 endpoint_19_56_w2
private theorem endpoint_19_56_w4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 4 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 6 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 4 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_p4 endpoint_19_56_w4
private theorem endpoint_19_56_w6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 6 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 8 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 6 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_p6 endpoint_19_56_w6
private theorem endpoint_19_56_w8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 8 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 10 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 8 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_p8 endpoint_19_56_w8
private theorem endpoint_19_56_w10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 10 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 12 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 10 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_p10 endpoint_19_56_w10
private theorem endpoint_19_56_w12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 12 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 14 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 12 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_p12 endpoint_19_56_w12
private theorem endpoint_19_56_w14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 14 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 16 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 14 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_p14 endpoint_19_56_w14
private theorem endpoint_19_56_w16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 16 2 156277604729435888 = some 156277604729435888 := by decide +kernel
private theorem endpoint_19_56_p18 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 18 149797388596074832 = some 156277604729435888 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 16 2 149797388596074832 156277604729435888 156277604729435888 endpoint_19_56_p16 endpoint_19_56_w16
def endpoint_19_56 : CertifiedEndpoint :=
  ⟨⟨19, 56, 1249⟩, 156277604729435888, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_56_flag endpoint_19_56_sources 18 149797388596074832 156277604729435888 rfl endpoint_19_56_base endpoint_19_56_p18) (by decide)⟩
def endpoint_19_57 : CertifiedEndpoint :=
  ⟨⟨19, 57, 1178⟩, 256993144548487325, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_58 : CertifiedEndpoint :=
  ⟨⟨19, 58, 1106⟩, 245837889324962990, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_59 : CertifiedEndpoint :=
  ⟨⟨19, 59, 1033⟩, 233756057791802370, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_60 : CertifiedEndpoint :=
  ⟨⟨19, 60, 958⟩, 220494506840221158, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_61 : CertifiedEndpoint :=
  ⟨⟨19, 61, 882⟩, 206268170603068797, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_62 : CertifiedEndpoint :=
  ⟨⟨19, 62, 804⟩, 190814353727577264, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_63 : CertifiedEndpoint :=
  ⟨⟨19, 63, 725⟩, 174357542590579718, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_64 : CertifiedEndpoint :=
  ⟨⟨19, 64, 644⟩, 156625489595324420, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_65 : CertifiedEndpoint :=
  ⟨⟨19, 65, 561⟩, 137589538009860222, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_66 : CertifiedEndpoint :=
  ⟨⟨19, 66, 476⟩, 117221031102235976, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_67 : CertifiedEndpoint :=
  ⟨⟨19, 67, 390⟩, 95763559737252273, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_68 : CertifiedEndpoint :=
  ⟨⟨19, 68, 301⟩, 72648748111446345, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_69 : CertifiedEndpoint :=
  ⟨⟨19, 69, 211⟩, 48397210808362380, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_70 : CertifiedEndpoint :=
  ⟨⟨19, 70, 119⟩, 22708043499297491, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_20 : CertifiedEndpoint :=
  ⟨⟨20, 20, 2763⟩, 150021766238417883, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_21 : CertifiedEndpoint :=
  ⟨⟨20, 21, 2721⟩, 152203997156694546, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_22 : CertifiedEndpoint :=
  ⟨⟨20, 22, 2679⟩, 154246964581675149, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_23 : CertifiedEndpoint :=
  ⟨⟨20, 23, 2636⟩, 164913270776649281, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_24 : CertifiedEndpoint :=
  ⟨⟨20, 24, 2593⟩, 175141634081686843, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_25 : CertifiedEndpoint :=
  ⟨⟨20, 25, 2549⟩, 184859055369097834, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_26 : CertifiedEndpoint :=
  ⟨⟨20, 26, 2504⟩, 194050433159918924, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_27 : CertifiedEndpoint :=
  ⟨⟨20, 27, 2458⟩, 202700665975186783, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_28 : CertifiedEndpoint :=
  ⟨⟨20, 28, 2412⟩, 210882752942591412, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_29 : CertifiedEndpoint :=
  ⟨⟨20, 29, 2366⟩, 218596694062132811, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_30 : CertifiedEndpoint :=
  ⟨⟨20, 30, 2318⟩, 225646152815219878, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_31 : CertifiedEndpoint :=
  ⟨⟨20, 31, 2270⟩, 232207330415159275, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_32 : CertifiedEndpoint :=
  ⟨⟨20, 32, 2222⟩, 238280226861951002, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_33 : CertifiedEndpoint :=
  ⟨⟨20, 33, 2172⟩, 243638302679077297, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_34 : CertifiedEndpoint :=
  ⟨⟨20, 34, 2122⟩, 248487962037771482, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_35 : CertifiedEndpoint :=
  ⟨⟨20, 35, 2071⟩, 252705867547132456, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_36 : CertifiedEndpoint :=
  ⟨⟨20, 36, 2019⟩, 256276917728196889, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_37 : CertifiedEndpoint :=
  ⟨⟨20, 37, 1966⟩, 259186011102001451, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_38 : CertifiedEndpoint :=
  ⟨⟨20, 38, 1913⟩, 261556485059447243, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_39 : CertifiedEndpoint :=
  ⟨⟨20, 39, 1859⟩, 263244866904348724, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_40 : CertifiedEndpoint :=
  ⟨⟨20, 40, 1804⟩, 264236055157742564, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_41 : CertifiedEndpoint :=
  ⟨⟨20, 41, 1748⟩, 264514948340665433, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_42 : CertifiedEndpoint :=
  ⟨⟨20, 42, 1691⟩, 264066444974154001, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_43 : CertifiedEndpoint :=
  ⟨⟨20, 43, 1633⟩, 262875443579244938, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_44 : CertifiedEndpoint :=
  ⟨⟨20, 44, 1574⟩, 260926842676974914, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock12 : List CertifiedEndpoint := [
  endpoint_18_32, endpoint_18_33, endpoint_18_34, endpoint_18_35, endpoint_18_36, endpoint_18_37, endpoint_18_38,
  endpoint_18_39, endpoint_18_40, endpoint_18_41, endpoint_18_42, endpoint_18_43, endpoint_18_44, endpoint_18_45,
  endpoint_18_46, endpoint_18_47, endpoint_18_48, endpoint_18_49, endpoint_18_50, endpoint_18_51, endpoint_18_52,
  endpoint_18_53, endpoint_18_54, endpoint_18_55, endpoint_18_56, endpoint_18_57, endpoint_18_58, endpoint_18_59,
  endpoint_18_60, endpoint_18_61, endpoint_18_62, endpoint_18_63, endpoint_18_64, endpoint_18_65, endpoint_18_66,
  endpoint_18_67, endpoint_18_68, endpoint_18_69, endpoint_18_70, endpoint_18_71, endpoint_18_72, endpoint_18_73,
  endpoint_18_74, endpoint_19_19, endpoint_19_20, endpoint_19_21, endpoint_19_22, endpoint_19_23, endpoint_19_24,
  endpoint_19_25, endpoint_19_26, endpoint_19_27, endpoint_19_28, endpoint_19_29, endpoint_19_30, endpoint_19_31,
  endpoint_19_32, endpoint_19_33, endpoint_19_34, endpoint_19_35, endpoint_19_36, endpoint_19_37, endpoint_19_38,
  endpoint_19_39, endpoint_19_40, endpoint_19_41, endpoint_19_42, endpoint_19_43, endpoint_19_44, endpoint_19_45,
  endpoint_19_46, endpoint_19_47, endpoint_19_48, endpoint_19_49, endpoint_19_50, endpoint_19_51, endpoint_19_52,
  endpoint_19_53, endpoint_19_54, endpoint_19_55, endpoint_19_56, endpoint_19_57, endpoint_19_58, endpoint_19_59,
  endpoint_19_60, endpoint_19_61, endpoint_19_62, endpoint_19_63, endpoint_19_64, endpoint_19_65, endpoint_19_66,
  endpoint_19_67, endpoint_19_68, endpoint_19_69, endpoint_19_70, endpoint_20_20, endpoint_20_21, endpoint_20_22,
  endpoint_20_23, endpoint_20_24, endpoint_20_25, endpoint_20_26, endpoint_20_27, endpoint_20_28, endpoint_20_29,
  endpoint_20_30, endpoint_20_31, endpoint_20_32, endpoint_20_33, endpoint_20_34, endpoint_20_35, endpoint_20_36,
  endpoint_20_37, endpoint_20_38, endpoint_20_39, endpoint_20_40, endpoint_20_41, endpoint_20_42, endpoint_20_43,
  endpoint_20_44
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
