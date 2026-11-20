import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_18_47_flag : Flag := ⟨18, 47, 2358⟩
private def endpoint_18_47_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_47_base : receiptBase endpoint_18_47_flag endpoint_18_47_sources = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_w0 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_w2 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 2 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 4 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 2 2 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_w0 endpoint_18_47_w2
private theorem endpoint_18_47_w4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 4 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 6 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 4 2 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_p4 endpoint_18_47_w4
private theorem endpoint_18_47_w6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 6 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 8 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 6 2 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_p6 endpoint_18_47_w6
private theorem endpoint_18_47_w8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 8 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 10 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 8 2 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_p8 endpoint_18_47_w8
private theorem endpoint_18_47_w10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 10 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 12 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 10 2 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_p10 endpoint_18_47_w10
private theorem endpoint_18_47_w12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 12 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 14 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 12 2 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_p12 endpoint_18_47_w12
private theorem endpoint_18_47_w14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 14 2 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 16 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 14 2 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_p14 endpoint_18_47_w14
private theorem endpoint_18_47_w16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 16 1 223351549254127951 = some 223351549254127951 := by decide +kernel
private theorem endpoint_18_47_p17 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 17 223351549254127951 = some 223351549254127951 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 16 1 223351549254127951 223351549254127951 223351549254127951 endpoint_18_47_p16 endpoint_18_47_w16
def endpoint_18_47 : CertifiedEndpoint :=
  ⟨⟨18, 47, 2358⟩, 223351549254127951, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_47_flag endpoint_18_47_sources 17 223351549254127951 223351549254127951 rfl endpoint_18_47_base endpoint_18_47_p17) (by decide)⟩
private def endpoint_18_48_flag : Flag := ⟨18, 48, 2303⟩
private def endpoint_18_48_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_48_base : receiptBase endpoint_18_48_flag endpoint_18_48_sources = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_w0 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_w2 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 2 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 4 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 2 2 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_w0 endpoint_18_48_w2
private theorem endpoint_18_48_w4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 4 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 6 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 4 2 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_p4 endpoint_18_48_w4
private theorem endpoint_18_48_w6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 6 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 8 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 6 2 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_p6 endpoint_18_48_w6
private theorem endpoint_18_48_w8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 8 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 10 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 8 2 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_p8 endpoint_18_48_w8
private theorem endpoint_18_48_w10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 10 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 12 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 10 2 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_p10 endpoint_18_48_w10
private theorem endpoint_18_48_w12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 12 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 14 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 12 2 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_p12 endpoint_18_48_w12
private theorem endpoint_18_48_w14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 14 2 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 16 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 14 2 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_p14 endpoint_18_48_w14
private theorem endpoint_18_48_w16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 16 1 223217120660734375 = some 223217120660734375 := by decide +kernel
private theorem endpoint_18_48_p17 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 17 223217120660734375 = some 223217120660734375 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 16 1 223217120660734375 223217120660734375 223217120660734375 endpoint_18_48_p16 endpoint_18_48_w16
def endpoint_18_48 : CertifiedEndpoint :=
  ⟨⟨18, 48, 2303⟩, 223217120660734375, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_48_flag endpoint_18_48_sources 17 223217120660734375 223217120660734375 rfl endpoint_18_48_base endpoint_18_48_p17) (by decide)⟩
private def endpoint_18_49_flag : Flag := ⟨18, 49, 2247⟩
private def endpoint_18_49_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_49_base : receiptBase endpoint_18_49_flag endpoint_18_49_sources = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_w0 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_w2 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 2 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 4 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 2 2 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_w0 endpoint_18_49_w2
private theorem endpoint_18_49_w4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 4 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 6 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 4 2 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_p4 endpoint_18_49_w4
private theorem endpoint_18_49_w6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 6 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 8 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 6 2 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_p6 endpoint_18_49_w6
private theorem endpoint_18_49_w8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 8 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 10 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 8 2 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_p8 endpoint_18_49_w8
private theorem endpoint_18_49_w10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 10 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 12 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 10 2 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_p10 endpoint_18_49_w10
private theorem endpoint_18_49_w12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 12 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 14 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 12 2 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_p12 endpoint_18_49_w12
private theorem endpoint_18_49_w14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 14 2 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 16 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 14 2 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_p14 endpoint_18_49_w14
private theorem endpoint_18_49_w16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 16 1 221902421269404201 = some 221902421269404201 := by decide +kernel
private theorem endpoint_18_49_p17 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 17 221902421269404201 = some 221902421269404201 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 16 1 221902421269404201 221902421269404201 221902421269404201 endpoint_18_49_p16 endpoint_18_49_w16
def endpoint_18_49 : CertifiedEndpoint :=
  ⟨⟨18, 49, 2247⟩, 221902421269404201, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_49_flag endpoint_18_49_sources 17 221902421269404201 221902421269404201 rfl endpoint_18_49_base endpoint_18_49_p17) (by decide)⟩
private def endpoint_18_50_flag : Flag := ⟨18, 50, 2190⟩
private def endpoint_18_50_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_50_base : receiptBase endpoint_18_50_flag endpoint_18_50_sources = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_w0 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_w2 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 2 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 4 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 2 2 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_w0 endpoint_18_50_w2
private theorem endpoint_18_50_w4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 4 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 6 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 4 2 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_p4 endpoint_18_50_w4
private theorem endpoint_18_50_w6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 6 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 8 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 6 2 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_p6 endpoint_18_50_w6
private theorem endpoint_18_50_w8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 8 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 10 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 8 2 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_p8 endpoint_18_50_w8
private theorem endpoint_18_50_w10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 10 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 12 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 10 2 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_p10 endpoint_18_50_w10
private theorem endpoint_18_50_w12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 12 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 14 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 12 2 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_p12 endpoint_18_50_w12
private theorem endpoint_18_50_w14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 14 2 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 16 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 14 2 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_p14 endpoint_18_50_w14
private theorem endpoint_18_50_w16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 16 1 220294806402248835 = some 220294806402248835 := by decide +kernel
private theorem endpoint_18_50_p17 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 17 220294806402248835 = some 220294806402248835 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 16 1 220294806402248835 220294806402248835 220294806402248835 endpoint_18_50_p16 endpoint_18_50_w16
def endpoint_18_50 : CertifiedEndpoint :=
  ⟨⟨18, 50, 2190⟩, 220294806402248835, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_50_flag endpoint_18_50_sources 17 220294806402248835 220294806402248835 rfl endpoint_18_50_base endpoint_18_50_p17) (by decide)⟩
private def endpoint_18_51_flag : Flag := ⟨18, 51, 2132⟩
private def endpoint_18_51_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_18_51_base : receiptBase endpoint_18_51_flag endpoint_18_51_sources = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_w0 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_w2 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 2 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 4 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 2 2 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_w0 endpoint_18_51_w2
private theorem endpoint_18_51_w4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 4 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 6 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 4 2 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_p4 endpoint_18_51_w4
private theorem endpoint_18_51_w6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 6 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 8 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 6 2 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_p6 endpoint_18_51_w6
private theorem endpoint_18_51_w8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 8 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 10 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 8 2 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_p8 endpoint_18_51_w8
private theorem endpoint_18_51_w10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 10 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 12 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 10 2 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_p10 endpoint_18_51_w10
private theorem endpoint_18_51_w12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 12 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 14 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 12 2 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_p12 endpoint_18_51_w12
private theorem endpoint_18_51_w14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 14 2 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 16 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 14 2 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_p14 endpoint_18_51_w14
private theorem endpoint_18_51_w16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 16 1 218454460476033539 = some 218454460476033539 := by decide +kernel
private theorem endpoint_18_51_p17 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 17 218454460476033539 = some 218454460476033539 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 16 1 218454460476033539 218454460476033539 218454460476033539 endpoint_18_51_p16 endpoint_18_51_w16
def endpoint_18_51 : CertifiedEndpoint :=
  ⟨⟨18, 51, 2132⟩, 218454460476033539, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_18_51_flag endpoint_18_51_sources 17 218454460476033539 218454460476033539 rfl endpoint_18_51_base endpoint_18_51_p17) (by decide)⟩
private def endpoint_18_52_flag : Flag := ⟨18, 52, 2072⟩
private def endpoint_18_52_sources : Sources := ⟨contact29, contact16, contact12⟩
private theorem endpoint_18_52_base : receiptBase endpoint_18_52_flag endpoint_18_52_sources = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_w0 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_w2 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 2 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 4 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 2 2 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_w0 endpoint_18_52_w2
private theorem endpoint_18_52_w4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 4 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 6 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 4 2 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_p4 endpoint_18_52_w4
private theorem endpoint_18_52_w6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 6 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 8 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 6 2 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_p6 endpoint_18_52_w6
private theorem endpoint_18_52_w8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 8 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 10 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 8 2 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_p8 endpoint_18_52_w8
private theorem endpoint_18_52_w10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 10 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 12 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 10 2 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_p10 endpoint_18_52_w10
private theorem endpoint_18_52_w12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 12 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 14 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 12 2 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_p12 endpoint_18_52_w12
private theorem endpoint_18_52_w14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 14 2 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 16 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 14 2 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_p14 endpoint_18_52_w14
private theorem endpoint_18_52_w16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 16 1 216644585967104287 = some 216644585967104287 := by decide +kernel
private theorem endpoint_18_52_p17 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 17 216644585967104287 = some 216644585967104287 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 16 1 216644585967104287 216644585967104287 216644585967104287 endpoint_18_52_p16 endpoint_18_52_w16
def endpoint_18_52 : CertifiedEndpoint :=
  ⟨⟨18, 52, 2072⟩, 216644585967104287, .terminal ⟨contact29, contact16, contact12⟩ (finish_receipt_window endpoint_18_52_flag endpoint_18_52_sources 17 216644585967104287 216644585967104287 rfl endpoint_18_52_base endpoint_18_52_p17) (by decide)⟩
private def endpoint_18_53_flag : Flag := ⟨18, 53, 2012⟩
private def endpoint_18_53_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_18_53_base : receiptBase endpoint_18_53_flag endpoint_18_53_sources = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_w0 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_w2 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 2 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 4 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 2 2 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_w0 endpoint_18_53_w2
private theorem endpoint_18_53_w4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 4 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 6 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 4 2 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_p4 endpoint_18_53_w4
private theorem endpoint_18_53_w6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 6 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 8 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 6 2 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_p6 endpoint_18_53_w6
private theorem endpoint_18_53_w8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 8 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 10 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 8 2 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_p8 endpoint_18_53_w8
private theorem endpoint_18_53_w10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 10 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 12 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 10 2 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_p10 endpoint_18_53_w10
private theorem endpoint_18_53_w12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 12 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 14 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 12 2 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_p12 endpoint_18_53_w12
private theorem endpoint_18_53_w14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 14 2 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 16 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 14 2 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_p14 endpoint_18_53_w14
private theorem endpoint_18_53_w16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 16 1 215877868653861575 = some 215877868653861575 := by decide +kernel
private theorem endpoint_18_53_p17 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 17 215877868653861575 = some 215877868653861575 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 16 1 215877868653861575 215877868653861575 215877868653861575 endpoint_18_53_p16 endpoint_18_53_w16
def endpoint_18_53 : CertifiedEndpoint :=
  ⟨⟨18, 53, 2012⟩, 215877868653861575, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_18_53_flag endpoint_18_53_sources 17 215877868653861575 215877868653861575 rfl endpoint_18_53_base endpoint_18_53_p17) (by decide)⟩
private def endpoint_18_54_flag : Flag := ⟨18, 54, 1950⟩
private def endpoint_18_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_54_base : receiptBase endpoint_18_54_flag endpoint_18_54_sources = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_w0 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_w2 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 2 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 4 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 2 2 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_w0 endpoint_18_54_w2
private theorem endpoint_18_54_w4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 4 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 6 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 4 2 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_p4 endpoint_18_54_w4
private theorem endpoint_18_54_w6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 6 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 8 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 6 2 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_p6 endpoint_18_54_w6
private theorem endpoint_18_54_w8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 8 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 10 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 8 2 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_p8 endpoint_18_54_w8
private theorem endpoint_18_54_w10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 10 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 12 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 10 2 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_p10 endpoint_18_54_w10
private theorem endpoint_18_54_w12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 12 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 14 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 12 2 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_p12 endpoint_18_54_w12
private theorem endpoint_18_54_w14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 14 2 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 16 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 14 2 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_p14 endpoint_18_54_w14
private theorem endpoint_18_54_w16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 16 1 215090377554361365 = some 215090377554361365 := by decide +kernel
private theorem endpoint_18_54_p17 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 17 215090377554361365 = some 215090377554361365 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 16 1 215090377554361365 215090377554361365 215090377554361365 endpoint_18_54_p16 endpoint_18_54_w16
def endpoint_18_54 : CertifiedEndpoint :=
  ⟨⟨18, 54, 1950⟩, 215090377554361365, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_54_flag endpoint_18_54_sources 17 215090377554361365 215090377554361365 rfl endpoint_18_54_base endpoint_18_54_p17) (by decide)⟩
private def endpoint_18_55_flag : Flag := ⟨18, 55, 1886⟩
private def endpoint_18_55_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_55_base : receiptBase endpoint_18_55_flag endpoint_18_55_sources = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_w0 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_w2 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 2 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 4 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 2 2 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_w0 endpoint_18_55_w2
private theorem endpoint_18_55_w4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 4 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 6 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 4 2 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_p4 endpoint_18_55_w4
private theorem endpoint_18_55_w6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 6 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 8 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 6 2 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_p6 endpoint_18_55_w6
private theorem endpoint_18_55_w8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 8 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 10 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 8 2 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_p8 endpoint_18_55_w8
private theorem endpoint_18_55_w10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 10 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 12 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 10 2 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_p10 endpoint_18_55_w10
private theorem endpoint_18_55_w12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 12 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 14 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 12 2 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_p12 endpoint_18_55_w12
private theorem endpoint_18_55_w14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 14 2 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 16 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 14 2 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_p14 endpoint_18_55_w14
private theorem endpoint_18_55_w16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 16 1 211465889797645042 = some 211465889797645042 := by decide +kernel
private theorem endpoint_18_55_p17 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 17 211465889797645042 = some 211465889797645042 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 16 1 211465889797645042 211465889797645042 211465889797645042 endpoint_18_55_p16 endpoint_18_55_w16
def endpoint_18_55 : CertifiedEndpoint :=
  ⟨⟨18, 55, 1886⟩, 211465889797645042, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_55_flag endpoint_18_55_sources 17 211465889797645042 211465889797645042 rfl endpoint_18_55_base endpoint_18_55_p17) (by decide)⟩
private def endpoint_18_56_flag : Flag := ⟨18, 56, 1822⟩
private def endpoint_18_56_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_56_base : receiptBase endpoint_18_56_flag endpoint_18_56_sources = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_w0 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_w2 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 2 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 4 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 2 2 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_w0 endpoint_18_56_w2
private theorem endpoint_18_56_w4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 4 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 6 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 4 2 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_p4 endpoint_18_56_w4
private theorem endpoint_18_56_w6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 6 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 8 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 6 2 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_p6 endpoint_18_56_w6
private theorem endpoint_18_56_w8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 8 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 10 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 8 2 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_p8 endpoint_18_56_w8
private theorem endpoint_18_56_w10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 10 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 12 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 10 2 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_p10 endpoint_18_56_w10
private theorem endpoint_18_56_w12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 12 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 14 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 12 2 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_p12 endpoint_18_56_w12
private theorem endpoint_18_56_w14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 14 2 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 16 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 14 2 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_p14 endpoint_18_56_w14
private theorem endpoint_18_56_w16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 16 1 205833793974828779 = some 205833793974828779 := by decide +kernel
private theorem endpoint_18_56_p17 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 17 205833793974828779 = some 205833793974828779 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 16 1 205833793974828779 205833793974828779 205833793974828779 endpoint_18_56_p16 endpoint_18_56_w16
def endpoint_18_56 : CertifiedEndpoint :=
  ⟨⟨18, 56, 1822⟩, 205833793974828779, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_56_flag endpoint_18_56_sources 17 205833793974828779 205833793974828779 rfl endpoint_18_56_base endpoint_18_56_p17) (by decide)⟩
private def endpoint_18_57_flag : Flag := ⟨18, 57, 1756⟩
private def endpoint_18_57_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_57_base : receiptBase endpoint_18_57_flag endpoint_18_57_sources = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_w0 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_w2 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 2 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 4 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 2 2 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_w0 endpoint_18_57_w2
private theorem endpoint_18_57_w4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 4 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 6 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 4 2 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_p4 endpoint_18_57_w4
private theorem endpoint_18_57_w6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 6 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 8 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 6 2 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_p6 endpoint_18_57_w6
private theorem endpoint_18_57_w8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 8 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 10 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 8 2 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_p8 endpoint_18_57_w8
private theorem endpoint_18_57_w10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 10 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 12 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 10 2 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_p10 endpoint_18_57_w10
private theorem endpoint_18_57_w12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 12 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 14 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 12 2 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_p12 endpoint_18_57_w12
private theorem endpoint_18_57_w14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 14 2 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 16 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 14 2 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_p14 endpoint_18_57_w14
private theorem endpoint_18_57_w16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 16 1 201579761721618222 = some 201579761721618222 := by decide +kernel
private theorem endpoint_18_57_p17 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 17 201579761721618222 = some 201579761721618222 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 16 1 201579761721618222 201579761721618222 201579761721618222 endpoint_18_57_p16 endpoint_18_57_w16
def endpoint_18_57 : CertifiedEndpoint :=
  ⟨⟨18, 57, 1756⟩, 201579761721618222, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_57_flag endpoint_18_57_sources 17 201579761721618222 201579761721618222 rfl endpoint_18_57_base endpoint_18_57_p17) (by decide)⟩
private def endpoint_18_58_flag : Flag := ⟨18, 58, 1688⟩
private def endpoint_18_58_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_58_base : receiptBase endpoint_18_58_flag endpoint_18_58_sources = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_w0 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_w2 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 2 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 4 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 2 2 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_w0 endpoint_18_58_w2
private theorem endpoint_18_58_w4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 4 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 6 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 4 2 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_p4 endpoint_18_58_w4
private theorem endpoint_18_58_w6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 6 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 8 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 6 2 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_p6 endpoint_18_58_w6
private theorem endpoint_18_58_w8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 8 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 10 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 8 2 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_p8 endpoint_18_58_w8
private theorem endpoint_18_58_w10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 10 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 12 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 10 2 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_p10 endpoint_18_58_w10
private theorem endpoint_18_58_w12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 12 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 14 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 12 2 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_p12 endpoint_18_58_w12
private theorem endpoint_18_58_w14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 14 2 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 16 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 14 2 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_p14 endpoint_18_58_w14
private theorem endpoint_18_58_w16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 16 1 198530734222205030 = some 198530734222205030 := by decide +kernel
private theorem endpoint_18_58_p17 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 17 198530734222205030 = some 198530734222205030 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 16 1 198530734222205030 198530734222205030 198530734222205030 endpoint_18_58_p16 endpoint_18_58_w16
def endpoint_18_58 : CertifiedEndpoint :=
  ⟨⟨18, 58, 1688⟩, 198530734222205030, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_58_flag endpoint_18_58_sources 17 198530734222205030 198530734222205030 rfl endpoint_18_58_base endpoint_18_58_p17) (by decide)⟩
private def endpoint_18_59_flag : Flag := ⟨18, 59, 1619⟩
private def endpoint_18_59_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_59_base : receiptBase endpoint_18_59_flag endpoint_18_59_sources = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_w0 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_w2 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 2 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 4 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 2 2 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_w0 endpoint_18_59_w2
private theorem endpoint_18_59_w4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 4 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 6 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 4 2 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_p4 endpoint_18_59_w4
private theorem endpoint_18_59_w6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 6 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 8 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 6 2 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_p6 endpoint_18_59_w6
private theorem endpoint_18_59_w8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 8 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 10 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 8 2 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_p8 endpoint_18_59_w8
private theorem endpoint_18_59_w10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 10 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 12 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 10 2 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_p10 endpoint_18_59_w10
private theorem endpoint_18_59_w12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 12 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 14 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 12 2 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_p12 endpoint_18_59_w12
private theorem endpoint_18_59_w14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 14 2 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 16 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 14 2 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_p14 endpoint_18_59_w14
private theorem endpoint_18_59_w16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 16 1 193396313832691685 = some 193396313832691685 := by decide +kernel
private theorem endpoint_18_59_p17 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 17 193396313832691685 = some 193396313832691685 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 16 1 193396313832691685 193396313832691685 193396313832691685 endpoint_18_59_p16 endpoint_18_59_w16
def endpoint_18_59 : CertifiedEndpoint :=
  ⟨⟨18, 59, 1619⟩, 193396313832691685, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_59_flag endpoint_18_59_sources 17 193396313832691685 193396313832691685 rfl endpoint_18_59_base endpoint_18_59_p17) (by decide)⟩
private def endpoint_18_60_flag : Flag := ⟨18, 60, 1549⟩
private def endpoint_18_60_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_60_base : receiptBase endpoint_18_60_flag endpoint_18_60_sources = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_w0 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_w2 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 2 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 4 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 2 2 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_w0 endpoint_18_60_w2
private theorem endpoint_18_60_w4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 4 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 6 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 4 2 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_p4 endpoint_18_60_w4
private theorem endpoint_18_60_w6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 6 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 8 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 6 2 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_p6 endpoint_18_60_w6
private theorem endpoint_18_60_w8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 8 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 10 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 8 2 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_p8 endpoint_18_60_w8
private theorem endpoint_18_60_w10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 10 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 12 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 10 2 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_p10 endpoint_18_60_w10
private theorem endpoint_18_60_w12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 12 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 14 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 12 2 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_p12 endpoint_18_60_w12
private theorem endpoint_18_60_w14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 14 2 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 16 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 14 2 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_p14 endpoint_18_60_w14
private theorem endpoint_18_60_w16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 16 1 187897110843205995 = some 187897110843205995 := by decide +kernel
private theorem endpoint_18_60_p17 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 17 187897110843205995 = some 187897110843205995 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 16 1 187897110843205995 187897110843205995 187897110843205995 endpoint_18_60_p16 endpoint_18_60_w16
def endpoint_18_60 : CertifiedEndpoint :=
  ⟨⟨18, 60, 1549⟩, 187897110843205995, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_60_flag endpoint_18_60_sources 17 187897110843205995 187897110843205995 rfl endpoint_18_60_base endpoint_18_60_p17) (by decide)⟩
private def endpoint_18_61_flag : Flag := ⟨18, 61, 1477⟩
private def endpoint_18_61_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_18_61_base : receiptBase endpoint_18_61_flag endpoint_18_61_sources = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_w0 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_w2 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 2 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 4 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 2 2 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_w0 endpoint_18_61_w2
private theorem endpoint_18_61_w4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 4 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 6 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 4 2 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_p4 endpoint_18_61_w4
private theorem endpoint_18_61_w6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 6 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 8 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 6 2 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_p6 endpoint_18_61_w6
private theorem endpoint_18_61_w8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 8 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 10 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 8 2 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_p8 endpoint_18_61_w8
private theorem endpoint_18_61_w10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 10 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 12 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 10 2 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_p10 endpoint_18_61_w10
private theorem endpoint_18_61_w12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 12 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 14 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 12 2 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_p12 endpoint_18_61_w12
private theorem endpoint_18_61_w14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 14 2 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 16 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 14 2 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_p14 endpoint_18_61_w14
private theorem endpoint_18_61_w16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 16 1 182173350143255532 = some 182173350143255532 := by decide +kernel
private theorem endpoint_18_61_p17 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 17 182173350143255532 = some 182173350143255532 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 16 1 182173350143255532 182173350143255532 182173350143255532 endpoint_18_61_p16 endpoint_18_61_w16
def endpoint_18_61 : CertifiedEndpoint :=
  ⟨⟨18, 61, 1477⟩, 182173350143255532, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_18_61_flag endpoint_18_61_sources 17 182173350143255532 182173350143255532 rfl endpoint_18_61_base endpoint_18_61_p17) (by decide)⟩
private def endpoint_18_62_flag : Flag := ⟨18, 62, 1404⟩
private def endpoint_18_62_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_18_62_base : receiptBase endpoint_18_62_flag endpoint_18_62_sources = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_w0 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_w2 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 2 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 4 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 2 2 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_w0 endpoint_18_62_w2
private theorem endpoint_18_62_w4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 4 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 6 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 4 2 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_p4 endpoint_18_62_w4
private theorem endpoint_18_62_w6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 6 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 8 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 6 2 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_p6 endpoint_18_62_w6
private theorem endpoint_18_62_w8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 8 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 10 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 8 2 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_p8 endpoint_18_62_w8
private theorem endpoint_18_62_w10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 10 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 12 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 10 2 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_p10 endpoint_18_62_w10
private theorem endpoint_18_62_w12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 12 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 14 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 12 2 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_p12 endpoint_18_62_w12
private theorem endpoint_18_62_w14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 14 2 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 16 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 14 2 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_p14 endpoint_18_62_w14
private theorem endpoint_18_62_w16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 16 1 177228799838982585 = some 177228799838982585 := by decide +kernel
private theorem endpoint_18_62_p17 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 17 177228799838982585 = some 177228799838982585 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 16 1 177228799838982585 177228799838982585 177228799838982585 endpoint_18_62_p16 endpoint_18_62_w16
def endpoint_18_62 : CertifiedEndpoint :=
  ⟨⟨18, 62, 1404⟩, 177228799838982585, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_18_62_flag endpoint_18_62_sources 17 177228799838982585 177228799838982585 rfl endpoint_18_62_base endpoint_18_62_p17) (by decide)⟩
private def endpoint_18_63_flag : Flag := ⟨18, 63, 1328⟩
private def endpoint_18_63_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_18_63_base : receiptBase endpoint_18_63_flag endpoint_18_63_sources = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_w0 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_w2 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 2 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 4 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 2 2 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_w0 endpoint_18_63_w2
private theorem endpoint_18_63_w4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 4 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 6 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 4 2 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_p4 endpoint_18_63_w4
private theorem endpoint_18_63_w6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 6 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 8 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 6 2 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_p6 endpoint_18_63_w6
private theorem endpoint_18_63_w8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 8 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 10 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 8 2 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_p8 endpoint_18_63_w8
private theorem endpoint_18_63_w10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 10 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 12 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 10 2 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_p10 endpoint_18_63_w10
private theorem endpoint_18_63_w12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 12 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 14 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 12 2 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_p12 endpoint_18_63_w12
private theorem endpoint_18_63_w14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 14 2 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 16 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 14 2 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_p14 endpoint_18_63_w14
private theorem endpoint_18_63_w16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 16 1 170260340816836128 = some 170260340816836128 := by decide +kernel
private theorem endpoint_18_63_p17 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 17 170260340816836128 = some 170260340816836128 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 16 1 170260340816836128 170260340816836128 170260340816836128 endpoint_18_63_p16 endpoint_18_63_w16
def endpoint_18_63 : CertifiedEndpoint :=
  ⟨⟨18, 63, 1328⟩, 170260340816836128, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_18_63_flag endpoint_18_63_sources 17 170260340816836128 170260340816836128 rfl endpoint_18_63_base endpoint_18_63_p17) (by decide)⟩
private def endpoint_18_64_flag : Flag := ⟨18, 64, 1251⟩
private def endpoint_18_64_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_64_base : receiptBase endpoint_18_64_flag endpoint_18_64_sources = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_w0 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_w2 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 2 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 4 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 2 2 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_w0 endpoint_18_64_w2
private theorem endpoint_18_64_w4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 4 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 6 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 4 2 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_p4 endpoint_18_64_w4
private theorem endpoint_18_64_w6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 6 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 8 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 6 2 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_p6 endpoint_18_64_w6
private theorem endpoint_18_64_w8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 8 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 10 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 8 2 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_p8 endpoint_18_64_w8
private theorem endpoint_18_64_w10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 10 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 12 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 10 2 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_p10 endpoint_18_64_w10
private theorem endpoint_18_64_w12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 12 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 14 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 12 2 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_p12 endpoint_18_64_w12
private theorem endpoint_18_64_w14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 14 2 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 16 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 14 2 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_p14 endpoint_18_64_w14
private theorem endpoint_18_64_w16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 16 1 164505241779269748 = some 164505241779269748 := by decide +kernel
private theorem endpoint_18_64_p17 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 17 164505241779269748 = some 164505241779269748 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 16 1 164505241779269748 164505241779269748 164505241779269748 endpoint_18_64_p16 endpoint_18_64_w16
def endpoint_18_64 : CertifiedEndpoint :=
  ⟨⟨18, 64, 1251⟩, 164505241779269748, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_64_flag endpoint_18_64_sources 17 164505241779269748 164505241779269748 rfl endpoint_18_64_base endpoint_18_64_p17) (by decide)⟩
private def endpoint_18_65_flag : Flag := ⟨18, 65, 1173⟩
private def endpoint_18_65_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_65_base : receiptBase endpoint_18_65_flag endpoint_18_65_sources = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_w0 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_w2 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 2 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p4 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 4 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 2 2 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_w0 endpoint_18_65_w2
private theorem endpoint_18_65_w4 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 4 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p6 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 6 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 4 2 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_p4 endpoint_18_65_w4
private theorem endpoint_18_65_w6 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 6 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p8 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 8 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 6 2 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_p6 endpoint_18_65_w6
private theorem endpoint_18_65_w8 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 8 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p10 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 10 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 8 2 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_p8 endpoint_18_65_w8
private theorem endpoint_18_65_w10 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 10 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p12 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 12 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 10 2 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_p10 endpoint_18_65_w10
private theorem endpoint_18_65_w12 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 12 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p14 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 14 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 12 2 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_p12 endpoint_18_65_w12
private theorem endpoint_18_65_w14 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 14 2 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p16 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 16 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 14 2 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_p14 endpoint_18_65_w14
private theorem endpoint_18_65_w16 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 16 1 156507768108290506 = some 156507768108290506 := by decide +kernel
private theorem endpoint_18_65_p17 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 17 156507768108290506 = some 156507768108290506 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 16 1 156507768108290506 156507768108290506 156507768108290506 endpoint_18_65_p16 endpoint_18_65_w16
def endpoint_18_65 : CertifiedEndpoint :=
  ⟨⟨18, 65, 1173⟩, 156507768108290506, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_65_flag endpoint_18_65_sources 17 156507768108290506 156507768108290506 rfl endpoint_18_65_base endpoint_18_65_p17) (by decide)⟩
private def endpoint_18_66_flag : Flag := ⟨18, 66, 1092⟩
private def endpoint_18_66_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_66_base : receiptBase endpoint_18_66_flag endpoint_18_66_sources = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_w0 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_w2 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 2 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p4 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 4 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 2 2 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_w0 endpoint_18_66_w2
private theorem endpoint_18_66_w4 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 4 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p6 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 6 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 4 2 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_p4 endpoint_18_66_w4
private theorem endpoint_18_66_w6 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 6 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p8 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 8 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 6 2 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_p6 endpoint_18_66_w6
private theorem endpoint_18_66_w8 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 8 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p10 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 10 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 8 2 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_p8 endpoint_18_66_w8
private theorem endpoint_18_66_w10 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 10 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p12 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 12 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 10 2 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_p10 endpoint_18_66_w10
private theorem endpoint_18_66_w12 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 12 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p14 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 14 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 12 2 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_p12 endpoint_18_66_w12
private theorem endpoint_18_66_w14 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 14 2 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p16 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 16 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 14 2 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_p14 endpoint_18_66_w14
private theorem endpoint_18_66_w16 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 16 1 147835110107056733 = some 147835110107056733 := by decide +kernel
private theorem endpoint_18_66_p17 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 17 147835110107056733 = some 147835110107056733 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 16 1 147835110107056733 147835110107056733 147835110107056733 endpoint_18_66_p16 endpoint_18_66_w16
def endpoint_18_66 : CertifiedEndpoint :=
  ⟨⟨18, 66, 1092⟩, 147835110107056733, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_66_flag endpoint_18_66_sources 17 147835110107056733 147835110107056733 rfl endpoint_18_66_base endpoint_18_66_p17) (by decide)⟩
def endpoint_18_67 : CertifiedEndpoint :=
  ⟨⟨18, 67, 1010⟩, 252535865232298787, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_68 : CertifiedEndpoint :=
  ⟨⟨18, 68, 925⟩, 234325907618187007, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_69 : CertifiedEndpoint :=
  ⟨⟨18, 69, 838⟩, 214805591601123967, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_70 : CertifiedEndpoint :=
  ⟨⟨18, 70, 750⟩, 194221179584119454, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_71 : CertifiedEndpoint :=
  ⟨⟨18, 71, 659⟩, 172003333660889592, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_72 : CertifiedEndpoint :=
  ⟨⟨18, 72, 566⟩, 148393797816781562, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_73 : CertifiedEndpoint :=
  ⟨⟨18, 73, 470⟩, 123078533383846487, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_74 : CertifiedEndpoint :=
  ⟨⟨18, 74, 372⟩, 96308321182756760, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_75 : CertifiedEndpoint :=
  ⟨⟨18, 75, 271⟩, 67760085710238292, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_76 : CertifiedEndpoint :=
  ⟨⟨18, 76, 168⟩, 37693644622288688, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_19 : CertifiedEndpoint :=
  ⟨⟨19, 19, 3274⟩, 161062008872184623, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_20 : CertifiedEndpoint :=
  ⟨⟨19, 20, 3237⟩, 164289678495528586, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_21 : CertifiedEndpoint :=
  ⟨⟨19, 21, 3199⟩, 167348474334535584, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_22 : CertifiedEndpoint :=
  ⟨⟨19, 22, 3161⟩, 180346361893175477, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_23 : CertifiedEndpoint :=
  ⟨⟨19, 23, 3122⟩, 192914389829332317, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_24 : CertifiedEndpoint :=
  ⟨⟨19, 24, 3083⟩, 205105104128132375, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_25 : CertifiedEndpoint :=
  ⟨⟨19, 25, 3043⟩, 216846854316481948, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_26 : CertifiedEndpoint :=
  ⟨⟨19, 26, 3003⟩, 228201738623491023, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_27 : CertifiedEndpoint :=
  ⟨⟨19, 27, 2961⟩, 239007351615004762, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_28 : CertifiedEndpoint :=
  ⟨⟨19, 28, 2920⟩, 249492973076279848, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_29 : CertifiedEndpoint :=
  ⟨⟨19, 29, 2877⟩, 259400666490108450, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_19_30_flag : Flag := ⟨19, 30, 2834⟩
private def endpoint_19_30_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_30_base : receiptBase endpoint_19_30_flag endpoint_19_30_sources = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_w0 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_w2 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 2 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p4 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 4 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 2 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_w0 endpoint_19_30_w2
private theorem endpoint_19_30_w4 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 4 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p6 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 6 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 4 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_p4 endpoint_19_30_w4
private theorem endpoint_19_30_w6 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 6 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p8 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 8 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 6 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_p6 endpoint_19_30_w6
private theorem endpoint_19_30_w8 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 8 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p10 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 10 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 8 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_p8 endpoint_19_30_w8
private theorem endpoint_19_30_w10 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 10 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p12 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 12 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 10 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_p10 endpoint_19_30_w10
private theorem endpoint_19_30_w12 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 12 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p14 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 14 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 12 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_p12 endpoint_19_30_w12
private theorem endpoint_19_30_w14 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 14 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p16 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 16 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 14 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_p14 endpoint_19_30_w14
private theorem endpoint_19_30_w16 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 16 2 183250771707248153 = some 183250771707248153 := by decide +kernel
private theorem endpoint_19_30_p18 : receiptWindow endpoint_19_30_flag endpoint_19_30_sources 0 18 183250771707248153 = some 183250771707248153 :=
  join_receipt_window endpoint_19_30_flag endpoint_19_30_sources 0 16 2 183250771707248153 183250771707248153 183250771707248153 endpoint_19_30_p16 endpoint_19_30_w16
def endpoint_19_30 : CertifiedEndpoint :=
  ⟨⟨19, 30, 2834⟩, 183250771707248153, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_30_flag endpoint_19_30_sources 18 183250771707248153 183250771707248153 rfl endpoint_19_30_base endpoint_19_30_p18) (by decide)⟩
private def endpoint_19_31_flag : Flag := ⟨19, 31, 2790⟩
private def endpoint_19_31_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_31_base : receiptBase endpoint_19_31_flag endpoint_19_31_sources = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_w0 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_w2 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 2 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p4 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 4 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 2 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_w0 endpoint_19_31_w2
private theorem endpoint_19_31_w4 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 4 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p6 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 6 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 4 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_p4 endpoint_19_31_w4
private theorem endpoint_19_31_w6 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 6 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p8 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 8 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 6 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_p6 endpoint_19_31_w6
private theorem endpoint_19_31_w8 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 8 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p10 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 10 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 8 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_p8 endpoint_19_31_w8
private theorem endpoint_19_31_w10 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 10 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p12 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 12 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 10 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_p10 endpoint_19_31_w10
private theorem endpoint_19_31_w12 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 12 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p14 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 14 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 12 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_p12 endpoint_19_31_w12
private theorem endpoint_19_31_w14 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 14 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p16 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 16 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 14 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_p14 endpoint_19_31_w14
private theorem endpoint_19_31_w16 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 16 2 185430120973843282 = some 185430120973843282 := by decide +kernel
private theorem endpoint_19_31_p18 : receiptWindow endpoint_19_31_flag endpoint_19_31_sources 0 18 185430120973843282 = some 185430120973843282 :=
  join_receipt_window endpoint_19_31_flag endpoint_19_31_sources 0 16 2 185430120973843282 185430120973843282 185430120973843282 endpoint_19_31_p16 endpoint_19_31_w16
def endpoint_19_31 : CertifiedEndpoint :=
  ⟨⟨19, 31, 2790⟩, 185430120973843282, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_31_flag endpoint_19_31_sources 18 185430120973843282 185430120973843282 rfl endpoint_19_31_base endpoint_19_31_p18) (by decide)⟩
private def endpoint_19_32_flag : Flag := ⟨19, 32, 2746⟩
private def endpoint_19_32_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_32_base : receiptBase endpoint_19_32_flag endpoint_19_32_sources = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_w0 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_w2 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 2 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 4 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 2 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_w0 endpoint_19_32_w2
private theorem endpoint_19_32_w4 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 4 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 6 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 4 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_p4 endpoint_19_32_w4
private theorem endpoint_19_32_w6 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 6 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 8 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 6 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_p6 endpoint_19_32_w6
private theorem endpoint_19_32_w8 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 8 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 10 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 8 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_p8 endpoint_19_32_w8
private theorem endpoint_19_32_w10 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 10 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 12 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 10 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_p10 endpoint_19_32_w10
private theorem endpoint_19_32_w12 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 12 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 14 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 12 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_p12 endpoint_19_32_w12
private theorem endpoint_19_32_w14 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 14 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 16 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 14 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_p14 endpoint_19_32_w14
private theorem endpoint_19_32_w16 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 16 2 187453568512012933 = some 187453568512012933 := by decide +kernel
private theorem endpoint_19_32_p18 : receiptWindow endpoint_19_32_flag endpoint_19_32_sources 0 18 187453568512012933 = some 187453568512012933 :=
  join_receipt_window endpoint_19_32_flag endpoint_19_32_sources 0 16 2 187453568512012933 187453568512012933 187453568512012933 endpoint_19_32_p16 endpoint_19_32_w16
def endpoint_19_32 : CertifiedEndpoint :=
  ⟨⟨19, 32, 2746⟩, 187453568512012933, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_32_flag endpoint_19_32_sources 18 187453568512012933 187453568512012933 rfl endpoint_19_32_base endpoint_19_32_p18) (by decide)⟩
private def endpoint_19_33_flag : Flag := ⟨19, 33, 2701⟩
private def endpoint_19_33_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_33_base : receiptBase endpoint_19_33_flag endpoint_19_33_sources = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_w0 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_w2 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 2 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 4 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 2 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_w0 endpoint_19_33_w2
private theorem endpoint_19_33_w4 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 4 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 6 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 4 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_p4 endpoint_19_33_w4
private theorem endpoint_19_33_w6 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 6 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 8 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 6 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_p6 endpoint_19_33_w6
private theorem endpoint_19_33_w8 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 8 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 10 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 8 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_p8 endpoint_19_33_w8
private theorem endpoint_19_33_w10 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 10 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 12 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 10 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_p10 endpoint_19_33_w10
private theorem endpoint_19_33_w12 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 12 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 14 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 12 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_p12 endpoint_19_33_w12
private theorem endpoint_19_33_w14 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 14 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 16 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 14 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_p14 endpoint_19_33_w14
private theorem endpoint_19_33_w16 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 16 2 189251965530816752 = some 189251965530816752 := by decide +kernel
private theorem endpoint_19_33_p18 : receiptWindow endpoint_19_33_flag endpoint_19_33_sources 0 18 189251965530816752 = some 189251965530816752 :=
  join_receipt_window endpoint_19_33_flag endpoint_19_33_sources 0 16 2 189251965530816752 189251965530816752 189251965530816752 endpoint_19_33_p16 endpoint_19_33_w16
def endpoint_19_33 : CertifiedEndpoint :=
  ⟨⟨19, 33, 2701⟩, 189251965530816752, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_33_flag endpoint_19_33_sources 18 189251965530816752 189251965530816752 rfl endpoint_19_33_base endpoint_19_33_p18) (by decide)⟩
private def endpoint_19_34_flag : Flag := ⟨19, 34, 2655⟩
private def endpoint_19_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_34_base : receiptBase endpoint_19_34_flag endpoint_19_34_sources = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_w0 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_w2 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 2 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 4 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 2 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_w0 endpoint_19_34_w2
private theorem endpoint_19_34_w4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 4 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 6 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 4 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_p4 endpoint_19_34_w4
private theorem endpoint_19_34_w6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 6 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 8 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 6 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_p6 endpoint_19_34_w6
private theorem endpoint_19_34_w8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 8 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 10 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 8 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_p8 endpoint_19_34_w8
private theorem endpoint_19_34_w10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 10 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 12 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 10 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_p10 endpoint_19_34_w10
private theorem endpoint_19_34_w12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 12 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 14 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 12 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_p12 endpoint_19_34_w12
private theorem endpoint_19_34_w14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 14 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 16 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 14 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_p14 endpoint_19_34_w14
private theorem endpoint_19_34_w16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 16 2 190820056915813429 = some 190820056915813429 := by decide +kernel
private theorem endpoint_19_34_p18 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 18 190820056915813429 = some 190820056915813429 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 16 2 190820056915813429 190820056915813429 190820056915813429 endpoint_19_34_p16 endpoint_19_34_w16
def endpoint_19_34 : CertifiedEndpoint :=
  ⟨⟨19, 34, 2655⟩, 190820056915813429, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_34_flag endpoint_19_34_sources 18 190820056915813429 190820056915813429 rfl endpoint_19_34_base endpoint_19_34_p18) (by decide)⟩
private def endpoint_19_35_flag : Flag := ⟨19, 35, 2608⟩
private def endpoint_19_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_35_base : receiptBase endpoint_19_35_flag endpoint_19_35_sources = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_w0 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_w2 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 2 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 4 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 2 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_w0 endpoint_19_35_w2
private theorem endpoint_19_35_w4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 4 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 6 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 4 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_p4 endpoint_19_35_w4
private theorem endpoint_19_35_w6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 6 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 8 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 6 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_p6 endpoint_19_35_w6
private theorem endpoint_19_35_w8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 8 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 10 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 8 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_p8 endpoint_19_35_w8
private theorem endpoint_19_35_w10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 10 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 12 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 10 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_p10 endpoint_19_35_w10
private theorem endpoint_19_35_w12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 12 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 14 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 12 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_p12 endpoint_19_35_w12
private theorem endpoint_19_35_w14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 14 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 16 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 14 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_p14 endpoint_19_35_w14
private theorem endpoint_19_35_w16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 16 2 192152587552561657 = some 192152587552561657 := by decide +kernel
private theorem endpoint_19_35_p18 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 18 192152587552561657 = some 192152587552561657 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 16 2 192152587552561657 192152587552561657 192152587552561657 endpoint_19_35_p16 endpoint_19_35_w16
def endpoint_19_35 : CertifiedEndpoint :=
  ⟨⟨19, 35, 2608⟩, 192152587552561657, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_35_flag endpoint_19_35_sources 18 192152587552561657 192152587552561657 rfl endpoint_19_35_base endpoint_19_35_p18) (by decide)⟩
private def endpoint_19_36_flag : Flag := ⟨19, 36, 2561⟩
private def endpoint_19_36_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_36_base : receiptBase endpoint_19_36_flag endpoint_19_36_sources = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_w0 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_w2 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 2 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 4 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 2 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_w0 endpoint_19_36_w2
private theorem endpoint_19_36_w4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 4 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 6 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 4 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_p4 endpoint_19_36_w4
private theorem endpoint_19_36_w6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 6 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 8 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 6 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_p6 endpoint_19_36_w6
private theorem endpoint_19_36_w8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 8 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 10 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 8 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_p8 endpoint_19_36_w8
private theorem endpoint_19_36_w10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 10 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 12 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 10 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_p10 endpoint_19_36_w10
private theorem endpoint_19_36_w12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 12 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 14 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 12 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_p12 endpoint_19_36_w12
private theorem endpoint_19_36_w14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 14 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 16 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 14 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_p14 endpoint_19_36_w14
private theorem endpoint_19_36_w16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 16 2 199229458801893633 = some 199229458801893633 := by decide +kernel
private theorem endpoint_19_36_p18 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 18 199229458801893633 = some 199229458801893633 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 16 2 199229458801893633 199229458801893633 199229458801893633 endpoint_19_36_p16 endpoint_19_36_w16
def endpoint_19_36 : CertifiedEndpoint :=
  ⟨⟨19, 36, 2561⟩, 199229458801893633, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_36_flag endpoint_19_36_sources 18 199229458801893633 199229458801893633 rfl endpoint_19_36_base endpoint_19_36_p18) (by decide)⟩
private def endpoint_19_37_flag : Flag := ⟨19, 37, 2513⟩
private def endpoint_19_37_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_37_base : receiptBase endpoint_19_37_flag endpoint_19_37_sources = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_w0 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_w2 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 2 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 4 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 2 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_w0 endpoint_19_37_w2
private theorem endpoint_19_37_w4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 4 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 6 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 4 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_p4 endpoint_19_37_w4
private theorem endpoint_19_37_w6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 6 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 8 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 6 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_p6 endpoint_19_37_w6
private theorem endpoint_19_37_w8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 8 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 10 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 8 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_p8 endpoint_19_37_w8
private theorem endpoint_19_37_w10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 10 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 12 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 10 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_p10 endpoint_19_37_w10
private theorem endpoint_19_37_w12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 12 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 14 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 12 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_p12 endpoint_19_37_w12
private theorem endpoint_19_37_w14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 14 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 16 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 14 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_p14 endpoint_19_37_w14
private theorem endpoint_19_37_w16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 16 2 200189445678652979 = some 200189445678652979 := by decide +kernel
private theorem endpoint_19_37_p18 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 18 200189445678652979 = some 200189445678652979 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 16 2 200189445678652979 200189445678652979 200189445678652979 endpoint_19_37_p16 endpoint_19_37_w16
def endpoint_19_37 : CertifiedEndpoint :=
  ⟨⟨19, 37, 2513⟩, 200189445678652979, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_37_flag endpoint_19_37_sources 18 200189445678652979 200189445678652979 rfl endpoint_19_37_base endpoint_19_37_p18) (by decide)⟩
private def endpoint_19_38_flag : Flag := ⟨19, 38, 2464⟩
private def endpoint_19_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_38_base : receiptBase endpoint_19_38_flag endpoint_19_38_sources = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_w0 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_w2 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 2 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 4 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 2 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_w0 endpoint_19_38_w2
private theorem endpoint_19_38_w4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 4 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 6 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 4 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_p4 endpoint_19_38_w4
private theorem endpoint_19_38_w6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 6 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 8 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 6 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_p6 endpoint_19_38_w6
private theorem endpoint_19_38_w8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 8 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 10 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 8 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_p8 endpoint_19_38_w8
private theorem endpoint_19_38_w10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 10 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 12 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 10 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_p10 endpoint_19_38_w10
private theorem endpoint_19_38_w12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 12 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 14 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 12 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_p12 endpoint_19_38_w12
private theorem endpoint_19_38_w14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 14 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 16 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 14 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_p14 endpoint_19_38_w14
private theorem endpoint_19_38_w16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 16 2 201502859476232790 = some 201502859476232790 := by decide +kernel
private theorem endpoint_19_38_p18 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 18 201502859476232790 = some 201502859476232790 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 16 2 201502859476232790 201502859476232790 201502859476232790 endpoint_19_38_p16 endpoint_19_38_w16
def endpoint_19_38 : CertifiedEndpoint :=
  ⟨⟨19, 38, 2464⟩, 201502859476232790, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_38_flag endpoint_19_38_sources 18 201502859476232790 201502859476232790 rfl endpoint_19_38_base endpoint_19_38_p18) (by decide)⟩
private def endpoint_19_39_flag : Flag := ⟨19, 39, 2414⟩
private def endpoint_19_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_39_base : receiptBase endpoint_19_39_flag endpoint_19_39_sources = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_w0 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_w2 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 2 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 4 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 2 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_w0 endpoint_19_39_w2
private theorem endpoint_19_39_w4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 4 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 6 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 4 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_p4 endpoint_19_39_w4
private theorem endpoint_19_39_w6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 6 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 8 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 6 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_p6 endpoint_19_39_w6
private theorem endpoint_19_39_w8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 8 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 10 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 8 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_p8 endpoint_19_39_w8
private theorem endpoint_19_39_w10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 10 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 12 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 10 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_p10 endpoint_19_39_w10
private theorem endpoint_19_39_w12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 12 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 14 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 12 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_p12 endpoint_19_39_w12
private theorem endpoint_19_39_w14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 14 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 16 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 14 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_p14 endpoint_19_39_w14
private theorem endpoint_19_39_w16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 16 2 201964181326350759 = some 201964181326350759 := by decide +kernel
private theorem endpoint_19_39_p18 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 18 201964181326350759 = some 201964181326350759 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 16 2 201964181326350759 201964181326350759 201964181326350759 endpoint_19_39_p16 endpoint_19_39_w16
def endpoint_19_39 : CertifiedEndpoint :=
  ⟨⟨19, 39, 2414⟩, 201964181326350759, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_39_flag endpoint_19_39_sources 18 201964181326350759 201964181326350759 rfl endpoint_19_39_base endpoint_19_39_p18) (by decide)⟩
private def endpoint_19_40_flag : Flag := ⟨19, 40, 2363⟩
private def endpoint_19_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_40_base : receiptBase endpoint_19_40_flag endpoint_19_40_sources = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_w0 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_w2 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 2 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 4 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 2 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_w0 endpoint_19_40_w2
private theorem endpoint_19_40_w4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 4 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 6 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 4 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_p4 endpoint_19_40_w4
private theorem endpoint_19_40_w6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 6 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 8 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 6 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_p6 endpoint_19_40_w6
private theorem endpoint_19_40_w8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 8 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 10 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 8 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_p8 endpoint_19_40_w8
private theorem endpoint_19_40_w10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 10 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 12 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 10 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_p10 endpoint_19_40_w10
private theorem endpoint_19_40_w12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 12 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 14 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 12 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_p12 endpoint_19_40_w12
private theorem endpoint_19_40_w14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 14 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 16 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 14 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_p14 endpoint_19_40_w14
private theorem endpoint_19_40_w16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 16 2 202160787131694239 = some 202160787131694239 := by decide +kernel
private theorem endpoint_19_40_p18 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 18 202160787131694239 = some 202160787131694239 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 16 2 202160787131694239 202160787131694239 202160787131694239 endpoint_19_40_p16 endpoint_19_40_w16
def endpoint_19_40 : CertifiedEndpoint :=
  ⟨⟨19, 40, 2363⟩, 202160787131694239, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_40_flag endpoint_19_40_sources 18 202160787131694239 202160787131694239 rfl endpoint_19_40_base endpoint_19_40_p18) (by decide)⟩
private def endpoint_19_41_flag : Flag := ⟨19, 41, 2312⟩
private def endpoint_19_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_41_base : receiptBase endpoint_19_41_flag endpoint_19_41_sources = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_w0 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_w2 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 2 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 4 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 2 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_w0 endpoint_19_41_w2
private theorem endpoint_19_41_w4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 4 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 6 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 4 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_p4 endpoint_19_41_w4
private theorem endpoint_19_41_w6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 6 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 8 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 6 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_p6 endpoint_19_41_w6
private theorem endpoint_19_41_w8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 8 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 10 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 8 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_p8 endpoint_19_41_w8
private theorem endpoint_19_41_w10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 10 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 12 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 10 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_p10 endpoint_19_41_w10
private theorem endpoint_19_41_w12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 12 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 14 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 12 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_p12 endpoint_19_41_w12
private theorem endpoint_19_41_w14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 14 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 16 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 14 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_p14 endpoint_19_41_w14
private theorem endpoint_19_41_w16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 16 2 202172694162260484 = some 202172694162260484 := by decide +kernel
private theorem endpoint_19_41_p18 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 18 202172694162260484 = some 202172694162260484 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 16 2 202172694162260484 202172694162260484 202172694162260484 endpoint_19_41_p16 endpoint_19_41_w16
def endpoint_19_41 : CertifiedEndpoint :=
  ⟨⟨19, 41, 2312⟩, 202172694162260484, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_41_flag endpoint_19_41_sources 18 202172694162260484 202172694162260484 rfl endpoint_19_41_base endpoint_19_41_p18) (by decide)⟩
private def endpoint_19_42_flag : Flag := ⟨19, 42, 2259⟩
private def endpoint_19_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_42_base : receiptBase endpoint_19_42_flag endpoint_19_42_sources = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_w0 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_w2 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 2 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 4 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 2 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_w0 endpoint_19_42_w2
private theorem endpoint_19_42_w4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 4 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 6 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 4 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_p4 endpoint_19_42_w4
private theorem endpoint_19_42_w6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 6 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 8 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 6 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_p6 endpoint_19_42_w6
private theorem endpoint_19_42_w8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 8 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 10 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 8 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_p8 endpoint_19_42_w8
private theorem endpoint_19_42_w10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 10 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 12 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 10 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_p10 endpoint_19_42_w10
private theorem endpoint_19_42_w12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 12 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 14 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 12 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_p12 endpoint_19_42_w12
private theorem endpoint_19_42_w14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 14 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 16 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 14 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_p14 endpoint_19_42_w14
private theorem endpoint_19_42_w16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 16 2 201825521730553160 = some 201825521730553160 := by decide +kernel
private theorem endpoint_19_42_p18 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 18 201825521730553160 = some 201825521730553160 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 16 2 201825521730553160 201825521730553160 201825521730553160 endpoint_19_42_p16 endpoint_19_42_w16
def endpoint_19_42 : CertifiedEndpoint :=
  ⟨⟨19, 42, 2259⟩, 201825521730553160, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_42_flag endpoint_19_42_sources 18 201825521730553160 201825521730553160 rfl endpoint_19_42_base endpoint_19_42_p18) (by decide)⟩
private def endpoint_19_43_flag : Flag := ⟨19, 43, 2206⟩
private def endpoint_19_43_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_43_base : receiptBase endpoint_19_43_flag endpoint_19_43_sources = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_w0 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_w2 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 2 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 4 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 2 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_w0 endpoint_19_43_w2
private theorem endpoint_19_43_w4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 4 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 6 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 4 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_p4 endpoint_19_43_w4
private theorem endpoint_19_43_w6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 6 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 8 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 6 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_p6 endpoint_19_43_w6
private theorem endpoint_19_43_w8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 8 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 10 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 8 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_p8 endpoint_19_43_w8
private theorem endpoint_19_43_w10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 10 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 12 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 10 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_p10 endpoint_19_43_w10
private theorem endpoint_19_43_w12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 12 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 14 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 12 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_p12 endpoint_19_43_w12
private theorem endpoint_19_43_w14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 14 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 16 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 14 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_p14 endpoint_19_43_w14
private theorem endpoint_19_43_w16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 16 2 201286477450317687 = some 201286477450317687 := by decide +kernel
private theorem endpoint_19_43_p18 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 18 201286477450317687 = some 201286477450317687 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 16 2 201286477450317687 201286477450317687 201286477450317687 endpoint_19_43_p16 endpoint_19_43_w16
def endpoint_19_43 : CertifiedEndpoint :=
  ⟨⟨19, 43, 2206⟩, 201286477450317687, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_43_flag endpoint_19_43_sources 18 201286477450317687 201286477450317687 rfl endpoint_19_43_base endpoint_19_43_p18) (by decide)⟩
private def endpoint_19_44_flag : Flag := ⟨19, 44, 2152⟩
private def endpoint_19_44_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_44_base : receiptBase endpoint_19_44_flag endpoint_19_44_sources = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_w0 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_w2 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 2 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 4 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 2 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_w0 endpoint_19_44_w2
private theorem endpoint_19_44_w4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 4 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 6 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 4 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_p4 endpoint_19_44_w4
private theorem endpoint_19_44_w6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 6 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 8 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 6 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_p6 endpoint_19_44_w6
private theorem endpoint_19_44_w8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 8 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 10 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 8 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_p8 endpoint_19_44_w8
private theorem endpoint_19_44_w10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 10 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 12 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 10 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_p10 endpoint_19_44_w10
private theorem endpoint_19_44_w12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 12 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 14 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 12 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_p12 endpoint_19_44_w12
private theorem endpoint_19_44_w14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 14 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 16 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 14 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_p14 endpoint_19_44_w14
private theorem endpoint_19_44_w16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 16 2 200464784440930443 = some 200464784440930443 := by decide +kernel
private theorem endpoint_19_44_p18 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 18 200464784440930443 = some 200464784440930443 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 16 2 200464784440930443 200464784440930443 200464784440930443 endpoint_19_44_p16 endpoint_19_44_w16
def endpoint_19_44 : CertifiedEndpoint :=
  ⟨⟨19, 44, 2152⟩, 200464784440930443, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_44_flag endpoint_19_44_sources 18 200464784440930443 200464784440930443 rfl endpoint_19_44_base endpoint_19_44_p18) (by decide)⟩
private def endpoint_19_45_flag : Flag := ⟨19, 45, 2097⟩
private def endpoint_19_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_45_base : receiptBase endpoint_19_45_flag endpoint_19_45_sources = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_w0 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_w2 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 2 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 4 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 2 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_w0 endpoint_19_45_w2
private theorem endpoint_19_45_w4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 4 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 6 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 4 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_p4 endpoint_19_45_w4
private theorem endpoint_19_45_w6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 6 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 8 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 6 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_p6 endpoint_19_45_w6
private theorem endpoint_19_45_w8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 8 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 10 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 8 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_p8 endpoint_19_45_w8
private theorem endpoint_19_45_w10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 10 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 12 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 10 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_p10 endpoint_19_45_w10
private theorem endpoint_19_45_w12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 12 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 14 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 12 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_p12 endpoint_19_45_w12
private theorem endpoint_19_45_w14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 14 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 16 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 14 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_p14 endpoint_19_45_w14
private theorem endpoint_19_45_w16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 16 2 201587349237025387 = some 201587349237025387 := by decide +kernel
private theorem endpoint_19_45_p18 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 18 201587349237025387 = some 201587349237025387 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 16 2 201587349237025387 201587349237025387 201587349237025387 endpoint_19_45_p16 endpoint_19_45_w16
def endpoint_19_45 : CertifiedEndpoint :=
  ⟨⟨19, 45, 2097⟩, 201587349237025387, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_45_flag endpoint_19_45_sources 18 201587349237025387 201587349237025387 rfl endpoint_19_45_base endpoint_19_45_p18) (by decide)⟩
private def endpoint_19_46_flag : Flag := ⟨19, 46, 2041⟩
private def endpoint_19_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_46_base : receiptBase endpoint_19_46_flag endpoint_19_46_sources = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_w0 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_w2 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 2 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 4 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 2 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_w0 endpoint_19_46_w2
private theorem endpoint_19_46_w4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 4 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 6 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 4 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_p4 endpoint_19_46_w4
private theorem endpoint_19_46_w6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 6 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 8 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 6 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_p6 endpoint_19_46_w6
private theorem endpoint_19_46_w8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 8 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 10 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 8 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_p8 endpoint_19_46_w8
private theorem endpoint_19_46_w10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 10 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 12 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 10 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_p10 endpoint_19_46_w10
private theorem endpoint_19_46_w12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 12 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 14 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 12 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_p12 endpoint_19_46_w12
private theorem endpoint_19_46_w14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 14 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 16 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 14 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_p14 endpoint_19_46_w14
private theorem endpoint_19_46_w16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 16 2 200115196894890069 = some 200115196894890069 := by decide +kernel
private theorem endpoint_19_46_p18 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 18 200115196894890069 = some 200115196894890069 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 16 2 200115196894890069 200115196894890069 200115196894890069 endpoint_19_46_p16 endpoint_19_46_w16
def endpoint_19_46 : CertifiedEndpoint :=
  ⟨⟨19, 46, 2041⟩, 200115196894890069, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_46_flag endpoint_19_46_sources 18 200115196894890069 200115196894890069 rfl endpoint_19_46_base endpoint_19_46_p18) (by decide)⟩
private def endpoint_19_47_flag : Flag := ⟨19, 47, 1984⟩
private def endpoint_19_47_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_47_base : receiptBase endpoint_19_47_flag endpoint_19_47_sources = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_w0 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_w2 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 2 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 4 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 2 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_w0 endpoint_19_47_w2
private theorem endpoint_19_47_w4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 4 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 6 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 4 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_p4 endpoint_19_47_w4
private theorem endpoint_19_47_w6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 6 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 8 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 6 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_p6 endpoint_19_47_w6
private theorem endpoint_19_47_w8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 8 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 10 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 8 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_p8 endpoint_19_47_w8
private theorem endpoint_19_47_w10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 10 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 12 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 10 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_p10 endpoint_19_47_w10
private theorem endpoint_19_47_w12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 12 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 14 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 12 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_p12 endpoint_19_47_w12
private theorem endpoint_19_47_w14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 14 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 16 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 14 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_p14 endpoint_19_47_w14
private theorem endpoint_19_47_w16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 16 2 198338945569726484 = some 198338945569726484 := by decide +kernel
private theorem endpoint_19_47_p18 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 18 198338945569726484 = some 198338945569726484 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 16 2 198338945569726484 198338945569726484 198338945569726484 endpoint_19_47_p16 endpoint_19_47_w16
def endpoint_19_47 : CertifiedEndpoint :=
  ⟨⟨19, 47, 1984⟩, 198338945569726484, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_47_flag endpoint_19_47_sources 18 198338945569726484 198338945569726484 rfl endpoint_19_47_base endpoint_19_47_p18) (by decide)⟩
private def endpoint_19_48_flag : Flag := ⟨19, 48, 1925⟩
private def endpoint_19_48_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_48_base : receiptBase endpoint_19_48_flag endpoint_19_48_sources = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_w0 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_w2 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 2 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 4 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 2 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_w0 endpoint_19_48_w2
private theorem endpoint_19_48_w4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 4 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 6 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 4 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_p4 endpoint_19_48_w4
private theorem endpoint_19_48_w6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 6 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 8 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 6 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_p6 endpoint_19_48_w6
private theorem endpoint_19_48_w8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 8 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 10 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 8 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_p8 endpoint_19_48_w8
private theorem endpoint_19_48_w10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 10 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 12 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 10 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_p10 endpoint_19_48_w10
private theorem endpoint_19_48_w12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 12 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 14 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 12 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_p12 endpoint_19_48_w12
private theorem endpoint_19_48_w14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 14 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 16 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 14 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_p14 endpoint_19_48_w14
private theorem endpoint_19_48_w16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 16 2 196153388276468495 = some 196153388276468495 := by decide +kernel
private theorem endpoint_19_48_p18 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 18 196153388276468495 = some 196153388276468495 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 16 2 196153388276468495 196153388276468495 196153388276468495 endpoint_19_48_p16 endpoint_19_48_w16
def endpoint_19_48 : CertifiedEndpoint :=
  ⟨⟨19, 48, 1925⟩, 196153388276468495, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_48_flag endpoint_19_48_sources 18 196153388276468495 196153388276468495 rfl endpoint_19_48_base endpoint_19_48_p18) (by decide)⟩
private def endpoint_19_49_flag : Flag := ⟨19, 49, 1866⟩
private def endpoint_19_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_49_base : receiptBase endpoint_19_49_flag endpoint_19_49_sources = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_w0 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_w2 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 2 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 4 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 2 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_w0 endpoint_19_49_w2
private theorem endpoint_19_49_w4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 4 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 6 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 4 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_p4 endpoint_19_49_w4
private theorem endpoint_19_49_w6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 6 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 8 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 6 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_p6 endpoint_19_49_w6
private theorem endpoint_19_49_w8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 8 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 10 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 8 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_p8 endpoint_19_49_w8
private theorem endpoint_19_49_w10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 10 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 12 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 10 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_p10 endpoint_19_49_w10
private theorem endpoint_19_49_w12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 12 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 14 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 12 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_p12 endpoint_19_49_w12
private theorem endpoint_19_49_w14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 14 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 16 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 14 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_p14 endpoint_19_49_w14
private theorem endpoint_19_49_w16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 16 2 196002395507897836 = some 196002395507897836 := by decide +kernel
private theorem endpoint_19_49_p18 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 18 196002395507897836 = some 196002395507897836 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 16 2 196002395507897836 196002395507897836 196002395507897836 endpoint_19_49_p16 endpoint_19_49_w16
def endpoint_19_49 : CertifiedEndpoint :=
  ⟨⟨19, 49, 1866⟩, 196002395507897836, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_49_flag endpoint_19_49_sources 18 196002395507897836 196002395507897836 rfl endpoint_19_49_base endpoint_19_49_p18) (by decide)⟩
private def endpoint_19_50_flag : Flag := ⟨19, 50, 1806⟩
private def endpoint_19_50_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_50_base : receiptBase endpoint_19_50_flag endpoint_19_50_sources = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_w0 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_w2 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 2 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 4 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 2 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_w0 endpoint_19_50_w2
private theorem endpoint_19_50_w4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 4 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 6 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 4 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_p4 endpoint_19_50_w4
private theorem endpoint_19_50_w6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 6 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 8 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 6 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_p6 endpoint_19_50_w6
private theorem endpoint_19_50_w8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 8 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 10 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 8 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_p8 endpoint_19_50_w8
private theorem endpoint_19_50_w10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 10 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 12 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 10 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_p10 endpoint_19_50_w10
private theorem endpoint_19_50_w12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 12 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 14 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 12 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_p12 endpoint_19_50_w12
private theorem endpoint_19_50_w14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 14 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 16 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 14 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_p14 endpoint_19_50_w14
private theorem endpoint_19_50_w16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 16 2 193126616660789810 = some 193126616660789810 := by decide +kernel
private theorem endpoint_19_50_p18 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 18 193126616660789810 = some 193126616660789810 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 16 2 193126616660789810 193126616660789810 193126616660789810 endpoint_19_50_p16 endpoint_19_50_w16
def endpoint_19_50 : CertifiedEndpoint :=
  ⟨⟨19, 50, 1806⟩, 193126616660789810, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_50_flag endpoint_19_50_sources 18 193126616660789810 193126616660789810 rfl endpoint_19_50_base endpoint_19_50_p18) (by decide)⟩
private def endpoint_19_51_flag : Flag := ⟨19, 51, 1744⟩
private def endpoint_19_51_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_51_base : receiptBase endpoint_19_51_flag endpoint_19_51_sources = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_w0 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_w2 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 2 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 4 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 2 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_w0 endpoint_19_51_w2
private theorem endpoint_19_51_w4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 4 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 6 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 4 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_p4 endpoint_19_51_w4
private theorem endpoint_19_51_w6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 6 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 8 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 6 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_p6 endpoint_19_51_w6
private theorem endpoint_19_51_w8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 8 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 10 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 8 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_p8 endpoint_19_51_w8
private theorem endpoint_19_51_w10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 10 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 12 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 10 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_p10 endpoint_19_51_w10
private theorem endpoint_19_51_w12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 12 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 14 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 12 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_p12 endpoint_19_51_w12
private theorem endpoint_19_51_w14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 14 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 16 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 14 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_p14 endpoint_19_51_w14
private theorem endpoint_19_51_w16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 16 2 189814310755238231 = some 189814310755238231 := by decide +kernel
private theorem endpoint_19_51_p18 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 18 189814310755238231 = some 189814310755238231 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 16 2 189814310755238231 189814310755238231 189814310755238231 endpoint_19_51_p16 endpoint_19_51_w16
def endpoint_19_51 : CertifiedEndpoint :=
  ⟨⟨19, 51, 1744⟩, 189814310755238231, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_51_flag endpoint_19_51_sources 18 189814310755238231 189814310755238231 rfl endpoint_19_51_base endpoint_19_51_p18) (by decide)⟩
private def endpoint_19_52_flag : Flag := ⟨19, 52, 1682⟩
private def endpoint_19_52_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_52_base : receiptBase endpoint_19_52_flag endpoint_19_52_sources = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_w0 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_w2 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 2 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 4 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 2 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_w0 endpoint_19_52_w2
private theorem endpoint_19_52_w4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 4 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 6 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 4 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_p4 endpoint_19_52_w4
private theorem endpoint_19_52_w6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 6 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 8 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 6 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_p6 endpoint_19_52_w6
private theorem endpoint_19_52_w8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 8 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 10 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 8 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_p8 endpoint_19_52_w8
private theorem endpoint_19_52_w10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 10 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 12 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 10 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_p10 endpoint_19_52_w10
private theorem endpoint_19_52_w12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 12 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 14 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 12 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_p12 endpoint_19_52_w12
private theorem endpoint_19_52_w14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 14 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 16 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 14 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_p14 endpoint_19_52_w14
private theorem endpoint_19_52_w16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 16 2 186272922953218788 = some 186272922953218788 := by decide +kernel
private theorem endpoint_19_52_p18 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 18 186272922953218788 = some 186272922953218788 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 16 2 186272922953218788 186272922953218788 186272922953218788 endpoint_19_52_p16 endpoint_19_52_w16
def endpoint_19_52 : CertifiedEndpoint :=
  ⟨⟨19, 52, 1682⟩, 186272922953218788, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_52_flag endpoint_19_52_sources 18 186272922953218788 186272922953218788 rfl endpoint_19_52_base endpoint_19_52_p18) (by decide)⟩
private def endpoint_19_53_flag : Flag := ⟨19, 53, 1618⟩
private def endpoint_19_53_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_53_base : receiptBase endpoint_19_53_flag endpoint_19_53_sources = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_w0 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_w2 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 2 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 4 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 2 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_w0 endpoint_19_53_w2
private theorem endpoint_19_53_w4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 4 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 6 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 4 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_p4 endpoint_19_53_w4
private theorem endpoint_19_53_w6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 6 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 8 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 6 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_p6 endpoint_19_53_w6
private theorem endpoint_19_53_w8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 8 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 10 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 8 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_p8 endpoint_19_53_w8
private theorem endpoint_19_53_w10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 10 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 12 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 10 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_p10 endpoint_19_53_w10
private theorem endpoint_19_53_w12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 12 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 14 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 12 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_p12 endpoint_19_53_w12
private theorem endpoint_19_53_w14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 14 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 16 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 14 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_p14 endpoint_19_53_w14
private theorem endpoint_19_53_w16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 16 2 182280346851381850 = some 182280346851381850 := by decide +kernel
private theorem endpoint_19_53_p18 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 18 182280346851381850 = some 182280346851381850 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 16 2 182280346851381850 182280346851381850 182280346851381850 endpoint_19_53_p16 endpoint_19_53_w16
def endpoint_19_53 : CertifiedEndpoint :=
  ⟨⟨19, 53, 1618⟩, 182280346851381850, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_53_flag endpoint_19_53_sources 18 182280346851381850 182280346851381850 rfl endpoint_19_53_base endpoint_19_53_p18) (by decide)⟩
private def endpoint_19_54_flag : Flag := ⟨19, 54, 1553⟩
private def endpoint_19_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_54_base : receiptBase endpoint_19_54_flag endpoint_19_54_sources = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_w0 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_w2 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 2 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 4 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 2 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_w0 endpoint_19_54_w2
private theorem endpoint_19_54_w4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 4 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 6 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 4 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_p4 endpoint_19_54_w4
private theorem endpoint_19_54_w6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 6 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 8 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 6 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_p6 endpoint_19_54_w6
private theorem endpoint_19_54_w8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 8 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 10 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 8 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_p8 endpoint_19_54_w8
private theorem endpoint_19_54_w10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 10 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 12 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 10 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_p10 endpoint_19_54_w10
private theorem endpoint_19_54_w12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 12 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 14 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 12 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_p12 endpoint_19_54_w12
private theorem endpoint_19_54_w14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 14 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 16 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 14 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_p14 endpoint_19_54_w14
private theorem endpoint_19_54_w16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 16 2 177938472375543517 = some 177938472375543517 := by decide +kernel
private theorem endpoint_19_54_p18 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 18 177938472375543517 = some 177938472375543517 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 16 2 177938472375543517 177938472375543517 177938472375543517 endpoint_19_54_p16 endpoint_19_54_w16
def endpoint_19_54 : CertifiedEndpoint :=
  ⟨⟨19, 54, 1553⟩, 177938472375543517, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_54_flag endpoint_19_54_sources 18 177938472375543517 177938472375543517 rfl endpoint_19_54_base endpoint_19_54_p18) (by decide)⟩
private def endpoint_19_55_flag : Flag := ⟨19, 55, 1487⟩
private def endpoint_19_55_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_55_base : receiptBase endpoint_19_55_flag endpoint_19_55_sources = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_w0 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_w2 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 2 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 4 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 2 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_w0 endpoint_19_55_w2
private theorem endpoint_19_55_w4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 4 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 6 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 4 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_p4 endpoint_19_55_w4
private theorem endpoint_19_55_w6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 6 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 8 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 6 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_p6 endpoint_19_55_w6
private theorem endpoint_19_55_w8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 8 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 10 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 8 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_p8 endpoint_19_55_w8
private theorem endpoint_19_55_w10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 10 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 12 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 10 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_p10 endpoint_19_55_w10
private theorem endpoint_19_55_w12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 12 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 14 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 12 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_p12 endpoint_19_55_w12
private theorem endpoint_19_55_w14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 14 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 16 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 14 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_p14 endpoint_19_55_w14
private theorem endpoint_19_55_w16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 16 2 173424847325611390 = some 173424847325611390 := by decide +kernel
private theorem endpoint_19_55_p18 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 18 173424847325611390 = some 173424847325611390 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 16 2 173424847325611390 173424847325611390 173424847325611390 endpoint_19_55_p16 endpoint_19_55_w16
def endpoint_19_55 : CertifiedEndpoint :=
  ⟨⟨19, 55, 1487⟩, 173424847325611390, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_55_flag endpoint_19_55_sources 18 173424847325611390 173424847325611390 rfl endpoint_19_55_base endpoint_19_55_p18) (by decide)⟩
private def endpoint_19_56_flag : Flag := ⟨19, 56, 1420⟩
private def endpoint_19_56_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_56_base : receiptBase endpoint_19_56_flag endpoint_19_56_sources = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_w0 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_w2 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 2 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 4 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 2 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_w0 endpoint_19_56_w2
private theorem endpoint_19_56_w4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 4 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 6 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 4 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_p4 endpoint_19_56_w4
private theorem endpoint_19_56_w6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 6 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 8 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 6 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_p6 endpoint_19_56_w6
private theorem endpoint_19_56_w8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 8 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 10 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 8 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_p8 endpoint_19_56_w8
private theorem endpoint_19_56_w10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 10 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 12 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 10 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_p10 endpoint_19_56_w10
private theorem endpoint_19_56_w12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 12 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 14 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 12 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_p12 endpoint_19_56_w12
private theorem endpoint_19_56_w14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 14 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 16 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 14 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_p14 endpoint_19_56_w14
private theorem endpoint_19_56_w16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 16 2 169975702413379187 = some 169975702413379187 := by decide +kernel
private theorem endpoint_19_56_p18 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 18 169975702413379187 = some 169975702413379187 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 16 2 169975702413379187 169975702413379187 169975702413379187 endpoint_19_56_p16 endpoint_19_56_w16
def endpoint_19_56 : CertifiedEndpoint :=
  ⟨⟨19, 56, 1420⟩, 169975702413379187, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_56_flag endpoint_19_56_sources 18 169975702413379187 169975702413379187 rfl endpoint_19_56_base endpoint_19_56_p18) (by decide)⟩
private def endpoint_19_57_flag : Flag := ⟨19, 57, 1351⟩
private def endpoint_19_57_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_57_base : receiptBase endpoint_19_57_flag endpoint_19_57_sources = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_w0 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_w2 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 2 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p4 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 4 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 2 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_w0 endpoint_19_57_w2
private theorem endpoint_19_57_w4 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 4 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p6 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 6 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 4 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_p4 endpoint_19_57_w4
private theorem endpoint_19_57_w6 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 6 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p8 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 8 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 6 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_p6 endpoint_19_57_w6
private theorem endpoint_19_57_w8 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 8 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p10 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 10 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 8 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_p8 endpoint_19_57_w8
private theorem endpoint_19_57_w10 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 10 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p12 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 12 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 10 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_p10 endpoint_19_57_w10
private theorem endpoint_19_57_w12 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 12 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p14 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 14 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 12 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_p12 endpoint_19_57_w12
private theorem endpoint_19_57_w14 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 14 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p16 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 16 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 14 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_p14 endpoint_19_57_w14
private theorem endpoint_19_57_w16 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 16 2 162921047211221217 = some 162921047211221217 := by decide +kernel
private theorem endpoint_19_57_p18 : receiptWindow endpoint_19_57_flag endpoint_19_57_sources 0 18 162921047211221217 = some 162921047211221217 :=
  join_receipt_window endpoint_19_57_flag endpoint_19_57_sources 0 16 2 162921047211221217 162921047211221217 162921047211221217 endpoint_19_57_p16 endpoint_19_57_w16
def endpoint_19_57 : CertifiedEndpoint :=
  ⟨⟨19, 57, 1351⟩, 162921047211221217, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_57_flag endpoint_19_57_sources 18 162921047211221217 162921047211221217 rfl endpoint_19_57_base endpoint_19_57_p18) (by decide)⟩
private def endpoint_19_58_flag : Flag := ⟨19, 58, 1281⟩
private def endpoint_19_58_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_58_base : receiptBase endpoint_19_58_flag endpoint_19_58_sources = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_w0 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_w2 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 2 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p4 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 4 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 2 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_w0 endpoint_19_58_w2
private theorem endpoint_19_58_w4 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 4 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p6 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 6 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 4 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_p4 endpoint_19_58_w4
private theorem endpoint_19_58_w6 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 6 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p8 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 8 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 6 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_p6 endpoint_19_58_w6
private theorem endpoint_19_58_w8 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 8 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p10 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 10 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 8 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_p8 endpoint_19_58_w8
private theorem endpoint_19_58_w10 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 10 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p12 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 12 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 10 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_p10 endpoint_19_58_w10
private theorem endpoint_19_58_w12 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 12 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p14 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 14 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 12 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_p12 endpoint_19_58_w12
private theorem endpoint_19_58_w14 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 14 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p16 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 16 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 14 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_p14 endpoint_19_58_w14
private theorem endpoint_19_58_w16 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 16 2 158354579841706852 = some 158354579841706852 := by decide +kernel
private theorem endpoint_19_58_p18 : receiptWindow endpoint_19_58_flag endpoint_19_58_sources 0 18 158354579841706852 = some 158354579841706852 :=
  join_receipt_window endpoint_19_58_flag endpoint_19_58_sources 0 16 2 158354579841706852 158354579841706852 158354579841706852 endpoint_19_58_p16 endpoint_19_58_w16
def endpoint_19_58 : CertifiedEndpoint :=
  ⟨⟨19, 58, 1281⟩, 158354579841706852, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_58_flag endpoint_19_58_sources 18 158354579841706852 158354579841706852 rfl endpoint_19_58_base endpoint_19_58_p18) (by decide)⟩
private def endpoint_19_59_flag : Flag := ⟨19, 59, 1209⟩
private def endpoint_19_59_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_59_base : receiptBase endpoint_19_59_flag endpoint_19_59_sources = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_w0 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_w2 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 2 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p4 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 4 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 2 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_w0 endpoint_19_59_w2
private theorem endpoint_19_59_w4 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 4 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p6 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 6 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 4 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_p4 endpoint_19_59_w4
private theorem endpoint_19_59_w6 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 6 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p8 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 8 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 6 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_p6 endpoint_19_59_w6
private theorem endpoint_19_59_w8 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 8 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p10 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 10 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 8 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_p8 endpoint_19_59_w8
private theorem endpoint_19_59_w10 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 10 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p12 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 12 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 10 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_p10 endpoint_19_59_w10
private theorem endpoint_19_59_w12 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 12 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p14 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 14 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 12 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_p12 endpoint_19_59_w12
private theorem endpoint_19_59_w14 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 14 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p16 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 16 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 14 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_p14 endpoint_19_59_w14
private theorem endpoint_19_59_w16 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 16 2 151847210084570296 = some 151847210084570296 := by decide +kernel
private theorem endpoint_19_59_p18 : receiptWindow endpoint_19_59_flag endpoint_19_59_sources 0 18 151847210084570296 = some 151847210084570296 :=
  join_receipt_window endpoint_19_59_flag endpoint_19_59_sources 0 16 2 151847210084570296 151847210084570296 151847210084570296 endpoint_19_59_p16 endpoint_19_59_w16
def endpoint_19_59 : CertifiedEndpoint :=
  ⟨⟨19, 59, 1209⟩, 151847210084570296, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_59_flag endpoint_19_59_sources 18 151847210084570296 151847210084570296 rfl endpoint_19_59_base endpoint_19_59_p18) (by decide)⟩
def endpoint_19_60 : CertifiedEndpoint :=
  ⟨⟨19, 60, 1136⟩, 263003531060175632, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_61 : CertifiedEndpoint :=
  ⟨⟨19, 61, 1062⟩, 250114526267175177, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_62 : CertifiedEndpoint :=
  ⟨⟨19, 62, 985⟩, 235768778337010533, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_63 : CertifiedEndpoint :=
  ⟨⟨19, 63, 908⟩, 220682731498107899, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_64 : CertifiedEndpoint :=
  ⟨⟨19, 64, 829⟩, 204340547288914945, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_65 : CertifiedEndpoint :=
  ⟨⟨19, 65, 748⟩, 186713568977480523, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_66 : CertifiedEndpoint :=
  ⟨⟨19, 66, 665⟩, 167773139831853485, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_67 : CertifiedEndpoint :=
  ⟨⟨19, 67, 581⟩, 147762850716834422, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_68 : CertifiedEndpoint :=
  ⟨⟨19, 68, 494⟩, 126114325828960566, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_69 : CertifiedEndpoint :=
  ⟨⟨19, 69, 406⟩, 103348179751776105, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_70 : CertifiedEndpoint :=
  ⟨⟨19, 70, 316⟩, 79163508156578152, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_71 : CertifiedEndpoint :=
  ⟨⟨19, 71, 224⟩, 53531654311415559, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_72 : CertifiedEndpoint :=
  ⟨⟨19, 72, 130⟩, 26423961484337178, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_20 : CertifiedEndpoint :=
  ⟨⟨20, 20, 2903⟩, 157663225415831623, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_21 : CertifiedEndpoint :=
  ⟨⟨20, 21, 2862⟩, 160133801906265342, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_22 : CertifiedEndpoint :=
  ⟨⟨20, 22, 2821⟩, 162468430700862431, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_23 : CertifiedEndpoint :=
  ⟨⟨20, 23, 2779⟩, 173912471708481964, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_24 : CertifiedEndpoint :=
  ⟨⟨20, 24, 2736⟩, 184860672177438256, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_25 : CertifiedEndpoint :=
  ⟨⟨20, 25, 2693⟩, 195370929756457978, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_26 : CertifiedEndpoint :=
  ⟨⟨20, 26, 2649⟩, 205365211491530019, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_27 : CertifiedEndpoint :=
  ⟨⟨20, 27, 2605⟩, 214911482684023270, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_28 : CertifiedEndpoint :=
  ⟨⟨20, 28, 2560⟩, 223921642727284400, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_29 : CertifiedEndpoint :=
  ⟨⟨20, 29, 2514⟩, 232380590142350079, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_30 : CertifiedEndpoint :=
  ⟨⟨20, 30, 2468⟩, 240371391709552528, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_31 : CertifiedEndpoint :=
  ⟨⟨20, 31, 2421⟩, 247790845343275086, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_32 : CertifiedEndpoint :=
  ⟨⟨20, 32, 2373⟩, 254623849564554423, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_33 : CertifiedEndpoint :=
  ⟨⟨20, 33, 2325⟩, 260968572632686090, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_20_34_flag : Flag := ⟨20, 34, 2276⟩
private def endpoint_20_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_20_34_base : receiptBase endpoint_20_34_flag endpoint_20_34_sources = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_w0 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_w2 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 2 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p4 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 4 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 2 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_w0 endpoint_20_34_w2
private theorem endpoint_20_34_w4 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 4 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p6 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 6 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 4 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p4 endpoint_20_34_w4
private theorem endpoint_20_34_w6 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 6 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p8 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 8 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 6 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p6 endpoint_20_34_w6
private theorem endpoint_20_34_w8 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 8 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p10 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 10 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 8 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p8 endpoint_20_34_w8
private theorem endpoint_20_34_w10 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 10 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p12 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 12 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 10 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p10 endpoint_20_34_w10
private theorem endpoint_20_34_w12 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 12 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p14 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 14 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 12 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p12 endpoint_20_34_w12
private theorem endpoint_20_34_w14 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 14 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p16 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 16 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 14 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p14 endpoint_20_34_w14
private theorem endpoint_20_34_w16 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 16 2 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p18 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 18 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 16 2 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p16 endpoint_20_34_w16
private theorem endpoint_20_34_w18 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 18 1 169224178579608994 = some 169224178579608994 := by decide +kernel
private theorem endpoint_20_34_p19 : receiptWindow endpoint_20_34_flag endpoint_20_34_sources 0 19 169224178579608994 = some 169224178579608994 :=
  join_receipt_window endpoint_20_34_flag endpoint_20_34_sources 0 18 1 169224178579608994 169224178579608994 169224178579608994 endpoint_20_34_p18 endpoint_20_34_w18
def endpoint_20_34 : CertifiedEndpoint :=
  ⟨⟨20, 34, 2276⟩, 169224178579608994, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_20_34_flag endpoint_20_34_sources 19 169224178579608994 169224178579608994 rfl endpoint_20_34_base endpoint_20_34_p19) (by decide)⟩
private def endpoint_20_35_flag : Flag := ⟨20, 35, 2226⟩
private def endpoint_20_35_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_35_base : receiptBase endpoint_20_35_flag endpoint_20_35_sources = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_w0 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_w2 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 2 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p4 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 4 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 2 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_w0 endpoint_20_35_w2
private theorem endpoint_20_35_w4 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 4 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p6 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 6 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 4 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p4 endpoint_20_35_w4
private theorem endpoint_20_35_w6 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 6 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p8 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 8 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 6 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p6 endpoint_20_35_w6
private theorem endpoint_20_35_w8 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 8 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p10 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 10 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 8 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p8 endpoint_20_35_w8
private theorem endpoint_20_35_w10 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 10 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p12 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 12 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 10 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p10 endpoint_20_35_w10
private theorem endpoint_20_35_w12 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 12 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p14 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 14 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 12 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p12 endpoint_20_35_w12
private theorem endpoint_20_35_w14 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 14 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p16 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 16 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 14 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p14 endpoint_20_35_w14
private theorem endpoint_20_35_w16 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 16 2 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p18 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 18 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 16 2 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p16 endpoint_20_35_w16
private theorem endpoint_20_35_w18 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 18 1 175513245386345692 = some 175513245386345692 := by decide +kernel
private theorem endpoint_20_35_p19 : receiptWindow endpoint_20_35_flag endpoint_20_35_sources 0 19 175513245386345692 = some 175513245386345692 :=
  join_receipt_window endpoint_20_35_flag endpoint_20_35_sources 0 18 1 175513245386345692 175513245386345692 175513245386345692 endpoint_20_35_p18 endpoint_20_35_w18
def endpoint_20_35 : CertifiedEndpoint :=
  ⟨⟨20, 35, 2226⟩, 175513245386345692, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_35_flag endpoint_20_35_sources 19 175513245386345692 175513245386345692 rfl endpoint_20_35_base endpoint_20_35_p19) (by decide)⟩
private def endpoint_20_36_flag : Flag := ⟨20, 36, 2175⟩
private def endpoint_20_36_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_36_base : receiptBase endpoint_20_36_flag endpoint_20_36_sources = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_w0 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_w2 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 2 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p4 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 4 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 2 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_w0 endpoint_20_36_w2
private theorem endpoint_20_36_w4 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 4 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p6 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 6 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 4 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p4 endpoint_20_36_w4
private theorem endpoint_20_36_w6 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 6 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p8 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 8 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 6 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p6 endpoint_20_36_w6
private theorem endpoint_20_36_w8 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 8 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p10 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 10 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 8 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p8 endpoint_20_36_w8
private theorem endpoint_20_36_w10 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 10 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p12 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 12 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 10 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p10 endpoint_20_36_w10
private theorem endpoint_20_36_w12 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 12 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p14 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 14 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 12 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p12 endpoint_20_36_w12
private theorem endpoint_20_36_w14 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 14 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p16 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 16 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 14 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p14 endpoint_20_36_w14
private theorem endpoint_20_36_w16 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 16 2 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p18 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 18 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 16 2 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p16 endpoint_20_36_w16
private theorem endpoint_20_36_w18 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 18 1 175781802604076834 = some 175781802604076834 := by decide +kernel
private theorem endpoint_20_36_p19 : receiptWindow endpoint_20_36_flag endpoint_20_36_sources 0 19 175781802604076834 = some 175781802604076834 :=
  join_receipt_window endpoint_20_36_flag endpoint_20_36_sources 0 18 1 175781802604076834 175781802604076834 175781802604076834 endpoint_20_36_p18 endpoint_20_36_w18
def endpoint_20_36 : CertifiedEndpoint :=
  ⟨⟨20, 36, 2175⟩, 175781802604076834, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_36_flag endpoint_20_36_sources 19 175781802604076834 175781802604076834 rfl endpoint_20_36_base endpoint_20_36_p19) (by decide)⟩
private def endpoint_20_37_flag : Flag := ⟨20, 37, 2124⟩
private def endpoint_20_37_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_37_base : receiptBase endpoint_20_37_flag endpoint_20_37_sources = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_w0 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_w2 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 2 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p4 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 4 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 2 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_w0 endpoint_20_37_w2
private theorem endpoint_20_37_w4 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 4 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p6 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 6 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 4 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p4 endpoint_20_37_w4
private theorem endpoint_20_37_w6 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 6 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p8 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 8 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 6 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p6 endpoint_20_37_w6
private theorem endpoint_20_37_w8 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 8 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p10 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 10 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 8 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p8 endpoint_20_37_w8
private theorem endpoint_20_37_w10 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 10 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p12 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 12 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 10 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p10 endpoint_20_37_w10
private theorem endpoint_20_37_w12 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 12 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p14 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 14 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 12 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p12 endpoint_20_37_w12
private theorem endpoint_20_37_w14 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 14 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p16 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 16 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 14 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p14 endpoint_20_37_w14
private theorem endpoint_20_37_w16 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 16 2 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p18 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 18 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 16 2 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p16 endpoint_20_37_w16
private theorem endpoint_20_37_w18 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 18 1 175858582832923605 = some 175858582832923605 := by decide +kernel
private theorem endpoint_20_37_p19 : receiptWindow endpoint_20_37_flag endpoint_20_37_sources 0 19 175858582832923605 = some 175858582832923605 :=
  join_receipt_window endpoint_20_37_flag endpoint_20_37_sources 0 18 1 175858582832923605 175858582832923605 175858582832923605 endpoint_20_37_p18 endpoint_20_37_w18
def endpoint_20_37 : CertifiedEndpoint :=
  ⟨⟨20, 37, 2124⟩, 175858582832923605, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_37_flag endpoint_20_37_sources 19 175858582832923605 175858582832923605 rfl endpoint_20_37_base endpoint_20_37_p19) (by decide)⟩
private def endpoint_20_38_flag : Flag := ⟨20, 38, 2072⟩
private def endpoint_20_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_38_base : receiptBase endpoint_20_38_flag endpoint_20_38_sources = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_w0 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_w2 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 2 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p4 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 4 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 2 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_w0 endpoint_20_38_w2
private theorem endpoint_20_38_w4 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 4 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p6 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 6 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 4 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p4 endpoint_20_38_w4
private theorem endpoint_20_38_w6 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 6 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p8 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 8 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 6 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p6 endpoint_20_38_w6
private theorem endpoint_20_38_w8 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 8 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p10 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 10 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 8 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p8 endpoint_20_38_w8
private theorem endpoint_20_38_w10 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 10 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p12 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 12 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 10 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p10 endpoint_20_38_w10
private theorem endpoint_20_38_w12 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 12 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p14 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 14 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 12 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p12 endpoint_20_38_w12
private theorem endpoint_20_38_w14 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 14 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p16 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 16 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 14 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p14 endpoint_20_38_w14
private theorem endpoint_20_38_w16 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 16 2 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p18 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 18 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 16 2 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p16 endpoint_20_38_w16
private theorem endpoint_20_38_w18 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 18 1 175660975114498744 = some 175660975114498744 := by decide +kernel
private theorem endpoint_20_38_p19 : receiptWindow endpoint_20_38_flag endpoint_20_38_sources 0 19 175660975114498744 = some 175660975114498744 :=
  join_receipt_window endpoint_20_38_flag endpoint_20_38_sources 0 18 1 175660975114498744 175660975114498744 175660975114498744 endpoint_20_38_p18 endpoint_20_38_w18
def endpoint_20_38 : CertifiedEndpoint :=
  ⟨⟨20, 38, 2072⟩, 175660975114498744, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_38_flag endpoint_20_38_sources 19 175660975114498744 175660975114498744 rfl endpoint_20_38_base endpoint_20_38_p19) (by decide)⟩
private def endpoint_20_39_flag : Flag := ⟨20, 39, 2019⟩
private def endpoint_20_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_39_base : receiptBase endpoint_20_39_flag endpoint_20_39_sources = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_w0 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_w2 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 2 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p4 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 4 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 2 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_w0 endpoint_20_39_w2
private theorem endpoint_20_39_w4 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 4 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p6 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 6 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 4 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p4 endpoint_20_39_w4
private theorem endpoint_20_39_w6 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 6 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p8 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 8 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 6 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p6 endpoint_20_39_w6
private theorem endpoint_20_39_w8 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 8 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p10 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 10 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 8 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p8 endpoint_20_39_w8
private theorem endpoint_20_39_w10 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 10 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p12 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 12 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 10 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p10 endpoint_20_39_w10
private theorem endpoint_20_39_w12 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 12 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p14 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 14 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 12 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p12 endpoint_20_39_w12
private theorem endpoint_20_39_w14 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 14 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p16 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 16 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 14 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p14 endpoint_20_39_w14
private theorem endpoint_20_39_w16 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 16 2 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p18 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 18 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 16 2 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p16 endpoint_20_39_w16
private theorem endpoint_20_39_w18 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 18 1 175183393481913131 = some 175183393481913131 := by decide +kernel
private theorem endpoint_20_39_p19 : receiptWindow endpoint_20_39_flag endpoint_20_39_sources 0 19 175183393481913131 = some 175183393481913131 :=
  join_receipt_window endpoint_20_39_flag endpoint_20_39_sources 0 18 1 175183393481913131 175183393481913131 175183393481913131 endpoint_20_39_p18 endpoint_20_39_w18
def endpoint_20_39 : CertifiedEndpoint :=
  ⟨⟨20, 39, 2019⟩, 175183393481913131, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_39_flag endpoint_20_39_sources 19 175183393481913131 175183393481913131 rfl endpoint_20_39_base endpoint_20_39_p19) (by decide)⟩
private def endpoint_20_40_flag : Flag := ⟨20, 40, 1965⟩
private def endpoint_20_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_40_base : receiptBase endpoint_20_40_flag endpoint_20_40_sources = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_w0 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_w2 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 2 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p4 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 4 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 2 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_w0 endpoint_20_40_w2
private theorem endpoint_20_40_w4 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 4 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p6 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 6 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 4 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p4 endpoint_20_40_w4
private theorem endpoint_20_40_w6 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 6 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p8 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 8 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 6 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p6 endpoint_20_40_w6
private theorem endpoint_20_40_w8 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 8 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p10 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 10 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 8 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p8 endpoint_20_40_w8
private theorem endpoint_20_40_w10 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 10 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p12 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 12 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 10 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p10 endpoint_20_40_w10
private theorem endpoint_20_40_w12 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 12 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p14 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 14 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 12 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p12 endpoint_20_40_w12
private theorem endpoint_20_40_w14 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 14 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p16 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 16 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 14 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p14 endpoint_20_40_w14
private theorem endpoint_20_40_w16 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 16 2 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p18 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 18 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 16 2 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p16 endpoint_20_40_w16
private theorem endpoint_20_40_w18 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 18 1 174420251968277644 = some 174420251968277644 := by decide +kernel
private theorem endpoint_20_40_p19 : receiptWindow endpoint_20_40_flag endpoint_20_40_sources 0 19 174420251968277644 = some 174420251968277644 :=
  join_receipt_window endpoint_20_40_flag endpoint_20_40_sources 0 18 1 174420251968277644 174420251968277644 174420251968277644 endpoint_20_40_p18 endpoint_20_40_w18
def endpoint_20_40 : CertifiedEndpoint :=
  ⟨⟨20, 40, 1965⟩, 174420251968277644, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_40_flag endpoint_20_40_sources 19 174420251968277644 174420251968277644 rfl endpoint_20_40_base endpoint_20_40_p19) (by decide)⟩
private def endpoint_20_41_flag : Flag := ⟨20, 41, 1910⟩
private def endpoint_20_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_41_base : receiptBase endpoint_20_41_flag endpoint_20_41_sources = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_w0 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_w2 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 2 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p4 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 4 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 2 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_w0 endpoint_20_41_w2
private theorem endpoint_20_41_w4 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 4 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p6 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 6 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 4 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p4 endpoint_20_41_w4
private theorem endpoint_20_41_w6 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 6 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p8 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 8 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 6 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p6 endpoint_20_41_w6
private theorem endpoint_20_41_w8 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 8 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p10 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 10 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 8 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p8 endpoint_20_41_w8
private theorem endpoint_20_41_w10 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 10 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p12 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 12 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 10 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p10 endpoint_20_41_w10
private theorem endpoint_20_41_w12 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 12 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p14 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 14 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 12 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p12 endpoint_20_41_w12
private theorem endpoint_20_41_w14 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 14 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p16 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 16 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 14 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p14 endpoint_20_41_w14
private theorem endpoint_20_41_w16 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 16 2 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p18 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 18 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 16 2 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p16 endpoint_20_41_w16
private theorem endpoint_20_41_w18 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 18 1 173365964606703162 = some 173365964606703162 := by decide +kernel
private theorem endpoint_20_41_p19 : receiptWindow endpoint_20_41_flag endpoint_20_41_sources 0 19 173365964606703162 = some 173365964606703162 :=
  join_receipt_window endpoint_20_41_flag endpoint_20_41_sources 0 18 1 173365964606703162 173365964606703162 173365964606703162 endpoint_20_41_p18 endpoint_20_41_w18
def endpoint_20_41 : CertifiedEndpoint :=
  ⟨⟨20, 41, 1910⟩, 173365964606703162, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_41_flag endpoint_20_41_sources 19 173365964606703162 173365964606703162 rfl endpoint_20_41_base endpoint_20_41_p19) (by decide)⟩
private def endpoint_20_42_flag : Flag := ⟨20, 42, 1855⟩
private def endpoint_20_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_20_42_base : receiptBase endpoint_20_42_flag endpoint_20_42_sources = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_w0 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_w2 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 2 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p4 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 4 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 2 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_w0 endpoint_20_42_w2
private theorem endpoint_20_42_w4 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 4 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p6 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 6 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 4 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p4 endpoint_20_42_w4
private theorem endpoint_20_42_w6 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 6 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p8 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 8 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 6 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p6 endpoint_20_42_w6
private theorem endpoint_20_42_w8 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 8 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p10 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 10 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 8 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p8 endpoint_20_42_w8
private theorem endpoint_20_42_w10 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 10 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p12 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 12 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 10 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p10 endpoint_20_42_w10
private theorem endpoint_20_42_w12 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 12 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p14 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 14 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 12 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p12 endpoint_20_42_w12
private theorem endpoint_20_42_w14 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 14 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p16 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 16 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 14 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p14 endpoint_20_42_w14
private theorem endpoint_20_42_w16 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 16 2 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p18 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 18 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 16 2 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p16 endpoint_20_42_w16
private theorem endpoint_20_42_w18 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 18 1 172105004344539987 = some 172105004344539987 := by decide +kernel
private theorem endpoint_20_42_p19 : receiptWindow endpoint_20_42_flag endpoint_20_42_sources 0 19 172105004344539987 = some 172105004344539987 :=
  join_receipt_window endpoint_20_42_flag endpoint_20_42_sources 0 18 1 172105004344539987 172105004344539987 172105004344539987 endpoint_20_42_p18 endpoint_20_42_w18
def endpoint_20_42 : CertifiedEndpoint :=
  ⟨⟨20, 42, 1855⟩, 172105004344539987, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_20_42_flag endpoint_20_42_sources 19 172105004344539987 172105004344539987 rfl endpoint_20_42_base endpoint_20_42_p19) (by decide)⟩
private def endpoint_20_43_flag : Flag := ⟨20, 43, 1798⟩
private def endpoint_20_43_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_43_base : receiptBase endpoint_20_43_flag endpoint_20_43_sources = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_w0 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_w2 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 2 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p4 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 4 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 2 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_w0 endpoint_20_43_w2
private theorem endpoint_20_43_w4 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 4 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p6 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 6 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 4 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p4 endpoint_20_43_w4
private theorem endpoint_20_43_w6 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 6 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p8 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 8 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 6 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p6 endpoint_20_43_w6
private theorem endpoint_20_43_w8 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 8 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p10 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 10 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 8 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p8 endpoint_20_43_w8
private theorem endpoint_20_43_w10 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 10 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p12 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 12 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 10 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p10 endpoint_20_43_w10
private theorem endpoint_20_43_w12 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 12 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p14 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 14 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 12 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p12 endpoint_20_43_w12
private theorem endpoint_20_43_w14 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 14 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p16 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 16 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 14 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p14 endpoint_20_43_w14
private theorem endpoint_20_43_w16 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 16 2 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p18 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 18 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 16 2 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p16 endpoint_20_43_w16
private theorem endpoint_20_43_w18 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 18 1 172130388609379149 = some 172130388609379149 := by decide +kernel
private theorem endpoint_20_43_p19 : receiptWindow endpoint_20_43_flag endpoint_20_43_sources 0 19 172130388609379149 = some 172130388609379149 :=
  join_receipt_window endpoint_20_43_flag endpoint_20_43_sources 0 18 1 172130388609379149 172130388609379149 172130388609379149 endpoint_20_43_p18 endpoint_20_43_w18
def endpoint_20_43 : CertifiedEndpoint :=
  ⟨⟨20, 43, 1798⟩, 172130388609379149, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_43_flag endpoint_20_43_sources 19 172130388609379149 172130388609379149 rfl endpoint_20_43_base endpoint_20_43_p19) (by decide)⟩
private def endpoint_20_44_flag : Flag := ⟨20, 44, 1741⟩
private def endpoint_20_44_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_44_base : receiptBase endpoint_20_44_flag endpoint_20_44_sources = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_w0 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_w2 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 2 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p4 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 4 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 2 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_w0 endpoint_20_44_w2
private theorem endpoint_20_44_w4 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 4 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p6 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 6 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 4 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p4 endpoint_20_44_w4
private theorem endpoint_20_44_w6 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 6 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p8 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 8 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 6 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p6 endpoint_20_44_w6
private theorem endpoint_20_44_w8 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 8 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p10 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 10 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 8 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p8 endpoint_20_44_w8
private theorem endpoint_20_44_w10 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 10 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p12 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 12 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 10 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p10 endpoint_20_44_w10
private theorem endpoint_20_44_w12 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 12 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p14 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 14 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 12 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p12 endpoint_20_44_w12
private theorem endpoint_20_44_w14 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 14 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p16 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 16 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 14 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p14 endpoint_20_44_w14
private theorem endpoint_20_44_w16 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 16 2 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p18 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 18 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 16 2 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p16 endpoint_20_44_w16
private theorem endpoint_20_44_w18 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 18 1 170185387619814353 = some 170185387619814353 := by decide +kernel
private theorem endpoint_20_44_p19 : receiptWindow endpoint_20_44_flag endpoint_20_44_sources 0 19 170185387619814353 = some 170185387619814353 :=
  join_receipt_window endpoint_20_44_flag endpoint_20_44_sources 0 18 1 170185387619814353 170185387619814353 170185387619814353 endpoint_20_44_p18 endpoint_20_44_w18
def endpoint_20_44 : CertifiedEndpoint :=
  ⟨⟨20, 44, 1741⟩, 170185387619814353, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_44_flag endpoint_20_44_sources 19 170185387619814353 170185387619814353 rfl endpoint_20_44_base endpoint_20_44_p19) (by decide)⟩
private def endpoint_20_45_flag : Flag := ⟨20, 45, 1683⟩
private def endpoint_20_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_45_base : receiptBase endpoint_20_45_flag endpoint_20_45_sources = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_w0 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_w2 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 2 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p4 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 4 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 2 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_w0 endpoint_20_45_w2
private theorem endpoint_20_45_w4 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 4 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p6 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 6 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 4 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p4 endpoint_20_45_w4
private theorem endpoint_20_45_w6 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 6 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p8 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 8 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 6 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p6 endpoint_20_45_w6
private theorem endpoint_20_45_w8 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 8 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p10 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 10 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 8 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p8 endpoint_20_45_w8
private theorem endpoint_20_45_w10 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 10 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p12 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 12 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 10 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p10 endpoint_20_45_w10
private theorem endpoint_20_45_w12 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 12 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p14 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 14 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 12 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p12 endpoint_20_45_w12
private theorem endpoint_20_45_w14 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 14 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p16 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 16 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 14 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p14 endpoint_20_45_w14
private theorem endpoint_20_45_w16 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 16 2 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p18 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 18 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 16 2 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p16 endpoint_20_45_w16
private theorem endpoint_20_45_w18 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 18 1 167925294301568624 = some 167925294301568624 := by decide +kernel
private theorem endpoint_20_45_p19 : receiptWindow endpoint_20_45_flag endpoint_20_45_sources 0 19 167925294301568624 = some 167925294301568624 :=
  join_receipt_window endpoint_20_45_flag endpoint_20_45_sources 0 18 1 167925294301568624 167925294301568624 167925294301568624 endpoint_20_45_p18 endpoint_20_45_w18
def endpoint_20_45 : CertifiedEndpoint :=
  ⟨⟨20, 45, 1683⟩, 167925294301568624, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_45_flag endpoint_20_45_sources 19 167925294301568624 167925294301568624 rfl endpoint_20_45_base endpoint_20_45_p19) (by decide)⟩
private def endpoint_20_46_flag : Flag := ⟨20, 46, 1623⟩
private def endpoint_20_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_20_46_base : receiptBase endpoint_20_46_flag endpoint_20_46_sources = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_w0 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_w2 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 2 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p4 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 4 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 2 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_w0 endpoint_20_46_w2
private theorem endpoint_20_46_w4 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 4 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p6 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 6 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 4 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p4 endpoint_20_46_w4
private theorem endpoint_20_46_w6 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 6 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p8 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 8 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 6 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p6 endpoint_20_46_w6
private theorem endpoint_20_46_w8 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 8 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p10 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 10 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 8 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p8 endpoint_20_46_w8
private theorem endpoint_20_46_w10 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 10 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p12 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 12 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 10 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p10 endpoint_20_46_w10
private theorem endpoint_20_46_w12 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 12 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p14 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 14 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 12 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p12 endpoint_20_46_w12
private theorem endpoint_20_46_w14 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 14 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p16 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 16 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 14 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p14 endpoint_20_46_w14
private theorem endpoint_20_46_w16 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 16 2 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p18 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 18 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 16 2 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p16 endpoint_20_46_w16
private theorem endpoint_20_46_w18 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 18 1 165245185841173545 = some 165245185841173545 := by decide +kernel
private theorem endpoint_20_46_p19 : receiptWindow endpoint_20_46_flag endpoint_20_46_sources 0 19 165245185841173545 = some 165245185841173545 :=
  join_receipt_window endpoint_20_46_flag endpoint_20_46_sources 0 18 1 165245185841173545 165245185841173545 165245185841173545 endpoint_20_46_p18 endpoint_20_46_w18
def endpoint_20_46 : CertifiedEndpoint :=
  ⟨⟨20, 46, 1623⟩, 165245185841173545, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_20_46_flag endpoint_20_46_sources 19 165245185841173545 165245185841173545 rfl endpoint_20_46_base endpoint_20_46_p19) (by decide)⟩
private def endpoint_20_47_flag : Flag := ⟨20, 47, 1563⟩
private def endpoint_20_47_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_47_base : receiptBase endpoint_20_47_flag endpoint_20_47_sources = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_w0 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_w2 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 2 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p4 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 4 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 2 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_w0 endpoint_20_47_w2
private theorem endpoint_20_47_w4 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 4 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p6 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 6 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 4 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p4 endpoint_20_47_w4
private theorem endpoint_20_47_w6 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 6 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p8 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 8 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 6 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p6 endpoint_20_47_w6
private theorem endpoint_20_47_w8 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 8 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p10 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 10 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 8 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p8 endpoint_20_47_w8
private theorem endpoint_20_47_w10 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 10 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p12 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 12 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 10 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p10 endpoint_20_47_w10
private theorem endpoint_20_47_w12 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 12 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p14 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 14 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 12 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p12 endpoint_20_47_w12
private theorem endpoint_20_47_w14 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 14 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p16 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 16 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 14 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p14 endpoint_20_47_w14
private theorem endpoint_20_47_w16 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 16 2 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p18 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 18 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 16 2 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p16 endpoint_20_47_w16
private theorem endpoint_20_47_w18 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 18 1 164038093425263165 = some 164038093425263165 := by decide +kernel
private theorem endpoint_20_47_p19 : receiptWindow endpoint_20_47_flag endpoint_20_47_sources 0 19 164038093425263165 = some 164038093425263165 :=
  join_receipt_window endpoint_20_47_flag endpoint_20_47_sources 0 18 1 164038093425263165 164038093425263165 164038093425263165 endpoint_20_47_p18 endpoint_20_47_w18
def endpoint_20_47 : CertifiedEndpoint :=
  ⟨⟨20, 47, 1563⟩, 164038093425263165, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_47_flag endpoint_20_47_sources 19 164038093425263165 164038093425263165 rfl endpoint_20_47_base endpoint_20_47_p19) (by decide)⟩
private def endpoint_20_48_flag : Flag := ⟨20, 48, 1502⟩
private def endpoint_20_48_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_48_base : receiptBase endpoint_20_48_flag endpoint_20_48_sources = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_w0 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_w2 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 2 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p4 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 4 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 2 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_w0 endpoint_20_48_w2
private theorem endpoint_20_48_w4 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 4 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p6 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 6 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 4 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p4 endpoint_20_48_w4
private theorem endpoint_20_48_w6 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 6 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p8 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 8 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 6 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p6 endpoint_20_48_w6
private theorem endpoint_20_48_w8 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 8 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p10 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 10 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 8 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p8 endpoint_20_48_w8
private theorem endpoint_20_48_w10 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 10 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p12 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 12 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 10 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p10 endpoint_20_48_w10
private theorem endpoint_20_48_w12 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 12 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p14 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 14 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 12 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p12 endpoint_20_48_w12
private theorem endpoint_20_48_w14 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 14 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p16 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 16 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 14 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p14 endpoint_20_48_w14
private theorem endpoint_20_48_w16 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 16 2 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p18 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 18 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 16 2 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p16 endpoint_20_48_w16
private theorem endpoint_20_48_w18 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 18 1 160632781454963196 = some 160632781454963196 := by decide +kernel
private theorem endpoint_20_48_p19 : receiptWindow endpoint_20_48_flag endpoint_20_48_sources 0 19 160632781454963196 = some 160632781454963196 :=
  join_receipt_window endpoint_20_48_flag endpoint_20_48_sources 0 18 1 160632781454963196 160632781454963196 160632781454963196 endpoint_20_48_p18 endpoint_20_48_w18
def endpoint_20_48 : CertifiedEndpoint :=
  ⟨⟨20, 48, 1502⟩, 160632781454963196, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_48_flag endpoint_20_48_sources 19 160632781454963196 160632781454963196 rfl endpoint_20_48_base endpoint_20_48_p19) (by decide)⟩
private def endpoint_20_49_flag : Flag := ⟨20, 49, 1439⟩
private def endpoint_20_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_49_base : receiptBase endpoint_20_49_flag endpoint_20_49_sources = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_w0 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_w2 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 2 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p4 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 4 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 2 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_w0 endpoint_20_49_w2
private theorem endpoint_20_49_w4 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 4 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p6 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 6 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 4 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p4 endpoint_20_49_w4
private theorem endpoint_20_49_w6 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 6 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p8 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 8 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 6 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p6 endpoint_20_49_w6
private theorem endpoint_20_49_w8 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 8 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p10 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 10 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 8 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p8 endpoint_20_49_w8
private theorem endpoint_20_49_w10 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 10 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p12 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 12 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 10 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p10 endpoint_20_49_w10
private theorem endpoint_20_49_w12 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 12 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p14 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 14 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 12 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p12 endpoint_20_49_w12
private theorem endpoint_20_49_w14 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 14 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p16 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 16 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 14 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p14 endpoint_20_49_w14
private theorem endpoint_20_49_w16 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 16 2 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p18 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 18 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 16 2 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p16 endpoint_20_49_w16
private theorem endpoint_20_49_w18 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 18 1 156779232197040137 = some 156779232197040137 := by decide +kernel
private theorem endpoint_20_49_p19 : receiptWindow endpoint_20_49_flag endpoint_20_49_sources 0 19 156779232197040137 = some 156779232197040137 :=
  join_receipt_window endpoint_20_49_flag endpoint_20_49_sources 0 18 1 156779232197040137 156779232197040137 156779232197040137 endpoint_20_49_p18 endpoint_20_49_w18
def endpoint_20_49 : CertifiedEndpoint :=
  ⟨⟨20, 49, 1439⟩, 156779232197040137, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_49_flag endpoint_20_49_sources 19 156779232197040137 156779232197040137 rfl endpoint_20_49_base endpoint_20_49_p19) (by decide)⟩
private def endpoint_20_50_flag : Flag := ⟨20, 50, 1376⟩
private def endpoint_20_50_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_20_50_base : receiptBase endpoint_20_50_flag endpoint_20_50_sources = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_w0 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_w2 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 2 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p4 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 4 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 2 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_w0 endpoint_20_50_w2
private theorem endpoint_20_50_w4 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 4 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p6 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 6 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 4 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p4 endpoint_20_50_w4
private theorem endpoint_20_50_w6 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 6 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p8 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 8 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 6 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p6 endpoint_20_50_w6
private theorem endpoint_20_50_w8 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 8 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p10 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 10 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 8 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p8 endpoint_20_50_w8
private theorem endpoint_20_50_w10 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 10 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p12 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 12 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 10 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p10 endpoint_20_50_w10
private theorem endpoint_20_50_w12 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 12 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p14 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 14 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 12 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p12 endpoint_20_50_w12
private theorem endpoint_20_50_w14 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 14 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p16 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 16 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 14 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p14 endpoint_20_50_w14
private theorem endpoint_20_50_w16 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 16 2 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p18 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 18 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 16 2 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p16 endpoint_20_50_w16
private theorem endpoint_20_50_w18 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 18 1 152684208225591104 = some 152684208225591104 := by decide +kernel
private theorem endpoint_20_50_p19 : receiptWindow endpoint_20_50_flag endpoint_20_50_sources 0 19 152684208225591104 = some 152684208225591104 :=
  join_receipt_window endpoint_20_50_flag endpoint_20_50_sources 0 18 1 152684208225591104 152684208225591104 152684208225591104 endpoint_20_50_p18 endpoint_20_50_w18
def endpoint_20_50 : CertifiedEndpoint :=
  ⟨⟨20, 50, 1376⟩, 152684208225591104, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_20_50_flag endpoint_20_50_sources 19 152684208225591104 152684208225591104 rfl endpoint_20_50_base endpoint_20_50_p19) (by decide)⟩
def endpoint_20_51 : CertifiedEndpoint :=
  ⟨⟨20, 51, 1312⟩, 261299597477014237, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_52 : CertifiedEndpoint :=
  ⟨⟨20, 52, 1246⟩, 253856514623015306, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_53 : CertifiedEndpoint :=
  ⟨⟨20, 53, 1179⟩, 245529986603627664, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_54 : CertifiedEndpoint :=
  ⟨⟨20, 54, 1111⟩, 236304911939887981, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_55 : CertifiedEndpoint :=
  ⟨⟨20, 55, 1042⟩, 226166189152832927, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_56 : CertifiedEndpoint :=
  ⟨⟨20, 56, 972⟩, 215098716763499172, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_57 : CertifiedEndpoint :=
  ⟨⟨20, 57, 900⟩, 202853311722957865, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_58 : CertifiedEndpoint :=
  ⟨⟨20, 58, 827⟩, 189638886469568977, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_59 : CertifiedEndpoint :=
  ⟨⟨20, 59, 753⟩, 175440339524369178, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock12 : List CertifiedEndpoint := [
  endpoint_18_47, endpoint_18_48, endpoint_18_49, endpoint_18_50, endpoint_18_51, endpoint_18_52, endpoint_18_53,
  endpoint_18_54, endpoint_18_55, endpoint_18_56, endpoint_18_57, endpoint_18_58, endpoint_18_59, endpoint_18_60,
  endpoint_18_61, endpoint_18_62, endpoint_18_63, endpoint_18_64, endpoint_18_65, endpoint_18_66, endpoint_18_67,
  endpoint_18_68, endpoint_18_69, endpoint_18_70, endpoint_18_71, endpoint_18_72, endpoint_18_73, endpoint_18_74,
  endpoint_18_75, endpoint_18_76, endpoint_19_19, endpoint_19_20, endpoint_19_21, endpoint_19_22, endpoint_19_23,
  endpoint_19_24, endpoint_19_25, endpoint_19_26, endpoint_19_27, endpoint_19_28, endpoint_19_29, endpoint_19_30,
  endpoint_19_31, endpoint_19_32, endpoint_19_33, endpoint_19_34, endpoint_19_35, endpoint_19_36, endpoint_19_37,
  endpoint_19_38, endpoint_19_39, endpoint_19_40, endpoint_19_41, endpoint_19_42, endpoint_19_43, endpoint_19_44,
  endpoint_19_45, endpoint_19_46, endpoint_19_47, endpoint_19_48, endpoint_19_49, endpoint_19_50, endpoint_19_51,
  endpoint_19_52, endpoint_19_53, endpoint_19_54, endpoint_19_55, endpoint_19_56, endpoint_19_57, endpoint_19_58,
  endpoint_19_59, endpoint_19_60, endpoint_19_61, endpoint_19_62, endpoint_19_63, endpoint_19_64, endpoint_19_65,
  endpoint_19_66, endpoint_19_67, endpoint_19_68, endpoint_19_69, endpoint_19_70, endpoint_19_71, endpoint_19_72,
  endpoint_20_20, endpoint_20_21, endpoint_20_22, endpoint_20_23, endpoint_20_24, endpoint_20_25, endpoint_20_26,
  endpoint_20_27, endpoint_20_28, endpoint_20_29, endpoint_20_30, endpoint_20_31, endpoint_20_32, endpoint_20_33,
  endpoint_20_34, endpoint_20_35, endpoint_20_36, endpoint_20_37, endpoint_20_38, endpoint_20_39, endpoint_20_40,
  endpoint_20_41, endpoint_20_42, endpoint_20_43, endpoint_20_44, endpoint_20_45, endpoint_20_46, endpoint_20_47,
  endpoint_20_48, endpoint_20_49, endpoint_20_50, endpoint_20_51, endpoint_20_52, endpoint_20_53, endpoint_20_54,
  endpoint_20_55, endpoint_20_56, endpoint_20_57, endpoint_20_58, endpoint_20_59
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
