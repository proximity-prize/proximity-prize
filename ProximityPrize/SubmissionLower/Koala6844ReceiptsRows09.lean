import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_13_32_flag : Flag := ⟨13, 32, 3628⟩
private def endpoint_13_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_32_base : receiptBase endpoint_13_32_flag endpoint_13_32_sources = some 187044651562241681 := by decide +kernel
private theorem endpoint_13_32_w0 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 2 187044651562241681 = some 187044651562241681 := by decide +kernel
private theorem endpoint_13_32_w2 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 2 2 187044651562241681 = some 187044651562241681 := by decide +kernel
private theorem endpoint_13_32_p4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 4 187044651562241681 = some 187044651562241681 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 2 2 187044651562241681 187044651562241681 187044651562241681 endpoint_13_32_w0 endpoint_13_32_w2
private theorem endpoint_13_32_w4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 4 2 187044651562241681 = some 187044651562241681 := by decide +kernel
private theorem endpoint_13_32_p6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 6 187044651562241681 = some 187044651562241681 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 4 2 187044651562241681 187044651562241681 187044651562241681 endpoint_13_32_p4 endpoint_13_32_w4
private theorem endpoint_13_32_w6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 6 2 187044651562241681 = some 187044651562241681 := by decide +kernel
private theorem endpoint_13_32_p8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 8 187044651562241681 = some 187044651562241681 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 6 2 187044651562241681 187044651562241681 187044651562241681 endpoint_13_32_p6 endpoint_13_32_w6
private theorem endpoint_13_32_w8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 8 2 187044651562241681 = some 187044651562241681 := by decide +kernel
private theorem endpoint_13_32_p10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 10 187044651562241681 = some 187044651562241681 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 8 2 187044651562241681 187044651562241681 187044651562241681 endpoint_13_32_p8 endpoint_13_32_w8
private theorem endpoint_13_32_w10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 10 2 187044651562241681 = some 187044651562241681 := by decide +kernel
private theorem endpoint_13_32_p12 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 12 187044651562241681 = some 187044651562241681 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 10 2 187044651562241681 187044651562241681 187044651562241681 endpoint_13_32_p10 endpoint_13_32_w10
def endpoint_13_32 : CertifiedEndpoint :=
  ⟨⟨13, 32, 3628⟩, 187044651562241681, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_32_flag endpoint_13_32_sources 12 187044651562241681 187044651562241681 rfl endpoint_13_32_base endpoint_13_32_p12) (by decide)⟩
private def endpoint_13_33_flag : Flag := ⟨13, 33, 3603⟩
private def endpoint_13_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_33_base : receiptBase endpoint_13_33_flag endpoint_13_33_sources = some 190585743742074545 := by decide +kernel
private theorem endpoint_13_33_w0 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 2 190585743742074545 = some 190585743742074545 := by decide +kernel
private theorem endpoint_13_33_w2 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 2 2 190585743742074545 = some 190585743742074545 := by decide +kernel
private theorem endpoint_13_33_p4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 4 190585743742074545 = some 190585743742074545 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 2 2 190585743742074545 190585743742074545 190585743742074545 endpoint_13_33_w0 endpoint_13_33_w2
private theorem endpoint_13_33_w4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 4 2 190585743742074545 = some 190585743742074545 := by decide +kernel
private theorem endpoint_13_33_p6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 6 190585743742074545 = some 190585743742074545 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 4 2 190585743742074545 190585743742074545 190585743742074545 endpoint_13_33_p4 endpoint_13_33_w4
private theorem endpoint_13_33_w6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 6 2 190585743742074545 = some 190585743742074545 := by decide +kernel
private theorem endpoint_13_33_p8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 8 190585743742074545 = some 190585743742074545 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 6 2 190585743742074545 190585743742074545 190585743742074545 endpoint_13_33_p6 endpoint_13_33_w6
private theorem endpoint_13_33_w8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 8 2 190585743742074545 = some 190585743742074545 := by decide +kernel
private theorem endpoint_13_33_p10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 10 190585743742074545 = some 190585743742074545 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 8 2 190585743742074545 190585743742074545 190585743742074545 endpoint_13_33_p8 endpoint_13_33_w8
private theorem endpoint_13_33_w10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 10 2 190585743742074545 = some 190585743742074545 := by decide +kernel
private theorem endpoint_13_33_p12 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 12 190585743742074545 = some 190585743742074545 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 10 2 190585743742074545 190585743742074545 190585743742074545 endpoint_13_33_p10 endpoint_13_33_w10
def endpoint_13_33 : CertifiedEndpoint :=
  ⟨⟨13, 33, 3603⟩, 190585743742074545, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_33_flag endpoint_13_33_sources 12 190585743742074545 190585743742074545 rfl endpoint_13_33_base endpoint_13_33_p12) (by decide)⟩
private def endpoint_13_34_flag : Flag := ⟨13, 34, 3578⟩
private def endpoint_13_34_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_34_base : receiptBase endpoint_13_34_flag endpoint_13_34_sources = some 194060228075563416 := by decide +kernel
private theorem endpoint_13_34_w0 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 2 194060228075563416 = some 194060228075563416 := by decide +kernel
private theorem endpoint_13_34_w2 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 2 2 194060228075563416 = some 194060228075563416 := by decide +kernel
private theorem endpoint_13_34_p4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 4 194060228075563416 = some 194060228075563416 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 2 2 194060228075563416 194060228075563416 194060228075563416 endpoint_13_34_w0 endpoint_13_34_w2
private theorem endpoint_13_34_w4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 4 2 194060228075563416 = some 194060228075563416 := by decide +kernel
private theorem endpoint_13_34_p6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 6 194060228075563416 = some 194060228075563416 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 4 2 194060228075563416 194060228075563416 194060228075563416 endpoint_13_34_p4 endpoint_13_34_w4
private theorem endpoint_13_34_w6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 6 2 194060228075563416 = some 194060228075563416 := by decide +kernel
private theorem endpoint_13_34_p8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 8 194060228075563416 = some 194060228075563416 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 6 2 194060228075563416 194060228075563416 194060228075563416 endpoint_13_34_p6 endpoint_13_34_w6
private theorem endpoint_13_34_w8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 8 2 194060228075563416 = some 194060228075563416 := by decide +kernel
private theorem endpoint_13_34_p10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 10 194060228075563416 = some 194060228075563416 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 8 2 194060228075563416 194060228075563416 194060228075563416 endpoint_13_34_p8 endpoint_13_34_w8
private theorem endpoint_13_34_w10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 10 2 194060228075563416 = some 194060228075563416 := by decide +kernel
private theorem endpoint_13_34_p12 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 12 194060228075563416 = some 194060228075563416 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 10 2 194060228075563416 194060228075563416 194060228075563416 endpoint_13_34_p10 endpoint_13_34_w10
def endpoint_13_34 : CertifiedEndpoint :=
  ⟨⟨13, 34, 3578⟩, 194060228075563416, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_34_flag endpoint_13_34_sources 12 194060228075563416 194060228075563416 rfl endpoint_13_34_base endpoint_13_34_p12) (by decide)⟩
private def endpoint_13_35_flag : Flag := ⟨13, 35, 3552⟩
private def endpoint_13_35_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_35_base : receiptBase endpoint_13_35_flag endpoint_13_35_sources = some 198001037132890137 := by decide +kernel
private theorem endpoint_13_35_w0 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 2 198001037132890137 = some 198001037132890137 := by decide +kernel
private theorem endpoint_13_35_w2 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 2 2 198001037132890137 = some 198001037132890137 := by decide +kernel
private theorem endpoint_13_35_p4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 4 198001037132890137 = some 198001037132890137 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 2 2 198001037132890137 198001037132890137 198001037132890137 endpoint_13_35_w0 endpoint_13_35_w2
private theorem endpoint_13_35_w4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 4 2 198001037132890137 = some 198001037132890137 := by decide +kernel
private theorem endpoint_13_35_p6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 6 198001037132890137 = some 198001037132890137 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 4 2 198001037132890137 198001037132890137 198001037132890137 endpoint_13_35_p4 endpoint_13_35_w4
private theorem endpoint_13_35_w6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 6 2 198001037132890137 = some 198001037132890137 := by decide +kernel
private theorem endpoint_13_35_p8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 8 198001037132890137 = some 198001037132890137 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 6 2 198001037132890137 198001037132890137 198001037132890137 endpoint_13_35_p6 endpoint_13_35_w6
private theorem endpoint_13_35_w8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 8 2 198001037132890137 = some 198001037132890137 := by decide +kernel
private theorem endpoint_13_35_p10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 10 198001037132890137 = some 198001037132890137 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 8 2 198001037132890137 198001037132890137 198001037132890137 endpoint_13_35_p8 endpoint_13_35_w8
private theorem endpoint_13_35_w10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 10 2 198001037132890137 = some 198001037132890137 := by decide +kernel
private theorem endpoint_13_35_p12 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 12 198001037132890137 = some 198001037132890137 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 10 2 198001037132890137 198001037132890137 198001037132890137 endpoint_13_35_p10 endpoint_13_35_w10
def endpoint_13_35 : CertifiedEndpoint :=
  ⟨⟨13, 35, 3552⟩, 198001037132890137, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_35_flag endpoint_13_35_sources 12 198001037132890137 198001037132890137 rfl endpoint_13_35_base endpoint_13_35_p12) (by decide)⟩
private def endpoint_13_36_flag : Flag := ⟨13, 36, 3526⟩
private def endpoint_13_36_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_36_base : receiptBase endpoint_13_36_flag endpoint_13_36_sources = some 201198060158190402 := by decide +kernel
private theorem endpoint_13_36_w0 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 2 201198060158190402 = some 201198060158190402 := by decide +kernel
private theorem endpoint_13_36_w2 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 2 2 201198060158190402 = some 201198060158190402 := by decide +kernel
private theorem endpoint_13_36_p4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 4 201198060158190402 = some 201198060158190402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 2 2 201198060158190402 201198060158190402 201198060158190402 endpoint_13_36_w0 endpoint_13_36_w2
private theorem endpoint_13_36_w4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 4 2 201198060158190402 = some 201198060158190402 := by decide +kernel
private theorem endpoint_13_36_p6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 6 201198060158190402 = some 201198060158190402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 4 2 201198060158190402 201198060158190402 201198060158190402 endpoint_13_36_p4 endpoint_13_36_w4
private theorem endpoint_13_36_w6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 6 2 201198060158190402 = some 201198060158190402 := by decide +kernel
private theorem endpoint_13_36_p8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 8 201198060158190402 = some 201198060158190402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 6 2 201198060158190402 201198060158190402 201198060158190402 endpoint_13_36_p6 endpoint_13_36_w6
private theorem endpoint_13_36_w8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 8 2 201198060158190402 = some 201198060158190402 := by decide +kernel
private theorem endpoint_13_36_p10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 10 201198060158190402 = some 201198060158190402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 8 2 201198060158190402 201198060158190402 201198060158190402 endpoint_13_36_p8 endpoint_13_36_w8
private theorem endpoint_13_36_w10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 10 2 201198060158190402 = some 201198060158190402 := by decide +kernel
private theorem endpoint_13_36_p12 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 12 201198060158190402 = some 201198060158190402 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 10 2 201198060158190402 201198060158190402 201198060158190402 endpoint_13_36_p10 endpoint_13_36_w10
def endpoint_13_36 : CertifiedEndpoint :=
  ⟨⟨13, 36, 3526⟩, 201198060158190402, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_36_flag endpoint_13_36_sources 12 201198060158190402 201198060158190402 rfl endpoint_13_36_base endpoint_13_36_p12) (by decide)⟩
private def endpoint_13_37_flag : Flag := ⟨13, 37, 3499⟩
private def endpoint_13_37_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_37_base : receiptBase endpoint_13_37_flag endpoint_13_37_sources = some 204269462001108837 := by decide +kernel
private theorem endpoint_13_37_w0 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 2 204269462001108837 = some 204269462001108837 := by decide +kernel
private theorem endpoint_13_37_w2 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 2 2 204269462001108837 = some 204269462001108837 := by decide +kernel
private theorem endpoint_13_37_p4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 4 204269462001108837 = some 204269462001108837 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 2 2 204269462001108837 204269462001108837 204269462001108837 endpoint_13_37_w0 endpoint_13_37_w2
private theorem endpoint_13_37_w4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 4 2 204269462001108837 = some 204269462001108837 := by decide +kernel
private theorem endpoint_13_37_p6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 6 204269462001108837 = some 204269462001108837 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 4 2 204269462001108837 204269462001108837 204269462001108837 endpoint_13_37_p4 endpoint_13_37_w4
private theorem endpoint_13_37_w6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 6 2 204269462001108837 = some 204269462001108837 := by decide +kernel
private theorem endpoint_13_37_p8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 8 204269462001108837 = some 204269462001108837 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 6 2 204269462001108837 204269462001108837 204269462001108837 endpoint_13_37_p6 endpoint_13_37_w6
private theorem endpoint_13_37_w8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 8 2 204269462001108837 = some 204269462001108837 := by decide +kernel
private theorem endpoint_13_37_p10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 10 204269462001108837 = some 204269462001108837 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 8 2 204269462001108837 204269462001108837 204269462001108837 endpoint_13_37_p8 endpoint_13_37_w8
private theorem endpoint_13_37_w10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 10 2 204269462001108837 = some 204269462001108837 := by decide +kernel
private theorem endpoint_13_37_p12 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 12 204269462001108837 = some 204269462001108837 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 10 2 204269462001108837 204269462001108837 204269462001108837 endpoint_13_37_p10 endpoint_13_37_w10
def endpoint_13_37 : CertifiedEndpoint :=
  ⟨⟨13, 37, 3499⟩, 204269462001108837, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_37_flag endpoint_13_37_sources 12 204269462001108837 204269462001108837 rfl endpoint_13_37_base endpoint_13_37_p12) (by decide)⟩
private def endpoint_13_38_flag : Flag := ⟨13, 38, 3472⟩
private def endpoint_13_38_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_38_base : receiptBase endpoint_13_38_flag endpoint_13_38_sources = some 207270167633837025 := by decide +kernel
private theorem endpoint_13_38_w0 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 2 207270167633837025 = some 207270167633837025 := by decide +kernel
private theorem endpoint_13_38_w2 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 2 2 207270167633837025 = some 207270167633837025 := by decide +kernel
private theorem endpoint_13_38_p4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 4 207270167633837025 = some 207270167633837025 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 2 2 207270167633837025 207270167633837025 207270167633837025 endpoint_13_38_w0 endpoint_13_38_w2
private theorem endpoint_13_38_w4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 4 2 207270167633837025 = some 207270167633837025 := by decide +kernel
private theorem endpoint_13_38_p6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 6 207270167633837025 = some 207270167633837025 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 4 2 207270167633837025 207270167633837025 207270167633837025 endpoint_13_38_p4 endpoint_13_38_w4
private theorem endpoint_13_38_w6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 6 2 207270167633837025 = some 207270167633837025 := by decide +kernel
private theorem endpoint_13_38_p8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 8 207270167633837025 = some 207270167633837025 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 6 2 207270167633837025 207270167633837025 207270167633837025 endpoint_13_38_p6 endpoint_13_38_w6
private theorem endpoint_13_38_w8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 8 2 207270167633837025 = some 207270167633837025 := by decide +kernel
private theorem endpoint_13_38_p10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 10 207270167633837025 = some 207270167633837025 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 8 2 207270167633837025 207270167633837025 207270167633837025 endpoint_13_38_p8 endpoint_13_38_w8
private theorem endpoint_13_38_w10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 10 2 207270167633837025 = some 207270167633837025 := by decide +kernel
private theorem endpoint_13_38_p12 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 12 207270167633837025 = some 207270167633837025 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 10 2 207270167633837025 207270167633837025 207270167633837025 endpoint_13_38_p10 endpoint_13_38_w10
def endpoint_13_38 : CertifiedEndpoint :=
  ⟨⟨13, 38, 3472⟩, 207270167633837025, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_38_flag endpoint_13_38_sources 12 207270167633837025 207270167633837025 rfl endpoint_13_38_base endpoint_13_38_p12) (by decide)⟩
private def endpoint_13_39_flag : Flag := ⟨13, 39, 3444⟩
private def endpoint_13_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_39_base : receiptBase endpoint_13_39_flag endpoint_13_39_sources = some 210140110541624091 := by decide +kernel
private theorem endpoint_13_39_w0 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 2 210140110541624091 = some 210140110541624091 := by decide +kernel
private theorem endpoint_13_39_w2 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 2 2 210140110541624091 = some 210140110541624091 := by decide +kernel
private theorem endpoint_13_39_p4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 4 210140110541624091 = some 210140110541624091 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 2 2 210140110541624091 210140110541624091 210140110541624091 endpoint_13_39_w0 endpoint_13_39_w2
private theorem endpoint_13_39_w4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 4 2 210140110541624091 = some 210140110541624091 := by decide +kernel
private theorem endpoint_13_39_p6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 6 210140110541624091 = some 210140110541624091 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 4 2 210140110541624091 210140110541624091 210140110541624091 endpoint_13_39_p4 endpoint_13_39_w4
private theorem endpoint_13_39_w6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 6 2 210140110541624091 = some 210140110541624091 := by decide +kernel
private theorem endpoint_13_39_p8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 8 210140110541624091 = some 210140110541624091 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 6 2 210140110541624091 210140110541624091 210140110541624091 endpoint_13_39_p6 endpoint_13_39_w6
private theorem endpoint_13_39_w8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 8 2 210140110541624091 = some 210140110541624091 := by decide +kernel
private theorem endpoint_13_39_p10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 10 210140110541624091 = some 210140110541624091 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 8 2 210140110541624091 210140110541624091 210140110541624091 endpoint_13_39_p8 endpoint_13_39_w8
private theorem endpoint_13_39_w10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 10 2 210140110541624091 = some 210140110541624091 := by decide +kernel
private theorem endpoint_13_39_p12 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 12 210140110541624091 = some 210140110541624091 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 10 2 210140110541624091 210140110541624091 210140110541624091 endpoint_13_39_p10 endpoint_13_39_w10
def endpoint_13_39 : CertifiedEndpoint :=
  ⟨⟨13, 39, 3444⟩, 210140110541624091, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_39_flag endpoint_13_39_sources 12 210140110541624091 210140110541624091 rfl endpoint_13_39_base endpoint_13_39_p12) (by decide)⟩
private def endpoint_13_40_flag : Flag := ⟨13, 40, 3416⟩
private def endpoint_13_40_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_40_base : receiptBase endpoint_13_40_flag endpoint_13_40_sources = some 213346970522435279 := by decide +kernel
private theorem endpoint_13_40_w0 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 2 213346970522435279 = some 213346970522435279 := by decide +kernel
private theorem endpoint_13_40_w2 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 2 2 213346970522435279 = some 213346970522435279 := by decide +kernel
private theorem endpoint_13_40_p4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 4 213346970522435279 = some 213346970522435279 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 2 2 213346970522435279 213346970522435279 213346970522435279 endpoint_13_40_w0 endpoint_13_40_w2
private theorem endpoint_13_40_w4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 4 2 213346970522435279 = some 213346970522435279 := by decide +kernel
private theorem endpoint_13_40_p6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 6 213346970522435279 = some 213346970522435279 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 4 2 213346970522435279 213346970522435279 213346970522435279 endpoint_13_40_p4 endpoint_13_40_w4
private theorem endpoint_13_40_w6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 6 2 213346970522435279 = some 213346970522435279 := by decide +kernel
private theorem endpoint_13_40_p8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 8 213346970522435279 = some 213346970522435279 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 6 2 213346970522435279 213346970522435279 213346970522435279 endpoint_13_40_p6 endpoint_13_40_w6
private theorem endpoint_13_40_w8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 8 2 213346970522435279 = some 213346970522435279 := by decide +kernel
private theorem endpoint_13_40_p10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 10 213346970522435279 = some 213346970522435279 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 8 2 213346970522435279 213346970522435279 213346970522435279 endpoint_13_40_p8 endpoint_13_40_w8
private theorem endpoint_13_40_w10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 10 2 213346970522435279 = some 213346970522435279 := by decide +kernel
private theorem endpoint_13_40_p12 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 12 213346970522435279 = some 213346970522435279 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 10 2 213346970522435279 213346970522435279 213346970522435279 endpoint_13_40_p10 endpoint_13_40_w10
def endpoint_13_40 : CertifiedEndpoint :=
  ⟨⟨13, 40, 3416⟩, 213346970522435279, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_40_flag endpoint_13_40_sources 12 213346970522435279 213346970522435279 rfl endpoint_13_40_base endpoint_13_40_p12) (by decide)⟩
private def endpoint_13_41_flag : Flag := ⟨13, 41, 3388⟩
private def endpoint_13_41_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_41_base : receiptBase endpoint_13_41_flag endpoint_13_41_sources = some 216081917416525018 := by decide +kernel
private theorem endpoint_13_41_w0 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 2 216081917416525018 = some 216081917416525018 := by decide +kernel
private theorem endpoint_13_41_w2 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 2 2 216081917416525018 = some 216081917416525018 := by decide +kernel
private theorem endpoint_13_41_p4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 4 216081917416525018 = some 216081917416525018 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 2 2 216081917416525018 216081917416525018 216081917416525018 endpoint_13_41_w0 endpoint_13_41_w2
private theorem endpoint_13_41_w4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 4 2 216081917416525018 = some 216081917416525018 := by decide +kernel
private theorem endpoint_13_41_p6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 6 216081917416525018 = some 216081917416525018 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 4 2 216081917416525018 216081917416525018 216081917416525018 endpoint_13_41_p4 endpoint_13_41_w4
private theorem endpoint_13_41_w6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 6 2 216081917416525018 = some 216081917416525018 := by decide +kernel
private theorem endpoint_13_41_p8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 8 216081917416525018 = some 216081917416525018 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 6 2 216081917416525018 216081917416525018 216081917416525018 endpoint_13_41_p6 endpoint_13_41_w6
private theorem endpoint_13_41_w8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 8 2 216081917416525018 = some 216081917416525018 := by decide +kernel
private theorem endpoint_13_41_p10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 10 216081917416525018 = some 216081917416525018 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 8 2 216081917416525018 216081917416525018 216081917416525018 endpoint_13_41_p8 endpoint_13_41_w8
private theorem endpoint_13_41_w10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 10 2 216081917416525018 = some 216081917416525018 := by decide +kernel
private theorem endpoint_13_41_p12 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 12 216081917416525018 = some 216081917416525018 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 10 2 216081917416525018 216081917416525018 216081917416525018 endpoint_13_41_p10 endpoint_13_41_w10
def endpoint_13_41 : CertifiedEndpoint :=
  ⟨⟨13, 41, 3388⟩, 216081917416525018, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_41_flag endpoint_13_41_sources 12 216081917416525018 216081917416525018 rfl endpoint_13_41_base endpoint_13_41_p12) (by decide)⟩
private def endpoint_13_42_flag : Flag := ⟨13, 42, 3359⟩
private def endpoint_13_42_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_42_base : receiptBase endpoint_13_42_flag endpoint_13_42_sources = some 218679283126521635 := by decide +kernel
private theorem endpoint_13_42_w0 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 2 218679283126521635 = some 218679283126521635 := by decide +kernel
private theorem endpoint_13_42_w2 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 2 2 218679283126521635 = some 218679283126521635 := by decide +kernel
private theorem endpoint_13_42_p4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 4 218679283126521635 = some 218679283126521635 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 2 2 218679283126521635 218679283126521635 218679283126521635 endpoint_13_42_w0 endpoint_13_42_w2
private theorem endpoint_13_42_w4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 4 2 218679283126521635 = some 218679283126521635 := by decide +kernel
private theorem endpoint_13_42_p6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 6 218679283126521635 = some 218679283126521635 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 4 2 218679283126521635 218679283126521635 218679283126521635 endpoint_13_42_p4 endpoint_13_42_w4
private theorem endpoint_13_42_w6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 6 2 218679283126521635 = some 218679283126521635 := by decide +kernel
private theorem endpoint_13_42_p8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 8 218679283126521635 = some 218679283126521635 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 6 2 218679283126521635 218679283126521635 218679283126521635 endpoint_13_42_p6 endpoint_13_42_w6
private theorem endpoint_13_42_w8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 8 2 218679283126521635 = some 218679283126521635 := by decide +kernel
private theorem endpoint_13_42_p10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 10 218679283126521635 = some 218679283126521635 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 8 2 218679283126521635 218679283126521635 218679283126521635 endpoint_13_42_p8 endpoint_13_42_w8
private theorem endpoint_13_42_w10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 10 2 218679283126521635 = some 218679283126521635 := by decide +kernel
private theorem endpoint_13_42_p12 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 12 218679283126521635 = some 218679283126521635 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 10 2 218679283126521635 218679283126521635 218679283126521635 endpoint_13_42_p10 endpoint_13_42_w10
def endpoint_13_42 : CertifiedEndpoint :=
  ⟨⟨13, 42, 3359⟩, 218679283126521635, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_42_flag endpoint_13_42_sources 12 218679283126521635 218679283126521635 rfl endpoint_13_42_base endpoint_13_42_p12) (by decide)⟩
private def endpoint_13_43_flag : Flag := ⟨13, 43, 3329⟩
private def endpoint_13_43_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_43_base : receiptBase endpoint_13_43_flag endpoint_13_43_sources = some 221135197994412131 := by decide +kernel
private theorem endpoint_13_43_w0 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 2 221135197994412131 = some 221135197994412131 := by decide +kernel
private theorem endpoint_13_43_w2 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 2 2 221135197994412131 = some 221135197994412131 := by decide +kernel
private theorem endpoint_13_43_p4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 4 221135197994412131 = some 221135197994412131 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 2 2 221135197994412131 221135197994412131 221135197994412131 endpoint_13_43_w0 endpoint_13_43_w2
private theorem endpoint_13_43_w4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 4 2 221135197994412131 = some 221135197994412131 := by decide +kernel
private theorem endpoint_13_43_p6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 6 221135197994412131 = some 221135197994412131 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 4 2 221135197994412131 221135197994412131 221135197994412131 endpoint_13_43_p4 endpoint_13_43_w4
private theorem endpoint_13_43_w6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 6 2 221135197994412131 = some 221135197994412131 := by decide +kernel
private theorem endpoint_13_43_p8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 8 221135197994412131 = some 221135197994412131 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 6 2 221135197994412131 221135197994412131 221135197994412131 endpoint_13_43_p6 endpoint_13_43_w6
private theorem endpoint_13_43_w8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 8 2 221135197994412131 = some 221135197994412131 := by decide +kernel
private theorem endpoint_13_43_p10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 10 221135197994412131 = some 221135197994412131 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 8 2 221135197994412131 221135197994412131 221135197994412131 endpoint_13_43_p8 endpoint_13_43_w8
private theorem endpoint_13_43_w10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 10 2 221135197994412131 = some 221135197994412131 := by decide +kernel
private theorem endpoint_13_43_p12 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 12 221135197994412131 = some 221135197994412131 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 10 2 221135197994412131 221135197994412131 221135197994412131 endpoint_13_43_p10 endpoint_13_43_w10
def endpoint_13_43 : CertifiedEndpoint :=
  ⟨⟨13, 43, 3329⟩, 221135197994412131, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_43_flag endpoint_13_43_sources 12 221135197994412131 221135197994412131 rfl endpoint_13_43_base endpoint_13_43_p12) (by decide)⟩
private def endpoint_13_44_flag : Flag := ⟨13, 44, 3299⟩
private def endpoint_13_44_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_44_base : receiptBase endpoint_13_44_flag endpoint_13_44_sources = some 223512425316433312 := by decide +kernel
private theorem endpoint_13_44_w0 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 2 223512425316433312 = some 226091321451309166 := by decide +kernel
private theorem endpoint_13_44_w2 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 2 2 226091321451309166 = some 226091321451309166 := by decide +kernel
private theorem endpoint_13_44_p4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 4 223512425316433312 = some 226091321451309166 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 2 2 223512425316433312 226091321451309166 226091321451309166 endpoint_13_44_w0 endpoint_13_44_w2
private theorem endpoint_13_44_w4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 4 2 226091321451309166 = some 226091321451309166 := by decide +kernel
private theorem endpoint_13_44_p6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 6 223512425316433312 = some 226091321451309166 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 4 2 223512425316433312 226091321451309166 226091321451309166 endpoint_13_44_p4 endpoint_13_44_w4
private theorem endpoint_13_44_w6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 6 2 226091321451309166 = some 226091321451309166 := by decide +kernel
private theorem endpoint_13_44_p8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 8 223512425316433312 = some 226091321451309166 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 6 2 223512425316433312 226091321451309166 226091321451309166 endpoint_13_44_p6 endpoint_13_44_w6
private theorem endpoint_13_44_w8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 8 2 226091321451309166 = some 226091321451309166 := by decide +kernel
private theorem endpoint_13_44_p10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 10 223512425316433312 = some 226091321451309166 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 8 2 223512425316433312 226091321451309166 226091321451309166 endpoint_13_44_p8 endpoint_13_44_w8
private theorem endpoint_13_44_w10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 10 2 226091321451309166 = some 226091321451309166 := by decide +kernel
private theorem endpoint_13_44_p12 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 12 223512425316433312 = some 226091321451309166 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 10 2 223512425316433312 226091321451309166 226091321451309166 endpoint_13_44_p10 endpoint_13_44_w10
def endpoint_13_44 : CertifiedEndpoint :=
  ⟨⟨13, 44, 3299⟩, 226091321451309166, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_44_flag endpoint_13_44_sources 12 223512425316433312 226091321451309166 rfl endpoint_13_44_base endpoint_13_44_p12) (by decide)⟩
private def endpoint_13_45_flag : Flag := ⟨13, 45, 3268⟩
private def endpoint_13_45_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_45_base : receiptBase endpoint_13_45_flag endpoint_13_45_sources = some 225743042252331040 := by decide +kernel
private theorem endpoint_13_45_w0 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 2 225743042252331040 = some 231104025497871884 := by decide +kernel
private theorem endpoint_13_45_w2 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 2 2 231104025497871884 = some 231104025497871884 := by decide +kernel
private theorem endpoint_13_45_p4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 4 225743042252331040 = some 231104025497871884 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 2 2 225743042252331040 231104025497871884 231104025497871884 endpoint_13_45_w0 endpoint_13_45_w2
private theorem endpoint_13_45_w4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 4 2 231104025497871884 = some 231104025497871884 := by decide +kernel
private theorem endpoint_13_45_p6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 6 225743042252331040 = some 231104025497871884 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 4 2 225743042252331040 231104025497871884 231104025497871884 endpoint_13_45_p4 endpoint_13_45_w4
private theorem endpoint_13_45_w6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 6 2 231104025497871884 = some 231104025497871884 := by decide +kernel
private theorem endpoint_13_45_p8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 8 225743042252331040 = some 231104025497871884 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 6 2 225743042252331040 231104025497871884 231104025497871884 endpoint_13_45_p6 endpoint_13_45_w6
private theorem endpoint_13_45_w8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 8 2 231104025497871884 = some 231104025497871884 := by decide +kernel
private theorem endpoint_13_45_p10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 10 225743042252331040 = some 231104025497871884 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 8 2 225743042252331040 231104025497871884 231104025497871884 endpoint_13_45_p8 endpoint_13_45_w8
private theorem endpoint_13_45_w10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 10 2 231104025497871884 = some 231104025497871884 := by decide +kernel
private theorem endpoint_13_45_p12 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 12 225743042252331040 = some 231104025497871884 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 10 2 225743042252331040 231104025497871884 231104025497871884 endpoint_13_45_p10 endpoint_13_45_w10
def endpoint_13_45 : CertifiedEndpoint :=
  ⟨⟨13, 45, 3268⟩, 231104025497871884, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_45_flag endpoint_13_45_sources 12 225743042252331040 231104025497871884 rfl endpoint_13_45_base endpoint_13_45_p12) (by decide)⟩
private def endpoint_13_46_flag : Flag := ⟨13, 46, 3237⟩
private def endpoint_13_46_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_46_base : receiptBase endpoint_13_46_flag endpoint_13_46_sources = some 227892391870350788 := by decide +kernel
private theorem endpoint_13_46_w0 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 2 227892391870350788 = some 236053574747274842 := by decide +kernel
private theorem endpoint_13_46_w2 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 2 2 236053574747274842 = some 236053574747274842 := by decide +kernel
private theorem endpoint_13_46_p4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 4 227892391870350788 = some 236053574747274842 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 2 2 227892391870350788 236053574747274842 236053574747274842 endpoint_13_46_w0 endpoint_13_46_w2
private theorem endpoint_13_46_w4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 4 2 236053574747274842 = some 236053574747274842 := by decide +kernel
private theorem endpoint_13_46_p6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 6 227892391870350788 = some 236053574747274842 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 4 2 227892391870350788 236053574747274842 236053574747274842 endpoint_13_46_p4 endpoint_13_46_w4
private theorem endpoint_13_46_w6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 6 2 236053574747274842 = some 236053574747274842 := by decide +kernel
private theorem endpoint_13_46_p8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 8 227892391870350788 = some 236053574747274842 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 6 2 227892391870350788 236053574747274842 236053574747274842 endpoint_13_46_p6 endpoint_13_46_w6
private theorem endpoint_13_46_w8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 8 2 236053574747274842 = some 236053574747274842 := by decide +kernel
private theorem endpoint_13_46_p10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 10 227892391870350788 = some 236053574747274842 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 8 2 227892391870350788 236053574747274842 236053574747274842 endpoint_13_46_p8 endpoint_13_46_w8
private theorem endpoint_13_46_w10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 10 2 236053574747274842 = some 236053574747274842 := by decide +kernel
private theorem endpoint_13_46_p12 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 12 227892391870350788 = some 236053574747274842 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 10 2 227892391870350788 236053574747274842 236053574747274842 endpoint_13_46_p10 endpoint_13_46_w10
def endpoint_13_46 : CertifiedEndpoint :=
  ⟨⟨13, 46, 3237⟩, 236053574747274842, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_46_flag endpoint_13_46_sources 12 227892391870350788 236053574747274842 rfl endpoint_13_46_base endpoint_13_46_p12) (by decide)⟩
private def endpoint_13_47_flag : Flag := ⟨13, 47, 3204⟩
private def endpoint_13_47_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_47_base : receiptBase endpoint_13_47_flag endpoint_13_47_sources = some 229819468945966952 := by decide +kernel
private theorem endpoint_13_47_w0 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 2 229819468945966952 = some 240863722977264414 := by decide +kernel
private theorem endpoint_13_47_w2 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 2 2 240863722977264414 = some 240863722977264414 := by decide +kernel
private theorem endpoint_13_47_p4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 4 229819468945966952 = some 240863722977264414 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 2 2 229819468945966952 240863722977264414 240863722977264414 endpoint_13_47_w0 endpoint_13_47_w2
private theorem endpoint_13_47_w4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 4 2 240863722977264414 = some 240863722977264414 := by decide +kernel
private theorem endpoint_13_47_p6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 6 229819468945966952 = some 240863722977264414 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 4 2 229819468945966952 240863722977264414 240863722977264414 endpoint_13_47_p4 endpoint_13_47_w4
private theorem endpoint_13_47_w6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 6 2 240863722977264414 = some 240863722977264414 := by decide +kernel
private theorem endpoint_13_47_p8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 8 229819468945966952 = some 240863722977264414 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 6 2 229819468945966952 240863722977264414 240863722977264414 endpoint_13_47_p6 endpoint_13_47_w6
private theorem endpoint_13_47_w8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 8 2 240863722977264414 = some 240863722977264414 := by decide +kernel
private theorem endpoint_13_47_p10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 10 229819468945966952 = some 240863722977264414 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 8 2 229819468945966952 240863722977264414 240863722977264414 endpoint_13_47_p8 endpoint_13_47_w8
private theorem endpoint_13_47_w10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 10 2 240863722977264414 = some 240863722977264414 := by decide +kernel
private theorem endpoint_13_47_p12 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 12 229819468945966952 = some 240863722977264414 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 10 2 229819468945966952 240863722977264414 240863722977264414 endpoint_13_47_p10 endpoint_13_47_w10
def endpoint_13_47 : CertifiedEndpoint :=
  ⟨⟨13, 47, 3204⟩, 240863722977264414, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_47_flag endpoint_13_47_sources 12 229819468945966952 240863722977264414 rfl endpoint_13_47_base endpoint_13_47_p12) (by decide)⟩
private def endpoint_13_48_flag : Flag := ⟨13, 48, 3171⟩
private def endpoint_13_48_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_48_base : receiptBase endpoint_13_48_flag endpoint_13_48_sources = some 232404490655063780 := by decide +kernel
private theorem endpoint_13_48_w0 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 2 232404490655063780 = some 241688900574269222 := by decide +kernel
private theorem endpoint_13_48_w2 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 2 2 241688900574269222 = some 241688900574269222 := by decide +kernel
private theorem endpoint_13_48_p4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 4 232404490655063780 = some 241688900574269222 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 2 2 232404490655063780 241688900574269222 241688900574269222 endpoint_13_48_w0 endpoint_13_48_w2
private theorem endpoint_13_48_w4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 4 2 241688900574269222 = some 241688900574269222 := by decide +kernel
private theorem endpoint_13_48_p6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 6 232404490655063780 = some 241688900574269222 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 4 2 232404490655063780 241688900574269222 241688900574269222 endpoint_13_48_p4 endpoint_13_48_w4
private theorem endpoint_13_48_w6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 6 2 241688900574269222 = some 241688900574269222 := by decide +kernel
private theorem endpoint_13_48_p8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 8 232404490655063780 = some 241688900574269222 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 6 2 232404490655063780 241688900574269222 241688900574269222 endpoint_13_48_p6 endpoint_13_48_w6
private theorem endpoint_13_48_w8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 8 2 241688900574269222 = some 241688900574269222 := by decide +kernel
private theorem endpoint_13_48_p10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 10 232404490655063780 = some 241688900574269222 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 8 2 232404490655063780 241688900574269222 241688900574269222 endpoint_13_48_p8 endpoint_13_48_w8
private theorem endpoint_13_48_w10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 10 2 241688900574269222 = some 241688900574269222 := by decide +kernel
private theorem endpoint_13_48_p12 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 12 232404490655063780 = some 241688900574269222 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 10 2 232404490655063780 241688900574269222 241688900574269222 endpoint_13_48_p10 endpoint_13_48_w10
def endpoint_13_48 : CertifiedEndpoint :=
  ⟨⟨13, 48, 3171⟩, 241688900574269222, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_48_flag endpoint_13_48_sources 12 232404490655063780 241688900574269222 rfl endpoint_13_48_base endpoint_13_48_p12) (by decide)⟩
private def endpoint_13_49_flag : Flag := ⟨13, 49, 3138⟩
private def endpoint_13_49_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_49_base : receiptBase endpoint_13_49_flag endpoint_13_49_sources = some 234169388240037773 := by decide +kernel
private theorem endpoint_13_49_w0 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 2 234169388240037773 = some 246268901496360482 := by decide +kernel
private theorem endpoint_13_49_w2 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 2 2 246268901496360482 = some 246268901496360482 := by decide +kernel
private theorem endpoint_13_49_p4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 4 234169388240037773 = some 246268901496360482 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 2 2 234169388240037773 246268901496360482 246268901496360482 endpoint_13_49_w0 endpoint_13_49_w2
private theorem endpoint_13_49_w4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 4 2 246268901496360482 = some 246268901496360482 := by decide +kernel
private theorem endpoint_13_49_p6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 6 234169388240037773 = some 246268901496360482 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 4 2 234169388240037773 246268901496360482 246268901496360482 endpoint_13_49_p4 endpoint_13_49_w4
private theorem endpoint_13_49_w6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 6 2 246268901496360482 = some 246268901496360482 := by decide +kernel
private theorem endpoint_13_49_p8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 8 234169388240037773 = some 246268901496360482 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 6 2 234169388240037773 246268901496360482 246268901496360482 endpoint_13_49_p6 endpoint_13_49_w6
private theorem endpoint_13_49_w8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 8 2 246268901496360482 = some 246268901496360482 := by decide +kernel
private theorem endpoint_13_49_p10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 10 234169388240037773 = some 246268901496360482 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 8 2 234169388240037773 246268901496360482 246268901496360482 endpoint_13_49_p8 endpoint_13_49_w8
private theorem endpoint_13_49_w10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 10 2 246268901496360482 = some 246268901496360482 := by decide +kernel
private theorem endpoint_13_49_p12 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 12 234169388240037773 = some 246268901496360482 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 10 2 234169388240037773 246268901496360482 246268901496360482 endpoint_13_49_p10 endpoint_13_49_w10
def endpoint_13_49 : CertifiedEndpoint :=
  ⟨⟨13, 49, 3138⟩, 246268901496360482, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_49_flag endpoint_13_49_sources 12 234169388240037773 246268901496360482 rfl endpoint_13_49_base endpoint_13_49_p12) (by decide)⟩
private def endpoint_13_50_flag : Flag := ⟨13, 50, 3103⟩
private def endpoint_13_50_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_50_base : receiptBase endpoint_13_50_flag endpoint_13_50_sources = some 235697851864485068 := by decide +kernel
private theorem endpoint_13_50_w0 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 2 235697851864485068 = some 250699794527187926 := by decide +kernel
private theorem endpoint_13_50_w2 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 2 2 250699794527187926 = some 250699794527187926 := by decide +kernel
private theorem endpoint_13_50_p4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 4 235697851864485068 = some 250699794527187926 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 2 2 235697851864485068 250699794527187926 250699794527187926 endpoint_13_50_w0 endpoint_13_50_w2
private theorem endpoint_13_50_w4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 4 2 250699794527187926 = some 250699794527187926 := by decide +kernel
private theorem endpoint_13_50_p6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 6 235697851864485068 = some 250699794527187926 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 4 2 235697851864485068 250699794527187926 250699794527187926 endpoint_13_50_p4 endpoint_13_50_w4
private theorem endpoint_13_50_w6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 6 2 250699794527187926 = some 250699794527187926 := by decide +kernel
private theorem endpoint_13_50_p8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 8 235697851864485068 = some 250699794527187926 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 6 2 235697851864485068 250699794527187926 250699794527187926 endpoint_13_50_p6 endpoint_13_50_w6
private theorem endpoint_13_50_w8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 8 2 250699794527187926 = some 250699794527187926 := by decide +kernel
private theorem endpoint_13_50_p10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 10 235697851864485068 = some 250699794527187926 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 8 2 235697851864485068 250699794527187926 250699794527187926 endpoint_13_50_p8 endpoint_13_50_w8
private theorem endpoint_13_50_w10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 10 2 250699794527187926 = some 250699794527187926 := by decide +kernel
private theorem endpoint_13_50_p12 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 12 235697851864485068 = some 250699794527187926 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 10 2 235697851864485068 250699794527187926 250699794527187926 endpoint_13_50_p10 endpoint_13_50_w10
def endpoint_13_50 : CertifiedEndpoint :=
  ⟨⟨13, 50, 3103⟩, 250699794527187926, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_50_flag endpoint_13_50_sources 12 235697851864485068 250699794527187926 rfl endpoint_13_50_base endpoint_13_50_p12) (by decide)⟩
private def endpoint_13_51_flag : Flag := ⟨13, 51, 3068⟩
private def endpoint_13_51_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_51_base : receiptBase endpoint_13_51_flag endpoint_13_51_sources = some 239063762987384177 := by decide +kernel
private theorem endpoint_13_51_w0 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 2 239063762987384177 = some 247786633345947045 := by decide +kernel
private theorem endpoint_13_51_w2 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 2 2 247786633345947045 = some 247786633345947045 := by decide +kernel
private theorem endpoint_13_51_p4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 4 239063762987384177 = some 247786633345947045 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 2 2 239063762987384177 247786633345947045 247786633345947045 endpoint_13_51_w0 endpoint_13_51_w2
private theorem endpoint_13_51_w4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 4 2 247786633345947045 = some 247786633345947045 := by decide +kernel
private theorem endpoint_13_51_p6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 6 239063762987384177 = some 247786633345947045 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 4 2 239063762987384177 247786633345947045 247786633345947045 endpoint_13_51_p4 endpoint_13_51_w4
private theorem endpoint_13_51_w6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 6 2 247786633345947045 = some 247786633345947045 := by decide +kernel
private theorem endpoint_13_51_p8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 8 239063762987384177 = some 247786633345947045 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 6 2 239063762987384177 247786633345947045 247786633345947045 endpoint_13_51_p6 endpoint_13_51_w6
private theorem endpoint_13_51_w8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 8 2 247786633345947045 = some 247786633345947045 := by decide +kernel
private theorem endpoint_13_51_p10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 10 239063762987384177 = some 247786633345947045 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 8 2 239063762987384177 247786633345947045 247786633345947045 endpoint_13_51_p8 endpoint_13_51_w8
private theorem endpoint_13_51_w10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 10 2 247786633345947045 = some 247786633345947045 := by decide +kernel
private theorem endpoint_13_51_p12 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 12 239063762987384177 = some 247786633345947045 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 10 2 239063762987384177 247786633345947045 247786633345947045 endpoint_13_51_p10 endpoint_13_51_w10
def endpoint_13_51 : CertifiedEndpoint :=
  ⟨⟨13, 51, 3068⟩, 247786633345947045, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_51_flag endpoint_13_51_sources 12 239063762987384177 247786633345947045 rfl endpoint_13_51_base endpoint_13_51_p12) (by decide)⟩
private def endpoint_13_52_flag : Flag := ⟨13, 52, 3031⟩
private def endpoint_13_52_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_52_base : receiptBase endpoint_13_52_flag endpoint_13_52_sources = some 240199774809086168 := by decide +kernel
private theorem endpoint_13_52_w0 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 2 240199774809086168 = some 251823607819719992 := by decide +kernel
private theorem endpoint_13_52_w2 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 2 2 251823607819719992 = some 251823607819719992 := by decide +kernel
private theorem endpoint_13_52_p4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 4 240199774809086168 = some 251823607819719992 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 2 2 240199774809086168 251823607819719992 251823607819719992 endpoint_13_52_w0 endpoint_13_52_w2
private theorem endpoint_13_52_w4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 4 2 251823607819719992 = some 251823607819719992 := by decide +kernel
private theorem endpoint_13_52_p6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 6 240199774809086168 = some 251823607819719992 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 4 2 240199774809086168 251823607819719992 251823607819719992 endpoint_13_52_p4 endpoint_13_52_w4
private theorem endpoint_13_52_w6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 6 2 251823607819719992 = some 251823607819719992 := by decide +kernel
private theorem endpoint_13_52_p8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 8 240199774809086168 = some 251823607819719992 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 6 2 240199774809086168 251823607819719992 251823607819719992 endpoint_13_52_p6 endpoint_13_52_w6
private theorem endpoint_13_52_w8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 8 2 251823607819719992 = some 251823607819719992 := by decide +kernel
private theorem endpoint_13_52_p10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 10 240199774809086168 = some 251823607819719992 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 8 2 240199774809086168 251823607819719992 251823607819719992 endpoint_13_52_p8 endpoint_13_52_w8
private theorem endpoint_13_52_w10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 10 2 251823607819719992 = some 251823607819719992 := by decide +kernel
private theorem endpoint_13_52_p12 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 12 240199774809086168 = some 251823607819719992 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 10 2 240199774809086168 251823607819719992 251823607819719992 endpoint_13_52_p10 endpoint_13_52_w10
def endpoint_13_52 : CertifiedEndpoint :=
  ⟨⟨13, 52, 3031⟩, 251823607819719992, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_52_flag endpoint_13_52_sources 12 240199774809086168 251823607819719992 rfl endpoint_13_52_base endpoint_13_52_p12) (by decide)⟩
private def endpoint_13_53_flag : Flag := ⟨13, 53, 2994⟩
private def endpoint_13_53_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_53_base : receiptBase endpoint_13_53_flag endpoint_13_53_sources = some 241238708051858918 := by decide +kernel
private theorem endpoint_13_53_w0 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 2 241238708051858918 = some 255785779250112663 := by decide +kernel
private theorem endpoint_13_53_w2 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 2 2 255785779250112663 = some 255785779250112663 := by decide +kernel
private theorem endpoint_13_53_p4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 4 241238708051858918 = some 255785779250112663 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 2 2 241238708051858918 255785779250112663 255785779250112663 endpoint_13_53_w0 endpoint_13_53_w2
private theorem endpoint_13_53_w4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 4 2 255785779250112663 = some 255785779250112663 := by decide +kernel
private theorem endpoint_13_53_p6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 6 241238708051858918 = some 255785779250112663 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 4 2 241238708051858918 255785779250112663 255785779250112663 endpoint_13_53_p4 endpoint_13_53_w4
private theorem endpoint_13_53_w6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 6 2 255785779250112663 = some 255785779250112663 := by decide +kernel
private theorem endpoint_13_53_p8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 8 241238708051858918 = some 255785779250112663 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 6 2 241238708051858918 255785779250112663 255785779250112663 endpoint_13_53_p6 endpoint_13_53_w6
private theorem endpoint_13_53_w8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 8 2 255785779250112663 = some 255785779250112663 := by decide +kernel
private theorem endpoint_13_53_p10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 10 241238708051858918 = some 255785779250112663 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 8 2 241238708051858918 255785779250112663 255785779250112663 endpoint_13_53_p8 endpoint_13_53_w8
private theorem endpoint_13_53_w10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 10 2 255785779250112663 = some 255785779250112663 := by decide +kernel
private theorem endpoint_13_53_p12 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 12 241238708051858918 = some 255785779250112663 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 10 2 241238708051858918 255785779250112663 255785779250112663 endpoint_13_53_p10 endpoint_13_53_w10
def endpoint_13_53 : CertifiedEndpoint :=
  ⟨⟨13, 53, 2994⟩, 255785779250112663, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_53_flag endpoint_13_53_sources 12 241238708051858918 255785779250112663 rfl endpoint_13_53_base endpoint_13_53_p12) (by decide)⟩
private def endpoint_13_54_flag : Flag := ⟨13, 54, 2955⟩
private def endpoint_13_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_54_base : receiptBase endpoint_13_54_flag endpoint_13_54_sources = some 242019192765268461 := by decide +kernel
private theorem endpoint_13_54_w0 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 2 242019192765268461 = some 259583311794280830 := by decide +kernel
private theorem endpoint_13_54_w2 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 2 2 259583311794280830 = some 259583311794280830 := by decide +kernel
private theorem endpoint_13_54_p4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 4 242019192765268461 = some 259583311794280830 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 2 2 242019192765268461 259583311794280830 259583311794280830 endpoint_13_54_w0 endpoint_13_54_w2
private theorem endpoint_13_54_w4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 4 2 259583311794280830 = some 259583311794280830 := by decide +kernel
private theorem endpoint_13_54_p6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 6 242019192765268461 = some 259583311794280830 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 4 2 242019192765268461 259583311794280830 259583311794280830 endpoint_13_54_p4 endpoint_13_54_w4
private theorem endpoint_13_54_w6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 6 2 259583311794280830 = some 259583311794280830 := by decide +kernel
private theorem endpoint_13_54_p8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 8 242019192765268461 = some 259583311794280830 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 6 2 242019192765268461 259583311794280830 259583311794280830 endpoint_13_54_p6 endpoint_13_54_w6
private theorem endpoint_13_54_w8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 8 2 259583311794280830 = some 259583311794280830 := by decide +kernel
private theorem endpoint_13_54_p10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 10 242019192765268461 = some 259583311794280830 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 8 2 242019192765268461 259583311794280830 259583311794280830 endpoint_13_54_p8 endpoint_13_54_w8
private theorem endpoint_13_54_w10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 10 2 259583311794280830 = some 259583311794280830 := by decide +kernel
private theorem endpoint_13_54_p12 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 12 242019192765268461 = some 259583311794280830 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 10 2 242019192765268461 259583311794280830 259583311794280830 endpoint_13_54_p10 endpoint_13_54_w10
def endpoint_13_54 : CertifiedEndpoint :=
  ⟨⟨13, 54, 2955⟩, 259583311794280830, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_54_flag endpoint_13_54_sources 12 242019192765268461 259583311794280830 rfl endpoint_13_54_base endpoint_13_54_p12) (by decide)⟩
private def endpoint_13_55_flag : Flag := ⟨13, 55, 2915⟩
private def endpoint_13_55_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_55_base : receiptBase endpoint_13_55_flag endpoint_13_55_sources = some 243497008769697082 := by decide +kernel
private theorem endpoint_13_55_w0 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 2 243497008769697082 = some 255414270663107530 := by decide +kernel
private theorem endpoint_13_55_w2 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 2 2 255414270663107530 = some 255414270663107530 := by decide +kernel
private theorem endpoint_13_55_p4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 4 243497008769697082 = some 255414270663107530 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 2 2 243497008769697082 255414270663107530 255414270663107530 endpoint_13_55_w0 endpoint_13_55_w2
private theorem endpoint_13_55_w4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 4 2 255414270663107530 = some 255414270663107530 := by decide +kernel
private theorem endpoint_13_55_p6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 6 243497008769697082 = some 255414270663107530 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 4 2 243497008769697082 255414270663107530 255414270663107530 endpoint_13_55_p4 endpoint_13_55_w4
private theorem endpoint_13_55_w6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 6 2 255414270663107530 = some 255414270663107530 := by decide +kernel
private theorem endpoint_13_55_p8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 8 243497008769697082 = some 255414270663107530 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 6 2 243497008769697082 255414270663107530 255414270663107530 endpoint_13_55_p6 endpoint_13_55_w6
private theorem endpoint_13_55_w8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 8 2 255414270663107530 = some 255414270663107530 := by decide +kernel
private theorem endpoint_13_55_p10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 10 243497008769697082 = some 255414270663107530 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 8 2 243497008769697082 255414270663107530 255414270663107530 endpoint_13_55_p8 endpoint_13_55_w8
private theorem endpoint_13_55_w10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 10 2 255414270663107530 = some 255414270663107530 := by decide +kernel
private theorem endpoint_13_55_p12 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 12 243497008769697082 = some 255414270663107530 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 10 2 243497008769697082 255414270663107530 255414270663107530 endpoint_13_55_p10 endpoint_13_55_w10
def endpoint_13_55 : CertifiedEndpoint :=
  ⟨⟨13, 55, 2915⟩, 255414270663107530, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_55_flag endpoint_13_55_sources 12 243497008769697082 255414270663107530 rfl endpoint_13_55_base endpoint_13_55_p12) (by decide)⟩
private def endpoint_13_56_flag : Flag := ⟨13, 56, 2874⟩
private def endpoint_13_56_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_56_base : receiptBase endpoint_13_56_flag endpoint_13_56_sources = some 243910344751354184 := by decide +kernel
private theorem endpoint_13_56_w0 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 2 243910344751354184 = some 258795618975097176 := by decide +kernel
private theorem endpoint_13_56_w2 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 2 2 258795618975097176 = some 258795618975097176 := by decide +kernel
private theorem endpoint_13_56_p4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 4 243910344751354184 = some 258795618975097176 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 2 2 243910344751354184 258795618975097176 258795618975097176 endpoint_13_56_w0 endpoint_13_56_w2
private theorem endpoint_13_56_w4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 4 2 258795618975097176 = some 258795618975097176 := by decide +kernel
private theorem endpoint_13_56_p6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 6 243910344751354184 = some 258795618975097176 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 4 2 243910344751354184 258795618975097176 258795618975097176 endpoint_13_56_p4 endpoint_13_56_w4
private theorem endpoint_13_56_w6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 6 2 258795618975097176 = some 258795618975097176 := by decide +kernel
private theorem endpoint_13_56_p8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 8 243910344751354184 = some 258795618975097176 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 6 2 243910344751354184 258795618975097176 258795618975097176 endpoint_13_56_p6 endpoint_13_56_w6
private theorem endpoint_13_56_w8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 8 2 258795618975097176 = some 258795618975097176 := by decide +kernel
private theorem endpoint_13_56_p10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 10 243910344751354184 = some 258795618975097176 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 8 2 243910344751354184 258795618975097176 258795618975097176 endpoint_13_56_p8 endpoint_13_56_w8
private theorem endpoint_13_56_w10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 10 2 258795618975097176 = some 258795618975097176 := by decide +kernel
private theorem endpoint_13_56_p12 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 12 243910344751354184 = some 258795618975097176 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 10 2 243910344751354184 258795618975097176 258795618975097176 endpoint_13_56_p10 endpoint_13_56_w10
def endpoint_13_56 : CertifiedEndpoint :=
  ⟨⟨13, 56, 2874⟩, 258795618975097176, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_56_flag endpoint_13_56_sources 12 243910344751354184 258795618975097176 rfl endpoint_13_56_base endpoint_13_56_p12) (by decide)⟩
private def endpoint_13_57_flag : Flag := ⟨13, 57, 2832⟩
private def endpoint_13_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_57_base : receiptBase endpoint_13_57_flag endpoint_13_57_sources = some 248040371661117692 := by decide +kernel
private theorem endpoint_13_57_w0 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 2 248040371661117692 = some 248040371661117692 := by decide +kernel
private theorem endpoint_13_57_w2 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 2 2 248040371661117692 = some 248040371661117692 := by decide +kernel
private theorem endpoint_13_57_p4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 4 248040371661117692 = some 248040371661117692 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 2 2 248040371661117692 248040371661117692 248040371661117692 endpoint_13_57_w0 endpoint_13_57_w2
private theorem endpoint_13_57_w4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 4 2 248040371661117692 = some 248040371661117692 := by decide +kernel
private theorem endpoint_13_57_p6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 6 248040371661117692 = some 248040371661117692 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 4 2 248040371661117692 248040371661117692 248040371661117692 endpoint_13_57_p4 endpoint_13_57_w4
private theorem endpoint_13_57_w6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 6 2 248040371661117692 = some 248040371661117692 := by decide +kernel
private theorem endpoint_13_57_p8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 8 248040371661117692 = some 248040371661117692 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 6 2 248040371661117692 248040371661117692 248040371661117692 endpoint_13_57_p6 endpoint_13_57_w6
private theorem endpoint_13_57_w8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 8 2 248040371661117692 = some 248040371661117692 := by decide +kernel
private theorem endpoint_13_57_p10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 10 248040371661117692 = some 248040371661117692 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 8 2 248040371661117692 248040371661117692 248040371661117692 endpoint_13_57_p8 endpoint_13_57_w8
private theorem endpoint_13_57_w10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 10 2 248040371661117692 = some 248040371661117692 := by decide +kernel
private theorem endpoint_13_57_p12 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 12 248040371661117692 = some 248040371661117692 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 10 2 248040371661117692 248040371661117692 248040371661117692 endpoint_13_57_p10 endpoint_13_57_w10
def endpoint_13_57 : CertifiedEndpoint :=
  ⟨⟨13, 57, 2832⟩, 248040371661117692, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_57_flag endpoint_13_57_sources 12 248040371661117692 248040371661117692 rfl endpoint_13_57_base endpoint_13_57_p12) (by decide)⟩
private def endpoint_13_58_flag : Flag := ⟨13, 58, 2788⟩
private def endpoint_13_58_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_13_58_base : receiptBase endpoint_13_58_flag endpoint_13_58_sources = some 245020338257355459 := by decide +kernel
private theorem endpoint_13_58_w0 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 2 245020338257355459 = some 259118726886760268 := by decide +kernel
private theorem endpoint_13_58_w2 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 2 2 259118726886760268 = some 259118726886760268 := by decide +kernel
private theorem endpoint_13_58_p4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 4 245020338257355459 = some 259118726886760268 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 2 2 245020338257355459 259118726886760268 259118726886760268 endpoint_13_58_w0 endpoint_13_58_w2
private theorem endpoint_13_58_w4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 4 2 259118726886760268 = some 259118726886760268 := by decide +kernel
private theorem endpoint_13_58_p6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 6 245020338257355459 = some 259118726886760268 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 4 2 245020338257355459 259118726886760268 259118726886760268 endpoint_13_58_p4 endpoint_13_58_w4
private theorem endpoint_13_58_w6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 6 2 259118726886760268 = some 259118726886760268 := by decide +kernel
private theorem endpoint_13_58_p8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 8 245020338257355459 = some 259118726886760268 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 6 2 245020338257355459 259118726886760268 259118726886760268 endpoint_13_58_p6 endpoint_13_58_w6
private theorem endpoint_13_58_w8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 8 2 259118726886760268 = some 259118726886760268 := by decide +kernel
private theorem endpoint_13_58_p10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 10 245020338257355459 = some 259118726886760268 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 8 2 245020338257355459 259118726886760268 259118726886760268 endpoint_13_58_p8 endpoint_13_58_w8
private theorem endpoint_13_58_w10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 10 2 259118726886760268 = some 259118726886760268 := by decide +kernel
private theorem endpoint_13_58_p12 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 12 245020338257355459 = some 259118726886760268 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 10 2 245020338257355459 259118726886760268 259118726886760268 endpoint_13_58_p10 endpoint_13_58_w10
def endpoint_13_58 : CertifiedEndpoint :=
  ⟨⟨13, 58, 2788⟩, 259118726886760268, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_13_58_flag endpoint_13_58_sources 12 245020338257355459 259118726886760268 rfl endpoint_13_58_base endpoint_13_58_p12) (by decide)⟩
private def endpoint_13_59_flag : Flag := ⟨13, 59, 2742⟩
private def endpoint_13_59_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_59_base : receiptBase endpoint_13_59_flag endpoint_13_59_sources = some 247652507582703462 := by decide +kernel
private theorem endpoint_13_59_w0 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 2 247652507582703462 = some 248097400593105393 := by decide +kernel
private theorem endpoint_13_59_w2 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 2 2 248097400593105393 = some 248097400593105393 := by decide +kernel
private theorem endpoint_13_59_p4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 4 247652507582703462 = some 248097400593105393 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 2 2 247652507582703462 248097400593105393 248097400593105393 endpoint_13_59_w0 endpoint_13_59_w2
private theorem endpoint_13_59_w4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 4 2 248097400593105393 = some 248097400593105393 := by decide +kernel
private theorem endpoint_13_59_p6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 6 247652507582703462 = some 248097400593105393 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 4 2 247652507582703462 248097400593105393 248097400593105393 endpoint_13_59_p4 endpoint_13_59_w4
private theorem endpoint_13_59_w6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 6 2 248097400593105393 = some 248097400593105393 := by decide +kernel
private theorem endpoint_13_59_p8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 8 247652507582703462 = some 248097400593105393 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 6 2 247652507582703462 248097400593105393 248097400593105393 endpoint_13_59_p6 endpoint_13_59_w6
private theorem endpoint_13_59_w8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 8 2 248097400593105393 = some 248097400593105393 := by decide +kernel
private theorem endpoint_13_59_p10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 10 247652507582703462 = some 248097400593105393 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 8 2 247652507582703462 248097400593105393 248097400593105393 endpoint_13_59_p8 endpoint_13_59_w8
private theorem endpoint_13_59_w10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 10 2 248097400593105393 = some 248097400593105393 := by decide +kernel
private theorem endpoint_13_59_p12 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 12 247652507582703462 = some 248097400593105393 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 10 2 247652507582703462 248097400593105393 248097400593105393 endpoint_13_59_p10 endpoint_13_59_w10
def endpoint_13_59 : CertifiedEndpoint :=
  ⟨⟨13, 59, 2742⟩, 248097400593105393, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_59_flag endpoint_13_59_sources 12 247652507582703462 248097400593105393 rfl endpoint_13_59_base endpoint_13_59_p12) (by decide)⟩
private def endpoint_13_60_flag : Flag := ⟨13, 60, 2694⟩
private def endpoint_13_60_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_60_base : receiptBase endpoint_13_60_flag endpoint_13_60_sources = some 247004100219075669 := by decide +kernel
private theorem endpoint_13_60_w0 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 2 247004100219075669 = some 250400255380866776 := by decide +kernel
private theorem endpoint_13_60_w2 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 2 2 250400255380866776 = some 250400255380866776 := by decide +kernel
private theorem endpoint_13_60_p4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 4 247004100219075669 = some 250400255380866776 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 2 2 247004100219075669 250400255380866776 250400255380866776 endpoint_13_60_w0 endpoint_13_60_w2
private theorem endpoint_13_60_w4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 4 2 250400255380866776 = some 250400255380866776 := by decide +kernel
private theorem endpoint_13_60_p6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 6 247004100219075669 = some 250400255380866776 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 4 2 247004100219075669 250400255380866776 250400255380866776 endpoint_13_60_p4 endpoint_13_60_w4
private theorem endpoint_13_60_w6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 6 2 250400255380866776 = some 250400255380866776 := by decide +kernel
private theorem endpoint_13_60_p8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 8 247004100219075669 = some 250400255380866776 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 6 2 247004100219075669 250400255380866776 250400255380866776 endpoint_13_60_p6 endpoint_13_60_w6
private theorem endpoint_13_60_w8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 8 2 250400255380866776 = some 250400255380866776 := by decide +kernel
private theorem endpoint_13_60_p10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 10 247004100219075669 = some 250400255380866776 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 8 2 247004100219075669 250400255380866776 250400255380866776 endpoint_13_60_p8 endpoint_13_60_w8
private theorem endpoint_13_60_w10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 10 2 250400255380866776 = some 250400255380866776 := by decide +kernel
private theorem endpoint_13_60_p12 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 12 247004100219075669 = some 250400255380866776 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 10 2 247004100219075669 250400255380866776 250400255380866776 endpoint_13_60_p10 endpoint_13_60_w10
def endpoint_13_60 : CertifiedEndpoint :=
  ⟨⟨13, 60, 2694⟩, 250400255380866776, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_60_flag endpoint_13_60_sources 12 247004100219075669 250400255380866776 rfl endpoint_13_60_base endpoint_13_60_p12) (by decide)⟩
private def endpoint_13_61_flag : Flag := ⟨13, 61, 2645⟩
private def endpoint_13_61_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_13_61_base : receiptBase endpoint_13_61_flag endpoint_13_61_sources = some 245204284040324181 := by decide +kernel
private theorem endpoint_13_61_w0 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 2 245204284040324181 = some 259982617626483715 := by decide +kernel
private theorem endpoint_13_61_w2 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 2 2 259982617626483715 = some 259982617626483715 := by decide +kernel
private theorem endpoint_13_61_p4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 4 245204284040324181 = some 259982617626483715 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 2 2 245204284040324181 259982617626483715 259982617626483715 endpoint_13_61_w0 endpoint_13_61_w2
private theorem endpoint_13_61_w4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 4 2 259982617626483715 = some 259982617626483715 := by decide +kernel
private theorem endpoint_13_61_p6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 6 245204284040324181 = some 259982617626483715 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 4 2 245204284040324181 259982617626483715 259982617626483715 endpoint_13_61_p4 endpoint_13_61_w4
private theorem endpoint_13_61_w6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 6 2 259982617626483715 = some 259982617626483715 := by decide +kernel
private theorem endpoint_13_61_p8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 8 245204284040324181 = some 259982617626483715 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 6 2 245204284040324181 259982617626483715 259982617626483715 endpoint_13_61_p6 endpoint_13_61_w6
private theorem endpoint_13_61_w8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 8 2 259982617626483715 = some 259982617626483715 := by decide +kernel
private theorem endpoint_13_61_p10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 10 245204284040324181 = some 259982617626483715 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 8 2 245204284040324181 259982617626483715 259982617626483715 endpoint_13_61_p8 endpoint_13_61_w8
private theorem endpoint_13_61_w10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 10 2 259982617626483715 = some 259982617626483715 := by decide +kernel
private theorem endpoint_13_61_p12 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 12 245204284040324181 = some 259982617626483715 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 10 2 245204284040324181 259982617626483715 259982617626483715 endpoint_13_61_p10 endpoint_13_61_w10
def endpoint_13_61 : CertifiedEndpoint :=
  ⟨⟨13, 61, 2645⟩, 259982617626483715, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_13_61_flag endpoint_13_61_sources 12 245204284040324181 259982617626483715 rfl endpoint_13_61_base endpoint_13_61_p12) (by decide)⟩
private def endpoint_13_62_flag : Flag := ⟨13, 62, 2593⟩
private def endpoint_13_62_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_62_base : receiptBase endpoint_13_62_flag endpoint_13_62_sources = some 244851382065811072 := by decide +kernel
private theorem endpoint_13_62_w0 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 2 244851382065811072 = some 254454073377523586 := by decide +kernel
private theorem endpoint_13_62_w2 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 2 2 254454073377523586 = some 254454073377523586 := by decide +kernel
private theorem endpoint_13_62_p4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 4 244851382065811072 = some 254454073377523586 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 2 2 244851382065811072 254454073377523586 254454073377523586 endpoint_13_62_w0 endpoint_13_62_w2
private theorem endpoint_13_62_w4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 4 2 254454073377523586 = some 254454073377523586 := by decide +kernel
private theorem endpoint_13_62_p6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 6 244851382065811072 = some 254454073377523586 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 4 2 244851382065811072 254454073377523586 254454073377523586 endpoint_13_62_p4 endpoint_13_62_w4
private theorem endpoint_13_62_w6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 6 2 254454073377523586 = some 254454073377523586 := by decide +kernel
private theorem endpoint_13_62_p8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 8 244851382065811072 = some 254454073377523586 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 6 2 244851382065811072 254454073377523586 254454073377523586 endpoint_13_62_p6 endpoint_13_62_w6
private theorem endpoint_13_62_w8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 8 2 254454073377523586 = some 254454073377523586 := by decide +kernel
private theorem endpoint_13_62_p10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 10 244851382065811072 = some 254454073377523586 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 8 2 244851382065811072 254454073377523586 254454073377523586 endpoint_13_62_p8 endpoint_13_62_w8
private theorem endpoint_13_62_w10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 10 2 254454073377523586 = some 254454073377523586 := by decide +kernel
private theorem endpoint_13_62_p12 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 12 244851382065811072 = some 254454073377523586 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 10 2 244851382065811072 254454073377523586 254454073377523586 endpoint_13_62_p10 endpoint_13_62_w10
def endpoint_13_62 : CertifiedEndpoint :=
  ⟨⟨13, 62, 2593⟩, 254454073377523586, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_62_flag endpoint_13_62_sources 12 244851382065811072 254454073377523586 rfl endpoint_13_62_base endpoint_13_62_p12) (by decide)⟩
private def endpoint_13_63_flag : Flag := ⟨13, 63, 2540⟩
private def endpoint_13_63_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_63_base : receiptBase endpoint_13_63_flag endpoint_13_63_sources = some 243333677459579090 := by decide +kernel
private theorem endpoint_13_63_w0 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 2 243333677459579090 = some 256195329714568583 := by decide +kernel
private theorem endpoint_13_63_w2 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 2 2 256195329714568583 = some 256195329714568583 := by decide +kernel
private theorem endpoint_13_63_p4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 4 243333677459579090 = some 256195329714568583 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 2 2 243333677459579090 256195329714568583 256195329714568583 endpoint_13_63_w0 endpoint_13_63_w2
private theorem endpoint_13_63_w4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 4 2 256195329714568583 = some 256195329714568583 := by decide +kernel
private theorem endpoint_13_63_p6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 6 243333677459579090 = some 256195329714568583 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 4 2 243333677459579090 256195329714568583 256195329714568583 endpoint_13_63_p4 endpoint_13_63_w4
private theorem endpoint_13_63_w6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 6 2 256195329714568583 = some 256195329714568583 := by decide +kernel
private theorem endpoint_13_63_p8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 8 243333677459579090 = some 256195329714568583 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 6 2 243333677459579090 256195329714568583 256195329714568583 endpoint_13_63_p6 endpoint_13_63_w6
private theorem endpoint_13_63_w8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 8 2 256195329714568583 = some 256195329714568583 := by decide +kernel
private theorem endpoint_13_63_p10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 10 243333677459579090 = some 256195329714568583 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 8 2 243333677459579090 256195329714568583 256195329714568583 endpoint_13_63_p8 endpoint_13_63_w8
private theorem endpoint_13_63_w10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 10 2 256195329714568583 = some 256195329714568583 := by decide +kernel
private theorem endpoint_13_63_p12 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 12 243333677459579090 = some 256195329714568583 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 10 2 243333677459579090 256195329714568583 256195329714568583 endpoint_13_63_p10 endpoint_13_63_w10
def endpoint_13_63 : CertifiedEndpoint :=
  ⟨⟨13, 63, 2540⟩, 256195329714568583, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_63_flag endpoint_13_63_sources 12 243333677459579090 256195329714568583 rfl endpoint_13_63_base endpoint_13_63_p12) (by decide)⟩
private def endpoint_13_64_flag : Flag := ⟨13, 64, 2484⟩
private def endpoint_13_64_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_64_base : receiptBase endpoint_13_64_flag endpoint_13_64_sources = some 241384936707967989 := by decide +kernel
private theorem endpoint_13_64_w0 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 2 241384936707967989 = some 257666846638494296 := by decide +kernel
private theorem endpoint_13_64_w2 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 2 2 257666846638494296 = some 257666846638494296 := by decide +kernel
private theorem endpoint_13_64_p4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 4 241384936707967989 = some 257666846638494296 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 2 2 241384936707967989 257666846638494296 257666846638494296 endpoint_13_64_w0 endpoint_13_64_w2
private theorem endpoint_13_64_w4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 4 2 257666846638494296 = some 257666846638494296 := by decide +kernel
private theorem endpoint_13_64_p6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 6 241384936707967989 = some 257666846638494296 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 4 2 241384936707967989 257666846638494296 257666846638494296 endpoint_13_64_p4 endpoint_13_64_w4
private theorem endpoint_13_64_w6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 6 2 257666846638494296 = some 257666846638494296 := by decide +kernel
private theorem endpoint_13_64_p8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 8 241384936707967989 = some 257666846638494296 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 6 2 241384936707967989 257666846638494296 257666846638494296 endpoint_13_64_p6 endpoint_13_64_w6
private theorem endpoint_13_64_w8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 8 2 257666846638494296 = some 257666846638494296 := by decide +kernel
private theorem endpoint_13_64_p10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 10 241384936707967989 = some 257666846638494296 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 8 2 241384936707967989 257666846638494296 257666846638494296 endpoint_13_64_p8 endpoint_13_64_w8
private theorem endpoint_13_64_w10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 10 2 257666846638494296 = some 257666846638494296 := by decide +kernel
private theorem endpoint_13_64_p12 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 12 241384936707967989 = some 257666846638494296 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 10 2 241384936707967989 257666846638494296 257666846638494296 endpoint_13_64_p10 endpoint_13_64_w10
def endpoint_13_64 : CertifiedEndpoint :=
  ⟨⟨13, 64, 2484⟩, 257666846638494296, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_64_flag endpoint_13_64_sources 12 241384936707967989 257666846638494296 rfl endpoint_13_64_base endpoint_13_64_p12) (by decide)⟩
private def endpoint_13_65_flag : Flag := ⟨13, 65, 2426⟩
private def endpoint_13_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_65_base : receiptBase endpoint_13_65_flag endpoint_13_65_sources = some 244752434027141609 := by decide +kernel
private theorem endpoint_13_65_w0 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 2 244752434027141609 = some 245962775003323213 := by decide +kernel
private theorem endpoint_13_65_w2 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 2 2 245962775003323213 = some 245962775003323213 := by decide +kernel
private theorem endpoint_13_65_p4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 4 244752434027141609 = some 245962775003323213 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 2 2 244752434027141609 245962775003323213 245962775003323213 endpoint_13_65_w0 endpoint_13_65_w2
private theorem endpoint_13_65_w4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 4 2 245962775003323213 = some 245962775003323213 := by decide +kernel
private theorem endpoint_13_65_p6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 6 244752434027141609 = some 245962775003323213 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 4 2 244752434027141609 245962775003323213 245962775003323213 endpoint_13_65_p4 endpoint_13_65_w4
private theorem endpoint_13_65_w6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 6 2 245962775003323213 = some 245962775003323213 := by decide +kernel
private theorem endpoint_13_65_p8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 8 244752434027141609 = some 245962775003323213 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 6 2 244752434027141609 245962775003323213 245962775003323213 endpoint_13_65_p6 endpoint_13_65_w6
private theorem endpoint_13_65_w8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 8 2 245962775003323213 = some 245962775003323213 := by decide +kernel
private theorem endpoint_13_65_p10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 10 244752434027141609 = some 245962775003323213 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 8 2 244752434027141609 245962775003323213 245962775003323213 endpoint_13_65_p8 endpoint_13_65_w8
private theorem endpoint_13_65_w10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 10 2 245962775003323213 = some 245962775003323213 := by decide +kernel
private theorem endpoint_13_65_p12 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 12 244752434027141609 = some 245962775003323213 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 10 2 244752434027141609 245962775003323213 245962775003323213 endpoint_13_65_p10 endpoint_13_65_w10
def endpoint_13_65 : CertifiedEndpoint :=
  ⟨⟨13, 65, 2426⟩, 245962775003323213, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_65_flag endpoint_13_65_sources 12 244752434027141609 245962775003323213 rfl endpoint_13_65_base endpoint_13_65_p12) (by decide)⟩
private def endpoint_13_66_flag : Flag := ⟨13, 66, 2366⟩
private def endpoint_13_66_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_66_base : receiptBase endpoint_13_66_flag endpoint_13_66_sources = some 242076670490702881 := by decide +kernel
private theorem endpoint_13_66_w0 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 2 242076670490702881 = some 246758539065254788 := by decide +kernel
private theorem endpoint_13_66_w2 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 2 2 246758539065254788 = some 246758539065254788 := by decide +kernel
private theorem endpoint_13_66_p4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 4 242076670490702881 = some 246758539065254788 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 2 2 242076670490702881 246758539065254788 246758539065254788 endpoint_13_66_w0 endpoint_13_66_w2
private theorem endpoint_13_66_w4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 4 2 246758539065254788 = some 246758539065254788 := by decide +kernel
private theorem endpoint_13_66_p6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 6 242076670490702881 = some 246758539065254788 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 4 2 242076670490702881 246758539065254788 246758539065254788 endpoint_13_66_p4 endpoint_13_66_w4
private theorem endpoint_13_66_w6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 6 2 246758539065254788 = some 246758539065254788 := by decide +kernel
private theorem endpoint_13_66_p8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 8 242076670490702881 = some 246758539065254788 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 6 2 242076670490702881 246758539065254788 246758539065254788 endpoint_13_66_p6 endpoint_13_66_w6
private theorem endpoint_13_66_w8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 8 2 246758539065254788 = some 246758539065254788 := by decide +kernel
private theorem endpoint_13_66_p10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 10 242076670490702881 = some 246758539065254788 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 8 2 242076670490702881 246758539065254788 246758539065254788 endpoint_13_66_p8 endpoint_13_66_w8
private theorem endpoint_13_66_w10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 10 2 246758539065254788 = some 246758539065254788 := by decide +kernel
private theorem endpoint_13_66_p12 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 12 242076670490702881 = some 246758539065254788 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 10 2 242076670490702881 246758539065254788 246758539065254788 endpoint_13_66_p10 endpoint_13_66_w10
def endpoint_13_66 : CertifiedEndpoint :=
  ⟨⟨13, 66, 2366⟩, 246758539065254788, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_66_flag endpoint_13_66_sources 12 242076670490702881 246758539065254788 rfl endpoint_13_66_base endpoint_13_66_p12) (by decide)⟩
private def endpoint_13_67_flag : Flag := ⟨13, 67, 2303⟩
private def endpoint_13_67_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_67_base : receiptBase endpoint_13_67_flag endpoint_13_67_sources = some 238934856022979124 := by decide +kernel
private theorem endpoint_13_67_w0 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 2 238934856022979124 = some 247262237908811090 := by decide +kernel
private theorem endpoint_13_67_w2 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 2 2 247262237908811090 = some 247262237908811090 := by decide +kernel
private theorem endpoint_13_67_p4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 4 238934856022979124 = some 247262237908811090 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 2 2 238934856022979124 247262237908811090 247262237908811090 endpoint_13_67_w0 endpoint_13_67_w2
private theorem endpoint_13_67_w4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 4 2 247262237908811090 = some 247262237908811090 := by decide +kernel
private theorem endpoint_13_67_p6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 6 238934856022979124 = some 247262237908811090 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 4 2 238934856022979124 247262237908811090 247262237908811090 endpoint_13_67_p4 endpoint_13_67_w4
private theorem endpoint_13_67_w6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 6 2 247262237908811090 = some 247262237908811090 := by decide +kernel
private theorem endpoint_13_67_p8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 8 238934856022979124 = some 247262237908811090 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 6 2 238934856022979124 247262237908811090 247262237908811090 endpoint_13_67_p6 endpoint_13_67_w6
private theorem endpoint_13_67_w8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 8 2 247262237908811090 = some 247262237908811090 := by decide +kernel
private theorem endpoint_13_67_p10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 10 238934856022979124 = some 247262237908811090 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 8 2 238934856022979124 247262237908811090 247262237908811090 endpoint_13_67_p8 endpoint_13_67_w8
private theorem endpoint_13_67_w10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 10 2 247262237908811090 = some 247262237908811090 := by decide +kernel
private theorem endpoint_13_67_p12 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 12 238934856022979124 = some 247262237908811090 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 10 2 238934856022979124 247262237908811090 247262237908811090 endpoint_13_67_p10 endpoint_13_67_w10
def endpoint_13_67 : CertifiedEndpoint :=
  ⟨⟨13, 67, 2303⟩, 247262237908811090, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_67_flag endpoint_13_67_sources 12 238934856022979124 247262237908811090 rfl endpoint_13_67_base endpoint_13_67_p12) (by decide)⟩
private def endpoint_13_68_flag : Flag := ⟨13, 68, 2238⟩
private def endpoint_13_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_68_base : receiptBase endpoint_13_68_flag endpoint_13_68_sources = some 235417498350441458 := by decide +kernel
private theorem endpoint_13_68_w0 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 2 235417498350441458 = some 247523642891339448 := by decide +kernel
private theorem endpoint_13_68_w2 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 2 2 247523642891339448 = some 247523642891339448 := by decide +kernel
private theorem endpoint_13_68_p4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 4 235417498350441458 = some 247523642891339448 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 2 2 235417498350441458 247523642891339448 247523642891339448 endpoint_13_68_w0 endpoint_13_68_w2
private theorem endpoint_13_68_w4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 4 2 247523642891339448 = some 247523642891339448 := by decide +kernel
private theorem endpoint_13_68_p6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 6 235417498350441458 = some 247523642891339448 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 4 2 235417498350441458 247523642891339448 247523642891339448 endpoint_13_68_p4 endpoint_13_68_w4
private theorem endpoint_13_68_w6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 6 2 247523642891339448 = some 247523642891339448 := by decide +kernel
private theorem endpoint_13_68_p8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 8 235417498350441458 = some 247523642891339448 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 6 2 235417498350441458 247523642891339448 247523642891339448 endpoint_13_68_p6 endpoint_13_68_w6
private theorem endpoint_13_68_w8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 8 2 247523642891339448 = some 247523642891339448 := by decide +kernel
private theorem endpoint_13_68_p10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 10 235417498350441458 = some 247523642891339448 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 8 2 235417498350441458 247523642891339448 247523642891339448 endpoint_13_68_p8 endpoint_13_68_w8
private theorem endpoint_13_68_w10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 10 2 247523642891339448 = some 247523642891339448 := by decide +kernel
private theorem endpoint_13_68_p12 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 12 235417498350441458 = some 247523642891339448 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 10 2 235417498350441458 247523642891339448 247523642891339448 endpoint_13_68_p10 endpoint_13_68_w10
def endpoint_13_68 : CertifiedEndpoint :=
  ⟨⟨13, 68, 2238⟩, 247523642891339448, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_68_flag endpoint_13_68_sources 12 235417498350441458 247523642891339448 rfl endpoint_13_68_base endpoint_13_68_p12) (by decide)⟩
private def endpoint_13_69_flag : Flag := ⟨13, 69, 2171⟩
private def endpoint_13_69_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_13_69_base : receiptBase endpoint_13_69_flag endpoint_13_69_sources = some 232805624581297680 := by decide +kernel
private theorem endpoint_13_69_w0 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 2 232805624581297680 = some 234924099436281094 := by decide +kernel
private theorem endpoint_13_69_w2 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 2 2 234924099436281094 = some 234924099436281094 := by decide +kernel
private theorem endpoint_13_69_p4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 4 232805624581297680 = some 234924099436281094 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 2 2 232805624581297680 234924099436281094 234924099436281094 endpoint_13_69_w0 endpoint_13_69_w2
private theorem endpoint_13_69_w4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 4 2 234924099436281094 = some 234924099436281094 := by decide +kernel
private theorem endpoint_13_69_p6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 6 232805624581297680 = some 234924099436281094 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 4 2 232805624581297680 234924099436281094 234924099436281094 endpoint_13_69_p4 endpoint_13_69_w4
private theorem endpoint_13_69_w6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 6 2 234924099436281094 = some 234924099436281094 := by decide +kernel
private theorem endpoint_13_69_p8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 8 232805624581297680 = some 234924099436281094 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 6 2 232805624581297680 234924099436281094 234924099436281094 endpoint_13_69_p6 endpoint_13_69_w6
private theorem endpoint_13_69_w8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 8 2 234924099436281094 = some 234924099436281094 := by decide +kernel
private theorem endpoint_13_69_p10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 10 232805624581297680 = some 234924099436281094 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 8 2 232805624581297680 234924099436281094 234924099436281094 endpoint_13_69_p8 endpoint_13_69_w8
private theorem endpoint_13_69_w10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 10 2 234924099436281094 = some 234924099436281094 := by decide +kernel
private theorem endpoint_13_69_p12 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 12 232805624581297680 = some 234924099436281094 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 10 2 232805624581297680 234924099436281094 234924099436281094 endpoint_13_69_p10 endpoint_13_69_w10
def endpoint_13_69 : CertifiedEndpoint :=
  ⟨⟨13, 69, 2171⟩, 234924099436281094, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_13_69_flag endpoint_13_69_sources 12 232805624581297680 234924099436281094 rfl endpoint_13_69_base endpoint_13_69_p12) (by decide)⟩
private def endpoint_13_70_flag : Flag := ⟨13, 70, 2101⟩
private def endpoint_13_70_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_13_70_base : receiptBase endpoint_13_70_flag endpoint_13_70_sources = some 228403219153498450 := by decide +kernel
private theorem endpoint_13_70_w0 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 2 228403219153498450 = some 234418841951830786 := by decide +kernel
private theorem endpoint_13_70_w2 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 2 2 234418841951830786 = some 234418841951830786 := by decide +kernel
private theorem endpoint_13_70_p4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 4 228403219153498450 = some 234418841951830786 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 2 2 228403219153498450 234418841951830786 234418841951830786 endpoint_13_70_w0 endpoint_13_70_w2
private theorem endpoint_13_70_w4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 4 2 234418841951830786 = some 234418841951830786 := by decide +kernel
private theorem endpoint_13_70_p6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 6 228403219153498450 = some 234418841951830786 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 4 2 228403219153498450 234418841951830786 234418841951830786 endpoint_13_70_p4 endpoint_13_70_w4
private theorem endpoint_13_70_w6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 6 2 234418841951830786 = some 234418841951830786 := by decide +kernel
private theorem endpoint_13_70_p8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 8 228403219153498450 = some 234418841951830786 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 6 2 228403219153498450 234418841951830786 234418841951830786 endpoint_13_70_p6 endpoint_13_70_w6
private theorem endpoint_13_70_w8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 8 2 234418841951830786 = some 234418841951830786 := by decide +kernel
private theorem endpoint_13_70_p10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 10 228403219153498450 = some 234418841951830786 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 8 2 228403219153498450 234418841951830786 234418841951830786 endpoint_13_70_p8 endpoint_13_70_w8
private theorem endpoint_13_70_w10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 10 2 234418841951830786 = some 234418841951830786 := by decide +kernel
private theorem endpoint_13_70_p12 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 12 228403219153498450 = some 234418841951830786 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 10 2 228403219153498450 234418841951830786 234418841951830786 endpoint_13_70_p10 endpoint_13_70_w10
def endpoint_13_70 : CertifiedEndpoint :=
  ⟨⟨13, 70, 2101⟩, 234418841951830786, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_13_70_flag endpoint_13_70_sources 12 228403219153498450 234418841951830786 rfl endpoint_13_70_base endpoint_13_70_p12) (by decide)⟩
private def endpoint_13_71_flag : Flag := ⟨13, 71, 2029⟩
private def endpoint_13_71_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_71_base : receiptBase endpoint_13_71_flag endpoint_13_71_sources = some 224989142090917006 := by decide +kernel
private theorem endpoint_13_71_w0 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 2 224989142090917006 = some 227268966386246324 := by decide +kernel
private theorem endpoint_13_71_w2 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 2 2 227268966386246324 = some 227268966386246324 := by decide +kernel
private theorem endpoint_13_71_p4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 4 224989142090917006 = some 227268966386246324 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 2 2 224989142090917006 227268966386246324 227268966386246324 endpoint_13_71_w0 endpoint_13_71_w2
private theorem endpoint_13_71_w4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 4 2 227268966386246324 = some 227268966386246324 := by decide +kernel
private theorem endpoint_13_71_p6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 6 224989142090917006 = some 227268966386246324 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 4 2 224989142090917006 227268966386246324 227268966386246324 endpoint_13_71_p4 endpoint_13_71_w4
private theorem endpoint_13_71_w6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 6 2 227268966386246324 = some 227268966386246324 := by decide +kernel
private theorem endpoint_13_71_p8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 8 224989142090917006 = some 227268966386246324 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 6 2 224989142090917006 227268966386246324 227268966386246324 endpoint_13_71_p6 endpoint_13_71_w6
private theorem endpoint_13_71_w8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 8 2 227268966386246324 = some 227268966386246324 := by decide +kernel
private theorem endpoint_13_71_p10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 10 224989142090917006 = some 227268966386246324 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 8 2 224989142090917006 227268966386246324 227268966386246324 endpoint_13_71_p8 endpoint_13_71_w8
private theorem endpoint_13_71_w10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 10 2 227268966386246324 = some 227268966386246324 := by decide +kernel
private theorem endpoint_13_71_p12 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 12 224989142090917006 = some 227268966386246324 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 10 2 224989142090917006 227268966386246324 227268966386246324 endpoint_13_71_p10 endpoint_13_71_w10
def endpoint_13_71 : CertifiedEndpoint :=
  ⟨⟨13, 71, 2029⟩, 227268966386246324, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_71_flag endpoint_13_71_sources 12 224989142090917006 227268966386246324 rfl endpoint_13_71_base endpoint_13_71_p12) (by decide)⟩
private def endpoint_13_72_flag : Flag := ⟨13, 72, 1955⟩
private def endpoint_13_72_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_72_base : receiptBase endpoint_13_72_flag endpoint_13_72_sources = some 219605896759328946 := by decide +kernel
private theorem endpoint_13_72_w0 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 2 219605896759328946 = some 226134394344125600 := by decide +kernel
private theorem endpoint_13_72_w2 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 2 2 226134394344125600 = some 226134394344125600 := by decide +kernel
private theorem endpoint_13_72_p4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 4 219605896759328946 = some 226134394344125600 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 2 2 219605896759328946 226134394344125600 226134394344125600 endpoint_13_72_w0 endpoint_13_72_w2
private theorem endpoint_13_72_w4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 4 2 226134394344125600 = some 226134394344125600 := by decide +kernel
private theorem endpoint_13_72_p6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 6 219605896759328946 = some 226134394344125600 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 4 2 219605896759328946 226134394344125600 226134394344125600 endpoint_13_72_p4 endpoint_13_72_w4
private theorem endpoint_13_72_w6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 6 2 226134394344125600 = some 226134394344125600 := by decide +kernel
private theorem endpoint_13_72_p8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 8 219605896759328946 = some 226134394344125600 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 6 2 219605896759328946 226134394344125600 226134394344125600 endpoint_13_72_p6 endpoint_13_72_w6
private theorem endpoint_13_72_w8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 8 2 226134394344125600 = some 226134394344125600 := by decide +kernel
private theorem endpoint_13_72_p10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 10 219605896759328946 = some 226134394344125600 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 8 2 219605896759328946 226134394344125600 226134394344125600 endpoint_13_72_p8 endpoint_13_72_w8
private theorem endpoint_13_72_w10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 10 2 226134394344125600 = some 226134394344125600 := by decide +kernel
private theorem endpoint_13_72_p12 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 12 219605896759328946 = some 226134394344125600 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 10 2 219605896759328946 226134394344125600 226134394344125600 endpoint_13_72_p10 endpoint_13_72_w10
def endpoint_13_72 : CertifiedEndpoint :=
  ⟨⟨13, 72, 1955⟩, 226134394344125600, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_72_flag endpoint_13_72_sources 12 219605896759328946 226134394344125600 rfl endpoint_13_72_base endpoint_13_72_p12) (by decide)⟩
private def endpoint_13_73_flag : Flag := ⟨13, 73, 1878⟩
private def endpoint_13_73_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_73_base : receiptBase endpoint_13_73_flag endpoint_13_73_sources = some 215268161640792144 := by decide +kernel
private theorem endpoint_13_73_w0 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 2 215268161640792144 = some 215268161640792144 := by decide +kernel
private theorem endpoint_13_73_w2 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 2 2 215268161640792144 = some 215268161640792144 := by decide +kernel
private theorem endpoint_13_73_p4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 4 215268161640792144 = some 215268161640792144 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 2 2 215268161640792144 215268161640792144 215268161640792144 endpoint_13_73_w0 endpoint_13_73_w2
private theorem endpoint_13_73_w4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 4 2 215268161640792144 = some 215268161640792144 := by decide +kernel
private theorem endpoint_13_73_p6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 6 215268161640792144 = some 215268161640792144 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 4 2 215268161640792144 215268161640792144 215268161640792144 endpoint_13_73_p4 endpoint_13_73_w4
private theorem endpoint_13_73_w6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 6 2 215268161640792144 = some 215268161640792144 := by decide +kernel
private theorem endpoint_13_73_p8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 8 215268161640792144 = some 215268161640792144 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 6 2 215268161640792144 215268161640792144 215268161640792144 endpoint_13_73_p6 endpoint_13_73_w6
private theorem endpoint_13_73_w8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 8 2 215268161640792144 = some 215268161640792144 := by decide +kernel
private theorem endpoint_13_73_p10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 10 215268161640792144 = some 215268161640792144 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 8 2 215268161640792144 215268161640792144 215268161640792144 endpoint_13_73_p8 endpoint_13_73_w8
private theorem endpoint_13_73_w10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 10 2 215268161640792144 = some 215268161640792144 := by decide +kernel
private theorem endpoint_13_73_p12 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 12 215268161640792144 = some 215268161640792144 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 10 2 215268161640792144 215268161640792144 215268161640792144 endpoint_13_73_p10 endpoint_13_73_w10
def endpoint_13_73 : CertifiedEndpoint :=
  ⟨⟨13, 73, 1878⟩, 215268161640792144, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_73_flag endpoint_13_73_sources 12 215268161640792144 215268161640792144 rfl endpoint_13_73_base endpoint_13_73_p12) (by decide)⟩
private def endpoint_13_74_flag : Flag := ⟨13, 74, 1798⟩
private def endpoint_13_74_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_74_base : receiptBase endpoint_13_74_flag endpoint_13_74_sources = some 208707076902013090 := by decide +kernel
private theorem endpoint_13_74_w0 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 2 208707076902013090 = some 208707076902013090 := by decide +kernel
private theorem endpoint_13_74_w2 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 2 2 208707076902013090 = some 208707076902013090 := by decide +kernel
private theorem endpoint_13_74_p4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 4 208707076902013090 = some 208707076902013090 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 2 2 208707076902013090 208707076902013090 208707076902013090 endpoint_13_74_w0 endpoint_13_74_w2
private theorem endpoint_13_74_w4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 4 2 208707076902013090 = some 208707076902013090 := by decide +kernel
private theorem endpoint_13_74_p6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 6 208707076902013090 = some 208707076902013090 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 4 2 208707076902013090 208707076902013090 208707076902013090 endpoint_13_74_p4 endpoint_13_74_w4
private theorem endpoint_13_74_w6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 6 2 208707076902013090 = some 208707076902013090 := by decide +kernel
private theorem endpoint_13_74_p8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 8 208707076902013090 = some 208707076902013090 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 6 2 208707076902013090 208707076902013090 208707076902013090 endpoint_13_74_p6 endpoint_13_74_w6
private theorem endpoint_13_74_w8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 8 2 208707076902013090 = some 208707076902013090 := by decide +kernel
private theorem endpoint_13_74_p10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 10 208707076902013090 = some 208707076902013090 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 8 2 208707076902013090 208707076902013090 208707076902013090 endpoint_13_74_p8 endpoint_13_74_w8
private theorem endpoint_13_74_w10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 10 2 208707076902013090 = some 208707076902013090 := by decide +kernel
private theorem endpoint_13_74_p12 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 12 208707076902013090 = some 208707076902013090 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 10 2 208707076902013090 208707076902013090 208707076902013090 endpoint_13_74_p10 endpoint_13_74_w10
def endpoint_13_74 : CertifiedEndpoint :=
  ⟨⟨13, 74, 1798⟩, 208707076902013090, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_74_flag endpoint_13_74_sources 12 208707076902013090 208707076902013090 rfl endpoint_13_74_base endpoint_13_74_p12) (by decide)⟩
private def endpoint_13_75_flag : Flag := ⟨13, 75, 1716⟩
private def endpoint_13_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_75_base : receiptBase endpoint_13_75_flag endpoint_13_75_sources = some 201690418554509618 := by decide +kernel
private theorem endpoint_13_75_w0 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 2 201690418554509618 = some 205275012918946937 := by decide +kernel
private theorem endpoint_13_75_w2 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 2 2 205275012918946937 = some 205275012918946937 := by decide +kernel
private theorem endpoint_13_75_p4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 4 201690418554509618 = some 205275012918946937 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 2 2 201690418554509618 205275012918946937 205275012918946937 endpoint_13_75_w0 endpoint_13_75_w2
private theorem endpoint_13_75_w4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 4 2 205275012918946937 = some 205275012918946937 := by decide +kernel
private theorem endpoint_13_75_p6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 6 201690418554509618 = some 205275012918946937 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 4 2 201690418554509618 205275012918946937 205275012918946937 endpoint_13_75_p4 endpoint_13_75_w4
private theorem endpoint_13_75_w6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 6 2 205275012918946937 = some 205275012918946937 := by decide +kernel
private theorem endpoint_13_75_p8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 8 201690418554509618 = some 205275012918946937 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 6 2 201690418554509618 205275012918946937 205275012918946937 endpoint_13_75_p6 endpoint_13_75_w6
private theorem endpoint_13_75_w8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 8 2 205275012918946937 = some 205275012918946937 := by decide +kernel
private theorem endpoint_13_75_p10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 10 201690418554509618 = some 205275012918946937 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 8 2 201690418554509618 205275012918946937 205275012918946937 endpoint_13_75_p8 endpoint_13_75_w8
private theorem endpoint_13_75_w10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 10 2 205275012918946937 = some 205275012918946937 := by decide +kernel
private theorem endpoint_13_75_p12 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 12 201690418554509618 = some 205275012918946937 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 10 2 201690418554509618 205275012918946937 205275012918946937 endpoint_13_75_p10 endpoint_13_75_w10
def endpoint_13_75 : CertifiedEndpoint :=
  ⟨⟨13, 75, 1716⟩, 205275012918946937, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_75_flag endpoint_13_75_sources 12 201690418554509618 205275012918946937 rfl endpoint_13_75_base endpoint_13_75_p12) (by decide)⟩
private def endpoint_13_76_flag : Flag := ⟨13, 76, 1631⟩
private def endpoint_13_76_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_76_base : receiptBase endpoint_13_76_flag endpoint_13_76_sources = some 197176805111163826 := by decide +kernel
private theorem endpoint_13_76_w0 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 2 197176805111163826 = some 197176805111163826 := by decide +kernel
private theorem endpoint_13_76_w2 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 2 2 197176805111163826 = some 197176805111163826 := by decide +kernel
private theorem endpoint_13_76_p4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 4 197176805111163826 = some 197176805111163826 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 2 2 197176805111163826 197176805111163826 197176805111163826 endpoint_13_76_w0 endpoint_13_76_w2
private theorem endpoint_13_76_w4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 4 2 197176805111163826 = some 197176805111163826 := by decide +kernel
private theorem endpoint_13_76_p6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 6 197176805111163826 = some 197176805111163826 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 4 2 197176805111163826 197176805111163826 197176805111163826 endpoint_13_76_p4 endpoint_13_76_w4
private theorem endpoint_13_76_w6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 6 2 197176805111163826 = some 197176805111163826 := by decide +kernel
private theorem endpoint_13_76_p8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 8 197176805111163826 = some 197176805111163826 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 6 2 197176805111163826 197176805111163826 197176805111163826 endpoint_13_76_p6 endpoint_13_76_w6
private theorem endpoint_13_76_w8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 8 2 197176805111163826 = some 197176805111163826 := by decide +kernel
private theorem endpoint_13_76_p10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 10 197176805111163826 = some 197176805111163826 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 8 2 197176805111163826 197176805111163826 197176805111163826 endpoint_13_76_p8 endpoint_13_76_w8
private theorem endpoint_13_76_w10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 10 2 197176805111163826 = some 197176805111163826 := by decide +kernel
private theorem endpoint_13_76_p12 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 12 197176805111163826 = some 197176805111163826 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 10 2 197176805111163826 197176805111163826 197176805111163826 endpoint_13_76_p10 endpoint_13_76_w10
def endpoint_13_76 : CertifiedEndpoint :=
  ⟨⟨13, 76, 1631⟩, 197176805111163826, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_76_flag endpoint_13_76_sources 12 197176805111163826 197176805111163826 rfl endpoint_13_76_base endpoint_13_76_p12) (by decide)⟩
private def endpoint_13_77_flag : Flag := ⟨13, 77, 1544⟩
private def endpoint_13_77_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_77_base : receiptBase endpoint_13_77_flag endpoint_13_77_sources = some 188919854096531905 := by decide +kernel
private theorem endpoint_13_77_w0 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 2 188919854096531905 = some 188919854096531905 := by decide +kernel
private theorem endpoint_13_77_w2 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 2 2 188919854096531905 = some 188919854096531905 := by decide +kernel
private theorem endpoint_13_77_p4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 4 188919854096531905 = some 188919854096531905 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 2 2 188919854096531905 188919854096531905 188919854096531905 endpoint_13_77_w0 endpoint_13_77_w2
private theorem endpoint_13_77_w4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 4 2 188919854096531905 = some 188919854096531905 := by decide +kernel
private theorem endpoint_13_77_p6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 6 188919854096531905 = some 188919854096531905 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 4 2 188919854096531905 188919854096531905 188919854096531905 endpoint_13_77_p4 endpoint_13_77_w4
private theorem endpoint_13_77_w6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 6 2 188919854096531905 = some 188919854096531905 := by decide +kernel
private theorem endpoint_13_77_p8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 8 188919854096531905 = some 188919854096531905 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 6 2 188919854096531905 188919854096531905 188919854096531905 endpoint_13_77_p6 endpoint_13_77_w6
private theorem endpoint_13_77_w8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 8 2 188919854096531905 = some 188919854096531905 := by decide +kernel
private theorem endpoint_13_77_p10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 10 188919854096531905 = some 188919854096531905 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 8 2 188919854096531905 188919854096531905 188919854096531905 endpoint_13_77_p8 endpoint_13_77_w8
private theorem endpoint_13_77_w10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 10 2 188919854096531905 = some 188919854096531905 := by decide +kernel
private theorem endpoint_13_77_p12 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 12 188919854096531905 = some 188919854096531905 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 10 2 188919854096531905 188919854096531905 188919854096531905 endpoint_13_77_p10 endpoint_13_77_w10
def endpoint_13_77 : CertifiedEndpoint :=
  ⟨⟨13, 77, 1544⟩, 188919854096531905, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_77_flag endpoint_13_77_sources 12 188919854096531905 188919854096531905 rfl endpoint_13_77_base endpoint_13_77_p12) (by decide)⟩
private def endpoint_13_78_flag : Flag := ⟨13, 78, 1454⟩
private def endpoint_13_78_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_13_78_base : receiptBase endpoint_13_78_flag endpoint_13_78_sources = some 180403339429309482 := by decide +kernel
private theorem endpoint_13_78_w0 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 2 180403339429309482 = some 180403339429309482 := by decide +kernel
private theorem endpoint_13_78_w2 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 2 2 180403339429309482 = some 180403339429309482 := by decide +kernel
private theorem endpoint_13_78_p4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 4 180403339429309482 = some 180403339429309482 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 2 2 180403339429309482 180403339429309482 180403339429309482 endpoint_13_78_w0 endpoint_13_78_w2
private theorem endpoint_13_78_w4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 4 2 180403339429309482 = some 180403339429309482 := by decide +kernel
private theorem endpoint_13_78_p6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 6 180403339429309482 = some 180403339429309482 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 4 2 180403339429309482 180403339429309482 180403339429309482 endpoint_13_78_p4 endpoint_13_78_w4
private theorem endpoint_13_78_w6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 6 2 180403339429309482 = some 180403339429309482 := by decide +kernel
private theorem endpoint_13_78_p8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 8 180403339429309482 = some 180403339429309482 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 6 2 180403339429309482 180403339429309482 180403339429309482 endpoint_13_78_p6 endpoint_13_78_w6
private theorem endpoint_13_78_w8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 8 2 180403339429309482 = some 180403339429309482 := by decide +kernel
private theorem endpoint_13_78_p10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 10 180403339429309482 = some 180403339429309482 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 8 2 180403339429309482 180403339429309482 180403339429309482 endpoint_13_78_p8 endpoint_13_78_w8
private theorem endpoint_13_78_w10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 10 2 180403339429309482 = some 180403339429309482 := by decide +kernel
private theorem endpoint_13_78_p12 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 12 180403339429309482 = some 180403339429309482 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 10 2 180403339429309482 180403339429309482 180403339429309482 endpoint_13_78_p10 endpoint_13_78_w10
def endpoint_13_78 : CertifiedEndpoint :=
  ⟨⟨13, 78, 1454⟩, 180403339429309482, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_13_78_flag endpoint_13_78_sources 12 180403339429309482 180403339429309482 rfl endpoint_13_78_base endpoint_13_78_p12) (by decide)⟩
private def endpoint_13_79_flag : Flag := ⟨13, 79, 1362⟩
private def endpoint_13_79_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_79_base : receiptBase endpoint_13_79_flag endpoint_13_79_sources = some 172027350196336985 := by decide +kernel
private theorem endpoint_13_79_w0 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 2 172027350196336985 = some 172027350196336985 := by decide +kernel
private theorem endpoint_13_79_w2 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 2 2 172027350196336985 = some 172027350196336985 := by decide +kernel
private theorem endpoint_13_79_p4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 4 172027350196336985 = some 172027350196336985 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 2 2 172027350196336985 172027350196336985 172027350196336985 endpoint_13_79_w0 endpoint_13_79_w2
private theorem endpoint_13_79_w4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 4 2 172027350196336985 = some 172027350196336985 := by decide +kernel
private theorem endpoint_13_79_p6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 6 172027350196336985 = some 172027350196336985 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 4 2 172027350196336985 172027350196336985 172027350196336985 endpoint_13_79_p4 endpoint_13_79_w4
private theorem endpoint_13_79_w6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 6 2 172027350196336985 = some 172027350196336985 := by decide +kernel
private theorem endpoint_13_79_p8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 8 172027350196336985 = some 172027350196336985 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 6 2 172027350196336985 172027350196336985 172027350196336985 endpoint_13_79_p6 endpoint_13_79_w6
private theorem endpoint_13_79_w8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 8 2 172027350196336985 = some 172027350196336985 := by decide +kernel
private theorem endpoint_13_79_p10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 10 172027350196336985 = some 172027350196336985 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 8 2 172027350196336985 172027350196336985 172027350196336985 endpoint_13_79_p8 endpoint_13_79_w8
private theorem endpoint_13_79_w10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 10 2 172027350196336985 = some 172027350196336985 := by decide +kernel
private theorem endpoint_13_79_p12 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 12 172027350196336985 = some 172027350196336985 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 10 2 172027350196336985 172027350196336985 172027350196336985 endpoint_13_79_p10 endpoint_13_79_w10
def endpoint_13_79 : CertifiedEndpoint :=
  ⟨⟨13, 79, 1362⟩, 172027350196336985, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_79_flag endpoint_13_79_sources 12 172027350196336985 172027350196336985 rfl endpoint_13_79_base endpoint_13_79_p12) (by decide)⟩
private def endpoint_13_80_flag : Flag := ⟨13, 80, 1267⟩
private def endpoint_13_80_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_80_base : receiptBase endpoint_13_80_flag endpoint_13_80_sources = some 161966535943906808 := by decide +kernel
private theorem endpoint_13_80_w0 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 2 161966535943906808 = some 161966535943906808 := by decide +kernel
private theorem endpoint_13_80_w2 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 2 2 161966535943906808 = some 161966535943906808 := by decide +kernel
private theorem endpoint_13_80_p4 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 4 161966535943906808 = some 161966535943906808 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 2 2 161966535943906808 161966535943906808 161966535943906808 endpoint_13_80_w0 endpoint_13_80_w2
private theorem endpoint_13_80_w4 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 4 2 161966535943906808 = some 161966535943906808 := by decide +kernel
private theorem endpoint_13_80_p6 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 6 161966535943906808 = some 161966535943906808 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 4 2 161966535943906808 161966535943906808 161966535943906808 endpoint_13_80_p4 endpoint_13_80_w4
private theorem endpoint_13_80_w6 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 6 2 161966535943906808 = some 161966535943906808 := by decide +kernel
private theorem endpoint_13_80_p8 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 8 161966535943906808 = some 161966535943906808 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 6 2 161966535943906808 161966535943906808 161966535943906808 endpoint_13_80_p6 endpoint_13_80_w6
private theorem endpoint_13_80_w8 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 8 2 161966535943906808 = some 161966535943906808 := by decide +kernel
private theorem endpoint_13_80_p10 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 10 161966535943906808 = some 161966535943906808 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 8 2 161966535943906808 161966535943906808 161966535943906808 endpoint_13_80_p8 endpoint_13_80_w8
private theorem endpoint_13_80_w10 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 10 2 161966535943906808 = some 161966535943906808 := by decide +kernel
private theorem endpoint_13_80_p12 : receiptWindow endpoint_13_80_flag endpoint_13_80_sources 0 12 161966535943906808 = some 161966535943906808 :=
  join_receipt_window endpoint_13_80_flag endpoint_13_80_sources 0 10 2 161966535943906808 161966535943906808 161966535943906808 endpoint_13_80_p10 endpoint_13_80_w10
def endpoint_13_80 : CertifiedEndpoint :=
  ⟨⟨13, 80, 1267⟩, 161966535943906808, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_80_flag endpoint_13_80_sources 12 161966535943906808 161966535943906808 rfl endpoint_13_80_base endpoint_13_80_p12) (by decide)⟩
private def endpoint_13_81_flag : Flag := ⟨13, 81, 1169⟩
private def endpoint_13_81_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_81_base : receiptBase endpoint_13_81_flag endpoint_13_81_sources = some 151251935281224380 := by decide +kernel
private theorem endpoint_13_81_w0 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 2 151251935281224380 = some 157078260290149842 := by decide +kernel
private theorem endpoint_13_81_w2 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 2 2 157078260290149842 = some 157078260290149842 := by decide +kernel
private theorem endpoint_13_81_p4 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 4 151251935281224380 = some 157078260290149842 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 2 2 151251935281224380 157078260290149842 157078260290149842 endpoint_13_81_w0 endpoint_13_81_w2
private theorem endpoint_13_81_w4 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 4 2 157078260290149842 = some 157078260290149842 := by decide +kernel
private theorem endpoint_13_81_p6 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 6 151251935281224380 = some 157078260290149842 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 4 2 151251935281224380 157078260290149842 157078260290149842 endpoint_13_81_p4 endpoint_13_81_w4
private theorem endpoint_13_81_w6 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 6 2 157078260290149842 = some 157078260290149842 := by decide +kernel
private theorem endpoint_13_81_p8 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 8 151251935281224380 = some 157078260290149842 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 6 2 151251935281224380 157078260290149842 157078260290149842 endpoint_13_81_p6 endpoint_13_81_w6
private theorem endpoint_13_81_w8 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 8 2 157078260290149842 = some 157078260290149842 := by decide +kernel
private theorem endpoint_13_81_p10 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 10 151251935281224380 = some 157078260290149842 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 8 2 151251935281224380 157078260290149842 157078260290149842 endpoint_13_81_p8 endpoint_13_81_w8
private theorem endpoint_13_81_w10 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 10 2 157078260290149842 = some 157078260290149842 := by decide +kernel
private theorem endpoint_13_81_p12 : receiptWindow endpoint_13_81_flag endpoint_13_81_sources 0 12 151251935281224380 = some 157078260290149842 :=
  join_receipt_window endpoint_13_81_flag endpoint_13_81_sources 0 10 2 151251935281224380 157078260290149842 157078260290149842 endpoint_13_81_p10 endpoint_13_81_w10
def endpoint_13_81 : CertifiedEndpoint :=
  ⟨⟨13, 81, 1169⟩, 157078260290149842, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_81_flag endpoint_13_81_sources 12 151251935281224380 157078260290149842 rfl endpoint_13_81_base endpoint_13_81_p12) (by decide)⟩
def endpoint_13_82 : CertifiedEndpoint :=
  ⟨⟨13, 82, 1069⟩, 248207393733347077, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_83 : CertifiedEndpoint :=
  ⟨⟨13, 83, 966⟩, 226109171627854233, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_84 : CertifiedEndpoint :=
  ⟨⟨13, 84, 861⟩, 202844939807845693, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_85 : CertifiedEndpoint :=
  ⟨⟨13, 85, 752⟩, 177891437866058615, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_86 : CertifiedEndpoint :=
  ⟨⟨13, 86, 642⟩, 151975418285093034, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_87 : CertifiedEndpoint :=
  ⟨⟨13, 87, 528⟩, 124311990454054687, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_88 : CertifiedEndpoint :=
  ⟨⟨13, 88, 412⟩, 95385656028010264, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_89 : CertifiedEndpoint :=
  ⟨⟨13, 89, 294⟩, 65177035630861689, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_90 : CertifiedEndpoint :=
  ⟨⟨13, 90, 172⟩, 33130569895182660, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_14 : CertifiedEndpoint :=
  ⟨⟨14, 14, 3920⟩, 106998285628013752, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_15 : CertifiedEndpoint :=
  ⟨⟨14, 15, 3899⟩, 110859841284192856, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_16 : CertifiedEndpoint :=
  ⟨⟨14, 16, 3878⟩, 114673412357381098, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_17 : CertifiedEndpoint :=
  ⟨⟨14, 17, 3857⟩, 127444823611326146, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_18 : CertifiedEndpoint :=
  ⟨⟨14, 18, 3836⟩, 140066268050410480, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_19 : CertifiedEndpoint :=
  ⟨⟨14, 19, 3814⟩, 152497629641534255, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_20 : CertifiedEndpoint :=
  ⟨⟨14, 20, 3792⟩, 164772049217106120, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_21 : CertifiedEndpoint :=
  ⟨⟨14, 21, 3770⟩, 176889526777126075, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_22 : CertifiedEndpoint :=
  ⟨⟨14, 22, 3747⟩, 188799483487457481, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_23 : CertifiedEndpoint :=
  ⟨⟨14, 23, 3724⟩, 200545522981545781, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_24 : CertifiedEndpoint :=
  ⟨⟨14, 24, 3701⟩, 212127645259390975, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_25 : CertifiedEndpoint :=
  ⟨⟨14, 25, 3678⟩, 223545850320993063, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_26 : CertifiedEndpoint :=
  ⟨⟨14, 26, 3654⟩, 234735608930833014, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_27 : CertifiedEndpoint :=
  ⟨⟨14, 27, 3630⟩, 245754475123738663, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_28 : CertifiedEndpoint :=
  ⟨⟨14, 28, 3606⟩, 256602448899710010, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_14_29_flag : Flag := ⟨14, 29, 3582⟩
private def endpoint_14_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_29_base : receiptBase endpoint_14_29_flag endpoint_14_29_sources = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_w0 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 2 178580071220913065 = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_w2 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 2 2 178580071220913065 = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_p4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 4 178580071220913065 = some 178580071220913065 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 2 2 178580071220913065 178580071220913065 178580071220913065 endpoint_14_29_w0 endpoint_14_29_w2
private theorem endpoint_14_29_w4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 4 2 178580071220913065 = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_p6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 6 178580071220913065 = some 178580071220913065 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 4 2 178580071220913065 178580071220913065 178580071220913065 endpoint_14_29_p4 endpoint_14_29_w4
private theorem endpoint_14_29_w6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 6 2 178580071220913065 = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_p8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 8 178580071220913065 = some 178580071220913065 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 6 2 178580071220913065 178580071220913065 178580071220913065 endpoint_14_29_p6 endpoint_14_29_w6
private theorem endpoint_14_29_w8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 8 2 178580071220913065 = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_p10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 10 178580071220913065 = some 178580071220913065 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 8 2 178580071220913065 178580071220913065 178580071220913065 endpoint_14_29_p8 endpoint_14_29_w8
private theorem endpoint_14_29_w10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 10 2 178580071220913065 = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_p12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 12 178580071220913065 = some 178580071220913065 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 10 2 178580071220913065 178580071220913065 178580071220913065 endpoint_14_29_p10 endpoint_14_29_w10
private theorem endpoint_14_29_w12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 12 1 178580071220913065 = some 178580071220913065 := by decide +kernel
private theorem endpoint_14_29_p13 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 13 178580071220913065 = some 178580071220913065 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 12 1 178580071220913065 178580071220913065 178580071220913065 endpoint_14_29_p12 endpoint_14_29_w12
def endpoint_14_29 : CertifiedEndpoint :=
  ⟨⟨14, 29, 3582⟩, 178580071220913065, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_29_flag endpoint_14_29_sources 13 178580071220913065 178580071220913065 rfl endpoint_14_29_base endpoint_14_29_p13) (by decide)⟩
private def endpoint_14_30_flag : Flag := ⟨14, 30, 3557⟩
private def endpoint_14_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_30_base : receiptBase endpoint_14_30_flag endpoint_14_30_sources = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_w0 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 2 182360717361271137 = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_w2 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 2 2 182360717361271137 = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_p4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 4 182360717361271137 = some 182360717361271137 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 2 2 182360717361271137 182360717361271137 182360717361271137 endpoint_14_30_w0 endpoint_14_30_w2
private theorem endpoint_14_30_w4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 4 2 182360717361271137 = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_p6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 6 182360717361271137 = some 182360717361271137 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 4 2 182360717361271137 182360717361271137 182360717361271137 endpoint_14_30_p4 endpoint_14_30_w4
private theorem endpoint_14_30_w6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 6 2 182360717361271137 = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_p8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 8 182360717361271137 = some 182360717361271137 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 6 2 182360717361271137 182360717361271137 182360717361271137 endpoint_14_30_p6 endpoint_14_30_w6
private theorem endpoint_14_30_w8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 8 2 182360717361271137 = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_p10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 10 182360717361271137 = some 182360717361271137 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 8 2 182360717361271137 182360717361271137 182360717361271137 endpoint_14_30_p8 endpoint_14_30_w8
private theorem endpoint_14_30_w10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 10 2 182360717361271137 = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_p12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 12 182360717361271137 = some 182360717361271137 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 10 2 182360717361271137 182360717361271137 182360717361271137 endpoint_14_30_p10 endpoint_14_30_w10
private theorem endpoint_14_30_w12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 12 1 182360717361271137 = some 182360717361271137 := by decide +kernel
private theorem endpoint_14_30_p13 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 13 182360717361271137 = some 182360717361271137 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 12 1 182360717361271137 182360717361271137 182360717361271137 endpoint_14_30_p12 endpoint_14_30_w12
def endpoint_14_30 : CertifiedEndpoint :=
  ⟨⟨14, 30, 3557⟩, 182360717361271137, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_30_flag endpoint_14_30_sources 13 182360717361271137 182360717361271137 rfl endpoint_14_30_base endpoint_14_30_p13) (by decide)⟩
private def endpoint_14_31_flag : Flag := ⟨14, 31, 3531⟩
private def endpoint_14_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_31_base : receiptBase endpoint_14_31_flag endpoint_14_31_sources = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_w0 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 2 186019412163638200 = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_w2 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 2 2 186019412163638200 = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_p4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 4 186019412163638200 = some 186019412163638200 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 2 2 186019412163638200 186019412163638200 186019412163638200 endpoint_14_31_w0 endpoint_14_31_w2
private theorem endpoint_14_31_w4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 4 2 186019412163638200 = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_p6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 6 186019412163638200 = some 186019412163638200 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 4 2 186019412163638200 186019412163638200 186019412163638200 endpoint_14_31_p4 endpoint_14_31_w4
private theorem endpoint_14_31_w6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 6 2 186019412163638200 = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_p8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 8 186019412163638200 = some 186019412163638200 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 6 2 186019412163638200 186019412163638200 186019412163638200 endpoint_14_31_p6 endpoint_14_31_w6
private theorem endpoint_14_31_w8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 8 2 186019412163638200 = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_p10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 10 186019412163638200 = some 186019412163638200 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 8 2 186019412163638200 186019412163638200 186019412163638200 endpoint_14_31_p8 endpoint_14_31_w8
private theorem endpoint_14_31_w10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 10 2 186019412163638200 = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_p12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 12 186019412163638200 = some 186019412163638200 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 10 2 186019412163638200 186019412163638200 186019412163638200 endpoint_14_31_p10 endpoint_14_31_w10
private theorem endpoint_14_31_w12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 12 1 186019412163638200 = some 186019412163638200 := by decide +kernel
private theorem endpoint_14_31_p13 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 13 186019412163638200 = some 186019412163638200 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 12 1 186019412163638200 186019412163638200 186019412163638200 endpoint_14_31_p12 endpoint_14_31_w12
def endpoint_14_31 : CertifiedEndpoint :=
  ⟨⟨14, 31, 3531⟩, 186019412163638200, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_31_flag endpoint_14_31_sources 13 186019412163638200 186019412163638200 rfl endpoint_14_31_base endpoint_14_31_p13) (by decide)⟩
private def endpoint_14_32_flag : Flag := ⟨14, 32, 3506⟩
private def endpoint_14_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_32_base : receiptBase endpoint_14_32_flag endpoint_14_32_sources = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_w0 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 2 189658458758022300 = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_w2 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 2 2 189658458758022300 = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_p4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 4 189658458758022300 = some 189658458758022300 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 2 2 189658458758022300 189658458758022300 189658458758022300 endpoint_14_32_w0 endpoint_14_32_w2
private theorem endpoint_14_32_w4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 4 2 189658458758022300 = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_p6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 6 189658458758022300 = some 189658458758022300 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 4 2 189658458758022300 189658458758022300 189658458758022300 endpoint_14_32_p4 endpoint_14_32_w4
private theorem endpoint_14_32_w6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 6 2 189658458758022300 = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_p8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 8 189658458758022300 = some 189658458758022300 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 6 2 189658458758022300 189658458758022300 189658458758022300 endpoint_14_32_p6 endpoint_14_32_w6
private theorem endpoint_14_32_w8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 8 2 189658458758022300 = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_p10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 10 189658458758022300 = some 189658458758022300 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 8 2 189658458758022300 189658458758022300 189658458758022300 endpoint_14_32_p8 endpoint_14_32_w8
private theorem endpoint_14_32_w10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 10 2 189658458758022300 = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_p12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 12 189658458758022300 = some 189658458758022300 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 10 2 189658458758022300 189658458758022300 189658458758022300 endpoint_14_32_p10 endpoint_14_32_w10
private theorem endpoint_14_32_w12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 12 1 189658458758022300 = some 189658458758022300 := by decide +kernel
private theorem endpoint_14_32_p13 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 13 189658458758022300 = some 189658458758022300 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 12 1 189658458758022300 189658458758022300 189658458758022300 endpoint_14_32_p12 endpoint_14_32_w12
def endpoint_14_32 : CertifiedEndpoint :=
  ⟨⟨14, 32, 3506⟩, 189658458758022300, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_32_flag endpoint_14_32_sources 13 189658458758022300 189658458758022300 rfl endpoint_14_32_base endpoint_14_32_p13) (by decide)⟩
private def endpoint_14_33_flag : Flag := ⟨14, 33, 3480⟩
private def endpoint_14_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_33_base : receiptBase endpoint_14_33_flag endpoint_14_33_sources = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_w0 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 2 193172805295007063 = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_w2 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 2 2 193172805295007063 = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_p4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 4 193172805295007063 = some 193172805295007063 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 2 2 193172805295007063 193172805295007063 193172805295007063 endpoint_14_33_w0 endpoint_14_33_w2
private theorem endpoint_14_33_w4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 4 2 193172805295007063 = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_p6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 6 193172805295007063 = some 193172805295007063 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 4 2 193172805295007063 193172805295007063 193172805295007063 endpoint_14_33_p4 endpoint_14_33_w4
private theorem endpoint_14_33_w6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 6 2 193172805295007063 = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_p8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 8 193172805295007063 = some 193172805295007063 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 6 2 193172805295007063 193172805295007063 193172805295007063 endpoint_14_33_p6 endpoint_14_33_w6
private theorem endpoint_14_33_w8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 8 2 193172805295007063 = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_p10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 10 193172805295007063 = some 193172805295007063 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 8 2 193172805295007063 193172805295007063 193172805295007063 endpoint_14_33_p8 endpoint_14_33_w8
private theorem endpoint_14_33_w10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 10 2 193172805295007063 = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_p12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 12 193172805295007063 = some 193172805295007063 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 10 2 193172805295007063 193172805295007063 193172805295007063 endpoint_14_33_p10 endpoint_14_33_w10
private theorem endpoint_14_33_w12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 12 1 193172805295007063 = some 193172805295007063 := by decide +kernel
private theorem endpoint_14_33_p13 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 13 193172805295007063 = some 193172805295007063 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 12 1 193172805295007063 193172805295007063 193172805295007063 endpoint_14_33_p12 endpoint_14_33_w12
def endpoint_14_33 : CertifiedEndpoint :=
  ⟨⟨14, 33, 3480⟩, 193172805295007063, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_33_flag endpoint_14_33_sources 13 193172805295007063 193172805295007063 rfl endpoint_14_33_base endpoint_14_33_p13) (by decide)⟩
private def endpoint_14_34_flag : Flag := ⟨14, 34, 3453⟩
private def endpoint_14_34_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_34_base : receiptBase endpoint_14_34_flag endpoint_14_34_sources = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_w0 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 2 197738702809526249 = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_w2 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 2 2 197738702809526249 = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_p4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 4 197738702809526249 = some 197738702809526249 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 2 2 197738702809526249 197738702809526249 197738702809526249 endpoint_14_34_w0 endpoint_14_34_w2
private theorem endpoint_14_34_w4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 4 2 197738702809526249 = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_p6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 6 197738702809526249 = some 197738702809526249 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 4 2 197738702809526249 197738702809526249 197738702809526249 endpoint_14_34_p4 endpoint_14_34_w4
private theorem endpoint_14_34_w6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 6 2 197738702809526249 = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_p8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 8 197738702809526249 = some 197738702809526249 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 6 2 197738702809526249 197738702809526249 197738702809526249 endpoint_14_34_p6 endpoint_14_34_w6
private theorem endpoint_14_34_w8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 8 2 197738702809526249 = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_p10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 10 197738702809526249 = some 197738702809526249 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 8 2 197738702809526249 197738702809526249 197738702809526249 endpoint_14_34_p8 endpoint_14_34_w8
private theorem endpoint_14_34_w10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 10 2 197738702809526249 = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_p12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 12 197738702809526249 = some 197738702809526249 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 10 2 197738702809526249 197738702809526249 197738702809526249 endpoint_14_34_p10 endpoint_14_34_w10
private theorem endpoint_14_34_w12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 12 1 197738702809526249 = some 197738702809526249 := by decide +kernel
private theorem endpoint_14_34_p13 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 13 197738702809526249 = some 197738702809526249 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 12 1 197738702809526249 197738702809526249 197738702809526249 endpoint_14_34_p12 endpoint_14_34_w12
def endpoint_14_34 : CertifiedEndpoint :=
  ⟨⟨14, 34, 3453⟩, 197738702809526249, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_34_flag endpoint_14_34_sources 13 197738702809526249 197738702809526249 rfl endpoint_14_34_base endpoint_14_34_p13) (by decide)⟩
private def endpoint_14_35_flag : Flag := ⟨14, 35, 3426⟩
private def endpoint_14_35_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_35_base : receiptBase endpoint_14_35_flag endpoint_14_35_sources = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_w0 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 2 200972699135268781 = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_w2 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 2 2 200972699135268781 = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_p4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 4 200972699135268781 = some 200972699135268781 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 2 2 200972699135268781 200972699135268781 200972699135268781 endpoint_14_35_w0 endpoint_14_35_w2
private theorem endpoint_14_35_w4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 4 2 200972699135268781 = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_p6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 6 200972699135268781 = some 200972699135268781 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 4 2 200972699135268781 200972699135268781 200972699135268781 endpoint_14_35_p4 endpoint_14_35_w4
private theorem endpoint_14_35_w6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 6 2 200972699135268781 = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_p8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 8 200972699135268781 = some 200972699135268781 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 6 2 200972699135268781 200972699135268781 200972699135268781 endpoint_14_35_p6 endpoint_14_35_w6
private theorem endpoint_14_35_w8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 8 2 200972699135268781 = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_p10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 10 200972699135268781 = some 200972699135268781 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 8 2 200972699135268781 200972699135268781 200972699135268781 endpoint_14_35_p8 endpoint_14_35_w8
private theorem endpoint_14_35_w10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 10 2 200972699135268781 = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_p12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 12 200972699135268781 = some 200972699135268781 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 10 2 200972699135268781 200972699135268781 200972699135268781 endpoint_14_35_p10 endpoint_14_35_w10
private theorem endpoint_14_35_w12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 12 1 200972699135268781 = some 200972699135268781 := by decide +kernel
private theorem endpoint_14_35_p13 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 13 200972699135268781 = some 200972699135268781 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 12 1 200972699135268781 200972699135268781 200972699135268781 endpoint_14_35_p12 endpoint_14_35_w12
def endpoint_14_35 : CertifiedEndpoint :=
  ⟨⟨14, 35, 3426⟩, 200972699135268781, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_35_flag endpoint_14_35_sources 13 200972699135268781 200972699135268781 rfl endpoint_14_35_base endpoint_14_35_p13) (by decide)⟩
private def endpoint_14_36_flag : Flag := ⟨14, 36, 3399⟩
private def endpoint_14_36_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_36_base : receiptBase endpoint_14_36_flag endpoint_14_36_sources = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_w0 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 2 204131967602275835 = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_w2 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 2 2 204131967602275835 = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_p4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 4 204131967602275835 = some 204131967602275835 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 2 2 204131967602275835 204131967602275835 204131967602275835 endpoint_14_36_w0 endpoint_14_36_w2
private theorem endpoint_14_36_w4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 4 2 204131967602275835 = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_p6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 6 204131967602275835 = some 204131967602275835 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 4 2 204131967602275835 204131967602275835 204131967602275835 endpoint_14_36_p4 endpoint_14_36_w4
private theorem endpoint_14_36_w6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 6 2 204131967602275835 = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_p8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 8 204131967602275835 = some 204131967602275835 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 6 2 204131967602275835 204131967602275835 204131967602275835 endpoint_14_36_p6 endpoint_14_36_w6
private theorem endpoint_14_36_w8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 8 2 204131967602275835 = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_p10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 10 204131967602275835 = some 204131967602275835 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 8 2 204131967602275835 204131967602275835 204131967602275835 endpoint_14_36_p8 endpoint_14_36_w8
private theorem endpoint_14_36_w10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 10 2 204131967602275835 = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_p12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 12 204131967602275835 = some 204131967602275835 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 10 2 204131967602275835 204131967602275835 204131967602275835 endpoint_14_36_p10 endpoint_14_36_w10
private theorem endpoint_14_36_w12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 12 1 204131967602275835 = some 204131967602275835 := by decide +kernel
private theorem endpoint_14_36_p13 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 13 204131967602275835 = some 204131967602275835 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 12 1 204131967602275835 204131967602275835 204131967602275835 endpoint_14_36_p12 endpoint_14_36_w12
def endpoint_14_36 : CertifiedEndpoint :=
  ⟨⟨14, 36, 3399⟩, 204131967602275835, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_36_flag endpoint_14_36_sources 13 204131967602275835 204131967602275835 rfl endpoint_14_36_base endpoint_14_36_p13) (by decide)⟩
private def endpoint_14_37_flag : Flag := ⟨14, 37, 3371⟩
private def endpoint_14_37_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_37_base : receiptBase endpoint_14_37_flag endpoint_14_37_sources = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_w0 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 2 207156025524711450 = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_w2 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 2 2 207156025524711450 = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_p4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 4 207156025524711450 = some 207156025524711450 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 2 2 207156025524711450 207156025524711450 207156025524711450 endpoint_14_37_w0 endpoint_14_37_w2
private theorem endpoint_14_37_w4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 4 2 207156025524711450 = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_p6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 6 207156025524711450 = some 207156025524711450 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 4 2 207156025524711450 207156025524711450 207156025524711450 endpoint_14_37_p4 endpoint_14_37_w4
private theorem endpoint_14_37_w6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 6 2 207156025524711450 = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_p8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 8 207156025524711450 = some 207156025524711450 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 6 2 207156025524711450 207156025524711450 207156025524711450 endpoint_14_37_p6 endpoint_14_37_w6
private theorem endpoint_14_37_w8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 8 2 207156025524711450 = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_p10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 10 207156025524711450 = some 207156025524711450 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 8 2 207156025524711450 207156025524711450 207156025524711450 endpoint_14_37_p8 endpoint_14_37_w8
private theorem endpoint_14_37_w10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 10 2 207156025524711450 = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_p12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 12 207156025524711450 = some 207156025524711450 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 10 2 207156025524711450 207156025524711450 207156025524711450 endpoint_14_37_p10 endpoint_14_37_w10
private theorem endpoint_14_37_w12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 12 1 207156025524711450 = some 207156025524711450 := by decide +kernel
private theorem endpoint_14_37_p13 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 13 207156025524711450 = some 207156025524711450 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 12 1 207156025524711450 207156025524711450 207156025524711450 endpoint_14_37_p12 endpoint_14_37_w12
def endpoint_14_37 : CertifiedEndpoint :=
  ⟨⟨14, 37, 3371⟩, 207156025524711450, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_37_flag endpoint_14_37_sources 13 207156025524711450 207156025524711450 rfl endpoint_14_37_base endpoint_14_37_p13) (by decide)⟩
private def endpoint_14_38_flag : Flag := ⟨14, 38, 3343⟩
private def endpoint_14_38_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_38_base : receiptBase endpoint_14_38_flag endpoint_14_38_sources = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_w0 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 2 210102638375352297 = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_w2 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 2 2 210102638375352297 = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_p4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 4 210102638375352297 = some 210102638375352297 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 2 2 210102638375352297 210102638375352297 210102638375352297 endpoint_14_38_w0 endpoint_14_38_w2
private theorem endpoint_14_38_w4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 4 2 210102638375352297 = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_p6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 6 210102638375352297 = some 210102638375352297 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 4 2 210102638375352297 210102638375352297 210102638375352297 endpoint_14_38_p4 endpoint_14_38_w4
private theorem endpoint_14_38_w6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 6 2 210102638375352297 = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_p8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 8 210102638375352297 = some 210102638375352297 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 6 2 210102638375352297 210102638375352297 210102638375352297 endpoint_14_38_p6 endpoint_14_38_w6
private theorem endpoint_14_38_w8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 8 2 210102638375352297 = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_p10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 10 210102638375352297 = some 210102638375352297 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 8 2 210102638375352297 210102638375352297 210102638375352297 endpoint_14_38_p8 endpoint_14_38_w8
private theorem endpoint_14_38_w10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 10 2 210102638375352297 = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_p12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 12 210102638375352297 = some 210102638375352297 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 10 2 210102638375352297 210102638375352297 210102638375352297 endpoint_14_38_p10 endpoint_14_38_w10
private theorem endpoint_14_38_w12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 12 1 210102638375352297 = some 210102638375352297 := by decide +kernel
private theorem endpoint_14_38_p13 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 13 210102638375352297 = some 210102638375352297 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 12 1 210102638375352297 210102638375352297 210102638375352297 endpoint_14_38_p12 endpoint_14_38_w12
def endpoint_14_38 : CertifiedEndpoint :=
  ⟨⟨14, 38, 3343⟩, 210102638375352297, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_38_flag endpoint_14_38_sources 13 210102638375352297 210102638375352297 rfl endpoint_14_38_base endpoint_14_38_p13) (by decide)⟩
private def endpoint_14_39_flag : Flag := ⟨14, 39, 3314⟩
private def endpoint_14_39_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_39_base : receiptBase endpoint_14_39_flag endpoint_14_39_sources = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_w0 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 2 212908606255303126 = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_w2 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 2 2 212908606255303126 = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_p4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 4 212908606255303126 = some 212908606255303126 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 2 2 212908606255303126 212908606255303126 212908606255303126 endpoint_14_39_w0 endpoint_14_39_w2
private theorem endpoint_14_39_w4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 4 2 212908606255303126 = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_p6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 6 212908606255303126 = some 212908606255303126 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 4 2 212908606255303126 212908606255303126 212908606255303126 endpoint_14_39_p4 endpoint_14_39_w4
private theorem endpoint_14_39_w6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 6 2 212908606255303126 = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_p8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 8 212908606255303126 = some 212908606255303126 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 6 2 212908606255303126 212908606255303126 212908606255303126 endpoint_14_39_p6 endpoint_14_39_w6
private theorem endpoint_14_39_w8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 8 2 212908606255303126 = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_p10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 10 212908606255303126 = some 212908606255303126 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 8 2 212908606255303126 212908606255303126 212908606255303126 endpoint_14_39_p8 endpoint_14_39_w8
private theorem endpoint_14_39_w10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 10 2 212908606255303126 = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_p12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 12 212908606255303126 = some 212908606255303126 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 10 2 212908606255303126 212908606255303126 212908606255303126 endpoint_14_39_p10 endpoint_14_39_w10
private theorem endpoint_14_39_w12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 12 1 212908606255303126 = some 212908606255303126 := by decide +kernel
private theorem endpoint_14_39_p13 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 13 212908606255303126 = some 212908606255303126 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 12 1 212908606255303126 212908606255303126 212908606255303126 endpoint_14_39_p12 endpoint_14_39_w12
def endpoint_14_39 : CertifiedEndpoint :=
  ⟨⟨14, 39, 3314⟩, 212908606255303126, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_39_flag endpoint_14_39_sources 13 212908606255303126 212908606255303126 rfl endpoint_14_39_base endpoint_14_39_p13) (by decide)⟩
private def endpoint_14_40_flag : Flag := ⟨14, 40, 3284⟩
private def endpoint_14_40_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_40_base : receiptBase endpoint_14_40_flag endpoint_14_40_sources = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_w0 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 2 216135020981127607 = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_w2 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 2 2 216135020981127607 = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_p4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 4 216135020981127607 = some 216135020981127607 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 2 2 216135020981127607 216135020981127607 216135020981127607 endpoint_14_40_w0 endpoint_14_40_w2
private theorem endpoint_14_40_w4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 4 2 216135020981127607 = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_p6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 6 216135020981127607 = some 216135020981127607 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 4 2 216135020981127607 216135020981127607 216135020981127607 endpoint_14_40_p4 endpoint_14_40_w4
private theorem endpoint_14_40_w6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 6 2 216135020981127607 = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_p8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 8 216135020981127607 = some 216135020981127607 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 6 2 216135020981127607 216135020981127607 216135020981127607 endpoint_14_40_p6 endpoint_14_40_w6
private theorem endpoint_14_40_w8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 8 2 216135020981127607 = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_p10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 10 216135020981127607 = some 216135020981127607 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 8 2 216135020981127607 216135020981127607 216135020981127607 endpoint_14_40_p8 endpoint_14_40_w8
private theorem endpoint_14_40_w10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 10 2 216135020981127607 = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_p12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 12 216135020981127607 = some 216135020981127607 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 10 2 216135020981127607 216135020981127607 216135020981127607 endpoint_14_40_p10 endpoint_14_40_w10
private theorem endpoint_14_40_w12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 12 1 216135020981127607 = some 216135020981127607 := by decide +kernel
private theorem endpoint_14_40_p13 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 13 216135020981127607 = some 216135020981127607 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 12 1 216135020981127607 216135020981127607 216135020981127607 endpoint_14_40_p12 endpoint_14_40_w12
def endpoint_14_40 : CertifiedEndpoint :=
  ⟨⟨14, 40, 3284⟩, 216135020981127607, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_40_flag endpoint_14_40_sources 13 216135020981127607 216135020981127607 rfl endpoint_14_40_base endpoint_14_40_p13) (by decide)⟩
private def endpoint_14_41_flag : Flag := ⟨14, 41, 3254⟩
private def endpoint_14_41_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_41_base : receiptBase endpoint_14_41_flag endpoint_14_41_sources = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_w0 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 2 218728017757694859 = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_w2 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 2 2 218728017757694859 = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_p4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 4 218728017757694859 = some 218728017757694859 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 2 2 218728017757694859 218728017757694859 218728017757694859 endpoint_14_41_w0 endpoint_14_41_w2
private theorem endpoint_14_41_w4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 4 2 218728017757694859 = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_p6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 6 218728017757694859 = some 218728017757694859 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 4 2 218728017757694859 218728017757694859 218728017757694859 endpoint_14_41_p4 endpoint_14_41_w4
private theorem endpoint_14_41_w6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 6 2 218728017757694859 = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_p8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 8 218728017757694859 = some 218728017757694859 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 6 2 218728017757694859 218728017757694859 218728017757694859 endpoint_14_41_p6 endpoint_14_41_w6
private theorem endpoint_14_41_w8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 8 2 218728017757694859 = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_p10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 10 218728017757694859 = some 218728017757694859 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 8 2 218728017757694859 218728017757694859 218728017757694859 endpoint_14_41_p8 endpoint_14_41_w8
private theorem endpoint_14_41_w10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 10 2 218728017757694859 = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_p12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 12 218728017757694859 = some 218728017757694859 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 10 2 218728017757694859 218728017757694859 218728017757694859 endpoint_14_41_p10 endpoint_14_41_w10
private theorem endpoint_14_41_w12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 12 1 218728017757694859 = some 218728017757694859 := by decide +kernel
private theorem endpoint_14_41_p13 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 13 218728017757694859 = some 218728017757694859 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 12 1 218728017757694859 218728017757694859 218728017757694859 endpoint_14_41_p12 endpoint_14_41_w12
def endpoint_14_41 : CertifiedEndpoint :=
  ⟨⟨14, 41, 3254⟩, 218728017757694859, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_41_flag endpoint_14_41_sources 13 218728017757694859 218728017757694859 rfl endpoint_14_41_base endpoint_14_41_p13) (by decide)⟩
private def endpoint_14_42_flag : Flag := ⟨14, 42, 3224⟩
private def endpoint_14_42_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_42_base : receiptBase endpoint_14_42_flag endpoint_14_42_sources = some 221237585991878533 := by decide +kernel
private theorem endpoint_14_42_w0 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 2 221237585991878533 = some 222766702619271458 := by decide +kernel
private theorem endpoint_14_42_w2 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 2 2 222766702619271458 = some 222766702619271458 := by decide +kernel
private theorem endpoint_14_42_p4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 4 221237585991878533 = some 222766702619271458 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 2 2 221237585991878533 222766702619271458 222766702619271458 endpoint_14_42_w0 endpoint_14_42_w2
private theorem endpoint_14_42_w4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 4 2 222766702619271458 = some 222766702619271458 := by decide +kernel
private theorem endpoint_14_42_p6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 6 221237585991878533 = some 222766702619271458 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 4 2 221237585991878533 222766702619271458 222766702619271458 endpoint_14_42_p4 endpoint_14_42_w4
private theorem endpoint_14_42_w6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 6 2 222766702619271458 = some 222766702619271458 := by decide +kernel
private theorem endpoint_14_42_p8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 8 221237585991878533 = some 222766702619271458 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 6 2 221237585991878533 222766702619271458 222766702619271458 endpoint_14_42_p6 endpoint_14_42_w6
private theorem endpoint_14_42_w8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 8 2 222766702619271458 = some 222766702619271458 := by decide +kernel
private theorem endpoint_14_42_p10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 10 221237585991878533 = some 222766702619271458 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 8 2 221237585991878533 222766702619271458 222766702619271458 endpoint_14_42_p8 endpoint_14_42_w8
private theorem endpoint_14_42_w10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 10 2 222766702619271458 = some 222766702619271458 := by decide +kernel
private theorem endpoint_14_42_p12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 12 221237585991878533 = some 222766702619271458 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 10 2 221237585991878533 222766702619271458 222766702619271458 endpoint_14_42_p10 endpoint_14_42_w10
private theorem endpoint_14_42_w12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 12 1 222766702619271458 = some 222766702619271458 := by decide +kernel
private theorem endpoint_14_42_p13 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 13 221237585991878533 = some 222766702619271458 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 12 1 221237585991878533 222766702619271458 222766702619271458 endpoint_14_42_p12 endpoint_14_42_w12
def endpoint_14_42 : CertifiedEndpoint :=
  ⟨⟨14, 42, 3224⟩, 222766702619271458, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_42_flag endpoint_14_42_sources 13 221237585991878533 222766702619271458 rfl endpoint_14_42_base endpoint_14_42_p13) (by decide)⟩
private def endpoint_14_43_flag : Flag := ⟨14, 43, 3193⟩
private def endpoint_14_43_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_43_base : receiptBase endpoint_14_43_flag endpoint_14_43_sources = some 223594833609879243 := by decide +kernel
private theorem endpoint_14_43_w0 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 2 223594833609879243 = some 228119945676526903 := by decide +kernel
private theorem endpoint_14_43_w2 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 2 2 228119945676526903 = some 228119945676526903 := by decide +kernel
private theorem endpoint_14_43_p4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 4 223594833609879243 = some 228119945676526903 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 2 2 223594833609879243 228119945676526903 228119945676526903 endpoint_14_43_w0 endpoint_14_43_w2
private theorem endpoint_14_43_w4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 4 2 228119945676526903 = some 228119945676526903 := by decide +kernel
private theorem endpoint_14_43_p6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 6 223594833609879243 = some 228119945676526903 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 4 2 223594833609879243 228119945676526903 228119945676526903 endpoint_14_43_p4 endpoint_14_43_w4
private theorem endpoint_14_43_w6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 6 2 228119945676526903 = some 228119945676526903 := by decide +kernel
private theorem endpoint_14_43_p8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 8 223594833609879243 = some 228119945676526903 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 6 2 223594833609879243 228119945676526903 228119945676526903 endpoint_14_43_p6 endpoint_14_43_w6
private theorem endpoint_14_43_w8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 8 2 228119945676526903 = some 228119945676526903 := by decide +kernel
private theorem endpoint_14_43_p10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 10 223594833609879243 = some 228119945676526903 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 8 2 223594833609879243 228119945676526903 228119945676526903 endpoint_14_43_p8 endpoint_14_43_w8
private theorem endpoint_14_43_w10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 10 2 228119945676526903 = some 228119945676526903 := by decide +kernel
private theorem endpoint_14_43_p12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 12 223594833609879243 = some 228119945676526903 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 10 2 223594833609879243 228119945676526903 228119945676526903 endpoint_14_43_p10 endpoint_14_43_w10
private theorem endpoint_14_43_w12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 12 1 228119945676526903 = some 228119945676526903 := by decide +kernel
private theorem endpoint_14_43_p13 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 13 223594833609879243 = some 228119945676526903 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 12 1 223594833609879243 228119945676526903 228119945676526903 endpoint_14_43_p12 endpoint_14_43_w12
def endpoint_14_43 : CertifiedEndpoint :=
  ⟨⟨14, 43, 3193⟩, 228119945676526903, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_43_flag endpoint_14_43_sources 13 223594833609879243 228119945676526903 rfl endpoint_14_43_base endpoint_14_43_p13) (by decide)⟩
private def endpoint_14_44_flag : Flag := ⟨14, 44, 3161⟩
private def endpoint_14_44_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_14_44_base : receiptBase endpoint_14_44_flag endpoint_14_44_sources = some 227037856535679925 := by decide +kernel
private theorem endpoint_14_44_w0 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 2 227037856535679925 = some 231711366114578916 := by decide +kernel
private theorem endpoint_14_44_w2 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 2 2 231711366114578916 = some 231711366114578916 := by decide +kernel
private theorem endpoint_14_44_p4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 4 227037856535679925 = some 231711366114578916 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 2 2 227037856535679925 231711366114578916 231711366114578916 endpoint_14_44_w0 endpoint_14_44_w2
private theorem endpoint_14_44_w4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 4 2 231711366114578916 = some 231711366114578916 := by decide +kernel
private theorem endpoint_14_44_p6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 6 227037856535679925 = some 231711366114578916 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 4 2 227037856535679925 231711366114578916 231711366114578916 endpoint_14_44_p4 endpoint_14_44_w4
private theorem endpoint_14_44_w6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 6 2 231711366114578916 = some 231711366114578916 := by decide +kernel
private theorem endpoint_14_44_p8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 8 227037856535679925 = some 231711366114578916 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 6 2 227037856535679925 231711366114578916 231711366114578916 endpoint_14_44_p6 endpoint_14_44_w6
private theorem endpoint_14_44_w8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 8 2 231711366114578916 = some 231711366114578916 := by decide +kernel
private theorem endpoint_14_44_p10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 10 227037856535679925 = some 231711366114578916 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 8 2 227037856535679925 231711366114578916 231711366114578916 endpoint_14_44_p8 endpoint_14_44_w8
private theorem endpoint_14_44_w10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 10 2 231711366114578916 = some 231711366114578916 := by decide +kernel
private theorem endpoint_14_44_p12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 12 227037856535679925 = some 231711366114578916 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 10 2 227037856535679925 231711366114578916 231711366114578916 endpoint_14_44_p10 endpoint_14_44_w10
private theorem endpoint_14_44_w12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 12 1 231711366114578916 = some 231711366114578916 := by decide +kernel
private theorem endpoint_14_44_p13 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 13 227037856535679925 = some 231711366114578916 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 12 1 227037856535679925 231711366114578916 231711366114578916 endpoint_14_44_p12 endpoint_14_44_w12
def endpoint_14_44 : CertifiedEndpoint :=
  ⟨⟨14, 44, 3161⟩, 231711366114578916, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_14_44_flag endpoint_14_44_sources 13 227037856535679925 231711366114578916 rfl endpoint_14_44_base endpoint_14_44_p13) (by decide)⟩
private def endpoint_14_45_flag : Flag := ⟨14, 45, 3128⟩
private def endpoint_14_45_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_45_base : receiptBase endpoint_14_45_flag endpoint_14_45_sources = some 230177276890104239 := by decide +kernel
private theorem endpoint_14_45_w0 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 2 230177276890104239 = some 231780945326449739 := by decide +kernel
private theorem endpoint_14_45_w2 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 2 2 231780945326449739 = some 231780945326449739 := by decide +kernel
private theorem endpoint_14_45_p4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 4 230177276890104239 = some 231780945326449739 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 2 2 230177276890104239 231780945326449739 231780945326449739 endpoint_14_45_w0 endpoint_14_45_w2
private theorem endpoint_14_45_w4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 4 2 231780945326449739 = some 231780945326449739 := by decide +kernel
private theorem endpoint_14_45_p6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 6 230177276890104239 = some 231780945326449739 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 4 2 230177276890104239 231780945326449739 231780945326449739 endpoint_14_45_p4 endpoint_14_45_w4
private theorem endpoint_14_45_w6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 6 2 231780945326449739 = some 231780945326449739 := by decide +kernel
private theorem endpoint_14_45_p8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 8 230177276890104239 = some 231780945326449739 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 6 2 230177276890104239 231780945326449739 231780945326449739 endpoint_14_45_p6 endpoint_14_45_w6
private theorem endpoint_14_45_w8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 8 2 231780945326449739 = some 231780945326449739 := by decide +kernel
private theorem endpoint_14_45_p10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 10 230177276890104239 = some 231780945326449739 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 8 2 230177276890104239 231780945326449739 231780945326449739 endpoint_14_45_p8 endpoint_14_45_w8
private theorem endpoint_14_45_w10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 10 2 231780945326449739 = some 231780945326449739 := by decide +kernel
private theorem endpoint_14_45_p12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 12 230177276890104239 = some 231780945326449739 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 10 2 230177276890104239 231780945326449739 231780945326449739 endpoint_14_45_p10 endpoint_14_45_w10
private theorem endpoint_14_45_w12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 12 1 231780945326449739 = some 231780945326449739 := by decide +kernel
private theorem endpoint_14_45_p13 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 13 230177276890104239 = some 231780945326449739 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 12 1 230177276890104239 231780945326449739 231780945326449739 endpoint_14_45_p12 endpoint_14_45_w12
def endpoint_14_45 : CertifiedEndpoint :=
  ⟨⟨14, 45, 3128⟩, 231780945326449739, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_45_flag endpoint_14_45_sources 13 230177276890104239 231780945326449739 rfl endpoint_14_45_base endpoint_14_45_p13) (by decide)⟩
private def endpoint_14_46_flag : Flag := ⟨14, 46, 3095⟩
private def endpoint_14_46_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_46_base : receiptBase endpoint_14_46_flag endpoint_14_46_sources = some 232070938897391782 := by decide +kernel
private theorem endpoint_14_46_w0 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 2 232070938897391782 = some 236664599209248554 := by decide +kernel
private theorem endpoint_14_46_w2 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 2 2 236664599209248554 = some 236664599209248554 := by decide +kernel
private theorem endpoint_14_46_p4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 4 232070938897391782 = some 236664599209248554 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 2 2 232070938897391782 236664599209248554 236664599209248554 endpoint_14_46_w0 endpoint_14_46_w2
private theorem endpoint_14_46_w4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 4 2 236664599209248554 = some 236664599209248554 := by decide +kernel
private theorem endpoint_14_46_p6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 6 232070938897391782 = some 236664599209248554 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 4 2 232070938897391782 236664599209248554 236664599209248554 endpoint_14_46_p4 endpoint_14_46_w4
private theorem endpoint_14_46_w6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 6 2 236664599209248554 = some 236664599209248554 := by decide +kernel
private theorem endpoint_14_46_p8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 8 232070938897391782 = some 236664599209248554 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 6 2 232070938897391782 236664599209248554 236664599209248554 endpoint_14_46_p6 endpoint_14_46_w6
private theorem endpoint_14_46_w8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 8 2 236664599209248554 = some 236664599209248554 := by decide +kernel
private theorem endpoint_14_46_p10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 10 232070938897391782 = some 236664599209248554 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 8 2 232070938897391782 236664599209248554 236664599209248554 endpoint_14_46_p8 endpoint_14_46_w8
private theorem endpoint_14_46_w10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 10 2 236664599209248554 = some 236664599209248554 := by decide +kernel
private theorem endpoint_14_46_p12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 12 232070938897391782 = some 236664599209248554 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 10 2 232070938897391782 236664599209248554 236664599209248554 endpoint_14_46_p10 endpoint_14_46_w10
private theorem endpoint_14_46_w12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 12 1 236664599209248554 = some 236664599209248554 := by decide +kernel
private theorem endpoint_14_46_p13 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 13 232070938897391782 = some 236664599209248554 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 12 1 232070938897391782 236664599209248554 236664599209248554 endpoint_14_46_p12 endpoint_14_46_w12
def endpoint_14_46 : CertifiedEndpoint :=
  ⟨⟨14, 46, 3095⟩, 236664599209248554, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_46_flag endpoint_14_46_sources 13 232070938897391782 236664599209248554 rfl endpoint_14_46_base endpoint_14_46_p13) (by decide)⟩
private def endpoint_14_47_flag : Flag := ⟨14, 47, 3061⟩
private def endpoint_14_47_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_47_base : receiptBase endpoint_14_47_flag endpoint_14_47_sources = some 233798009535950397 := by decide +kernel
private theorem endpoint_14_47_w0 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 2 233798009535950397 = some 241434321896711808 := by decide +kernel
private theorem endpoint_14_47_w2 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 2 2 241434321896711808 = some 241434321896711808 := by decide +kernel
private theorem endpoint_14_47_p4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 4 233798009535950397 = some 241434321896711808 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 2 2 233798009535950397 241434321896711808 241434321896711808 endpoint_14_47_w0 endpoint_14_47_w2
private theorem endpoint_14_47_w4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 4 2 241434321896711808 = some 241434321896711808 := by decide +kernel
private theorem endpoint_14_47_p6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 6 233798009535950397 = some 241434321896711808 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 4 2 233798009535950397 241434321896711808 241434321896711808 endpoint_14_47_p4 endpoint_14_47_w4
private theorem endpoint_14_47_w6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 6 2 241434321896711808 = some 241434321896711808 := by decide +kernel
private theorem endpoint_14_47_p8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 8 233798009535950397 = some 241434321896711808 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 6 2 233798009535950397 241434321896711808 241434321896711808 endpoint_14_47_p6 endpoint_14_47_w6
private theorem endpoint_14_47_w8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 8 2 241434321896711808 = some 241434321896711808 := by decide +kernel
private theorem endpoint_14_47_p10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 10 233798009535950397 = some 241434321896711808 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 8 2 233798009535950397 241434321896711808 241434321896711808 endpoint_14_47_p8 endpoint_14_47_w8
private theorem endpoint_14_47_w10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 10 2 241434321896711808 = some 241434321896711808 := by decide +kernel
private theorem endpoint_14_47_p12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 12 233798009535950397 = some 241434321896711808 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 10 2 233798009535950397 241434321896711808 241434321896711808 endpoint_14_47_p10 endpoint_14_47_w10
private theorem endpoint_14_47_w12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 12 1 241434321896711808 = some 241434321896711808 := by decide +kernel
private theorem endpoint_14_47_p13 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 13 233798009535950397 = some 241434321896711808 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 12 1 233798009535950397 241434321896711808 241434321896711808 endpoint_14_47_p12 endpoint_14_47_w12
def endpoint_14_47 : CertifiedEndpoint :=
  ⟨⟨14, 47, 3061⟩, 241434321896711808, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_47_flag endpoint_14_47_sources 13 233798009535950397 241434321896711808 rfl endpoint_14_47_base endpoint_14_47_p13) (by decide)⟩
private def endpoint_14_48_flag : Flag := ⟨14, 48, 3026⟩
private def endpoint_14_48_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_48_base : receiptBase endpoint_14_48_flag endpoint_14_48_sources = some 236089146981743485 := by decide +kernel
private theorem endpoint_14_48_w0 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 2 236089146981743485 = some 238910595055347368 := by decide +kernel
private theorem endpoint_14_48_w2 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 2 2 238910595055347368 = some 238910595055347368 := by decide +kernel
private theorem endpoint_14_48_p4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 4 236089146981743485 = some 238910595055347368 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 2 2 236089146981743485 238910595055347368 238910595055347368 endpoint_14_48_w0 endpoint_14_48_w2
private theorem endpoint_14_48_w4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 4 2 238910595055347368 = some 238910595055347368 := by decide +kernel
private theorem endpoint_14_48_p6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 6 236089146981743485 = some 238910595055347368 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 4 2 236089146981743485 238910595055347368 238910595055347368 endpoint_14_48_p4 endpoint_14_48_w4
private theorem endpoint_14_48_w6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 6 2 238910595055347368 = some 238910595055347368 := by decide +kernel
private theorem endpoint_14_48_p8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 8 236089146981743485 = some 238910595055347368 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 6 2 236089146981743485 238910595055347368 238910595055347368 endpoint_14_48_p6 endpoint_14_48_w6
private theorem endpoint_14_48_w8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 8 2 238910595055347368 = some 238910595055347368 := by decide +kernel
private theorem endpoint_14_48_p10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 10 236089146981743485 = some 238910595055347368 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 8 2 236089146981743485 238910595055347368 238910595055347368 endpoint_14_48_p8 endpoint_14_48_w8
private theorem endpoint_14_48_w10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 10 2 238910595055347368 = some 238910595055347368 := by decide +kernel
private theorem endpoint_14_48_p12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 12 236089146981743485 = some 238910595055347368 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 10 2 236089146981743485 238910595055347368 238910595055347368 endpoint_14_48_p10 endpoint_14_48_w10
private theorem endpoint_14_48_w12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 12 1 238910595055347368 = some 238910595055347368 := by decide +kernel
private theorem endpoint_14_48_p13 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 13 236089146981743485 = some 238910595055347368 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 12 1 236089146981743485 238910595055347368 238910595055347368 endpoint_14_48_p12 endpoint_14_48_w12
def endpoint_14_48 : CertifiedEndpoint :=
  ⟨⟨14, 48, 3026⟩, 238910595055347368, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_48_flag endpoint_14_48_sources 13 236089146981743485 238910595055347368 rfl endpoint_14_48_base endpoint_14_48_p13) (by decide)⟩
private def endpoint_14_49_flag : Flag := ⟨14, 49, 2990⟩
private def endpoint_14_49_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_49_base : receiptBase endpoint_14_49_flag endpoint_14_49_sources = some 237481176297639113 := by decide +kernel
private theorem endpoint_14_49_w0 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 2 237481176297639113 = some 243264734848652399 := by decide +kernel
private theorem endpoint_14_49_w2 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 2 2 243264734848652399 = some 243264734848652399 := by decide +kernel
private theorem endpoint_14_49_p4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 4 237481176297639113 = some 243264734848652399 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 2 2 237481176297639113 243264734848652399 243264734848652399 endpoint_14_49_w0 endpoint_14_49_w2
private theorem endpoint_14_49_w4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 4 2 243264734848652399 = some 243264734848652399 := by decide +kernel
private theorem endpoint_14_49_p6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 6 237481176297639113 = some 243264734848652399 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 4 2 237481176297639113 243264734848652399 243264734848652399 endpoint_14_49_p4 endpoint_14_49_w4
private theorem endpoint_14_49_w6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 6 2 243264734848652399 = some 243264734848652399 := by decide +kernel
private theorem endpoint_14_49_p8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 8 237481176297639113 = some 243264734848652399 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 6 2 237481176297639113 243264734848652399 243264734848652399 endpoint_14_49_p6 endpoint_14_49_w6
private theorem endpoint_14_49_w8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 8 2 243264734848652399 = some 243264734848652399 := by decide +kernel
private theorem endpoint_14_49_p10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 10 237481176297639113 = some 243264734848652399 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 8 2 237481176297639113 243264734848652399 243264734848652399 endpoint_14_49_p8 endpoint_14_49_w8
private theorem endpoint_14_49_w10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 10 2 243264734848652399 = some 243264734848652399 := by decide +kernel
private theorem endpoint_14_49_p12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 12 237481176297639113 = some 243264734848652399 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 10 2 237481176297639113 243264734848652399 243264734848652399 endpoint_14_49_p10 endpoint_14_49_w10
private theorem endpoint_14_49_w12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 12 1 243264734848652399 = some 243264734848652399 := by decide +kernel
private theorem endpoint_14_49_p13 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 13 237481176297639113 = some 243264734848652399 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 12 1 237481176297639113 243264734848652399 243264734848652399 endpoint_14_49_p12 endpoint_14_49_w12
def endpoint_14_49 : CertifiedEndpoint :=
  ⟨⟨14, 49, 2990⟩, 243264734848652399, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_49_flag endpoint_14_49_sources 13 237481176297639113 243264734848652399 rfl endpoint_14_49_base endpoint_14_49_p13) (by decide)⟩
private def endpoint_14_50_flag : Flag := ⟨14, 50, 2953⟩
private def endpoint_14_50_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_50_base : receiptBase endpoint_14_50_flag endpoint_14_50_sources = some 238693368523499326 := by decide +kernel
private theorem endpoint_14_50_w0 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 2 238693368523499326 = some 247495434148968726 := by decide +kernel
private theorem endpoint_14_50_w2 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 2 2 247495434148968726 = some 247495434148968726 := by decide +kernel
private theorem endpoint_14_50_p4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 4 238693368523499326 = some 247495434148968726 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 2 2 238693368523499326 247495434148968726 247495434148968726 endpoint_14_50_w0 endpoint_14_50_w2
private theorem endpoint_14_50_w4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 4 2 247495434148968726 = some 247495434148968726 := by decide +kernel
private theorem endpoint_14_50_p6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 6 238693368523499326 = some 247495434148968726 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 4 2 238693368523499326 247495434148968726 247495434148968726 endpoint_14_50_p4 endpoint_14_50_w4
private theorem endpoint_14_50_w6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 6 2 247495434148968726 = some 247495434148968726 := by decide +kernel
private theorem endpoint_14_50_p8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 8 238693368523499326 = some 247495434148968726 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 6 2 238693368523499326 247495434148968726 247495434148968726 endpoint_14_50_p6 endpoint_14_50_w6
private theorem endpoint_14_50_w8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 8 2 247495434148968726 = some 247495434148968726 := by decide +kernel
private theorem endpoint_14_50_p10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 10 238693368523499326 = some 247495434148968726 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 8 2 238693368523499326 247495434148968726 247495434148968726 endpoint_14_50_p8 endpoint_14_50_w8
private theorem endpoint_14_50_w10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 10 2 247495434148968726 = some 247495434148968726 := by decide +kernel
private theorem endpoint_14_50_p12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 12 238693368523499326 = some 247495434148968726 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 10 2 238693368523499326 247495434148968726 247495434148968726 endpoint_14_50_p10 endpoint_14_50_w10
private theorem endpoint_14_50_w12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 12 1 247495434148968726 = some 247495434148968726 := by decide +kernel
private theorem endpoint_14_50_p13 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 13 238693368523499326 = some 247495434148968726 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 12 1 238693368523499326 247495434148968726 247495434148968726 endpoint_14_50_p12 endpoint_14_50_w12
def endpoint_14_50 : CertifiedEndpoint :=
  ⟨⟨14, 50, 2953⟩, 247495434148968726, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_50_flag endpoint_14_50_sources 13 238693368523499326 247495434148968726 rfl endpoint_14_50_base endpoint_14_50_p13) (by decide)⟩
private def endpoint_14_51_flag : Flag := ⟨14, 51, 2915⟩
private def endpoint_14_51_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_51_base : receiptBase endpoint_14_51_flag endpoint_14_51_sources = some 239721607352403956 := by decide +kernel
private theorem endpoint_14_51_w0 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 2 239721607352403956 = some 251599523190411968 := by decide +kernel
private theorem endpoint_14_51_w2 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 2 2 251599523190411968 = some 251599523190411968 := by decide +kernel
private theorem endpoint_14_51_p4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 4 239721607352403956 = some 251599523190411968 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 2 2 239721607352403956 251599523190411968 251599523190411968 endpoint_14_51_w0 endpoint_14_51_w2
private theorem endpoint_14_51_w4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 4 2 251599523190411968 = some 251599523190411968 := by decide +kernel
private theorem endpoint_14_51_p6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 6 239721607352403956 = some 251599523190411968 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 4 2 239721607352403956 251599523190411968 251599523190411968 endpoint_14_51_p4 endpoint_14_51_w4
private theorem endpoint_14_51_w6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 6 2 251599523190411968 = some 251599523190411968 := by decide +kernel
private theorem endpoint_14_51_p8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 8 239721607352403956 = some 251599523190411968 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 6 2 239721607352403956 251599523190411968 251599523190411968 endpoint_14_51_p6 endpoint_14_51_w6
private theorem endpoint_14_51_w8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 8 2 251599523190411968 = some 251599523190411968 := by decide +kernel
private theorem endpoint_14_51_p10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 10 239721607352403956 = some 251599523190411968 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 8 2 239721607352403956 251599523190411968 251599523190411968 endpoint_14_51_p8 endpoint_14_51_w8
private theorem endpoint_14_51_w10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 10 2 251599523190411968 = some 251599523190411968 := by decide +kernel
private theorem endpoint_14_51_p12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 12 239721607352403956 = some 251599523190411968 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 10 2 239721607352403956 251599523190411968 251599523190411968 endpoint_14_51_p10 endpoint_14_51_w10
private theorem endpoint_14_51_w12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 12 1 251599523190411968 = some 251599523190411968 := by decide +kernel
private theorem endpoint_14_51_p13 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 13 239721607352403956 = some 251599523190411968 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 12 1 239721607352403956 251599523190411968 251599523190411968 endpoint_14_51_p12 endpoint_14_51_w12
def endpoint_14_51 : CertifiedEndpoint :=
  ⟨⟨14, 51, 2915⟩, 251599523190411968, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_51_flag endpoint_14_51_sources 13 239721607352403956 251599523190411968 rfl endpoint_14_51_base endpoint_14_51_p13) (by decide)⟩
private def endpoint_14_52_flag : Flag := ⟨14, 52, 2876⟩
private def endpoint_14_52_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_52_base : receiptBase endpoint_14_52_flag endpoint_14_52_sources = some 240561776477432837 := by decide +kernel
private theorem endpoint_14_52_w0 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 2 240561776477432837 = some 255573832207097744 := by decide +kernel
private theorem endpoint_14_52_w2 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 2 2 255573832207097744 = some 255573832207097744 := by decide +kernel
private theorem endpoint_14_52_p4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 4 240561776477432837 = some 255573832207097744 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 2 2 240561776477432837 255573832207097744 255573832207097744 endpoint_14_52_w0 endpoint_14_52_w2
private theorem endpoint_14_52_w4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 4 2 255573832207097744 = some 255573832207097744 := by decide +kernel
private theorem endpoint_14_52_p6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 6 240561776477432837 = some 255573832207097744 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 4 2 240561776477432837 255573832207097744 255573832207097744 endpoint_14_52_p4 endpoint_14_52_w4
private theorem endpoint_14_52_w6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 6 2 255573832207097744 = some 255573832207097744 := by decide +kernel
private theorem endpoint_14_52_p8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 8 240561776477432837 = some 255573832207097744 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 6 2 240561776477432837 255573832207097744 255573832207097744 endpoint_14_52_p6 endpoint_14_52_w6
private theorem endpoint_14_52_w8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 8 2 255573832207097744 = some 255573832207097744 := by decide +kernel
private theorem endpoint_14_52_p10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 10 240561776477432837 = some 255573832207097744 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 8 2 240561776477432837 255573832207097744 255573832207097744 endpoint_14_52_p8 endpoint_14_52_w8
private theorem endpoint_14_52_w10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 10 2 255573832207097744 = some 255573832207097744 := by decide +kernel
private theorem endpoint_14_52_p12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 12 240561776477432837 = some 255573832207097744 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 10 2 240561776477432837 255573832207097744 255573832207097744 endpoint_14_52_p10 endpoint_14_52_w10
private theorem endpoint_14_52_w12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 12 1 255573832207097744 = some 255573832207097744 := by decide +kernel
private theorem endpoint_14_52_p13 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 13 240561776477432837 = some 255573832207097744 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 12 1 240561776477432837 255573832207097744 255573832207097744 endpoint_14_52_p12 endpoint_14_52_w12
def endpoint_14_52 : CertifiedEndpoint :=
  ⟨⟨14, 52, 2876⟩, 255573832207097744, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_52_flag endpoint_14_52_sources 13 240561776477432837 255573832207097744 rfl endpoint_14_52_base endpoint_14_52_p13) (by decide)⟩
private def endpoint_14_53_flag : Flag := ⟨14, 53, 2836⟩
private def endpoint_14_53_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_53_base : receiptBase endpoint_14_53_flag endpoint_14_53_sources = some 242041979538957201 := by decide +kernel
private theorem endpoint_14_53_w0 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 2 242041979538957201 = some 253610595442777344 := by decide +kernel
private theorem endpoint_14_53_w2 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 2 2 253610595442777344 = some 253610595442777344 := by decide +kernel
private theorem endpoint_14_53_p4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 4 242041979538957201 = some 253610595442777344 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 2 2 242041979538957201 253610595442777344 253610595442777344 endpoint_14_53_w0 endpoint_14_53_w2
private theorem endpoint_14_53_w4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 4 2 253610595442777344 = some 253610595442777344 := by decide +kernel
private theorem endpoint_14_53_p6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 6 242041979538957201 = some 253610595442777344 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 4 2 242041979538957201 253610595442777344 253610595442777344 endpoint_14_53_p4 endpoint_14_53_w4
private theorem endpoint_14_53_w6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 6 2 253610595442777344 = some 253610595442777344 := by decide +kernel
private theorem endpoint_14_53_p8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 8 242041979538957201 = some 253610595442777344 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 6 2 242041979538957201 253610595442777344 253610595442777344 endpoint_14_53_p6 endpoint_14_53_w6
private theorem endpoint_14_53_w8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 8 2 253610595442777344 = some 253610595442777344 := by decide +kernel
private theorem endpoint_14_53_p10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 10 242041979538957201 = some 253610595442777344 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 8 2 242041979538957201 253610595442777344 253610595442777344 endpoint_14_53_p8 endpoint_14_53_w8
private theorem endpoint_14_53_w10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 10 2 253610595442777344 = some 253610595442777344 := by decide +kernel
private theorem endpoint_14_53_p12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 12 242041979538957201 = some 253610595442777344 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 10 2 242041979538957201 253610595442777344 253610595442777344 endpoint_14_53_p10 endpoint_14_53_w10
private theorem endpoint_14_53_w12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 12 1 253610595442777344 = some 253610595442777344 := by decide +kernel
private theorem endpoint_14_53_p13 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 13 242041979538957201 = some 253610595442777344 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 12 1 242041979538957201 253610595442777344 253610595442777344 endpoint_14_53_p12 endpoint_14_53_w12
def endpoint_14_53 : CertifiedEndpoint :=
  ⟨⟨14, 53, 2836⟩, 253610595442777344, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_53_flag endpoint_14_53_sources 13 242041979538957201 253610595442777344 rfl endpoint_14_53_base endpoint_14_53_p13) (by decide)⟩
private def endpoint_14_54_flag : Flag := ⟨14, 54, 2795⟩
private def endpoint_14_54_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_54_base : receiptBase endpoint_14_54_flag endpoint_14_54_sources = some 242500359951522557 := by decide +kernel
private theorem endpoint_14_54_w0 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 2 242500359951522557 = some 257187609976390124 := by decide +kernel
private theorem endpoint_14_54_w2 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 2 2 257187609976390124 = some 257187609976390124 := by decide +kernel
private theorem endpoint_14_54_p4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 4 242500359951522557 = some 257187609976390124 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 2 2 242500359951522557 257187609976390124 257187609976390124 endpoint_14_54_w0 endpoint_14_54_w2
private theorem endpoint_14_54_w4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 4 2 257187609976390124 = some 257187609976390124 := by decide +kernel
private theorem endpoint_14_54_p6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 6 242500359951522557 = some 257187609976390124 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 4 2 242500359951522557 257187609976390124 257187609976390124 endpoint_14_54_p4 endpoint_14_54_w4
private theorem endpoint_14_54_w6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 6 2 257187609976390124 = some 257187609976390124 := by decide +kernel
private theorem endpoint_14_54_p8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 8 242500359951522557 = some 257187609976390124 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 6 2 242500359951522557 257187609976390124 257187609976390124 endpoint_14_54_p6 endpoint_14_54_w6
private theorem endpoint_14_54_w8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 8 2 257187609976390124 = some 257187609976390124 := by decide +kernel
private theorem endpoint_14_54_p10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 10 242500359951522557 = some 257187609976390124 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 8 2 242500359951522557 257187609976390124 257187609976390124 endpoint_14_54_p8 endpoint_14_54_w8
private theorem endpoint_14_54_w10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 10 2 257187609976390124 = some 257187609976390124 := by decide +kernel
private theorem endpoint_14_54_p12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 12 242500359951522557 = some 257187609976390124 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 10 2 242500359951522557 257187609976390124 257187609976390124 endpoint_14_54_p10 endpoint_14_54_w10
private theorem endpoint_14_54_w12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 12 1 257187609976390124 = some 257187609976390124 := by decide +kernel
private theorem endpoint_14_54_p13 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 13 242500359951522557 = some 257187609976390124 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 12 1 242500359951522557 257187609976390124 257187609976390124 endpoint_14_54_p12 endpoint_14_54_w12
def endpoint_14_54 : CertifiedEndpoint :=
  ⟨⟨14, 54, 2795⟩, 257187609976390124, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_54_flag endpoint_14_54_sources 13 242500359951522557 257187609976390124 rfl endpoint_14_54_base endpoint_14_54_p13) (by decide)⟩
private def endpoint_14_55_flag : Flag := ⟨14, 55, 2752⟩
private def endpoint_14_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_55_base : receiptBase endpoint_14_55_flag endpoint_14_55_sources = some 245316543326309522 := by decide +kernel
private theorem endpoint_14_55_w0 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 2 245316543326309522 = some 246912879539396569 := by decide +kernel
private theorem endpoint_14_55_w2 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 2 2 246912879539396569 = some 246912879539396569 := by decide +kernel
private theorem endpoint_14_55_p4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 4 245316543326309522 = some 246912879539396569 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 2 2 245316543326309522 246912879539396569 246912879539396569 endpoint_14_55_w0 endpoint_14_55_w2
private theorem endpoint_14_55_w4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 4 2 246912879539396569 = some 246912879539396569 := by decide +kernel
private theorem endpoint_14_55_p6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 6 245316543326309522 = some 246912879539396569 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 4 2 245316543326309522 246912879539396569 246912879539396569 endpoint_14_55_p4 endpoint_14_55_w4
private theorem endpoint_14_55_w6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 6 2 246912879539396569 = some 246912879539396569 := by decide +kernel
private theorem endpoint_14_55_p8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 8 245316543326309522 = some 246912879539396569 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 6 2 245316543326309522 246912879539396569 246912879539396569 endpoint_14_55_p6 endpoint_14_55_w6
private theorem endpoint_14_55_w8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 8 2 246912879539396569 = some 246912879539396569 := by decide +kernel
private theorem endpoint_14_55_p10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 10 245316543326309522 = some 246912879539396569 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 8 2 245316543326309522 246912879539396569 246912879539396569 endpoint_14_55_p8 endpoint_14_55_w8
private theorem endpoint_14_55_w10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 10 2 246912879539396569 = some 246912879539396569 := by decide +kernel
private theorem endpoint_14_55_p12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 12 245316543326309522 = some 246912879539396569 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 10 2 245316543326309522 246912879539396569 246912879539396569 endpoint_14_55_p10 endpoint_14_55_w10
private theorem endpoint_14_55_w12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 12 1 246912879539396569 = some 246912879539396569 := by decide +kernel
private theorem endpoint_14_55_p13 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 13 245316543326309522 = some 246912879539396569 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 12 1 245316543326309522 246912879539396569 246912879539396569 endpoint_14_55_p12 endpoint_14_55_w12
def endpoint_14_55 : CertifiedEndpoint :=
  ⟨⟨14, 55, 2752⟩, 246912879539396569, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_55_flag endpoint_14_55_sources 13 245316543326309522 246912879539396569 rfl endpoint_14_55_base endpoint_14_55_p13) (by decide)⟩
private def endpoint_14_56_flag : Flag := ⟨14, 56, 2708⟩
private def endpoint_14_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_56_base : receiptBase endpoint_14_56_flag endpoint_14_56_sources = some 245293079102158949 := by decide +kernel
private theorem endpoint_14_56_w0 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 2 245293079102158949 = some 249867563443526520 := by decide +kernel
private theorem endpoint_14_56_w2 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 2 2 249867563443526520 = some 249867563443526520 := by decide +kernel
private theorem endpoint_14_56_p4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 4 245293079102158949 = some 249867563443526520 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 2 2 245293079102158949 249867563443526520 249867563443526520 endpoint_14_56_w0 endpoint_14_56_w2
private theorem endpoint_14_56_w4 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 4 2 249867563443526520 = some 249867563443526520 := by decide +kernel
private theorem endpoint_14_56_p6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 6 245293079102158949 = some 249867563443526520 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 4 2 245293079102158949 249867563443526520 249867563443526520 endpoint_14_56_p4 endpoint_14_56_w4
private theorem endpoint_14_56_w6 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 6 2 249867563443526520 = some 249867563443526520 := by decide +kernel
private theorem endpoint_14_56_p8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 8 245293079102158949 = some 249867563443526520 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 6 2 245293079102158949 249867563443526520 249867563443526520 endpoint_14_56_p6 endpoint_14_56_w6
private theorem endpoint_14_56_w8 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 8 2 249867563443526520 = some 249867563443526520 := by decide +kernel
private theorem endpoint_14_56_p10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 10 245293079102158949 = some 249867563443526520 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 8 2 245293079102158949 249867563443526520 249867563443526520 endpoint_14_56_p8 endpoint_14_56_w8
private theorem endpoint_14_56_w10 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 10 2 249867563443526520 = some 249867563443526520 := by decide +kernel
private theorem endpoint_14_56_p12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 12 245293079102158949 = some 249867563443526520 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 10 2 245293079102158949 249867563443526520 249867563443526520 endpoint_14_56_p10 endpoint_14_56_w10
private theorem endpoint_14_56_w12 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 12 1 249867563443526520 = some 249867563443526520 := by decide +kernel
private theorem endpoint_14_56_p13 : receiptWindow endpoint_14_56_flag endpoint_14_56_sources 0 13 245293079102158949 = some 249867563443526520 :=
  join_receipt_window endpoint_14_56_flag endpoint_14_56_sources 0 12 1 245293079102158949 249867563443526520 249867563443526520 endpoint_14_56_p12 endpoint_14_56_w12
def endpoint_14_56 : CertifiedEndpoint :=
  ⟨⟨14, 56, 2708⟩, 249867563443526520, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_56_flag endpoint_14_56_sources 13 245293079102158949 249867563443526520 rfl endpoint_14_56_base endpoint_14_56_p13) (by decide)⟩
private def endpoint_14_57_flag : Flag := ⟨14, 57, 2663⟩
private def endpoint_14_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_57_base : receiptBase endpoint_14_57_flag endpoint_14_57_sources = some 245053480560938596 := by decide +kernel
private theorem endpoint_14_57_w0 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 2 245053480560938596 = some 252674505316220846 := by decide +kernel
private theorem endpoint_14_57_w2 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 2 2 252674505316220846 = some 252674505316220846 := by decide +kernel
private theorem endpoint_14_57_p4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 4 245053480560938596 = some 252674505316220846 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 2 2 245053480560938596 252674505316220846 252674505316220846 endpoint_14_57_w0 endpoint_14_57_w2
private theorem endpoint_14_57_w4 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 4 2 252674505316220846 = some 252674505316220846 := by decide +kernel
private theorem endpoint_14_57_p6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 6 245053480560938596 = some 252674505316220846 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 4 2 245053480560938596 252674505316220846 252674505316220846 endpoint_14_57_p4 endpoint_14_57_w4
private theorem endpoint_14_57_w6 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 6 2 252674505316220846 = some 252674505316220846 := by decide +kernel
private theorem endpoint_14_57_p8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 8 245053480560938596 = some 252674505316220846 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 6 2 245053480560938596 252674505316220846 252674505316220846 endpoint_14_57_p6 endpoint_14_57_w6
private theorem endpoint_14_57_w8 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 8 2 252674505316220846 = some 252674505316220846 := by decide +kernel
private theorem endpoint_14_57_p10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 10 245053480560938596 = some 252674505316220846 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 8 2 245053480560938596 252674505316220846 252674505316220846 endpoint_14_57_p8 endpoint_14_57_w8
private theorem endpoint_14_57_w10 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 10 2 252674505316220846 = some 252674505316220846 := by decide +kernel
private theorem endpoint_14_57_p12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 12 245053480560938596 = some 252674505316220846 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 10 2 245053480560938596 252674505316220846 252674505316220846 endpoint_14_57_p10 endpoint_14_57_w10
private theorem endpoint_14_57_w12 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 12 1 252674505316220846 = some 252674505316220846 := by decide +kernel
private theorem endpoint_14_57_p13 : receiptWindow endpoint_14_57_flag endpoint_14_57_sources 0 13 245053480560938596 = some 252674505316220846 :=
  join_receipt_window endpoint_14_57_flag endpoint_14_57_sources 0 12 1 245053480560938596 252674505316220846 252674505316220846 endpoint_14_57_p12 endpoint_14_57_w12
def endpoint_14_57 : CertifiedEndpoint :=
  ⟨⟨14, 57, 2663⟩, 252674505316220846, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_57_flag endpoint_14_57_sources 13 245053480560938596 252674505316220846 rfl endpoint_14_57_base endpoint_14_57_p13) (by decide)⟩
private def endpoint_14_58_flag : Flag := ⟨14, 58, 2616⟩
private def endpoint_14_58_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_58_base : receiptBase endpoint_14_58_flag endpoint_14_58_sources = some 244501302071289204 := by decide +kernel
private theorem endpoint_14_58_w0 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 2 244501302071289204 = some 255277946466822936 := by decide +kernel
private theorem endpoint_14_58_w2 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 2 2 255277946466822936 = some 255277946466822936 := by decide +kernel
private theorem endpoint_14_58_p4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 4 244501302071289204 = some 255277946466822936 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 2 2 244501302071289204 255277946466822936 255277946466822936 endpoint_14_58_w0 endpoint_14_58_w2
private theorem endpoint_14_58_w4 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 4 2 255277946466822936 = some 255277946466822936 := by decide +kernel
private theorem endpoint_14_58_p6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 6 244501302071289204 = some 255277946466822936 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 4 2 244501302071289204 255277946466822936 255277946466822936 endpoint_14_58_p4 endpoint_14_58_w4
private theorem endpoint_14_58_w6 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 6 2 255277946466822936 = some 255277946466822936 := by decide +kernel
private theorem endpoint_14_58_p8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 8 244501302071289204 = some 255277946466822936 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 6 2 244501302071289204 255277946466822936 255277946466822936 endpoint_14_58_p6 endpoint_14_58_w6
private theorem endpoint_14_58_w8 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 8 2 255277946466822936 = some 255277946466822936 := by decide +kernel
private theorem endpoint_14_58_p10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 10 244501302071289204 = some 255277946466822936 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 8 2 244501302071289204 255277946466822936 255277946466822936 endpoint_14_58_p8 endpoint_14_58_w8
private theorem endpoint_14_58_w10 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 10 2 255277946466822936 = some 255277946466822936 := by decide +kernel
private theorem endpoint_14_58_p12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 12 244501302071289204 = some 255277946466822936 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 10 2 244501302071289204 255277946466822936 255277946466822936 endpoint_14_58_p10 endpoint_14_58_w10
private theorem endpoint_14_58_w12 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 12 1 255277946466822936 = some 255277946466822936 := by decide +kernel
private theorem endpoint_14_58_p13 : receiptWindow endpoint_14_58_flag endpoint_14_58_sources 0 13 244501302071289204 = some 255277946466822936 :=
  join_receipt_window endpoint_14_58_flag endpoint_14_58_sources 0 12 1 244501302071289204 255277946466822936 255277946466822936 endpoint_14_58_p12 endpoint_14_58_w12
def endpoint_14_58 : CertifiedEndpoint :=
  ⟨⟨14, 58, 2616⟩, 255277946466822936, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_58_flag endpoint_14_58_sources 13 244501302071289204 255277946466822936 rfl endpoint_14_58_base endpoint_14_58_p13) (by decide)⟩
private def endpoint_14_59_flag : Flag := ⟨14, 59, 2567⟩
private def endpoint_14_59_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_59_base : receiptBase endpoint_14_59_flag endpoint_14_59_sources = some 243628095020101795 := by decide +kernel
private theorem endpoint_14_59_w0 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 2 243628095020101795 = some 257671547363564028 := by decide +kernel
private theorem endpoint_14_59_w2 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 2 2 257671547363564028 = some 257671547363564028 := by decide +kernel
private theorem endpoint_14_59_p4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 4 243628095020101795 = some 257671547363564028 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 2 2 243628095020101795 257671547363564028 257671547363564028 endpoint_14_59_w0 endpoint_14_59_w2
private theorem endpoint_14_59_w4 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 4 2 257671547363564028 = some 257671547363564028 := by decide +kernel
private theorem endpoint_14_59_p6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 6 243628095020101795 = some 257671547363564028 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 4 2 243628095020101795 257671547363564028 257671547363564028 endpoint_14_59_p4 endpoint_14_59_w4
private theorem endpoint_14_59_w6 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 6 2 257671547363564028 = some 257671547363564028 := by decide +kernel
private theorem endpoint_14_59_p8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 8 243628095020101795 = some 257671547363564028 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 6 2 243628095020101795 257671547363564028 257671547363564028 endpoint_14_59_p6 endpoint_14_59_w6
private theorem endpoint_14_59_w8 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 8 2 257671547363564028 = some 257671547363564028 := by decide +kernel
private theorem endpoint_14_59_p10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 10 243628095020101795 = some 257671547363564028 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 8 2 243628095020101795 257671547363564028 257671547363564028 endpoint_14_59_p8 endpoint_14_59_w8
private theorem endpoint_14_59_w10 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 10 2 257671547363564028 = some 257671547363564028 := by decide +kernel
private theorem endpoint_14_59_p12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 12 243628095020101795 = some 257671547363564028 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 10 2 243628095020101795 257671547363564028 257671547363564028 endpoint_14_59_p10 endpoint_14_59_w10
private theorem endpoint_14_59_w12 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 12 1 257671547363564028 = some 257671547363564028 := by decide +kernel
private theorem endpoint_14_59_p13 : receiptWindow endpoint_14_59_flag endpoint_14_59_sources 0 13 243628095020101795 = some 257671547363564028 :=
  join_receipt_window endpoint_14_59_flag endpoint_14_59_sources 0 12 1 243628095020101795 257671547363564028 257671547363564028 endpoint_14_59_p12 endpoint_14_59_w12
def endpoint_14_59 : CertifiedEndpoint :=
  ⟨⟨14, 59, 2567⟩, 257671547363564028, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_59_flag endpoint_14_59_sources 13 243628095020101795 257671547363564028 rfl endpoint_14_59_base endpoint_14_59_p13) (by decide)⟩
private def endpoint_14_60_flag : Flag := ⟨14, 60, 2517⟩
private def endpoint_14_60_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_60_base : receiptBase endpoint_14_60_flag endpoint_14_60_sources = some 242520448323441820 := by decide +kernel
private theorem endpoint_14_60_w0 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 2 242520448323441820 = some 259903670576703844 := by decide +kernel
private theorem endpoint_14_60_w2 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 2 2 259903670576703844 = some 259903670576703844 := by decide +kernel
private theorem endpoint_14_60_p4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 4 242520448323441820 = some 259903670576703844 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 2 2 242520448323441820 259903670576703844 259903670576703844 endpoint_14_60_w0 endpoint_14_60_w2
private theorem endpoint_14_60_w4 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 4 2 259903670576703844 = some 259903670576703844 := by decide +kernel
private theorem endpoint_14_60_p6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 6 242520448323441820 = some 259903670576703844 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 4 2 242520448323441820 259903670576703844 259903670576703844 endpoint_14_60_p4 endpoint_14_60_w4
private theorem endpoint_14_60_w6 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 6 2 259903670576703844 = some 259903670576703844 := by decide +kernel
private theorem endpoint_14_60_p8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 8 242520448323441820 = some 259903670576703844 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 6 2 242520448323441820 259903670576703844 259903670576703844 endpoint_14_60_p6 endpoint_14_60_w6
private theorem endpoint_14_60_w8 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 8 2 259903670576703844 = some 259903670576703844 := by decide +kernel
private theorem endpoint_14_60_p10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 10 242520448323441820 = some 259903670576703844 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 8 2 242520448323441820 259903670576703844 259903670576703844 endpoint_14_60_p8 endpoint_14_60_w8
private theorem endpoint_14_60_w10 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 10 2 259903670576703844 = some 259903670576703844 := by decide +kernel
private theorem endpoint_14_60_p12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 12 242520448323441820 = some 259903670576703844 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 10 2 242520448323441820 259903670576703844 259903670576703844 endpoint_14_60_p10 endpoint_14_60_w10
private theorem endpoint_14_60_w12 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 12 1 259903670576703844 = some 259903670576703844 := by decide +kernel
private theorem endpoint_14_60_p13 : receiptWindow endpoint_14_60_flag endpoint_14_60_sources 0 13 242520448323441820 = some 259903670576703844 :=
  join_receipt_window endpoint_14_60_flag endpoint_14_60_sources 0 12 1 242520448323441820 259903670576703844 259903670576703844 endpoint_14_60_p12 endpoint_14_60_w12
def endpoint_14_60 : CertifiedEndpoint :=
  ⟨⟨14, 60, 2517⟩, 259903670576703844, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_60_flag endpoint_14_60_sources 13 242520448323441820 259903670576703844 rfl endpoint_14_60_base endpoint_14_60_p13) (by decide)⟩
private def endpoint_14_61_flag : Flag := ⟨14, 61, 2465⟩
private def endpoint_14_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_61_base : receiptBase endpoint_14_61_flag endpoint_14_61_sources = some 246953272463024789 := by decide +kernel
private theorem endpoint_14_61_w0 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 2 246953272463024789 = some 248949210146453696 := by decide +kernel
private theorem endpoint_14_61_w2 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 2 2 248949210146453696 = some 248949210146453696 := by decide +kernel
private theorem endpoint_14_61_p4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 4 246953272463024789 = some 248949210146453696 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 2 2 246953272463024789 248949210146453696 248949210146453696 endpoint_14_61_w0 endpoint_14_61_w2
private theorem endpoint_14_61_w4 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 4 2 248949210146453696 = some 248949210146453696 := by decide +kernel
private theorem endpoint_14_61_p6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 6 246953272463024789 = some 248949210146453696 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 4 2 246953272463024789 248949210146453696 248949210146453696 endpoint_14_61_p4 endpoint_14_61_w4
private theorem endpoint_14_61_w6 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 6 2 248949210146453696 = some 248949210146453696 := by decide +kernel
private theorem endpoint_14_61_p8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 8 246953272463024789 = some 248949210146453696 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 6 2 246953272463024789 248949210146453696 248949210146453696 endpoint_14_61_p6 endpoint_14_61_w6
private theorem endpoint_14_61_w8 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 8 2 248949210146453696 = some 248949210146453696 := by decide +kernel
private theorem endpoint_14_61_p10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 10 246953272463024789 = some 248949210146453696 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 8 2 246953272463024789 248949210146453696 248949210146453696 endpoint_14_61_p8 endpoint_14_61_w8
private theorem endpoint_14_61_w10 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 10 2 248949210146453696 = some 248949210146453696 := by decide +kernel
private theorem endpoint_14_61_p12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 12 246953272463024789 = some 248949210146453696 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 10 2 246953272463024789 248949210146453696 248949210146453696 endpoint_14_61_p10 endpoint_14_61_w10
private theorem endpoint_14_61_w12 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 12 1 248949210146453696 = some 248949210146453696 := by decide +kernel
private theorem endpoint_14_61_p13 : receiptWindow endpoint_14_61_flag endpoint_14_61_sources 0 13 246953272463024789 = some 248949210146453696 :=
  join_receipt_window endpoint_14_61_flag endpoint_14_61_sources 0 12 1 246953272463024789 248949210146453696 248949210146453696 endpoint_14_61_p12 endpoint_14_61_w12
def endpoint_14_61 : CertifiedEndpoint :=
  ⟨⟨14, 61, 2465⟩, 248949210146453696, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_61_flag endpoint_14_61_sources 13 246953272463024789 248949210146453696 rfl endpoint_14_61_base endpoint_14_61_p13) (by decide)⟩
private def endpoint_14_62_flag : Flag := ⟨14, 62, 2411⟩
private def endpoint_14_62_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_62_base : receiptBase endpoint_14_62_flag endpoint_14_62_sources = some 245146666646651502 := by decide +kernel
private theorem endpoint_14_62_w0 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 2 245146666646651502 = some 250490771120059686 := by decide +kernel
private theorem endpoint_14_62_w2 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 2 2 250490771120059686 = some 250490771120059686 := by decide +kernel
private theorem endpoint_14_62_p4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 4 245146666646651502 = some 250490771120059686 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 2 2 245146666646651502 250490771120059686 250490771120059686 endpoint_14_62_w0 endpoint_14_62_w2
private theorem endpoint_14_62_w4 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 4 2 250490771120059686 = some 250490771120059686 := by decide +kernel
private theorem endpoint_14_62_p6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 6 245146666646651502 = some 250490771120059686 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 4 2 245146666646651502 250490771120059686 250490771120059686 endpoint_14_62_p4 endpoint_14_62_w4
private theorem endpoint_14_62_w6 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 6 2 250490771120059686 = some 250490771120059686 := by decide +kernel
private theorem endpoint_14_62_p8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 8 245146666646651502 = some 250490771120059686 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 6 2 245146666646651502 250490771120059686 250490771120059686 endpoint_14_62_p6 endpoint_14_62_w6
private theorem endpoint_14_62_w8 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 8 2 250490771120059686 = some 250490771120059686 := by decide +kernel
private theorem endpoint_14_62_p10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 10 245146666646651502 = some 250490771120059686 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 8 2 245146666646651502 250490771120059686 250490771120059686 endpoint_14_62_p8 endpoint_14_62_w8
private theorem endpoint_14_62_w10 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 10 2 250490771120059686 = some 250490771120059686 := by decide +kernel
private theorem endpoint_14_62_p12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 12 245146666646651502 = some 250490771120059686 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 10 2 245146666646651502 250490771120059686 250490771120059686 endpoint_14_62_p10 endpoint_14_62_w10
private theorem endpoint_14_62_w12 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 12 1 250490771120059686 = some 250490771120059686 := by decide +kernel
private theorem endpoint_14_62_p13 : receiptWindow endpoint_14_62_flag endpoint_14_62_sources 0 13 245146666646651502 = some 250490771120059686 :=
  join_receipt_window endpoint_14_62_flag endpoint_14_62_sources 0 12 1 245146666646651502 250490771120059686 250490771120059686 endpoint_14_62_p12 endpoint_14_62_w12
def endpoint_14_62 : CertifiedEndpoint :=
  ⟨⟨14, 62, 2411⟩, 250490771120059686, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_62_flag endpoint_14_62_sources 13 245146666646651502 250490771120059686 rfl endpoint_14_62_base endpoint_14_62_p13) (by decide)⟩
private def endpoint_14_63_flag : Flag := ⟨14, 63, 2355⟩
private def endpoint_14_63_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_63_base : receiptBase endpoint_14_63_flag endpoint_14_63_sources = some 242985017023517590 := by decide +kernel
private theorem endpoint_14_63_w0 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 2 242985017023517590 = some 251799246889985884 := by decide +kernel
private theorem endpoint_14_63_w2 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 2 2 251799246889985884 = some 251799246889985884 := by decide +kernel
private theorem endpoint_14_63_p4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 4 242985017023517590 = some 251799246889985884 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 2 2 242985017023517590 251799246889985884 251799246889985884 endpoint_14_63_w0 endpoint_14_63_w2
private theorem endpoint_14_63_w4 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 4 2 251799246889985884 = some 251799246889985884 := by decide +kernel
private theorem endpoint_14_63_p6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 6 242985017023517590 = some 251799246889985884 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 4 2 242985017023517590 251799246889985884 251799246889985884 endpoint_14_63_p4 endpoint_14_63_w4
private theorem endpoint_14_63_w6 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 6 2 251799246889985884 = some 251799246889985884 := by decide +kernel
private theorem endpoint_14_63_p8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 8 242985017023517590 = some 251799246889985884 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 6 2 242985017023517590 251799246889985884 251799246889985884 endpoint_14_63_p6 endpoint_14_63_w6
private theorem endpoint_14_63_w8 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 8 2 251799246889985884 = some 251799246889985884 := by decide +kernel
private theorem endpoint_14_63_p10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 10 242985017023517590 = some 251799246889985884 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 8 2 242985017023517590 251799246889985884 251799246889985884 endpoint_14_63_p8 endpoint_14_63_w8
private theorem endpoint_14_63_w10 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 10 2 251799246889985884 = some 251799246889985884 := by decide +kernel
private theorem endpoint_14_63_p12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 12 242985017023517590 = some 251799246889985884 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 10 2 242985017023517590 251799246889985884 251799246889985884 endpoint_14_63_p10 endpoint_14_63_w10
private theorem endpoint_14_63_w12 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 12 1 251799246889985884 = some 251799246889985884 := by decide +kernel
private theorem endpoint_14_63_p13 : receiptWindow endpoint_14_63_flag endpoint_14_63_sources 0 13 242985017023517590 = some 251799246889985884 :=
  join_receipt_window endpoint_14_63_flag endpoint_14_63_sources 0 12 1 242985017023517590 251799246889985884 251799246889985884 endpoint_14_63_p12 endpoint_14_63_w12
def endpoint_14_63 : CertifiedEndpoint :=
  ⟨⟨14, 63, 2355⟩, 251799246889985884, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_63_flag endpoint_14_63_sources 13 242985017023517590 251799246889985884 rfl endpoint_14_63_base endpoint_14_63_p13) (by decide)⟩
private def endpoint_14_64_flag : Flag := ⟨14, 64, 2297⟩
private def endpoint_14_64_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_64_base : receiptBase endpoint_14_64_flag endpoint_14_64_sources = some 240459861846255800 := by decide +kernel
private theorem endpoint_14_64_w0 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 2 240459861846255800 = some 252868297924463528 := by decide +kernel
private theorem endpoint_14_64_w2 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 2 2 252868297924463528 = some 252868297924463528 := by decide +kernel
private theorem endpoint_14_64_p4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 4 240459861846255800 = some 252868297924463528 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 2 2 240459861846255800 252868297924463528 252868297924463528 endpoint_14_64_w0 endpoint_14_64_w2
private theorem endpoint_14_64_w4 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 4 2 252868297924463528 = some 252868297924463528 := by decide +kernel
private theorem endpoint_14_64_p6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 6 240459861846255800 = some 252868297924463528 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 4 2 240459861846255800 252868297924463528 252868297924463528 endpoint_14_64_p4 endpoint_14_64_w4
private theorem endpoint_14_64_w6 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 6 2 252868297924463528 = some 252868297924463528 := by decide +kernel
private theorem endpoint_14_64_p8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 8 240459861846255800 = some 252868297924463528 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 6 2 240459861846255800 252868297924463528 252868297924463528 endpoint_14_64_p6 endpoint_14_64_w6
private theorem endpoint_14_64_w8 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 8 2 252868297924463528 = some 252868297924463528 := by decide +kernel
private theorem endpoint_14_64_p10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 10 240459861846255800 = some 252868297924463528 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 8 2 240459861846255800 252868297924463528 252868297924463528 endpoint_14_64_p8 endpoint_14_64_w8
private theorem endpoint_14_64_w10 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 10 2 252868297924463528 = some 252868297924463528 := by decide +kernel
private theorem endpoint_14_64_p12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 12 240459861846255800 = some 252868297924463528 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 10 2 240459861846255800 252868297924463528 252868297924463528 endpoint_14_64_p10 endpoint_14_64_w10
private theorem endpoint_14_64_w12 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 12 1 252868297924463528 = some 252868297924463528 := by decide +kernel
private theorem endpoint_14_64_p13 : receiptWindow endpoint_14_64_flag endpoint_14_64_sources 0 13 240459861846255800 = some 252868297924463528 :=
  join_receipt_window endpoint_14_64_flag endpoint_14_64_sources 0 12 1 240459861846255800 252868297924463528 252868297924463528 endpoint_14_64_p12 endpoint_14_64_w12
def endpoint_14_64 : CertifiedEndpoint :=
  ⟨⟨14, 64, 2297⟩, 252868297924463528, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_64_flag endpoint_14_64_sources 13 240459861846255800 252868297924463528 rfl endpoint_14_64_base endpoint_14_64_p13) (by decide)⟩
private def endpoint_14_65_flag : Flag := ⟨14, 65, 2237⟩
private def endpoint_14_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_14_65_base : receiptBase endpoint_14_65_flag endpoint_14_65_sources = some 237562739367498883 := by decide +kernel
private theorem endpoint_14_65_w0 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 2 237562739367498883 = some 253691584691723856 := by decide +kernel
private theorem endpoint_14_65_w2 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 2 2 253691584691723856 = some 253691584691723856 := by decide +kernel
private theorem endpoint_14_65_p4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 4 237562739367498883 = some 253691584691723856 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 2 2 237562739367498883 253691584691723856 253691584691723856 endpoint_14_65_w0 endpoint_14_65_w2
private theorem endpoint_14_65_w4 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 4 2 253691584691723856 = some 253691584691723856 := by decide +kernel
private theorem endpoint_14_65_p6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 6 237562739367498883 = some 253691584691723856 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 4 2 237562739367498883 253691584691723856 253691584691723856 endpoint_14_65_p4 endpoint_14_65_w4
private theorem endpoint_14_65_w6 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 6 2 253691584691723856 = some 253691584691723856 := by decide +kernel
private theorem endpoint_14_65_p8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 8 237562739367498883 = some 253691584691723856 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 6 2 237562739367498883 253691584691723856 253691584691723856 endpoint_14_65_p6 endpoint_14_65_w6
private theorem endpoint_14_65_w8 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 8 2 253691584691723856 = some 253691584691723856 := by decide +kernel
private theorem endpoint_14_65_p10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 10 237562739367498883 = some 253691584691723856 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 8 2 237562739367498883 253691584691723856 253691584691723856 endpoint_14_65_p8 endpoint_14_65_w8
private theorem endpoint_14_65_w10 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 10 2 253691584691723856 = some 253691584691723856 := by decide +kernel
private theorem endpoint_14_65_p12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 12 237562739367498883 = some 253691584691723856 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 10 2 237562739367498883 253691584691723856 253691584691723856 endpoint_14_65_p10 endpoint_14_65_w10
private theorem endpoint_14_65_w12 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 12 1 253691584691723856 = some 253691584691723856 := by decide +kernel
private theorem endpoint_14_65_p13 : receiptWindow endpoint_14_65_flag endpoint_14_65_sources 0 13 237562739367498883 = some 253691584691723856 :=
  join_receipt_window endpoint_14_65_flag endpoint_14_65_sources 0 12 1 237562739367498883 253691584691723856 253691584691723856 endpoint_14_65_p12 endpoint_14_65_w12
def endpoint_14_65 : CertifiedEndpoint :=
  ⟨⟨14, 65, 2237⟩, 253691584691723856, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_14_65_flag endpoint_14_65_sources 13 237562739367498883 253691584691723856 rfl endpoint_14_65_base endpoint_14_65_p13) (by decide)⟩
private def endpoint_14_66_flag : Flag := ⟨14, 66, 2175⟩
private def endpoint_14_66_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_66_base : receiptBase endpoint_14_66_flag endpoint_14_66_sources = some 235444732855421347 := by decide +kernel
private theorem endpoint_14_66_w0 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 2 235444732855421347 = some 241345897808691550 := by decide +kernel
private theorem endpoint_14_66_w2 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 2 2 241345897808691550 = some 241345897808691550 := by decide +kernel
private theorem endpoint_14_66_p4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 4 235444732855421347 = some 241345897808691550 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 2 2 235444732855421347 241345897808691550 241345897808691550 endpoint_14_66_w0 endpoint_14_66_w2
private theorem endpoint_14_66_w4 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 4 2 241345897808691550 = some 241345897808691550 := by decide +kernel
private theorem endpoint_14_66_p6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 6 235444732855421347 = some 241345897808691550 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 4 2 235444732855421347 241345897808691550 241345897808691550 endpoint_14_66_p4 endpoint_14_66_w4
private theorem endpoint_14_66_w6 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 6 2 241345897808691550 = some 241345897808691550 := by decide +kernel
private theorem endpoint_14_66_p8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 8 235444732855421347 = some 241345897808691550 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 6 2 235444732855421347 241345897808691550 241345897808691550 endpoint_14_66_p6 endpoint_14_66_w6
private theorem endpoint_14_66_w8 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 8 2 241345897808691550 = some 241345897808691550 := by decide +kernel
private theorem endpoint_14_66_p10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 10 235444732855421347 = some 241345897808691550 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 8 2 235444732855421347 241345897808691550 241345897808691550 endpoint_14_66_p8 endpoint_14_66_w8
private theorem endpoint_14_66_w10 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 10 2 241345897808691550 = some 241345897808691550 := by decide +kernel
private theorem endpoint_14_66_p12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 12 235444732855421347 = some 241345897808691550 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 10 2 235444732855421347 241345897808691550 241345897808691550 endpoint_14_66_p10 endpoint_14_66_w10
private theorem endpoint_14_66_w12 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 12 1 241345897808691550 = some 241345897808691550 := by decide +kernel
private theorem endpoint_14_66_p13 : receiptWindow endpoint_14_66_flag endpoint_14_66_sources 0 13 235444732855421347 = some 241345897808691550 :=
  join_receipt_window endpoint_14_66_flag endpoint_14_66_sources 0 12 1 235444732855421347 241345897808691550 241345897808691550 endpoint_14_66_p12 endpoint_14_66_w12
def endpoint_14_66 : CertifiedEndpoint :=
  ⟨⟨14, 66, 2175⟩, 241345897808691550, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_66_flag endpoint_14_66_sources 13 235444732855421347 241345897808691550 rfl endpoint_14_66_base endpoint_14_66_p13) (by decide)⟩
private def endpoint_14_67_flag : Flag := ⟨14, 67, 2111⟩
private def endpoint_14_67_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_14_67_base : receiptBase endpoint_14_67_flag endpoint_14_67_sources = some 231747195130772836 := by decide +kernel
private theorem endpoint_14_67_w0 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 2 231747195130772836 = some 241436960092612622 := by decide +kernel
private theorem endpoint_14_67_w2 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 2 2 241436960092612622 = some 241436960092612622 := by decide +kernel
private theorem endpoint_14_67_p4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 4 231747195130772836 = some 241436960092612622 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 2 2 231747195130772836 241436960092612622 241436960092612622 endpoint_14_67_w0 endpoint_14_67_w2
private theorem endpoint_14_67_w4 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 4 2 241436960092612622 = some 241436960092612622 := by decide +kernel
private theorem endpoint_14_67_p6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 6 231747195130772836 = some 241436960092612622 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 4 2 231747195130772836 241436960092612622 241436960092612622 endpoint_14_67_p4 endpoint_14_67_w4
private theorem endpoint_14_67_w6 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 6 2 241436960092612622 = some 241436960092612622 := by decide +kernel
private theorem endpoint_14_67_p8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 8 231747195130772836 = some 241436960092612622 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 6 2 231747195130772836 241436960092612622 241436960092612622 endpoint_14_67_p6 endpoint_14_67_w6
private theorem endpoint_14_67_w8 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 8 2 241436960092612622 = some 241436960092612622 := by decide +kernel
private theorem endpoint_14_67_p10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 10 231747195130772836 = some 241436960092612622 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 8 2 231747195130772836 241436960092612622 241436960092612622 endpoint_14_67_p8 endpoint_14_67_w8
private theorem endpoint_14_67_w10 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 10 2 241436960092612622 = some 241436960092612622 := by decide +kernel
private theorem endpoint_14_67_p12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 12 231747195130772836 = some 241436960092612622 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 10 2 231747195130772836 241436960092612622 241436960092612622 endpoint_14_67_p10 endpoint_14_67_w10
private theorem endpoint_14_67_w12 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 12 1 241436960092612622 = some 241436960092612622 := by decide +kernel
private theorem endpoint_14_67_p13 : receiptWindow endpoint_14_67_flag endpoint_14_67_sources 0 13 231747195130772836 = some 241436960092612622 :=
  join_receipt_window endpoint_14_67_flag endpoint_14_67_sources 0 12 1 231747195130772836 241436960092612622 241436960092612622 endpoint_14_67_p12 endpoint_14_67_w12
def endpoint_14_67 : CertifiedEndpoint :=
  ⟨⟨14, 67, 2111⟩, 241436960092612622, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_14_67_flag endpoint_14_67_sources 13 231747195130772836 241436960092612622 rfl endpoint_14_67_base endpoint_14_67_p13) (by decide)⟩
private def endpoint_14_68_flag : Flag := ⟨14, 68, 2044⟩
private def endpoint_14_68_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_14_68_base : receiptBase endpoint_14_68_flag endpoint_14_68_sources = some 227579482388001398 := by decide +kernel
private theorem endpoint_14_68_w0 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 2 227579482388001398 = some 241200084702956592 := by decide +kernel
private theorem endpoint_14_68_w2 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 2 2 241200084702956592 = some 241200084702956592 := by decide +kernel
private theorem endpoint_14_68_p4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 4 227579482388001398 = some 241200084702956592 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 2 2 227579482388001398 241200084702956592 241200084702956592 endpoint_14_68_w0 endpoint_14_68_w2
private theorem endpoint_14_68_w4 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 4 2 241200084702956592 = some 241200084702956592 := by decide +kernel
private theorem endpoint_14_68_p6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 6 227579482388001398 = some 241200084702956592 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 4 2 227579482388001398 241200084702956592 241200084702956592 endpoint_14_68_p4 endpoint_14_68_w4
private theorem endpoint_14_68_w6 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 6 2 241200084702956592 = some 241200084702956592 := by decide +kernel
private theorem endpoint_14_68_p8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 8 227579482388001398 = some 241200084702956592 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 6 2 227579482388001398 241200084702956592 241200084702956592 endpoint_14_68_p6 endpoint_14_68_w6
private theorem endpoint_14_68_w8 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 8 2 241200084702956592 = some 241200084702956592 := by decide +kernel
private theorem endpoint_14_68_p10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 10 227579482388001398 = some 241200084702956592 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 8 2 227579482388001398 241200084702956592 241200084702956592 endpoint_14_68_p8 endpoint_14_68_w8
private theorem endpoint_14_68_w10 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 10 2 241200084702956592 = some 241200084702956592 := by decide +kernel
private theorem endpoint_14_68_p12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 12 227579482388001398 = some 241200084702956592 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 10 2 227579482388001398 241200084702956592 241200084702956592 endpoint_14_68_p10 endpoint_14_68_w10
private theorem endpoint_14_68_w12 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 12 1 241200084702956592 = some 241200084702956592 := by decide +kernel
private theorem endpoint_14_68_p13 : receiptWindow endpoint_14_68_flag endpoint_14_68_sources 0 13 227579482388001398 = some 241200084702956592 :=
  join_receipt_window endpoint_14_68_flag endpoint_14_68_sources 0 12 1 227579482388001398 241200084702956592 241200084702956592 endpoint_14_68_p12 endpoint_14_68_w12
def endpoint_14_68 : CertifiedEndpoint :=
  ⟨⟨14, 68, 2044⟩, 241200084702956592, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_14_68_flag endpoint_14_68_sources 13 227579482388001398 241200084702956592 rfl endpoint_14_68_base endpoint_14_68_p13) (by decide)⟩
private def endpoint_14_69_flag : Flag := ⟨14, 69, 1975⟩
private def endpoint_14_69_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_14_69_base : receiptBase endpoint_14_69_flag endpoint_14_69_sources = some 224239902428845194 := by decide +kernel
private theorem endpoint_14_69_w0 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 2 224239902428845194 = some 234032178686800194 := by decide +kernel
private theorem endpoint_14_69_w2 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 2 2 234032178686800194 = some 234032178686800194 := by decide +kernel
private theorem endpoint_14_69_p4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 4 224239902428845194 = some 234032178686800194 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 2 2 224239902428845194 234032178686800194 234032178686800194 endpoint_14_69_w0 endpoint_14_69_w2
private theorem endpoint_14_69_w4 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 4 2 234032178686800194 = some 234032178686800194 := by decide +kernel
private theorem endpoint_14_69_p6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 6 224239902428845194 = some 234032178686800194 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 4 2 224239902428845194 234032178686800194 234032178686800194 endpoint_14_69_p4 endpoint_14_69_w4
private theorem endpoint_14_69_w6 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 6 2 234032178686800194 = some 234032178686800194 := by decide +kernel
private theorem endpoint_14_69_p8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 8 224239902428845194 = some 234032178686800194 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 6 2 224239902428845194 234032178686800194 234032178686800194 endpoint_14_69_p6 endpoint_14_69_w6
private theorem endpoint_14_69_w8 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 8 2 234032178686800194 = some 234032178686800194 := by decide +kernel
private theorem endpoint_14_69_p10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 10 224239902428845194 = some 234032178686800194 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 8 2 224239902428845194 234032178686800194 234032178686800194 endpoint_14_69_p8 endpoint_14_69_w8
private theorem endpoint_14_69_w10 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 10 2 234032178686800194 = some 234032178686800194 := by decide +kernel
private theorem endpoint_14_69_p12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 12 224239902428845194 = some 234032178686800194 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 10 2 224239902428845194 234032178686800194 234032178686800194 endpoint_14_69_p10 endpoint_14_69_w10
private theorem endpoint_14_69_w12 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 12 1 234032178686800194 = some 234032178686800194 := by decide +kernel
private theorem endpoint_14_69_p13 : receiptWindow endpoint_14_69_flag endpoint_14_69_sources 0 13 224239902428845194 = some 234032178686800194 :=
  join_receipt_window endpoint_14_69_flag endpoint_14_69_sources 0 12 1 224239902428845194 234032178686800194 234032178686800194 endpoint_14_69_p12 endpoint_14_69_w12
def endpoint_14_69 : CertifiedEndpoint :=
  ⟨⟨14, 69, 1975⟩, 234032178686800194, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_14_69_flag endpoint_14_69_sources 13 224239902428845194 234032178686800194 rfl endpoint_14_69_base endpoint_14_69_p13) (by decide)⟩
private def endpoint_14_70_flag : Flag := ⟨14, 70, 1903⟩
private def endpoint_14_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_14_70_base : receiptBase endpoint_14_70_flag endpoint_14_70_sources = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_w0 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 2 220504384029761450 = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_w2 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 2 2 220504384029761450 = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_p4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 4 220504384029761450 = some 220504384029761450 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 2 2 220504384029761450 220504384029761450 220504384029761450 endpoint_14_70_w0 endpoint_14_70_w2
private theorem endpoint_14_70_w4 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 4 2 220504384029761450 = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_p6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 6 220504384029761450 = some 220504384029761450 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 4 2 220504384029761450 220504384029761450 220504384029761450 endpoint_14_70_p4 endpoint_14_70_w4
private theorem endpoint_14_70_w6 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 6 2 220504384029761450 = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_p8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 8 220504384029761450 = some 220504384029761450 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 6 2 220504384029761450 220504384029761450 220504384029761450 endpoint_14_70_p6 endpoint_14_70_w6
private theorem endpoint_14_70_w8 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 8 2 220504384029761450 = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_p10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 10 220504384029761450 = some 220504384029761450 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 8 2 220504384029761450 220504384029761450 220504384029761450 endpoint_14_70_p8 endpoint_14_70_w8
private theorem endpoint_14_70_w10 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 10 2 220504384029761450 = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_p12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 12 220504384029761450 = some 220504384029761450 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 10 2 220504384029761450 220504384029761450 220504384029761450 endpoint_14_70_p10 endpoint_14_70_w10
private theorem endpoint_14_70_w12 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 12 1 220504384029761450 = some 220504384029761450 := by decide +kernel
private theorem endpoint_14_70_p13 : receiptWindow endpoint_14_70_flag endpoint_14_70_sources 0 13 220504384029761450 = some 220504384029761450 :=
  join_receipt_window endpoint_14_70_flag endpoint_14_70_sources 0 12 1 220504384029761450 220504384029761450 220504384029761450 endpoint_14_70_p12 endpoint_14_70_w12
def endpoint_14_70 : CertifiedEndpoint :=
  ⟨⟨14, 70, 1903⟩, 220504384029761450, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_14_70_flag endpoint_14_70_sources 13 220504384029761450 220504384029761450 rfl endpoint_14_70_base endpoint_14_70_p13) (by decide)⟩
private def endpoint_14_71_flag : Flag := ⟨14, 71, 1829⟩
private def endpoint_14_71_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_71_base : receiptBase endpoint_14_71_flag endpoint_14_71_sources = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_w0 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 2 216292870200600802 = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_w2 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 2 2 216292870200600802 = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_p4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 4 216292870200600802 = some 216292870200600802 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 2 2 216292870200600802 216292870200600802 216292870200600802 endpoint_14_71_w0 endpoint_14_71_w2
private theorem endpoint_14_71_w4 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 4 2 216292870200600802 = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_p6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 6 216292870200600802 = some 216292870200600802 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 4 2 216292870200600802 216292870200600802 216292870200600802 endpoint_14_71_p4 endpoint_14_71_w4
private theorem endpoint_14_71_w6 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 6 2 216292870200600802 = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_p8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 8 216292870200600802 = some 216292870200600802 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 6 2 216292870200600802 216292870200600802 216292870200600802 endpoint_14_71_p6 endpoint_14_71_w6
private theorem endpoint_14_71_w8 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 8 2 216292870200600802 = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_p10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 10 216292870200600802 = some 216292870200600802 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 8 2 216292870200600802 216292870200600802 216292870200600802 endpoint_14_71_p8 endpoint_14_71_w8
private theorem endpoint_14_71_w10 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 10 2 216292870200600802 = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_p12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 12 216292870200600802 = some 216292870200600802 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 10 2 216292870200600802 216292870200600802 216292870200600802 endpoint_14_71_p10 endpoint_14_71_w10
private theorem endpoint_14_71_w12 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 12 1 216292870200600802 = some 216292870200600802 := by decide +kernel
private theorem endpoint_14_71_p13 : receiptWindow endpoint_14_71_flag endpoint_14_71_sources 0 13 216292870200600802 = some 216292870200600802 :=
  join_receipt_window endpoint_14_71_flag endpoint_14_71_sources 0 12 1 216292870200600802 216292870200600802 216292870200600802 endpoint_14_71_p12 endpoint_14_71_w12
def endpoint_14_71 : CertifiedEndpoint :=
  ⟨⟨14, 71, 1829⟩, 216292870200600802, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_71_flag endpoint_14_71_sources 13 216292870200600802 216292870200600802 rfl endpoint_14_71_base endpoint_14_71_p13) (by decide)⟩
private def endpoint_14_72_flag : Flag := ⟨14, 72, 1753⟩
private def endpoint_14_72_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_72_base : receiptBase endpoint_14_72_flag endpoint_14_72_sources = some 209974891799787387 := by decide +kernel
private theorem endpoint_14_72_w0 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 2 209974891799787387 = some 213509798659633008 := by decide +kernel
private theorem endpoint_14_72_w2 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 2 2 213509798659633008 = some 213509798659633008 := by decide +kernel
private theorem endpoint_14_72_p4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 4 209974891799787387 = some 213509798659633008 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 2 2 209974891799787387 213509798659633008 213509798659633008 endpoint_14_72_w0 endpoint_14_72_w2
private theorem endpoint_14_72_w4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 4 2 213509798659633008 = some 213509798659633008 := by decide +kernel
private theorem endpoint_14_72_p6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 6 209974891799787387 = some 213509798659633008 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 4 2 209974891799787387 213509798659633008 213509798659633008 endpoint_14_72_p4 endpoint_14_72_w4
private theorem endpoint_14_72_w6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 6 2 213509798659633008 = some 213509798659633008 := by decide +kernel
private theorem endpoint_14_72_p8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 8 209974891799787387 = some 213509798659633008 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 6 2 209974891799787387 213509798659633008 213509798659633008 endpoint_14_72_p6 endpoint_14_72_w6
private theorem endpoint_14_72_w8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 8 2 213509798659633008 = some 213509798659633008 := by decide +kernel
private theorem endpoint_14_72_p10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 10 209974891799787387 = some 213509798659633008 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 8 2 209974891799787387 213509798659633008 213509798659633008 endpoint_14_72_p8 endpoint_14_72_w8
private theorem endpoint_14_72_w10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 10 2 213509798659633008 = some 213509798659633008 := by decide +kernel
private theorem endpoint_14_72_p12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 12 209974891799787387 = some 213509798659633008 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 10 2 209974891799787387 213509798659633008 213509798659633008 endpoint_14_72_p10 endpoint_14_72_w10
private theorem endpoint_14_72_w12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 12 1 213509798659633008 = some 213509798659633008 := by decide +kernel
private theorem endpoint_14_72_p13 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 13 209974891799787387 = some 213509798659633008 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 12 1 209974891799787387 213509798659633008 213509798659633008 endpoint_14_72_p12 endpoint_14_72_w12
def endpoint_14_72 : CertifiedEndpoint :=
  ⟨⟨14, 72, 1753⟩, 213509798659633008, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_72_flag endpoint_14_72_sources 13 209974891799787387 213509798659633008 rfl endpoint_14_72_base endpoint_14_72_p13) (by decide)⟩
private def endpoint_14_73_flag : Flag := ⟨14, 73, 1674⟩
private def endpoint_14_73_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_73_base : receiptBase endpoint_14_73_flag endpoint_14_73_sources = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_w0 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 2 204696326862507350 = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_w2 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 2 2 204696326862507350 = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_p4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 4 204696326862507350 = some 204696326862507350 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 2 2 204696326862507350 204696326862507350 204696326862507350 endpoint_14_73_w0 endpoint_14_73_w2
private theorem endpoint_14_73_w4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 4 2 204696326862507350 = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_p6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 6 204696326862507350 = some 204696326862507350 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 4 2 204696326862507350 204696326862507350 204696326862507350 endpoint_14_73_p4 endpoint_14_73_w4
private theorem endpoint_14_73_w6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 6 2 204696326862507350 = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_p8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 8 204696326862507350 = some 204696326862507350 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 6 2 204696326862507350 204696326862507350 204696326862507350 endpoint_14_73_p6 endpoint_14_73_w6
private theorem endpoint_14_73_w8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 8 2 204696326862507350 = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_p10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 10 204696326862507350 = some 204696326862507350 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 8 2 204696326862507350 204696326862507350 204696326862507350 endpoint_14_73_p8 endpoint_14_73_w8
private theorem endpoint_14_73_w10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 10 2 204696326862507350 = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_p12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 12 204696326862507350 = some 204696326862507350 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 10 2 204696326862507350 204696326862507350 204696326862507350 endpoint_14_73_p10 endpoint_14_73_w10
private theorem endpoint_14_73_w12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 12 1 204696326862507350 = some 204696326862507350 := by decide +kernel
private theorem endpoint_14_73_p13 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 13 204696326862507350 = some 204696326862507350 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 12 1 204696326862507350 204696326862507350 204696326862507350 endpoint_14_73_p12 endpoint_14_73_w12
def endpoint_14_73 : CertifiedEndpoint :=
  ⟨⟨14, 73, 1674⟩, 204696326862507350, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_73_flag endpoint_14_73_sources 13 204696326862507350 204696326862507350 rfl endpoint_14_73_base endpoint_14_73_p13) (by decide)⟩
private def endpoint_14_74_flag : Flag := ⟨14, 74, 1593⟩
private def endpoint_14_74_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_74_base : receiptBase endpoint_14_74_flag endpoint_14_74_sources = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_w0 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 2 197241403824475038 = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_w2 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 2 2 197241403824475038 = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_p4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 4 197241403824475038 = some 197241403824475038 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 2 2 197241403824475038 197241403824475038 197241403824475038 endpoint_14_74_w0 endpoint_14_74_w2
private theorem endpoint_14_74_w4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 4 2 197241403824475038 = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_p6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 6 197241403824475038 = some 197241403824475038 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 4 2 197241403824475038 197241403824475038 197241403824475038 endpoint_14_74_p4 endpoint_14_74_w4
private theorem endpoint_14_74_w6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 6 2 197241403824475038 = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_p8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 8 197241403824475038 = some 197241403824475038 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 6 2 197241403824475038 197241403824475038 197241403824475038 endpoint_14_74_p6 endpoint_14_74_w6
private theorem endpoint_14_74_w8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 8 2 197241403824475038 = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_p10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 10 197241403824475038 = some 197241403824475038 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 8 2 197241403824475038 197241403824475038 197241403824475038 endpoint_14_74_p8 endpoint_14_74_w8
private theorem endpoint_14_74_w10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 10 2 197241403824475038 = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_p12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 12 197241403824475038 = some 197241403824475038 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 10 2 197241403824475038 197241403824475038 197241403824475038 endpoint_14_74_p10 endpoint_14_74_w10
private theorem endpoint_14_74_w12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 12 1 197241403824475038 = some 197241403824475038 := by decide +kernel
private theorem endpoint_14_74_p13 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 13 197241403824475038 = some 197241403824475038 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 12 1 197241403824475038 197241403824475038 197241403824475038 endpoint_14_74_p12 endpoint_14_74_w12
def endpoint_14_74 : CertifiedEndpoint :=
  ⟨⟨14, 74, 1593⟩, 197241403824475038, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_74_flag endpoint_14_74_sources 13 197241403824475038 197241403824475038 rfl endpoint_14_74_base endpoint_14_74_p13) (by decide)⟩
private def endpoint_14_75_flag : Flag := ⟨14, 75, 1509⟩
private def endpoint_14_75_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_75_base : receiptBase endpoint_14_75_flag endpoint_14_75_sources = some 189171465666345116 := by decide +kernel
private theorem endpoint_14_75_w0 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 2 189171465666345116 = some 190480812140224192 := by decide +kernel
private theorem endpoint_14_75_w2 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 2 2 190480812140224192 = some 190480812140224192 := by decide +kernel
private theorem endpoint_14_75_p4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 4 189171465666345116 = some 190480812140224192 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 2 2 189171465666345116 190480812140224192 190480812140224192 endpoint_14_75_w0 endpoint_14_75_w2
private theorem endpoint_14_75_w4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 4 2 190480812140224192 = some 190480812140224192 := by decide +kernel
private theorem endpoint_14_75_p6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 6 189171465666345116 = some 190480812140224192 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 4 2 189171465666345116 190480812140224192 190480812140224192 endpoint_14_75_p4 endpoint_14_75_w4
private theorem endpoint_14_75_w6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 6 2 190480812140224192 = some 190480812140224192 := by decide +kernel
private theorem endpoint_14_75_p8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 8 189171465666345116 = some 190480812140224192 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 6 2 189171465666345116 190480812140224192 190480812140224192 endpoint_14_75_p6 endpoint_14_75_w6
private theorem endpoint_14_75_w8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 8 2 190480812140224192 = some 190480812140224192 := by decide +kernel
private theorem endpoint_14_75_p10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 10 189171465666345116 = some 190480812140224192 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 8 2 189171465666345116 190480812140224192 190480812140224192 endpoint_14_75_p8 endpoint_14_75_w8
private theorem endpoint_14_75_w10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 10 2 190480812140224192 = some 190480812140224192 := by decide +kernel
private theorem endpoint_14_75_p12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 12 189171465666345116 = some 190480812140224192 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 10 2 189171465666345116 190480812140224192 190480812140224192 endpoint_14_75_p10 endpoint_14_75_w10
private theorem endpoint_14_75_w12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 12 1 190480812140224192 = some 190480812140224192 := by decide +kernel
private theorem endpoint_14_75_p13 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 13 189171465666345116 = some 190480812140224192 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 12 1 189171465666345116 190480812140224192 190480812140224192 endpoint_14_75_p12 endpoint_14_75_w12
def endpoint_14_75 : CertifiedEndpoint :=
  ⟨⟨14, 75, 1509⟩, 190480812140224192, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_75_flag endpoint_14_75_sources 13 189171465666345116 190480812140224192 rfl endpoint_14_75_base endpoint_14_75_p13) (by decide)⟩
private def endpoint_14_76_flag : Flag := ⟨14, 76, 1423⟩
private def endpoint_14_76_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_76_base : receiptBase endpoint_14_76_flag endpoint_14_76_sources = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_w0 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 2 182066555952696111 = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_w2 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 2 2 182066555952696111 = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_p4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 4 182066555952696111 = some 182066555952696111 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 2 2 182066555952696111 182066555952696111 182066555952696111 endpoint_14_76_w0 endpoint_14_76_w2
private theorem endpoint_14_76_w4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 4 2 182066555952696111 = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_p6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 6 182066555952696111 = some 182066555952696111 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 4 2 182066555952696111 182066555952696111 182066555952696111 endpoint_14_76_p4 endpoint_14_76_w4
private theorem endpoint_14_76_w6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 6 2 182066555952696111 = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_p8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 8 182066555952696111 = some 182066555952696111 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 6 2 182066555952696111 182066555952696111 182066555952696111 endpoint_14_76_p6 endpoint_14_76_w6
private theorem endpoint_14_76_w8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 8 2 182066555952696111 = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_p10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 10 182066555952696111 = some 182066555952696111 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 8 2 182066555952696111 182066555952696111 182066555952696111 endpoint_14_76_p8 endpoint_14_76_w8
private theorem endpoint_14_76_w10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 10 2 182066555952696111 = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_p12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 12 182066555952696111 = some 182066555952696111 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 10 2 182066555952696111 182066555952696111 182066555952696111 endpoint_14_76_p10 endpoint_14_76_w10
private theorem endpoint_14_76_w12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 12 1 182066555952696111 = some 182066555952696111 := by decide +kernel
private theorem endpoint_14_76_p13 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 13 182066555952696111 = some 182066555952696111 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 12 1 182066555952696111 182066555952696111 182066555952696111 endpoint_14_76_p12 endpoint_14_76_w12
def endpoint_14_76 : CertifiedEndpoint :=
  ⟨⟨14, 76, 1423⟩, 182066555952696111, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_76_flag endpoint_14_76_sources 13 182066555952696111 182066555952696111 rfl endpoint_14_76_base endpoint_14_76_p13) (by decide)⟩
private def endpoint_14_77_flag : Flag := ⟨14, 77, 1334⟩
private def endpoint_14_77_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_77_base : receiptBase endpoint_14_77_flag endpoint_14_77_sources = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_w0 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 2 172812565938200872 = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_w2 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 2 2 172812565938200872 = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_p4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 4 172812565938200872 = some 172812565938200872 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 2 2 172812565938200872 172812565938200872 172812565938200872 endpoint_14_77_w0 endpoint_14_77_w2
private theorem endpoint_14_77_w4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 4 2 172812565938200872 = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_p6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 6 172812565938200872 = some 172812565938200872 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 4 2 172812565938200872 172812565938200872 172812565938200872 endpoint_14_77_p4 endpoint_14_77_w4
private theorem endpoint_14_77_w6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 6 2 172812565938200872 = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_p8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 8 172812565938200872 = some 172812565938200872 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 6 2 172812565938200872 172812565938200872 172812565938200872 endpoint_14_77_p6 endpoint_14_77_w6
private theorem endpoint_14_77_w8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 8 2 172812565938200872 = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_p10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 10 172812565938200872 = some 172812565938200872 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 8 2 172812565938200872 172812565938200872 172812565938200872 endpoint_14_77_p8 endpoint_14_77_w8
private theorem endpoint_14_77_w10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 10 2 172812565938200872 = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_p12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 12 172812565938200872 = some 172812565938200872 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 10 2 172812565938200872 172812565938200872 172812565938200872 endpoint_14_77_p10 endpoint_14_77_w10
private theorem endpoint_14_77_w12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 12 1 172812565938200872 = some 172812565938200872 := by decide +kernel
private theorem endpoint_14_77_p13 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 13 172812565938200872 = some 172812565938200872 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 12 1 172812565938200872 172812565938200872 172812565938200872 endpoint_14_77_p12 endpoint_14_77_w12
def endpoint_14_77 : CertifiedEndpoint :=
  ⟨⟨14, 77, 1334⟩, 172812565938200872, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_77_flag endpoint_14_77_sources 13 172812565938200872 172812565938200872 rfl endpoint_14_77_base endpoint_14_77_p13) (by decide)⟩
private def endpoint_14_78_flag : Flag := ⟨14, 78, 1243⟩
private def endpoint_14_78_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_78_base : receiptBase endpoint_14_78_flag endpoint_14_78_sources = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_w0 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 2 164319603932466799 = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_w2 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 2 2 164319603932466799 = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_p4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 4 164319603932466799 = some 164319603932466799 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 2 2 164319603932466799 164319603932466799 164319603932466799 endpoint_14_78_w0 endpoint_14_78_w2
private theorem endpoint_14_78_w4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 4 2 164319603932466799 = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_p6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 6 164319603932466799 = some 164319603932466799 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 4 2 164319603932466799 164319603932466799 164319603932466799 endpoint_14_78_p4 endpoint_14_78_w4
private theorem endpoint_14_78_w6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 6 2 164319603932466799 = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_p8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 8 164319603932466799 = some 164319603932466799 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 6 2 164319603932466799 164319603932466799 164319603932466799 endpoint_14_78_p6 endpoint_14_78_w6
private theorem endpoint_14_78_w8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 8 2 164319603932466799 = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_p10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 10 164319603932466799 = some 164319603932466799 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 8 2 164319603932466799 164319603932466799 164319603932466799 endpoint_14_78_p8 endpoint_14_78_w8
private theorem endpoint_14_78_w10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 10 2 164319603932466799 = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_p12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 12 164319603932466799 = some 164319603932466799 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 10 2 164319603932466799 164319603932466799 164319603932466799 endpoint_14_78_p10 endpoint_14_78_w10
private theorem endpoint_14_78_w12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 12 1 164319603932466799 = some 164319603932466799 := by decide +kernel
private theorem endpoint_14_78_p13 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 13 164319603932466799 = some 164319603932466799 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 12 1 164319603932466799 164319603932466799 164319603932466799 endpoint_14_78_p12 endpoint_14_78_w12
def endpoint_14_78 : CertifiedEndpoint :=
  ⟨⟨14, 78, 1243⟩, 164319603932466799, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_78_flag endpoint_14_78_sources 13 164319603932466799 164319603932466799 rfl endpoint_14_78_base endpoint_14_78_p13) (by decide)⟩
private def endpoint_14_79_flag : Flag := ⟨14, 79, 1149⟩
private def endpoint_14_79_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_79_base : receiptBase endpoint_14_79_flag endpoint_14_79_sources = some 153738422104567348 := by decide +kernel
private theorem endpoint_14_79_w0 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 2 153738422104567348 = some 154491966402972387 := by decide +kernel
private theorem endpoint_14_79_w2 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 2 2 154491966402972387 = some 154491966402972387 := by decide +kernel
private theorem endpoint_14_79_p4 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 4 153738422104567348 = some 154491966402972387 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 2 2 153738422104567348 154491966402972387 154491966402972387 endpoint_14_79_w0 endpoint_14_79_w2
private theorem endpoint_14_79_w4 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 4 2 154491966402972387 = some 154491966402972387 := by decide +kernel
private theorem endpoint_14_79_p6 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 6 153738422104567348 = some 154491966402972387 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 4 2 153738422104567348 154491966402972387 154491966402972387 endpoint_14_79_p4 endpoint_14_79_w4
private theorem endpoint_14_79_w6 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 6 2 154491966402972387 = some 154491966402972387 := by decide +kernel
private theorem endpoint_14_79_p8 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 8 153738422104567348 = some 154491966402972387 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 6 2 153738422104567348 154491966402972387 154491966402972387 endpoint_14_79_p6 endpoint_14_79_w6
private theorem endpoint_14_79_w8 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 8 2 154491966402972387 = some 154491966402972387 := by decide +kernel
private theorem endpoint_14_79_p10 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 10 153738422104567348 = some 154491966402972387 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 8 2 153738422104567348 154491966402972387 154491966402972387 endpoint_14_79_p8 endpoint_14_79_w8
private theorem endpoint_14_79_w10 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 10 2 154491966402972387 = some 154491966402972387 := by decide +kernel
private theorem endpoint_14_79_p12 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 12 153738422104567348 = some 154491966402972387 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 10 2 153738422104567348 154491966402972387 154491966402972387 endpoint_14_79_p10 endpoint_14_79_w10
private theorem endpoint_14_79_w12 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 12 1 154491966402972387 = some 154491966402972387 := by decide +kernel
private theorem endpoint_14_79_p13 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 13 153738422104567348 = some 154491966402972387 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 12 1 153738422104567348 154491966402972387 154491966402972387 endpoint_14_79_p12 endpoint_14_79_w12
def endpoint_14_79 : CertifiedEndpoint :=
  ⟨⟨14, 79, 1149⟩, 154491966402972387, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_79_flag endpoint_14_79_sources 13 153738422104567348 154491966402972387 rfl endpoint_14_79_base endpoint_14_79_p13) (by decide)⟩
def endpoint_14_80 : CertifiedEndpoint :=
  ⟨⟨14, 80, 1052⟩, 254972626353944060, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock09 : List CertifiedEndpoint := [
  endpoint_13_32, endpoint_13_33, endpoint_13_34, endpoint_13_35, endpoint_13_36, endpoint_13_37, endpoint_13_38,
  endpoint_13_39, endpoint_13_40, endpoint_13_41, endpoint_13_42, endpoint_13_43, endpoint_13_44, endpoint_13_45,
  endpoint_13_46, endpoint_13_47, endpoint_13_48, endpoint_13_49, endpoint_13_50, endpoint_13_51, endpoint_13_52,
  endpoint_13_53, endpoint_13_54, endpoint_13_55, endpoint_13_56, endpoint_13_57, endpoint_13_58, endpoint_13_59,
  endpoint_13_60, endpoint_13_61, endpoint_13_62, endpoint_13_63, endpoint_13_64, endpoint_13_65, endpoint_13_66,
  endpoint_13_67, endpoint_13_68, endpoint_13_69, endpoint_13_70, endpoint_13_71, endpoint_13_72, endpoint_13_73,
  endpoint_13_74, endpoint_13_75, endpoint_13_76, endpoint_13_77, endpoint_13_78, endpoint_13_79, endpoint_13_80,
  endpoint_13_81, endpoint_13_82, endpoint_13_83, endpoint_13_84, endpoint_13_85, endpoint_13_86, endpoint_13_87,
  endpoint_13_88, endpoint_13_89, endpoint_13_90, endpoint_14_14, endpoint_14_15, endpoint_14_16, endpoint_14_17,
  endpoint_14_18, endpoint_14_19, endpoint_14_20, endpoint_14_21, endpoint_14_22, endpoint_14_23, endpoint_14_24,
  endpoint_14_25, endpoint_14_26, endpoint_14_27, endpoint_14_28, endpoint_14_29, endpoint_14_30, endpoint_14_31,
  endpoint_14_32, endpoint_14_33, endpoint_14_34, endpoint_14_35, endpoint_14_36, endpoint_14_37, endpoint_14_38,
  endpoint_14_39, endpoint_14_40, endpoint_14_41, endpoint_14_42, endpoint_14_43, endpoint_14_44, endpoint_14_45,
  endpoint_14_46, endpoint_14_47, endpoint_14_48, endpoint_14_49, endpoint_14_50, endpoint_14_51, endpoint_14_52,
  endpoint_14_53, endpoint_14_54, endpoint_14_55, endpoint_14_56, endpoint_14_57, endpoint_14_58, endpoint_14_59,
  endpoint_14_60, endpoint_14_61, endpoint_14_62, endpoint_14_63, endpoint_14_64, endpoint_14_65, endpoint_14_66,
  endpoint_14_67, endpoint_14_68, endpoint_14_69, endpoint_14_70, endpoint_14_71, endpoint_14_72, endpoint_14_73,
  endpoint_14_74, endpoint_14_75, endpoint_14_76, endpoint_14_77, endpoint_14_78, endpoint_14_79, endpoint_14_80
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
