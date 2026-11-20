import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


private def endpoint_19_34_flag : Flag := ⟨19, 34, 2291⟩
private def endpoint_19_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_34_base : receiptBase endpoint_19_34_flag endpoint_19_34_sources = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_window_0 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_window_2 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 2 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 4 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 2 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_window_0 endpoint_19_34_window_2
private theorem endpoint_19_34_window_4 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 4 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 6 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 4 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_prefix_4 endpoint_19_34_window_4
private theorem endpoint_19_34_window_6 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 6 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 8 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 6 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_prefix_6 endpoint_19_34_window_6
private theorem endpoint_19_34_window_8 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 8 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 10 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 8 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_prefix_8 endpoint_19_34_window_8
private theorem endpoint_19_34_window_10 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 10 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 12 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 10 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_prefix_10 endpoint_19_34_window_10
private theorem endpoint_19_34_window_12 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 12 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 14 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 12 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_prefix_12 endpoint_19_34_window_12
private theorem endpoint_19_34_window_14 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 14 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 16 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 14 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_prefix_14 endpoint_19_34_window_14
private theorem endpoint_19_34_window_16 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 16 2 164952025141752870 = some 164952025141752870 := by decide +kernel
private theorem endpoint_19_34_prefix_18 : receiptWindow endpoint_19_34_flag endpoint_19_34_sources 0 18 164952025141752870 = some 164952025141752870 :=
  join_receipt_window endpoint_19_34_flag endpoint_19_34_sources 0 16 2 164952025141752870 164952025141752870 164952025141752870 endpoint_19_34_prefix_16 endpoint_19_34_window_16

def endpoint_19_34 : CertifiedEndpoint :=
  ⟨⟨19, 34, 2291⟩, 164952025141752870, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_34_flag endpoint_19_34_sources 18 164952025141752870 164952025141752870 rfl endpoint_19_34_base endpoint_19_34_prefix_18) (by decide)⟩
private def endpoint_19_35_flag : Flag := ⟨19, 35, 2250⟩
private def endpoint_19_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_19_35_base : receiptBase endpoint_19_35_flag endpoint_19_35_sources = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_window_0 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_window_2 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 2 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 4 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 2 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_window_0 endpoint_19_35_window_2
private theorem endpoint_19_35_window_4 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 4 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 6 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 4 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_prefix_4 endpoint_19_35_window_4
private theorem endpoint_19_35_window_6 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 6 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 8 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 6 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_prefix_6 endpoint_19_35_window_6
private theorem endpoint_19_35_window_8 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 8 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 10 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 8 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_prefix_8 endpoint_19_35_window_8
private theorem endpoint_19_35_window_10 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 10 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 12 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 10 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_prefix_10 endpoint_19_35_window_10
private theorem endpoint_19_35_window_12 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 12 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 14 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 12 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_prefix_12 endpoint_19_35_window_12
private theorem endpoint_19_35_window_14 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 14 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 16 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 14 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_prefix_14 endpoint_19_35_window_14
private theorem endpoint_19_35_window_16 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 16 2 166080332110598600 = some 166080332110598600 := by decide +kernel
private theorem endpoint_19_35_prefix_18 : receiptWindow endpoint_19_35_flag endpoint_19_35_sources 0 18 166080332110598600 = some 166080332110598600 :=
  join_receipt_window endpoint_19_35_flag endpoint_19_35_sources 0 16 2 166080332110598600 166080332110598600 166080332110598600 endpoint_19_35_prefix_16 endpoint_19_35_window_16

def endpoint_19_35 : CertifiedEndpoint :=
  ⟨⟨19, 35, 2250⟩, 166080332110598600, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_19_35_flag endpoint_19_35_sources 18 166080332110598600 166080332110598600 rfl endpoint_19_35_base endpoint_19_35_prefix_18) (by decide)⟩
private def endpoint_19_36_flag : Flag := ⟨19, 36, 2209⟩
private def endpoint_19_36_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_36_base : receiptBase endpoint_19_36_flag endpoint_19_36_sources = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_window_0 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_window_2 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 2 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 4 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 2 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_window_0 endpoint_19_36_window_2
private theorem endpoint_19_36_window_4 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 4 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 6 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 4 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_prefix_4 endpoint_19_36_window_4
private theorem endpoint_19_36_window_6 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 6 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 8 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 6 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_prefix_6 endpoint_19_36_window_6
private theorem endpoint_19_36_window_8 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 8 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 10 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 8 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_prefix_8 endpoint_19_36_window_8
private theorem endpoint_19_36_window_10 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 10 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 12 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 10 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_prefix_10 endpoint_19_36_window_10
private theorem endpoint_19_36_window_12 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 12 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 14 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 12 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_prefix_12 endpoint_19_36_window_12
private theorem endpoint_19_36_window_14 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 14 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 16 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 14 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_prefix_14 endpoint_19_36_window_14
private theorem endpoint_19_36_window_16 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 16 2 172344092756663392 = some 172344092756663392 := by decide +kernel
private theorem endpoint_19_36_prefix_18 : receiptWindow endpoint_19_36_flag endpoint_19_36_sources 0 18 172344092756663392 = some 172344092756663392 :=
  join_receipt_window endpoint_19_36_flag endpoint_19_36_sources 0 16 2 172344092756663392 172344092756663392 172344092756663392 endpoint_19_36_prefix_16 endpoint_19_36_window_16

def endpoint_19_36 : CertifiedEndpoint :=
  ⟨⟨19, 36, 2209⟩, 172344092756663392, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_36_flag endpoint_19_36_sources 18 172344092756663392 172344092756663392 rfl endpoint_19_36_base endpoint_19_36_prefix_18) (by decide)⟩
private def endpoint_19_37_flag : Flag := ⟨19, 37, 2167⟩
private def endpoint_19_37_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_19_37_base : receiptBase endpoint_19_37_flag endpoint_19_37_sources = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_window_0 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_window_2 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 2 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 4 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 2 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_window_0 endpoint_19_37_window_2
private theorem endpoint_19_37_window_4 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 4 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 6 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 4 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_prefix_4 endpoint_19_37_window_4
private theorem endpoint_19_37_window_6 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 6 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 8 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 6 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_prefix_6 endpoint_19_37_window_6
private theorem endpoint_19_37_window_8 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 8 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 10 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 8 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_prefix_8 endpoint_19_37_window_8
private theorem endpoint_19_37_window_10 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 10 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 12 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 10 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_prefix_10 endpoint_19_37_window_10
private theorem endpoint_19_37_window_12 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 12 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 14 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 12 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_prefix_12 endpoint_19_37_window_12
private theorem endpoint_19_37_window_14 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 14 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 16 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 14 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_prefix_14 endpoint_19_37_window_14
private theorem endpoint_19_37_window_16 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 16 2 173143323803283108 = some 173143323803283108 := by decide +kernel
private theorem endpoint_19_37_prefix_18 : receiptWindow endpoint_19_37_flag endpoint_19_37_sources 0 18 173143323803283108 = some 173143323803283108 :=
  join_receipt_window endpoint_19_37_flag endpoint_19_37_sources 0 16 2 173143323803283108 173143323803283108 173143323803283108 endpoint_19_37_prefix_16 endpoint_19_37_window_16

def endpoint_19_37 : CertifiedEndpoint :=
  ⟨⟨19, 37, 2167⟩, 173143323803283108, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_19_37_flag endpoint_19_37_sources 18 173143323803283108 173143323803283108 rfl endpoint_19_37_base endpoint_19_37_prefix_18) (by decide)⟩
private def endpoint_19_38_flag : Flag := ⟨19, 38, 2124⟩
private def endpoint_19_38_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_38_base : receiptBase endpoint_19_38_flag endpoint_19_38_sources = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_window_0 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_window_2 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 2 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 4 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 2 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_window_0 endpoint_19_38_window_2
private theorem endpoint_19_38_window_4 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 4 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 6 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 4 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_prefix_4 endpoint_19_38_window_4
private theorem endpoint_19_38_window_6 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 6 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 8 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 6 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_prefix_6 endpoint_19_38_window_6
private theorem endpoint_19_38_window_8 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 8 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 10 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 8 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_prefix_8 endpoint_19_38_window_8
private theorem endpoint_19_38_window_10 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 10 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 12 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 10 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_prefix_10 endpoint_19_38_window_10
private theorem endpoint_19_38_window_12 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 12 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 14 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 12 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_prefix_12 endpoint_19_38_window_12
private theorem endpoint_19_38_window_14 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 14 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 16 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 14 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_prefix_14 endpoint_19_38_window_14
private theorem endpoint_19_38_window_16 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 16 2 174187618348319473 = some 174187618348319473 := by decide +kernel
private theorem endpoint_19_38_prefix_18 : receiptWindow endpoint_19_38_flag endpoint_19_38_sources 0 18 174187618348319473 = some 174187618348319473 :=
  join_receipt_window endpoint_19_38_flag endpoint_19_38_sources 0 16 2 174187618348319473 174187618348319473 174187618348319473 endpoint_19_38_prefix_16 endpoint_19_38_window_16

def endpoint_19_38 : CertifiedEndpoint :=
  ⟨⟨19, 38, 2124⟩, 174187618348319473, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_38_flag endpoint_19_38_sources 18 174187618348319473 174187618348319473 rfl endpoint_19_38_base endpoint_19_38_prefix_18) (by decide)⟩
private def endpoint_19_39_flag : Flag := ⟨19, 39, 2080⟩
private def endpoint_19_39_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_39_base : receiptBase endpoint_19_39_flag endpoint_19_39_sources = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_window_0 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_window_2 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 2 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 4 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 2 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_window_0 endpoint_19_39_window_2
private theorem endpoint_19_39_window_4 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 4 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 6 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 4 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_prefix_4 endpoint_19_39_window_4
private theorem endpoint_19_39_window_6 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 6 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 8 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 6 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_prefix_6 endpoint_19_39_window_6
private theorem endpoint_19_39_window_8 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 8 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 10 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 8 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_prefix_8 endpoint_19_39_window_8
private theorem endpoint_19_39_window_10 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 10 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 12 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 10 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_prefix_10 endpoint_19_39_window_10
private theorem endpoint_19_39_window_12 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 12 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 14 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 12 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_prefix_12 endpoint_19_39_window_12
private theorem endpoint_19_39_window_14 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 14 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 16 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 14 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_prefix_14 endpoint_19_39_window_14
private theorem endpoint_19_39_window_16 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 16 2 174526437190392078 = some 174526437190392078 := by decide +kernel
private theorem endpoint_19_39_prefix_18 : receiptWindow endpoint_19_39_flag endpoint_19_39_sources 0 18 174526437190392078 = some 174526437190392078 :=
  join_receipt_window endpoint_19_39_flag endpoint_19_39_sources 0 16 2 174526437190392078 174526437190392078 174526437190392078 endpoint_19_39_prefix_16 endpoint_19_39_window_16

def endpoint_19_39 : CertifiedEndpoint :=
  ⟨⟨19, 39, 2080⟩, 174526437190392078, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_39_flag endpoint_19_39_sources 18 174526437190392078 174526437190392078 rfl endpoint_19_39_base endpoint_19_39_prefix_18) (by decide)⟩
private def endpoint_19_40_flag : Flag := ⟨19, 40, 2036⟩
private def endpoint_19_40_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_40_base : receiptBase endpoint_19_40_flag endpoint_19_40_sources = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_window_0 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_window_2 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 2 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 4 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 2 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_window_0 endpoint_19_40_window_2
private theorem endpoint_19_40_window_4 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 4 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 6 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 4 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_prefix_4 endpoint_19_40_window_4
private theorem endpoint_19_40_window_6 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 6 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 8 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 6 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_prefix_6 endpoint_19_40_window_6
private theorem endpoint_19_40_window_8 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 8 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 10 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 8 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_prefix_8 endpoint_19_40_window_8
private theorem endpoint_19_40_window_10 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 10 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 12 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 10 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_prefix_10 endpoint_19_40_window_10
private theorem endpoint_19_40_window_12 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 12 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 14 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 12 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_prefix_12 endpoint_19_40_window_12
private theorem endpoint_19_40_window_14 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 14 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 16 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 14 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_prefix_14 endpoint_19_40_window_14
private theorem endpoint_19_40_window_16 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 16 2 174705663015984483 = some 174705663015984483 := by decide +kernel
private theorem endpoint_19_40_prefix_18 : receiptWindow endpoint_19_40_flag endpoint_19_40_sources 0 18 174705663015984483 = some 174705663015984483 :=
  join_receipt_window endpoint_19_40_flag endpoint_19_40_sources 0 16 2 174705663015984483 174705663015984483 174705663015984483 endpoint_19_40_prefix_16 endpoint_19_40_window_16

def endpoint_19_40 : CertifiedEndpoint :=
  ⟨⟨19, 40, 2036⟩, 174705663015984483, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_40_flag endpoint_19_40_sources 18 174705663015984483 174705663015984483 rfl endpoint_19_40_base endpoint_19_40_prefix_18) (by decide)⟩
private def endpoint_19_41_flag : Flag := ⟨19, 41, 1991⟩
private def endpoint_19_41_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_41_base : receiptBase endpoint_19_41_flag endpoint_19_41_sources = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_window_0 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_window_2 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 2 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 4 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 2 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_window_0 endpoint_19_41_window_2
private theorem endpoint_19_41_window_4 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 4 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 6 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 4 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_prefix_4 endpoint_19_41_window_4
private theorem endpoint_19_41_window_6 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 6 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 8 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 6 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_prefix_6 endpoint_19_41_window_6
private theorem endpoint_19_41_window_8 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 8 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 10 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 8 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_prefix_8 endpoint_19_41_window_8
private theorem endpoint_19_41_window_10 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 10 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 12 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 10 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_prefix_10 endpoint_19_41_window_10
private theorem endpoint_19_41_window_12 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 12 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 14 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 12 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_prefix_12 endpoint_19_41_window_12
private theorem endpoint_19_41_window_14 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 14 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 16 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 14 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_prefix_14 endpoint_19_41_window_14
private theorem endpoint_19_41_window_16 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 16 2 174639898749940728 = some 174639898749940728 := by decide +kernel
private theorem endpoint_19_41_prefix_18 : receiptWindow endpoint_19_41_flag endpoint_19_41_sources 0 18 174639898749940728 = some 174639898749940728 :=
  join_receipt_window endpoint_19_41_flag endpoint_19_41_sources 0 16 2 174639898749940728 174639898749940728 174639898749940728 endpoint_19_41_prefix_16 endpoint_19_41_window_16

def endpoint_19_41 : CertifiedEndpoint :=
  ⟨⟨19, 41, 1991⟩, 174639898749940728, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_41_flag endpoint_19_41_sources 18 174639898749940728 174639898749940728 rfl endpoint_19_41_base endpoint_19_41_prefix_18) (by decide)⟩
private def endpoint_19_42_flag : Flag := ⟨19, 42, 1945⟩
private def endpoint_19_42_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_42_base : receiptBase endpoint_19_42_flag endpoint_19_42_sources = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_window_0 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_window_2 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 2 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 4 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 2 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_window_0 endpoint_19_42_window_2
private theorem endpoint_19_42_window_4 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 4 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 6 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 4 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_prefix_4 endpoint_19_42_window_4
private theorem endpoint_19_42_window_6 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 6 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 8 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 6 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_prefix_6 endpoint_19_42_window_6
private theorem endpoint_19_42_window_8 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 8 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 10 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 8 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_prefix_8 endpoint_19_42_window_8
private theorem endpoint_19_42_window_10 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 10 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 12 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 10 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_prefix_10 endpoint_19_42_window_10
private theorem endpoint_19_42_window_12 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 12 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 14 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 12 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_prefix_12 endpoint_19_42_window_12
private theorem endpoint_19_42_window_14 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 14 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 16 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 14 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_prefix_14 endpoint_19_42_window_14
private theorem endpoint_19_42_window_16 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 16 2 174323764586953319 = some 174323764586953319 := by decide +kernel
private theorem endpoint_19_42_prefix_18 : receiptWindow endpoint_19_42_flag endpoint_19_42_sources 0 18 174323764586953319 = some 174323764586953319 :=
  join_receipt_window endpoint_19_42_flag endpoint_19_42_sources 0 16 2 174323764586953319 174323764586953319 174323764586953319 endpoint_19_42_prefix_16 endpoint_19_42_window_16

def endpoint_19_42 : CertifiedEndpoint :=
  ⟨⟨19, 42, 1945⟩, 174323764586953319, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_42_flag endpoint_19_42_sources 18 174323764586953319 174323764586953319 rfl endpoint_19_42_base endpoint_19_42_prefix_18) (by decide)⟩
private def endpoint_19_43_flag : Flag := ⟨19, 43, 1899⟩
private def endpoint_19_43_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_43_base : receiptBase endpoint_19_43_flag endpoint_19_43_sources = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_window_0 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_window_2 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 2 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 4 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 2 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_window_0 endpoint_19_43_window_2
private theorem endpoint_19_43_window_4 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 4 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 6 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 4 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_prefix_4 endpoint_19_43_window_4
private theorem endpoint_19_43_window_6 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 6 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 8 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 6 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_prefix_6 endpoint_19_43_window_6
private theorem endpoint_19_43_window_8 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 8 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 10 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 8 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_prefix_8 endpoint_19_43_window_8
private theorem endpoint_19_43_window_10 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 10 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 12 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 10 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_prefix_10 endpoint_19_43_window_10
private theorem endpoint_19_43_window_12 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 12 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 14 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 12 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_prefix_12 endpoint_19_43_window_12
private theorem endpoint_19_43_window_14 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 14 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 16 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 14 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_prefix_14 endpoint_19_43_window_14
private theorem endpoint_19_43_window_16 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 16 2 173840864333742385 = some 173840864333742385 := by decide +kernel
private theorem endpoint_19_43_prefix_18 : receiptWindow endpoint_19_43_flag endpoint_19_43_sources 0 18 173840864333742385 = some 173840864333742385 :=
  join_receipt_window endpoint_19_43_flag endpoint_19_43_sources 0 16 2 173840864333742385 173840864333742385 173840864333742385 endpoint_19_43_prefix_16 endpoint_19_43_window_16

def endpoint_19_43 : CertifiedEndpoint :=
  ⟨⟨19, 43, 1899⟩, 173840864333742385, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_43_flag endpoint_19_43_sources 18 173840864333742385 173840864333742385 rfl endpoint_19_43_base endpoint_19_43_prefix_18) (by decide)⟩
private def endpoint_19_44_flag : Flag := ⟨19, 44, 1851⟩
private def endpoint_19_44_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_19_44_base : receiptBase endpoint_19_44_flag endpoint_19_44_sources = some 173009644229381018 := by decide +kernel
private theorem endpoint_19_44_window_0 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 2 173009644229381018 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_window_2 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 2 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 4 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 2 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_window_0 endpoint_19_44_window_2
private theorem endpoint_19_44_window_4 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 4 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 6 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 4 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_prefix_4 endpoint_19_44_window_4
private theorem endpoint_19_44_window_6 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 6 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 8 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 6 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_prefix_6 endpoint_19_44_window_6
private theorem endpoint_19_44_window_8 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 8 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 10 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 8 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_prefix_8 endpoint_19_44_window_8
private theorem endpoint_19_44_window_10 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 10 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 12 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 10 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_prefix_10 endpoint_19_44_window_10
private theorem endpoint_19_44_window_12 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 12 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 14 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 12 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_prefix_12 endpoint_19_44_window_12
private theorem endpoint_19_44_window_14 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 14 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 16 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 14 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_prefix_14 endpoint_19_44_window_14
private theorem endpoint_19_44_window_16 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 16 2 175189645648999476 = some 175189645648999476 := by decide +kernel
private theorem endpoint_19_44_prefix_18 : receiptWindow endpoint_19_44_flag endpoint_19_44_sources 0 18 173009644229381018 = some 175189645648999476 :=
  join_receipt_window endpoint_19_44_flag endpoint_19_44_sources 0 16 2 173009644229381018 175189645648999476 175189645648999476 endpoint_19_44_prefix_16 endpoint_19_44_window_16

def endpoint_19_44 : CertifiedEndpoint :=
  ⟨⟨19, 44, 1851⟩, 175189645648999476, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_19_44_flag endpoint_19_44_sources 18 173009644229381018 175189645648999476 rfl endpoint_19_44_base endpoint_19_44_prefix_18) (by decide)⟩
private def endpoint_19_45_flag : Flag := ⟨19, 45, 1803⟩
private def endpoint_19_45_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_45_base : receiptBase endpoint_19_45_flag endpoint_19_45_sources = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_window_0 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_window_2 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 2 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 4 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 2 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_window_0 endpoint_19_45_window_2
private theorem endpoint_19_45_window_4 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 4 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 6 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 4 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_prefix_4 endpoint_19_45_window_4
private theorem endpoint_19_45_window_6 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 6 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 8 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 6 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_prefix_6 endpoint_19_45_window_6
private theorem endpoint_19_45_window_8 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 8 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 10 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 8 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_prefix_8 endpoint_19_45_window_8
private theorem endpoint_19_45_window_10 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 10 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 12 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 10 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_prefix_10 endpoint_19_45_window_10
private theorem endpoint_19_45_window_12 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 12 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 14 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 12 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_prefix_12 endpoint_19_45_window_12
private theorem endpoint_19_45_window_14 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 14 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 16 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 14 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_prefix_14 endpoint_19_45_window_14
private theorem endpoint_19_45_window_16 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 16 2 173777683431071682 = some 173777683431071682 := by decide +kernel
private theorem endpoint_19_45_prefix_18 : receiptWindow endpoint_19_45_flag endpoint_19_45_sources 0 18 173777683431071682 = some 173777683431071682 :=
  join_receipt_window endpoint_19_45_flag endpoint_19_45_sources 0 16 2 173777683431071682 173777683431071682 173777683431071682 endpoint_19_45_prefix_16 endpoint_19_45_window_16

def endpoint_19_45 : CertifiedEndpoint :=
  ⟨⟨19, 45, 1803⟩, 173777683431071682, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_45_flag endpoint_19_45_sources 18 173777683431071682 173777683431071682 rfl endpoint_19_45_base endpoint_19_45_prefix_18) (by decide)⟩
private def endpoint_19_46_flag : Flag := ⟨19, 46, 1754⟩
private def endpoint_19_46_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_46_base : receiptBase endpoint_19_46_flag endpoint_19_46_sources = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_window_0 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_window_2 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 2 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 4 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 2 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_window_0 endpoint_19_46_window_2
private theorem endpoint_19_46_window_4 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 4 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 6 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 4 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_prefix_4 endpoint_19_46_window_4
private theorem endpoint_19_46_window_6 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 6 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 8 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 6 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_prefix_6 endpoint_19_46_window_6
private theorem endpoint_19_46_window_8 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 8 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 10 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 8 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_prefix_8 endpoint_19_46_window_8
private theorem endpoint_19_46_window_10 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 10 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 12 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 10 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_prefix_10 endpoint_19_46_window_10
private theorem endpoint_19_46_window_12 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 12 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 14 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 12 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_prefix_12 endpoint_19_46_window_12
private theorem endpoint_19_46_window_14 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 14 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 16 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 14 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_prefix_14 endpoint_19_46_window_14
private theorem endpoint_19_46_window_16 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 16 2 172439000405861333 = some 172439000405861333 := by decide +kernel
private theorem endpoint_19_46_prefix_18 : receiptWindow endpoint_19_46_flag endpoint_19_46_sources 0 18 172439000405861333 = some 172439000405861333 :=
  join_receipt_window endpoint_19_46_flag endpoint_19_46_sources 0 16 2 172439000405861333 172439000405861333 172439000405861333 endpoint_19_46_prefix_16 endpoint_19_46_window_16

def endpoint_19_46 : CertifiedEndpoint :=
  ⟨⟨19, 46, 1754⟩, 172439000405861333, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_46_flag endpoint_19_46_sources 18 172439000405861333 172439000405861333 rfl endpoint_19_46_base endpoint_19_46_prefix_18) (by decide)⟩
private def endpoint_19_47_flag : Flag := ⟨19, 47, 1704⟩
private def endpoint_19_47_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_47_base : receiptBase endpoint_19_47_flag endpoint_19_47_sources = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_window_0 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_window_2 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 2 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 4 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 2 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_window_0 endpoint_19_47_window_2
private theorem endpoint_19_47_window_4 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 4 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 6 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 4 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_prefix_4 endpoint_19_47_window_4
private theorem endpoint_19_47_window_6 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 6 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 8 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 6 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_prefix_6 endpoint_19_47_window_6
private theorem endpoint_19_47_window_8 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 8 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 10 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 8 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_prefix_8 endpoint_19_47_window_8
private theorem endpoint_19_47_window_10 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 10 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 12 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 10 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_prefix_10 endpoint_19_47_window_10
private theorem endpoint_19_47_window_12 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 12 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 14 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 12 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_prefix_12 endpoint_19_47_window_12
private theorem endpoint_19_47_window_14 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 14 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 16 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 14 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_prefix_14 endpoint_19_47_window_14
private theorem endpoint_19_47_window_16 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 16 2 170821765170575718 = some 170821765170575718 := by decide +kernel
private theorem endpoint_19_47_prefix_18 : receiptWindow endpoint_19_47_flag endpoint_19_47_sources 0 18 170821765170575718 = some 170821765170575718 :=
  join_receipt_window endpoint_19_47_flag endpoint_19_47_sources 0 16 2 170821765170575718 170821765170575718 170821765170575718 endpoint_19_47_prefix_16 endpoint_19_47_window_16

def endpoint_19_47 : CertifiedEndpoint :=
  ⟨⟨19, 47, 1704⟩, 170821765170575718, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_47_flag endpoint_19_47_sources 18 170821765170575718 170821765170575718 rfl endpoint_19_47_base endpoint_19_47_prefix_18) (by decide)⟩
private def endpoint_19_48_flag : Flag := ⟨19, 48, 1653⟩
private def endpoint_19_48_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_19_48_base : receiptBase endpoint_19_48_flag endpoint_19_48_sources = some 168920503416809653 := by decide +kernel
private theorem endpoint_19_48_window_0 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 2 168920503416809653 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_window_2 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 2 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 4 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 2 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_window_0 endpoint_19_48_window_2
private theorem endpoint_19_48_window_4 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 4 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 6 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 4 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_prefix_4 endpoint_19_48_window_4
private theorem endpoint_19_48_window_6 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 6 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 8 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 6 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_prefix_6 endpoint_19_48_window_6
private theorem endpoint_19_48_window_8 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 8 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 10 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 8 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_prefix_8 endpoint_19_48_window_8
private theorem endpoint_19_48_window_10 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 10 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 12 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 10 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_prefix_10 endpoint_19_48_window_10
private theorem endpoint_19_48_window_12 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 12 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 14 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 12 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_prefix_12 endpoint_19_48_window_12
private theorem endpoint_19_48_window_14 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 14 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 16 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 14 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_prefix_14 endpoint_19_48_window_14
private theorem endpoint_19_48_window_16 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 16 2 171188828099859194 = some 171188828099859194 := by decide +kernel
private theorem endpoint_19_48_prefix_18 : receiptWindow endpoint_19_48_flag endpoint_19_48_sources 0 18 168920503416809653 = some 171188828099859194 :=
  join_receipt_window endpoint_19_48_flag endpoint_19_48_sources 0 16 2 168920503416809653 171188828099859194 171188828099859194 endpoint_19_48_prefix_16 endpoint_19_48_window_16

def endpoint_19_48 : CertifiedEndpoint :=
  ⟨⟨19, 48, 1653⟩, 171188828099859194, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_19_48_flag endpoint_19_48_sources 18 168920503416809653 171188828099859194 rfl endpoint_19_48_base endpoint_19_48_prefix_18) (by decide)⟩
private def endpoint_19_49_flag : Flag := ⟨19, 49, 1601⟩
private def endpoint_19_49_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_49_base : receiptBase endpoint_19_49_flag endpoint_19_49_sources = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_window_0 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_window_2 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 2 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 4 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 2 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_window_0 endpoint_19_49_window_2
private theorem endpoint_19_49_window_4 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 4 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 6 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 4 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_prefix_4 endpoint_19_49_window_4
private theorem endpoint_19_49_window_6 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 6 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 8 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 6 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_prefix_6 endpoint_19_49_window_6
private theorem endpoint_19_49_window_8 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 8 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 10 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 8 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_prefix_8 endpoint_19_49_window_8
private theorem endpoint_19_49_window_10 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 10 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 12 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 10 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_prefix_10 endpoint_19_49_window_10
private theorem endpoint_19_49_window_12 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 12 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 14 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 12 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_prefix_12 endpoint_19_49_window_12
private theorem endpoint_19_49_window_14 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 14 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 16 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 14 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_prefix_14 endpoint_19_49_window_14
private theorem endpoint_19_49_window_16 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 16 2 168462683249649058 = some 168462683249649058 := by decide +kernel
private theorem endpoint_19_49_prefix_18 : receiptWindow endpoint_19_49_flag endpoint_19_49_sources 0 18 168462683249649058 = some 168462683249649058 :=
  join_receipt_window endpoint_19_49_flag endpoint_19_49_sources 0 16 2 168462683249649058 168462683249649058 168462683249649058 endpoint_19_49_prefix_16 endpoint_19_49_window_16

def endpoint_19_49 : CertifiedEndpoint :=
  ⟨⟨19, 49, 1601⟩, 168462683249649058, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_49_flag endpoint_19_49_sources 18 168462683249649058 168462683249649058 rfl endpoint_19_49_base endpoint_19_49_prefix_18) (by decide)⟩
private def endpoint_19_50_flag : Flag := ⟨19, 50, 1549⟩
private def endpoint_19_50_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_50_base : receiptBase endpoint_19_50_flag endpoint_19_50_sources = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_window_0 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_window_2 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 2 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 4 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 2 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_window_0 endpoint_19_50_window_2
private theorem endpoint_19_50_window_4 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 4 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 6 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 4 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_prefix_4 endpoint_19_50_window_4
private theorem endpoint_19_50_window_6 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 6 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 8 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 6 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_prefix_6 endpoint_19_50_window_6
private theorem endpoint_19_50_window_8 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 8 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 10 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 8 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_prefix_8 endpoint_19_50_window_8
private theorem endpoint_19_50_window_10 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 10 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 12 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 10 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_prefix_10 endpoint_19_50_window_10
private theorem endpoint_19_50_window_12 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 12 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 14 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 12 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_prefix_12 endpoint_19_50_window_12
private theorem endpoint_19_50_window_14 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 14 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 16 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 14 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_prefix_14 endpoint_19_50_window_14
private theorem endpoint_19_50_window_16 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 16 2 165944184709345251 = some 165944184709345251 := by decide +kernel
private theorem endpoint_19_50_prefix_18 : receiptWindow endpoint_19_50_flag endpoint_19_50_sources 0 18 165944184709345251 = some 165944184709345251 :=
  join_receipt_window endpoint_19_50_flag endpoint_19_50_sources 0 16 2 165944184709345251 165944184709345251 165944184709345251 endpoint_19_50_prefix_16 endpoint_19_50_window_16

def endpoint_19_50 : CertifiedEndpoint :=
  ⟨⟨19, 50, 1549⟩, 165944184709345251, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_50_flag endpoint_19_50_sources 18 165944184709345251 165944184709345251 rfl endpoint_19_50_base endpoint_19_50_prefix_18) (by decide)⟩
private def endpoint_19_51_flag : Flag := ⟨19, 51, 1495⟩
private def endpoint_19_51_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_51_base : receiptBase endpoint_19_51_flag endpoint_19_51_sources = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_window_0 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_window_2 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 2 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 4 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 2 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_window_0 endpoint_19_51_window_2
private theorem endpoint_19_51_window_4 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 4 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 6 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 4 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_prefix_4 endpoint_19_51_window_4
private theorem endpoint_19_51_window_6 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 6 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 8 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 6 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_prefix_6 endpoint_19_51_window_6
private theorem endpoint_19_51_window_8 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 8 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 10 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 8 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_prefix_8 endpoint_19_51_window_8
private theorem endpoint_19_51_window_10 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 10 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 12 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 10 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_prefix_10 endpoint_19_51_window_10
private theorem endpoint_19_51_window_12 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 12 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 14 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 12 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_prefix_12 endpoint_19_51_window_12
private theorem endpoint_19_51_window_14 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 14 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 16 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 14 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_prefix_14 endpoint_19_51_window_14
private theorem endpoint_19_51_window_16 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 16 2 163018481593984018 = some 163018481593984018 := by decide +kernel
private theorem endpoint_19_51_prefix_18 : receiptWindow endpoint_19_51_flag endpoint_19_51_sources 0 18 163018481593984018 = some 163018481593984018 :=
  join_receipt_window endpoint_19_51_flag endpoint_19_51_sources 0 16 2 163018481593984018 163018481593984018 163018481593984018 endpoint_19_51_prefix_16 endpoint_19_51_window_16

def endpoint_19_51 : CertifiedEndpoint :=
  ⟨⟨19, 51, 1495⟩, 163018481593984018, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_51_flag endpoint_19_51_sources 18 163018481593984018 163018481593984018 rfl endpoint_19_51_base endpoint_19_51_prefix_18) (by decide)⟩
private def endpoint_19_52_flag : Flag := ⟨19, 52, 1440⟩
private def endpoint_19_52_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_52_base : receiptBase endpoint_19_52_flag endpoint_19_52_sources = some 159783798518847243 := by decide +kernel
private theorem endpoint_19_52_window_0 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 2 159783798518847243 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_window_2 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 2 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 4 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 2 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_window_0 endpoint_19_52_window_2
private theorem endpoint_19_52_window_4 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 4 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 6 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 4 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_prefix_4 endpoint_19_52_window_4
private theorem endpoint_19_52_window_6 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 6 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 8 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 6 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_prefix_6 endpoint_19_52_window_6
private theorem endpoint_19_52_window_8 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 8 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 10 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 8 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_prefix_8 endpoint_19_52_window_8
private theorem endpoint_19_52_window_10 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 10 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 12 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 10 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_prefix_10 endpoint_19_52_window_10
private theorem endpoint_19_52_window_12 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 12 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 14 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 12 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_prefix_12 endpoint_19_52_window_12
private theorem endpoint_19_52_window_14 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 14 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 16 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 14 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_prefix_14 endpoint_19_52_window_14
private theorem endpoint_19_52_window_16 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 16 2 162853086509843410 = some 162853086509843410 := by decide +kernel
private theorem endpoint_19_52_prefix_18 : receiptWindow endpoint_19_52_flag endpoint_19_52_sources 0 18 159783798518847243 = some 162853086509843410 :=
  join_receipt_window endpoint_19_52_flag endpoint_19_52_sources 0 16 2 159783798518847243 162853086509843410 162853086509843410 endpoint_19_52_prefix_16 endpoint_19_52_window_16

def endpoint_19_52 : CertifiedEndpoint :=
  ⟨⟨19, 52, 1440⟩, 162853086509843410, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_52_flag endpoint_19_52_sources 18 159783798518847243 162853086509843410 rfl endpoint_19_52_base endpoint_19_52_prefix_18) (by decide)⟩
private def endpoint_19_53_flag : Flag := ⟨19, 53, 1385⟩
private def endpoint_19_53_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_53_base : receiptBase endpoint_19_53_flag endpoint_19_53_sources = some 156345690719894851 := by decide +kernel
private theorem endpoint_19_53_window_0 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 2 156345690719894851 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_window_2 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 2 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 4 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 2 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_window_0 endpoint_19_53_window_2
private theorem endpoint_19_53_window_4 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 4 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 6 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 4 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_prefix_4 endpoint_19_53_window_4
private theorem endpoint_19_53_window_6 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 6 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 8 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 6 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_prefix_6 endpoint_19_53_window_6
private theorem endpoint_19_53_window_8 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 8 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 10 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 8 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_prefix_8 endpoint_19_53_window_8
private theorem endpoint_19_53_window_10 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 10 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 12 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 10 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_prefix_10 endpoint_19_53_window_10
private theorem endpoint_19_53_window_12 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 12 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 14 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 12 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_prefix_12 endpoint_19_53_window_12
private theorem endpoint_19_53_window_14 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 14 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 16 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 14 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_prefix_14 endpoint_19_53_window_14
private theorem endpoint_19_53_window_16 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 16 2 163226756119679215 = some 163226756119679215 := by decide +kernel
private theorem endpoint_19_53_prefix_18 : receiptWindow endpoint_19_53_flag endpoint_19_53_sources 0 18 156345690719894851 = some 163226756119679215 :=
  join_receipt_window endpoint_19_53_flag endpoint_19_53_sources 0 16 2 156345690719894851 163226756119679215 163226756119679215 endpoint_19_53_prefix_16 endpoint_19_53_window_16

def endpoint_19_53 : CertifiedEndpoint :=
  ⟨⟨19, 53, 1385⟩, 163226756119679215, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_53_flag endpoint_19_53_sources 18 156345690719894851 163226756119679215 rfl endpoint_19_53_base endpoint_19_53_prefix_18) (by decide)⟩
private def endpoint_19_54_flag : Flag := ⟨19, 54, 1328⟩
private def endpoint_19_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_19_54_base : receiptBase endpoint_19_54_flag endpoint_19_54_sources = some 152478386483850912 := by decide +kernel
private theorem endpoint_19_54_window_0 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 2 152478386483850912 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_window_2 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 2 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 4 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 2 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_window_0 endpoint_19_54_window_2
private theorem endpoint_19_54_window_4 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 4 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 6 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 4 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_prefix_4 endpoint_19_54_window_4
private theorem endpoint_19_54_window_6 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 6 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 8 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 6 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_prefix_6 endpoint_19_54_window_6
private theorem endpoint_19_54_window_8 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 8 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 10 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 8 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_prefix_8 endpoint_19_54_window_8
private theorem endpoint_19_54_window_10 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 10 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 12 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 10 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_prefix_10 endpoint_19_54_window_10
private theorem endpoint_19_54_window_12 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 12 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 14 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 12 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_prefix_12 endpoint_19_54_window_12
private theorem endpoint_19_54_window_14 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 14 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 16 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 14 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_prefix_14 endpoint_19_54_window_14
private theorem endpoint_19_54_window_16 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 16 2 163303842183459240 = some 163303842183459240 := by decide +kernel
private theorem endpoint_19_54_prefix_18 : receiptWindow endpoint_19_54_flag endpoint_19_54_sources 0 18 152478386483850912 = some 163303842183459240 :=
  join_receipt_window endpoint_19_54_flag endpoint_19_54_sources 0 16 2 152478386483850912 163303842183459240 163303842183459240 endpoint_19_54_prefix_16 endpoint_19_54_window_16

def endpoint_19_54 : CertifiedEndpoint :=
  ⟨⟨19, 54, 1328⟩, 163303842183459240, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_19_54_flag endpoint_19_54_sources 18 152478386483850912 163303842183459240 rfl endpoint_19_54_base endpoint_19_54_prefix_18) (by decide)⟩
private def endpoint_19_55_flag : Flag := ⟨19, 55, 1270⟩
private def endpoint_19_55_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_19_55_base : receiptBase endpoint_19_55_flag endpoint_19_55_sources = some 148538675084059291 := by decide +kernel
private theorem endpoint_19_55_window_0 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 2 148538675084059291 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_window_2 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 2 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 4 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 2 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_window_0 endpoint_19_55_window_2
private theorem endpoint_19_55_window_4 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 4 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 6 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 4 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_prefix_4 endpoint_19_55_window_4
private theorem endpoint_19_55_window_6 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 6 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 8 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 6 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_prefix_6 endpoint_19_55_window_6
private theorem endpoint_19_55_window_8 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 8 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 10 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 8 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_prefix_8 endpoint_19_55_window_8
private theorem endpoint_19_55_window_10 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 10 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 12 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 10 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_prefix_10 endpoint_19_55_window_10
private theorem endpoint_19_55_window_12 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 12 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 14 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 12 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_prefix_12 endpoint_19_55_window_12
private theorem endpoint_19_55_window_14 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 14 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 16 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 14 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_prefix_14 endpoint_19_55_window_14
private theorem endpoint_19_55_window_16 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 16 2 160292984555255633 = some 160292984555255633 := by decide +kernel
private theorem endpoint_19_55_prefix_18 : receiptWindow endpoint_19_55_flag endpoint_19_55_sources 0 18 148538675084059291 = some 160292984555255633 :=
  join_receipt_window endpoint_19_55_flag endpoint_19_55_sources 0 16 2 148538675084059291 160292984555255633 160292984555255633 endpoint_19_55_prefix_16 endpoint_19_55_window_16

def endpoint_19_55 : CertifiedEndpoint :=
  ⟨⟨19, 55, 1270⟩, 160292984555255633, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_19_55_flag endpoint_19_55_sources 18 148538675084059291 160292984555255633 rfl endpoint_19_55_base endpoint_19_55_prefix_18) (by decide)⟩
private def endpoint_19_56_flag : Flag := ⟨19, 56, 1211⟩
private def endpoint_19_56_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_19_56_base : receiptBase endpoint_19_56_flag endpoint_19_56_sources = some 145262369755742892 := by decide +kernel
private theorem endpoint_19_56_window_0 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 2 145262369755742892 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_window_2 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 2 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 4 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 2 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_window_0 endpoint_19_56_window_2
private theorem endpoint_19_56_window_4 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 4 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 6 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 4 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_prefix_4 endpoint_19_56_window_4
private theorem endpoint_19_56_window_6 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 6 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 8 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 6 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_prefix_6 endpoint_19_56_window_6
private theorem endpoint_19_56_window_8 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 8 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 10 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 8 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_prefix_8 endpoint_19_56_window_8
private theorem endpoint_19_56_window_10 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 10 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 12 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 10 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_prefix_10 endpoint_19_56_window_10
private theorem endpoint_19_56_window_12 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 12 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 14 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 12 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_prefix_12 endpoint_19_56_window_12
private theorem endpoint_19_56_window_14 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 14 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 16 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 14 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_prefix_14 endpoint_19_56_window_14
private theorem endpoint_19_56_window_16 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 16 2 153028053433699750 = some 153028053433699750 := by decide +kernel
private theorem endpoint_19_56_prefix_18 : receiptWindow endpoint_19_56_flag endpoint_19_56_sources 0 18 145262369755742892 = some 153028053433699750 :=
  join_receipt_window endpoint_19_56_flag endpoint_19_56_sources 0 16 2 145262369755742892 153028053433699750 153028053433699750 endpoint_19_56_prefix_16 endpoint_19_56_window_16

def endpoint_19_56 : CertifiedEndpoint :=
  ⟨⟨19, 56, 1211⟩, 153028053433699750, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_19_56_flag endpoint_19_56_sources 18 145262369755742892 153028053433699750 rfl endpoint_19_56_base endpoint_19_56_prefix_18) (by decide)⟩
def endpoint_19_57 : CertifiedEndpoint :=
  ⟨⟨19, 57, 1151⟩, 250932012373992032, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_58 : CertifiedEndpoint :=
  ⟨⟨19, 58, 1090⟩, 242169689343762718, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_59 : CertifiedEndpoint :=
  ⟨⟨19, 59, 1027⟩, 232351826066901120, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_60 : CertifiedEndpoint :=
  ⟨⟨19, 60, 964⟩, 221927395297073556, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_61 : CertifiedEndpoint :=
  ⟨⟨19, 61, 898⟩, 210165624439878253, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_62 : CertifiedEndpoint :=
  ⟨⟨19, 62, 832⟩, 197768629357765836, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_63 : CertifiedEndpoint :=
  ⟨⟨19, 63, 764⟩, 184230123833167691, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_64 : CertifiedEndpoint :=
  ⟨⟨19, 64, 695⟩, 169779370364908835, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_65 : CertifiedEndpoint :=
  ⟨⟨19, 65, 625⟩, 154402040587013694, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_66 : CertifiedEndpoint :=
  ⟨⟨19, 66, 553⟩, 137816334658746813, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_67 : CertifiedEndpoint :=
  ⟨⟨19, 67, 479⟩, 119993595848157044, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_68 : CertifiedEndpoint :=
  ⟨⟨19, 68, 404⟩, 101182191142036836, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_69 : CertifiedEndpoint :=
  ⟨⟨19, 69, 327⟩, 81085992333675160, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_70 : CertifiedEndpoint :=
  ⟨⟨19, 70, 248⟩, 59676342691120868, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_71 : CertifiedEndpoint :=
  ⟨⟨19, 71, 168⟩, 37215937567141983, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_19_72 : CertifiedEndpoint :=
  ⟨⟨19, 72, 86⟩, 13394320389051902, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_20 : CertifiedEndpoint :=
  ⟨⟨20, 20, 2504⟩, 135885066760202464, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_21 : CertifiedEndpoint :=
  ⟨⟨20, 21, 2469⟩, 138031580157461634, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_22 : CertifiedEndpoint :=
  ⟨⟨20, 22, 2432⟩, 139946245346187412, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_23 : CertifiedEndpoint :=
  ⟨⟨20, 23, 2396⟩, 149809716765181841, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_24 : CertifiedEndpoint :=
  ⟨⟨20, 24, 2359⟩, 159237753561366349, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_25 : CertifiedEndpoint :=
  ⟨⟨20, 25, 2321⟩, 168215254255777606, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_26 : CertifiedEndpoint :=
  ⟨⟨20, 26, 2282⟩, 176727117369452282, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_27 : CertifiedEndpoint :=
  ⟨⟨20, 27, 2244⟩, 184924374984091489, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_28 : CertifiedEndpoint :=
  ⟨⟨20, 28, 2204⟩, 192557826758698564, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_29 : CertifiedEndpoint :=
  ⟨⟨20, 29, 2164⟩, 199783538601295729, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_30 : CertifiedEndpoint :=
  ⟨⟨20, 30, 2124⟩, 206601510511882984, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_31 : CertifiedEndpoint :=
  ⟨⟨20, 31, 2083⟩, 212908540404843668, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_32 : CertifiedEndpoint :=
  ⟨⟨20, 32, 2041⟩, 218689526801214451, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_33 : CertifiedEndpoint :=
  ⟨⟨20, 33, 1998⟩, 223929368222032003, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_34 : CertifiedEndpoint :=
  ⟨⟨20, 34, 1955⟩, 228731266752912985, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_35 : CertifiedEndpoint :=
  ⟨⟨20, 35, 1912⟩, 233095222393857397, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_36 : CertifiedEndpoint :=
  ⟨⟨20, 36, 1868⟩, 236892863927643028, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_37 : CertifiedEndpoint :=
  ⟨⟨20, 37, 1823⟩, 240109089875306548, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_38 : CertifiedEndpoint :=
  ⟨⟨20, 38, 1777⟩, 242728798757884627, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_39 : CertifiedEndpoint :=
  ⟨⟨20, 39, 1730⟩, 244736889096413935, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_40 : CertifiedEndpoint :=
  ⟨⟨20, 40, 1683⟩, 246266765934437793, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_41 : CertifiedEndpoint :=
  ⟨⟨20, 41, 1635⟩, 247164888923128440, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_42 : CertifiedEndpoint :=
  ⟨⟨20, 42, 1587⟩, 247574730758671417, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_43 : CertifiedEndpoint :=
  ⟨⟨20, 43, 1537⟩, 247169075438126762, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_44 : CertifiedEndpoint :=
  ⟨⟨20, 44, 1487⟩, 246255003659149997, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_45 : CertifiedEndpoint :=
  ⟨⟨20, 45, 1436⟩, 244658839767628921, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_46 : CertifiedEndpoint :=
  ⟨⟨20, 46, 1384⟩, 242365482284600204, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_47 : CertifiedEndpoint :=
  ⟨⟨20, 47, 1332⟩, 239543573037854937, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_48 : CertifiedEndpoint :=
  ⟨⟨20, 48, 1278⟩, 235815557761242058, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_49 : CertifiedEndpoint :=
  ⟨⟨20, 49, 1224⟩, 231538855415628189, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_50 : CertifiedEndpoint :=
  ⟨⟨20, 50, 1168⟩, 226315776429577828, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_51 : CertifiedEndpoint :=
  ⟨⟨20, 51, 1112⟩, 220523875069242037, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_52 : CertifiedEndpoint :=
  ⟨⟨20, 52, 1055⟩, 213954238896260845, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_53 : CertifiedEndpoint :=
  ⟨⟨20, 53, 996⟩, 206377820166989841, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_54 : CertifiedEndpoint :=
  ⟨⟨20, 54, 937⟩, 198202376105506747, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_55 : CertifiedEndpoint :=
  ⟨⟨20, 55, 877⟩, 189203892794488262, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_56 : CertifiedEndpoint :=
  ⟨⟨20, 56, 815⟩, 179138221011326645, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_57 : CertifiedEndpoint :=
  ⟨⟨20, 57, 753⟩, 168443320938026278, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_58 : CertifiedEndpoint :=
  ⟨⟨20, 58, 689⟩, 156640961782013899, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_59 : CertifiedEndpoint :=
  ⟨⟨20, 59, 624⟩, 143945089807970589, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_60 : CertifiedEndpoint :=
  ⟨⟨20, 60, 558⟩, 130340603536933018, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_61 : CertifiedEndpoint :=
  ⟨⟨20, 61, 491⟩, 115812401489937856, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_62 : CertifiedEndpoint :=
  ⟨⟨20, 62, 422⟩, 100086131486450702, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_63 : CertifiedEndpoint :=
  ⟨⟨20, 63, 352⟩, 83395875096437077, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_64 : CertifiedEndpoint :=
  ⟨⟨20, 64, 281⟩, 65726530840933651, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_65 : CertifiedEndpoint :=
  ⟨⟨20, 65, 209⟩, 47062997240977094, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_20_66 : CertifiedEndpoint :=
  ⟨⟨20, 66, 135⟩, 27110786810748565, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_21 : CertifiedEndpoint :=
  ⟨⟨21, 21, 2127⟩, 126754822660104684, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_22 : CertifiedEndpoint :=
  ⟨⟨21, 22, 2088⟩, 128015012780816344, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_23 : CertifiedEndpoint :=
  ⟨⟨21, 23, 2049⟩, 129139186488049682, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_24 : CertifiedEndpoint :=
  ⟨⟨21, 24, 2009⟩, 137105239928090513, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_25 : CertifiedEndpoint :=
  ⟨⟨21, 25, 1968⟩, 144568589307494975, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_26 : CertifiedEndpoint :=
  ⟨⟨21, 26, 1927⟩, 151592741642919391, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_27 : CertifiedEndpoint :=
  ⟨⟨21, 27, 1886⟩, 158177696934363761, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_28 : CertifiedEndpoint :=
  ⟨⟨21, 28, 1844⟩, 164233490511919952, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_29 : CertifiedEndpoint :=
  ⟨⟨21, 29, 1801⟩, 169744247783636878, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_30 : CertifiedEndpoint :=
  ⟨⟨21, 30, 1758⟩, 174794641888772310, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_31 : CertifiedEndpoint :=
  ⟨⟨21, 31, 1714⟩, 179278833565467029, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_32 : CertifiedEndpoint :=
  ⟨⟨21, 32, 1669⟩, 183180948221769949, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_33 : CertifiedEndpoint :=
  ⟨⟨21, 33, 1624⟩, 186601533588889927, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_34 : CertifiedEndpoint :=
  ⟨⟨21, 34, 1578⟩, 189418875813016658, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_35 : CertifiedEndpoint :=
  ⟨⟨21, 35, 1532⟩, 191744105686659723, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_36 : CertifiedEndpoint :=
  ⟨⟨21, 36, 1485⟩, 193444926294708093, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_37 : CertifiedEndpoint :=
  ⟨⟨21, 37, 1437⟩, 194505463045210682, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_38 : CertifiedEndpoint :=
  ⟨⟨21, 38, 1389⟩, 195052721322628157, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_39 : CertifiedEndpoint :=
  ⟨⟨21, 39, 1339⟩, 194790358112836288, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_40 : CertifiedEndpoint :=
  ⟨⟨21, 40, 1290⟩, 194147013345070334, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_41 : CertifiedEndpoint :=
  ⟨⟨21, 41, 1239⟩, 192662297906192864, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_42 : CertifiedEndpoint :=
  ⟨⟨21, 42, 1188⟩, 190632554810328108, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_43 : CertifiedEndpoint :=
  ⟨⟨21, 43, 1135⟩, 187719108798148940, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_44 : CertifiedEndpoint :=
  ⟨⟨21, 44, 1082⟩, 184239469006381038, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_45 : CertifiedEndpoint :=
  ⟨⟨21, 45, 1029⟩, 180193635435024402, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_46 : CertifiedEndpoint :=
  ⟨⟨21, 46, 974⟩, 175211183640849734, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_47 : CertifiedEndpoint :=
  ⟨⟨21, 47, 919⟩, 169641371944484884, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_48 : CertifiedEndpoint :=
  ⟨⟨21, 48, 863⟩, 163288405063014479, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_49 : CertifiedEndpoint :=
  ⟨⟨21, 49, 805⟩, 155935321590921698, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_50 : CertifiedEndpoint :=
  ⟨⟨21, 50, 747⟩, 147963129032736563, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_51 : CertifiedEndpoint :=
  ⟨⟨21, 51, 688⟩, 139160157513592615, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_52 : CertifiedEndpoint :=
  ⟨⟨21, 52, 628⟩, 129510532441538768, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_53 : CertifiedEndpoint :=
  ⟨⟨21, 53, 568⟩, 119220632160791119, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_54 : CertifiedEndpoint :=
  ⟨⟨21, 54, 506⟩, 107835367737714578, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_55 : CertifiedEndpoint :=
  ⟨⟨21, 55, 443⟩, 95555825985874880, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_56 : CertifiedEndpoint :=
  ⟨⟨21, 56, 379⟩, 82366132313320939, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_57 : CertifiedEndpoint :=
  ⟨⟨21, 57, 314⟩, 68250412128101669, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_58 : CertifiedEndpoint :=
  ⟨⟨21, 58, 248⟩, 53192790838265984, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_59 : CertifiedEndpoint :=
  ⟨⟨21, 59, 181⟩, 37177393851862798, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_21_60 : CertifiedEndpoint :=
  ⟨⟨21, 60, 112⟩, 19929052926221308, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_22 : CertifiedEndpoint :=
  ⟨⟨22, 22, 1702⟩, 110810010366710102, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_23 : CertifiedEndpoint :=
  ⟨⟨22, 23, 1660⟩, 111043385411589328, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_24 : CertifiedEndpoint :=
  ⟨⟨22, 24, 1618⟩, 111123065520734382, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_25 : CertifiedEndpoint :=
  ⟨⟨22, 25, 1574⟩, 116669145209376287, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_26 : CertifiedEndpoint :=
  ⟨⟨22, 26, 1531⟩, 121801815543707001, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_27 : CertifiedEndpoint :=
  ⟨⟨22, 27, 1486⟩, 126279658847103159, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_28 : CertifiedEndpoint :=
  ⟨⟨22, 28, 1441⟩, 130252521767354443, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_29 : CertifiedEndpoint :=
  ⟨⟨22, 29, 1396⟩, 133720404304460853, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_30 : CertifiedEndpoint :=
  ⟨⟨22, 30, 1350⟩, 136580636959629478, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_31 : CertifiedEndpoint :=
  ⟨⟨22, 31, 1303⟩, 138816572027921476, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_32 : CertifiedEndpoint :=
  ⟨⟨22, 32, 1256⟩, 140525329773150144, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_33 : CertifiedEndpoint :=
  ⟨⟨22, 33, 1208⟩, 141587592991583729, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_34 : CertifiedEndpoint :=
  ⟨⟨22, 34, 1160⟩, 142111580416994756, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_35 : CertifiedEndpoint :=
  ⟨⟨22, 35, 1110⟩, 141836460702001263, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_36 : CertifiedEndpoint :=
  ⟨⟨22, 36, 1061⟩, 141136833162737351, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_37 : CertifiedEndpoint :=
  ⟨⟨22, 37, 1010⟩, 139604803073191235, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_38 : CertifiedEndpoint :=
  ⟨⟨22, 38, 959⟩, 137501201780744877, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_39 : CertifiedEndpoint :=
  ⟨⟨22, 39, 907⟩, 134673416671788840, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_40 : CertifiedEndpoint :=
  ⟨⟨22, 40, 854⟩, 131104800041384282, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_41 : CertifiedEndpoint :=
  ⟨⟨22, 41, 801⟩, 126942415268161026, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_42 : CertifiedEndpoint :=
  ⟨⟨22, 42, 747⟩, 122017002033570793, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_43 : CertifiedEndpoint :=
  ⟨⟨22, 43, 692⟩, 116311912632674741, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_44 : CertifiedEndpoint :=
  ⟨⟨22, 44, 636⟩, 109810499360534028, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_45 : CertifiedEndpoint :=
  ⟨⟨22, 45, 580⟩, 102682022535696933, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_46 : CertifiedEndpoint :=
  ⟨⟨22, 46, 523⟩, 94735024899696721, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_47 : CertifiedEndpoint :=
  ⟨⟨22, 47, 465⟩, 85952858747594550, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_48 : CertifiedEndpoint :=
  ⟨⟨22, 48, 406⟩, 76318876374451578, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_49 : CertifiedEndpoint :=
  ⟨⟨22, 49, 346⟩, 65816430075328963, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_50 : CertifiedEndpoint :=
  ⟨⟨22, 50, 285⟩, 54428872145287863, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_51 : CertifiedEndpoint :=
  ⟨⟨22, 51, 224⟩, 42358758312754241, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_52 : CertifiedEndpoint :=
  ⟨⟨22, 52, 161⟩, 29156583241039259, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_22_53 : CertifiedEndpoint :=
  ⟨⟨22, 53, 98⟩, 15249655326913299, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_23 : CertifiedEndpoint :=
  ⟨⟨23, 23, 1230⟩, 86973090321275379, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_24 : CertifiedEndpoint :=
  ⟨⟨23, 24, 1184⟩, 85896561934887478, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_25 : CertifiedEndpoint :=
  ⟨⟨23, 25, 1138⟩, 84643798067074613, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_26 : CertifiedEndpoint :=
  ⟨⟨23, 26, 1092⟩, 87363951026824584, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_27 : CertifiedEndpoint :=
  ⟨⟨23, 27, 1045⟩, 89456945886728902, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_28 : CertifiedEndpoint :=
  ⟨⟨23, 28, 997⟩, 90905361828860969, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_29 : CertifiedEndpoint :=
  ⟨⟨23, 29, 949⟩, 91790504658033034, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_30 : CertifiedEndpoint :=
  ⟨⟨23, 30, 900⟩, 92007840812197384, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_31 : CertifiedEndpoint :=
  ⟨⟨23, 31, 851⟩, 91650289974784000, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_32 : CertifiedEndpoint :=
  ⟨⟨23, 32, 801⟩, 90601704705127437, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_33 : CertifiedEndpoint :=
  ⟨⟨23, 33, 751⟩, 88966618565275408, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_34 : CertifiedEndpoint :=
  ⟨⟨23, 34, 699⟩, 86489508916661559, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_35 : CertifiedEndpoint :=
  ⟨⟨23, 35, 647⟩, 83402670640616780, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_36 : CertifiedEndpoint :=
  ⟨⟨23, 36, 595⟩, 79706103737141071, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_37 : CertifiedEndpoint :=
  ⟨⟨23, 37, 542⟩, 75254626069024657, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_38 : CertifiedEndpoint :=
  ⟨⟨23, 38, 488⟩, 70030816818340940, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_39 : CertifiedEndpoint :=
  ⟨⟨23, 39, 433⟩, 64017255167163322, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_40 : CertifiedEndpoint :=
  ⟨⟨23, 40, 378⟩, 57359123252701578, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_41 : CertifiedEndpoint :=
  ⟨⟨23, 41, 322⟩, 49888011180510469, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_42 : CertifiedEndpoint :=
  ⟨⟨23, 42, 265⟩, 41586498132663397, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_43 : CertifiedEndpoint :=
  ⟨⟨23, 43, 207⟩, 32437163291233764, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_44 : CertifiedEndpoint :=
  ⟨⟨23, 44, 149⟩, 22608416550666809, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_23_45 : CertifiedEndpoint :=
  ⟨⟨23, 45, 90⟩, 11908620259281829, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_24 : CertifiedEndpoint :=
  ⟨⟨24, 24, 709⟩, 53883511818107493, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_25 : CertifiedEndpoint :=
  ⟨⟨24, 25, 661⟩, 51416306980908806, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_26 : CertifiedEndpoint :=
  ⟨⟨24, 26, 611⟩, 48593195018671641, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_27 : CertifiedEndpoint :=
  ⟨⟨24, 27, 562⟩, 47828625712265071, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_28 : CertifiedEndpoint :=
  ⟨⟨24, 28, 511⟩, 46275635418290765, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_29 : CertifiedEndpoint :=
  ⟨⟨24, 29, 461⟩, 44198062106925450, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_30 : CertifiedEndpoint :=
  ⟨⟨24, 30, 409⟩, 41295679946163691, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_31 : CertifiedEndpoint :=
  ⟨⟨24, 31, 357⟩, 37756510203399542, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_32 : CertifiedEndpoint :=
  ⟨⟨24, 32, 304⟩, 33462283670383504, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_33 : CertifiedEndpoint :=
  ⟨⟨24, 33, 251⟩, 28519140268088840, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_34 : CertifiedEndpoint :=
  ⟨⟨24, 34, 197⟩, 22796681500989815, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_35 : CertifiedEndpoint :=
  ⟨⟨24, 35, 143⟩, 16413176577335928, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_24_36 : CertifiedEndpoint :=
  ⟨⟨24, 36, 87⟩, 9083569931523237, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_25_25 : CertifiedEndpoint :=
  ⟨⟨25, 25, 141⟩, 10393691350889146, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_25_26 : CertifiedEndpoint :=
  ⟨⟨25, 26, 89⟩, 6137081091074104, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_25_27 : CertifiedEndpoint :=
  ⟨⟨25, 27, 37⟩, 1663380612965022, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock13 : List CertifiedEndpoint := [
  endpoint_19_34, endpoint_19_35, endpoint_19_36, endpoint_19_37, endpoint_19_38, endpoint_19_39,
  endpoint_19_40, endpoint_19_41, endpoint_19_42, endpoint_19_43, endpoint_19_44, endpoint_19_45,
  endpoint_19_46, endpoint_19_47, endpoint_19_48, endpoint_19_49, endpoint_19_50, endpoint_19_51,
  endpoint_19_52, endpoint_19_53, endpoint_19_54, endpoint_19_55, endpoint_19_56, endpoint_19_57,
  endpoint_19_58, endpoint_19_59, endpoint_19_60, endpoint_19_61, endpoint_19_62, endpoint_19_63,
  endpoint_19_64, endpoint_19_65, endpoint_19_66, endpoint_19_67, endpoint_19_68, endpoint_19_69,
  endpoint_19_70, endpoint_19_71, endpoint_19_72, endpoint_20_20, endpoint_20_21, endpoint_20_22,
  endpoint_20_23, endpoint_20_24, endpoint_20_25, endpoint_20_26, endpoint_20_27, endpoint_20_28,
  endpoint_20_29, endpoint_20_30, endpoint_20_31, endpoint_20_32, endpoint_20_33, endpoint_20_34,
  endpoint_20_35, endpoint_20_36, endpoint_20_37, endpoint_20_38, endpoint_20_39, endpoint_20_40,
  endpoint_20_41, endpoint_20_42, endpoint_20_43, endpoint_20_44, endpoint_20_45, endpoint_20_46,
  endpoint_20_47, endpoint_20_48, endpoint_20_49, endpoint_20_50, endpoint_20_51, endpoint_20_52,
  endpoint_20_53, endpoint_20_54, endpoint_20_55, endpoint_20_56, endpoint_20_57, endpoint_20_58,
  endpoint_20_59, endpoint_20_60, endpoint_20_61, endpoint_20_62, endpoint_20_63, endpoint_20_64,
  endpoint_20_65, endpoint_20_66, endpoint_21_21, endpoint_21_22, endpoint_21_23, endpoint_21_24,
  endpoint_21_25, endpoint_21_26, endpoint_21_27, endpoint_21_28, endpoint_21_29, endpoint_21_30,
  endpoint_21_31, endpoint_21_32, endpoint_21_33, endpoint_21_34, endpoint_21_35, endpoint_21_36,
  endpoint_21_37, endpoint_21_38, endpoint_21_39, endpoint_21_40, endpoint_21_41, endpoint_21_42,
  endpoint_21_43, endpoint_21_44, endpoint_21_45, endpoint_21_46, endpoint_21_47, endpoint_21_48,
  endpoint_21_49, endpoint_21_50, endpoint_21_51, endpoint_21_52, endpoint_21_53, endpoint_21_54,
  endpoint_21_55, endpoint_21_56, endpoint_21_57, endpoint_21_58, endpoint_21_59, endpoint_21_60,
  endpoint_22_22, endpoint_22_23, endpoint_22_24, endpoint_22_25, endpoint_22_26, endpoint_22_27,
  endpoint_22_28, endpoint_22_29, endpoint_22_30, endpoint_22_31, endpoint_22_32, endpoint_22_33,
  endpoint_22_34, endpoint_22_35, endpoint_22_36, endpoint_22_37, endpoint_22_38, endpoint_22_39,
  endpoint_22_40, endpoint_22_41, endpoint_22_42, endpoint_22_43, endpoint_22_44, endpoint_22_45,
  endpoint_22_46, endpoint_22_47, endpoint_22_48, endpoint_22_49, endpoint_22_50, endpoint_22_51,
  endpoint_22_52, endpoint_22_53, endpoint_23_23, endpoint_23_24, endpoint_23_25, endpoint_23_26,
  endpoint_23_27, endpoint_23_28, endpoint_23_29, endpoint_23_30, endpoint_23_31, endpoint_23_32,
  endpoint_23_33, endpoint_23_34, endpoint_23_35, endpoint_23_36, endpoint_23_37, endpoint_23_38,
  endpoint_23_39, endpoint_23_40, endpoint_23_41, endpoint_23_42, endpoint_23_43, endpoint_23_44,
  endpoint_23_45, endpoint_24_24, endpoint_24_25, endpoint_24_26, endpoint_24_27, endpoint_24_28,
  endpoint_24_29, endpoint_24_30, endpoint_24_31, endpoint_24_32, endpoint_24_33, endpoint_24_34,
  endpoint_24_35, endpoint_24_36, endpoint_25_25, endpoint_25_26, endpoint_25_27
]

end ProximityPrize.SubmissionLower.Koala6844Receipts
