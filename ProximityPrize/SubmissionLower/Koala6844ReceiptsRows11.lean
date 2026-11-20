import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_16_53_flag : Flag := ⟨16, 53, 2664⟩
private def endpoint_16_53_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_53_base : receiptBase endpoint_16_53_flag endpoint_16_53_sources = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_w0 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 2 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_w2 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 2 2 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_p4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 4 251271057564180115 = some 251271057564180115 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 2 2 251271057564180115 251271057564180115 251271057564180115 endpoint_16_53_w0 endpoint_16_53_w2
private theorem endpoint_16_53_w4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 4 2 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_p6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 6 251271057564180115 = some 251271057564180115 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 4 2 251271057564180115 251271057564180115 251271057564180115 endpoint_16_53_p4 endpoint_16_53_w4
private theorem endpoint_16_53_w6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 6 2 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_p8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 8 251271057564180115 = some 251271057564180115 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 6 2 251271057564180115 251271057564180115 251271057564180115 endpoint_16_53_p6 endpoint_16_53_w6
private theorem endpoint_16_53_w8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 8 2 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_p10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 10 251271057564180115 = some 251271057564180115 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 8 2 251271057564180115 251271057564180115 251271057564180115 endpoint_16_53_p8 endpoint_16_53_w8
private theorem endpoint_16_53_w10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 10 2 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_p12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 12 251271057564180115 = some 251271057564180115 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 10 2 251271057564180115 251271057564180115 251271057564180115 endpoint_16_53_p10 endpoint_16_53_w10
private theorem endpoint_16_53_w12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 12 2 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_p14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 14 251271057564180115 = some 251271057564180115 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 12 2 251271057564180115 251271057564180115 251271057564180115 endpoint_16_53_p12 endpoint_16_53_w12
private theorem endpoint_16_53_w14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 14 1 251271057564180115 = some 251271057564180115 := by decide +kernel
private theorem endpoint_16_53_p15 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 15 251271057564180115 = some 251271057564180115 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 14 1 251271057564180115 251271057564180115 251271057564180115 endpoint_16_53_p14 endpoint_16_53_w14
def endpoint_16_53 : CertifiedEndpoint :=
  ⟨⟨16, 53, 2664⟩, 251271057564180115, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_53_flag endpoint_16_53_sources 15 251271057564180115 251271057564180115 rfl endpoint_16_53_base endpoint_16_53_p15) (by decide)⟩
private def endpoint_16_54_flag : Flag := ⟨16, 54, 2609⟩
private def endpoint_16_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_54_base : receiptBase endpoint_16_54_flag endpoint_16_54_sources = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_w0 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 2 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_w2 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 2 2 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_p4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 4 250237958930608740 = some 250237958930608740 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 2 2 250237958930608740 250237958930608740 250237958930608740 endpoint_16_54_w0 endpoint_16_54_w2
private theorem endpoint_16_54_w4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 4 2 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_p6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 6 250237958930608740 = some 250237958930608740 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 4 2 250237958930608740 250237958930608740 250237958930608740 endpoint_16_54_p4 endpoint_16_54_w4
private theorem endpoint_16_54_w6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 6 2 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_p8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 8 250237958930608740 = some 250237958930608740 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 6 2 250237958930608740 250237958930608740 250237958930608740 endpoint_16_54_p6 endpoint_16_54_w6
private theorem endpoint_16_54_w8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 8 2 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_p10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 10 250237958930608740 = some 250237958930608740 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 8 2 250237958930608740 250237958930608740 250237958930608740 endpoint_16_54_p8 endpoint_16_54_w8
private theorem endpoint_16_54_w10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 10 2 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_p12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 12 250237958930608740 = some 250237958930608740 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 10 2 250237958930608740 250237958930608740 250237958930608740 endpoint_16_54_p10 endpoint_16_54_w10
private theorem endpoint_16_54_w12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 12 2 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_p14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 14 250237958930608740 = some 250237958930608740 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 12 2 250237958930608740 250237958930608740 250237958930608740 endpoint_16_54_p12 endpoint_16_54_w12
private theorem endpoint_16_54_w14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 14 1 250237958930608740 = some 250237958930608740 := by decide +kernel
private theorem endpoint_16_54_p15 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 15 250237958930608740 = some 250237958930608740 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 14 1 250237958930608740 250237958930608740 250237958930608740 endpoint_16_54_p14 endpoint_16_54_w14
def endpoint_16_54 : CertifiedEndpoint :=
  ⟨⟨16, 54, 2609⟩, 250237958930608740, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_54_flag endpoint_16_54_sources 15 250237958930608740 250237958930608740 rfl endpoint_16_54_base endpoint_16_54_p15) (by decide)⟩
private def endpoint_16_55_flag : Flag := ⟨16, 55, 2551⟩
private def endpoint_16_55_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_55_base : receiptBase endpoint_16_55_flag endpoint_16_55_sources = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_w0 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 2 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_w2 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 2 2 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_p4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 4 254833941694761765 = some 254833941694761765 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 2 2 254833941694761765 254833941694761765 254833941694761765 endpoint_16_55_w0 endpoint_16_55_w2
private theorem endpoint_16_55_w4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 4 2 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_p6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 6 254833941694761765 = some 254833941694761765 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 4 2 254833941694761765 254833941694761765 254833941694761765 endpoint_16_55_p4 endpoint_16_55_w4
private theorem endpoint_16_55_w6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 6 2 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_p8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 8 254833941694761765 = some 254833941694761765 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 6 2 254833941694761765 254833941694761765 254833941694761765 endpoint_16_55_p6 endpoint_16_55_w6
private theorem endpoint_16_55_w8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 8 2 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_p10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 10 254833941694761765 = some 254833941694761765 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 8 2 254833941694761765 254833941694761765 254833941694761765 endpoint_16_55_p8 endpoint_16_55_w8
private theorem endpoint_16_55_w10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 10 2 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_p12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 12 254833941694761765 = some 254833941694761765 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 10 2 254833941694761765 254833941694761765 254833941694761765 endpoint_16_55_p10 endpoint_16_55_w10
private theorem endpoint_16_55_w12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 12 2 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_p14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 14 254833941694761765 = some 254833941694761765 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 12 2 254833941694761765 254833941694761765 254833941694761765 endpoint_16_55_p12 endpoint_16_55_w12
private theorem endpoint_16_55_w14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 14 1 254833941694761765 = some 254833941694761765 := by decide +kernel
private theorem endpoint_16_55_p15 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 15 254833941694761765 = some 254833941694761765 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 14 1 254833941694761765 254833941694761765 254833941694761765 endpoint_16_55_p14 endpoint_16_55_w14
def endpoint_16_55 : CertifiedEndpoint :=
  ⟨⟨16, 55, 2551⟩, 254833941694761765, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_55_flag endpoint_16_55_sources 15 254833941694761765 254833941694761765 rfl endpoint_16_55_base endpoint_16_55_p15) (by decide)⟩
private def endpoint_16_56_flag : Flag := ⟨16, 56, 2493⟩
private def endpoint_16_56_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_56_base : receiptBase endpoint_16_56_flag endpoint_16_56_sources = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_w0 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 2 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_w2 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 2 2 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_p4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 4 253191500644515440 = some 253191500644515440 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 2 2 253191500644515440 253191500644515440 253191500644515440 endpoint_16_56_w0 endpoint_16_56_w2
private theorem endpoint_16_56_w4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 4 2 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_p6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 6 253191500644515440 = some 253191500644515440 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 4 2 253191500644515440 253191500644515440 253191500644515440 endpoint_16_56_p4 endpoint_16_56_w4
private theorem endpoint_16_56_w6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 6 2 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_p8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 8 253191500644515440 = some 253191500644515440 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 6 2 253191500644515440 253191500644515440 253191500644515440 endpoint_16_56_p6 endpoint_16_56_w6
private theorem endpoint_16_56_w8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 8 2 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_p10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 10 253191500644515440 = some 253191500644515440 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 8 2 253191500644515440 253191500644515440 253191500644515440 endpoint_16_56_p8 endpoint_16_56_w8
private theorem endpoint_16_56_w10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 10 2 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_p12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 12 253191500644515440 = some 253191500644515440 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 10 2 253191500644515440 253191500644515440 253191500644515440 endpoint_16_56_p10 endpoint_16_56_w10
private theorem endpoint_16_56_w12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 12 2 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_p14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 14 253191500644515440 = some 253191500644515440 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 12 2 253191500644515440 253191500644515440 253191500644515440 endpoint_16_56_p12 endpoint_16_56_w12
private theorem endpoint_16_56_w14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 14 1 253191500644515440 = some 253191500644515440 := by decide +kernel
private theorem endpoint_16_56_p15 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 15 253191500644515440 = some 253191500644515440 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 14 1 253191500644515440 253191500644515440 253191500644515440 endpoint_16_56_p14 endpoint_16_56_w14
def endpoint_16_56 : CertifiedEndpoint :=
  ⟨⟨16, 56, 2493⟩, 253191500644515440, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_56_flag endpoint_16_56_sources 15 253191500644515440 253191500644515440 rfl endpoint_16_56_base endpoint_16_56_p15) (by decide)⟩
private def endpoint_16_57_flag : Flag := ⟨16, 57, 2433⟩
private def endpoint_16_57_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_57_base : receiptBase endpoint_16_57_flag endpoint_16_57_sources = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_w0 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 2 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_w2 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 2 2 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_p4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 4 252375810876661395 = some 252375810876661395 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 2 2 252375810876661395 252375810876661395 252375810876661395 endpoint_16_57_w0 endpoint_16_57_w2
private theorem endpoint_16_57_w4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 4 2 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_p6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 6 252375810876661395 = some 252375810876661395 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 4 2 252375810876661395 252375810876661395 252375810876661395 endpoint_16_57_p4 endpoint_16_57_w4
private theorem endpoint_16_57_w6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 6 2 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_p8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 8 252375810876661395 = some 252375810876661395 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 6 2 252375810876661395 252375810876661395 252375810876661395 endpoint_16_57_p6 endpoint_16_57_w6
private theorem endpoint_16_57_w8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 8 2 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_p10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 10 252375810876661395 = some 252375810876661395 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 8 2 252375810876661395 252375810876661395 252375810876661395 endpoint_16_57_p8 endpoint_16_57_w8
private theorem endpoint_16_57_w10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 10 2 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_p12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 12 252375810876661395 = some 252375810876661395 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 10 2 252375810876661395 252375810876661395 252375810876661395 endpoint_16_57_p10 endpoint_16_57_w10
private theorem endpoint_16_57_w12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 12 2 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_p14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 14 252375810876661395 = some 252375810876661395 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 12 2 252375810876661395 252375810876661395 252375810876661395 endpoint_16_57_p12 endpoint_16_57_w12
private theorem endpoint_16_57_w14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 14 1 252375810876661395 = some 252375810876661395 := by decide +kernel
private theorem endpoint_16_57_p15 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 15 252375810876661395 = some 252375810876661395 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 14 1 252375810876661395 252375810876661395 252375810876661395 endpoint_16_57_p14 endpoint_16_57_w14
def endpoint_16_57 : CertifiedEndpoint :=
  ⟨⟨16, 57, 2433⟩, 252375810876661395, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_57_flag endpoint_16_57_sources 15 252375810876661395 252375810876661395 rfl endpoint_16_57_base endpoint_16_57_p15) (by decide)⟩
private def endpoint_16_58_flag : Flag := ⟨16, 58, 2371⟩
private def endpoint_16_58_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_58_base : receiptBase endpoint_16_58_flag endpoint_16_58_sources = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_w0 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 2 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_w2 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 2 2 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_p4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 4 249884089811521892 = some 249884089811521892 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 2 2 249884089811521892 249884089811521892 249884089811521892 endpoint_16_58_w0 endpoint_16_58_w2
private theorem endpoint_16_58_w4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 4 2 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_p6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 6 249884089811521892 = some 249884089811521892 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 4 2 249884089811521892 249884089811521892 249884089811521892 endpoint_16_58_p4 endpoint_16_58_w4
private theorem endpoint_16_58_w6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 6 2 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_p8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 8 249884089811521892 = some 249884089811521892 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 6 2 249884089811521892 249884089811521892 249884089811521892 endpoint_16_58_p6 endpoint_16_58_w6
private theorem endpoint_16_58_w8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 8 2 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_p10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 10 249884089811521892 = some 249884089811521892 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 8 2 249884089811521892 249884089811521892 249884089811521892 endpoint_16_58_p8 endpoint_16_58_w8
private theorem endpoint_16_58_w10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 10 2 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_p12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 12 249884089811521892 = some 249884089811521892 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 10 2 249884089811521892 249884089811521892 249884089811521892 endpoint_16_58_p10 endpoint_16_58_w10
private theorem endpoint_16_58_w12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 12 2 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_p14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 14 249884089811521892 = some 249884089811521892 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 12 2 249884089811521892 249884089811521892 249884089811521892 endpoint_16_58_p12 endpoint_16_58_w12
private theorem endpoint_16_58_w14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 14 1 249884089811521892 = some 249884089811521892 := by decide +kernel
private theorem endpoint_16_58_p15 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 15 249884089811521892 = some 249884089811521892 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 14 1 249884089811521892 249884089811521892 249884089811521892 endpoint_16_58_p14 endpoint_16_58_w14
def endpoint_16_58 : CertifiedEndpoint :=
  ⟨⟨16, 58, 2371⟩, 249884089811521892, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_58_flag endpoint_16_58_sources 15 249884089811521892 249884089811521892 rfl endpoint_16_58_base endpoint_16_58_p15) (by decide)⟩
private def endpoint_16_59_flag : Flag := ⟨16, 59, 2307⟩
private def endpoint_16_59_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_59_base : receiptBase endpoint_16_59_flag endpoint_16_59_sources = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_w0 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 2 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_w2 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 2 2 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_p4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 4 246987914415307110 = some 246987914415307110 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 2 2 246987914415307110 246987914415307110 246987914415307110 endpoint_16_59_w0 endpoint_16_59_w2
private theorem endpoint_16_59_w4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 4 2 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_p6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 6 246987914415307110 = some 246987914415307110 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 4 2 246987914415307110 246987914415307110 246987914415307110 endpoint_16_59_p4 endpoint_16_59_w4
private theorem endpoint_16_59_w6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 6 2 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_p8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 8 246987914415307110 = some 246987914415307110 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 6 2 246987914415307110 246987914415307110 246987914415307110 endpoint_16_59_p6 endpoint_16_59_w6
private theorem endpoint_16_59_w8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 8 2 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_p10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 10 246987914415307110 = some 246987914415307110 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 8 2 246987914415307110 246987914415307110 246987914415307110 endpoint_16_59_p8 endpoint_16_59_w8
private theorem endpoint_16_59_w10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 10 2 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_p12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 12 246987914415307110 = some 246987914415307110 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 10 2 246987914415307110 246987914415307110 246987914415307110 endpoint_16_59_p10 endpoint_16_59_w10
private theorem endpoint_16_59_w12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 12 2 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_p14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 14 246987914415307110 = some 246987914415307110 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 12 2 246987914415307110 246987914415307110 246987914415307110 endpoint_16_59_p12 endpoint_16_59_w12
private theorem endpoint_16_59_w14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 14 1 246987914415307110 = some 246987914415307110 := by decide +kernel
private theorem endpoint_16_59_p15 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 15 246987914415307110 = some 246987914415307110 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 14 1 246987914415307110 246987914415307110 246987914415307110 endpoint_16_59_p14 endpoint_16_59_w14
def endpoint_16_59 : CertifiedEndpoint :=
  ⟨⟨16, 59, 2307⟩, 246987914415307110, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_59_flag endpoint_16_59_sources 15 246987914415307110 246987914415307110 rfl endpoint_16_59_base endpoint_16_59_p15) (by decide)⟩
private def endpoint_16_60_flag : Flag := ⟨16, 60, 2242⟩
private def endpoint_16_60_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_60_base : receiptBase endpoint_16_60_flag endpoint_16_60_sources = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_w0 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 2 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_w2 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 2 2 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_p4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 4 243783976790444833 = some 243783976790444833 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 2 2 243783976790444833 243783976790444833 243783976790444833 endpoint_16_60_w0 endpoint_16_60_w2
private theorem endpoint_16_60_w4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 4 2 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_p6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 6 243783976790444833 = some 243783976790444833 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 4 2 243783976790444833 243783976790444833 243783976790444833 endpoint_16_60_p4 endpoint_16_60_w4
private theorem endpoint_16_60_w6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 6 2 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_p8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 8 243783976790444833 = some 243783976790444833 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 6 2 243783976790444833 243783976790444833 243783976790444833 endpoint_16_60_p6 endpoint_16_60_w6
private theorem endpoint_16_60_w8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 8 2 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_p10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 10 243783976790444833 = some 243783976790444833 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 8 2 243783976790444833 243783976790444833 243783976790444833 endpoint_16_60_p8 endpoint_16_60_w8
private theorem endpoint_16_60_w10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 10 2 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_p12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 12 243783976790444833 = some 243783976790444833 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 10 2 243783976790444833 243783976790444833 243783976790444833 endpoint_16_60_p10 endpoint_16_60_w10
private theorem endpoint_16_60_w12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 12 2 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_p14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 14 243783976790444833 = some 243783976790444833 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 12 2 243783976790444833 243783976790444833 243783976790444833 endpoint_16_60_p12 endpoint_16_60_w12
private theorem endpoint_16_60_w14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 14 1 243783976790444833 = some 243783976790444833 := by decide +kernel
private theorem endpoint_16_60_p15 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 15 243783976790444833 = some 243783976790444833 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 14 1 243783976790444833 243783976790444833 243783976790444833 endpoint_16_60_p14 endpoint_16_60_w14
def endpoint_16_60 : CertifiedEndpoint :=
  ⟨⟨16, 60, 2242⟩, 243783976790444833, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_60_flag endpoint_16_60_sources 15 243783976790444833 243783976790444833 rfl endpoint_16_60_base endpoint_16_60_p15) (by decide)⟩
private def endpoint_16_61_flag : Flag := ⟨16, 61, 2175⟩
private def endpoint_16_61_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_61_base : receiptBase endpoint_16_61_flag endpoint_16_61_sources = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_w0 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 2 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_w2 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 2 2 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_p4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 4 240159950010342853 = some 240159950010342853 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 2 2 240159950010342853 240159950010342853 240159950010342853 endpoint_16_61_w0 endpoint_16_61_w2
private theorem endpoint_16_61_w4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 4 2 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_p6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 6 240159950010342853 = some 240159950010342853 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 4 2 240159950010342853 240159950010342853 240159950010342853 endpoint_16_61_p4 endpoint_16_61_w4
private theorem endpoint_16_61_w6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 6 2 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_p8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 8 240159950010342853 = some 240159950010342853 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 6 2 240159950010342853 240159950010342853 240159950010342853 endpoint_16_61_p6 endpoint_16_61_w6
private theorem endpoint_16_61_w8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 8 2 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_p10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 10 240159950010342853 = some 240159950010342853 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 8 2 240159950010342853 240159950010342853 240159950010342853 endpoint_16_61_p8 endpoint_16_61_w8
private theorem endpoint_16_61_w10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 10 2 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_p12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 12 240159950010342853 = some 240159950010342853 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 10 2 240159950010342853 240159950010342853 240159950010342853 endpoint_16_61_p10 endpoint_16_61_w10
private theorem endpoint_16_61_w12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 12 2 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_p14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 14 240159950010342853 = some 240159950010342853 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 12 2 240159950010342853 240159950010342853 240159950010342853 endpoint_16_61_p12 endpoint_16_61_w12
private theorem endpoint_16_61_w14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 14 1 240159950010342853 = some 240159950010342853 := by decide +kernel
private theorem endpoint_16_61_p15 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 15 240159950010342853 = some 240159950010342853 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 14 1 240159950010342853 240159950010342853 240159950010342853 endpoint_16_61_p14 endpoint_16_61_w14
def endpoint_16_61 : CertifiedEndpoint :=
  ⟨⟨16, 61, 2175⟩, 240159950010342853, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_61_flag endpoint_16_61_sources 15 240159950010342853 240159950010342853 rfl endpoint_16_61_base endpoint_16_61_p15) (by decide)⟩
private def endpoint_16_62_flag : Flag := ⟨16, 62, 2107⟩
private def endpoint_16_62_sources : Sources := ⟨contact15, contact15, contact12⟩
private theorem endpoint_16_62_base : receiptBase endpoint_16_62_flag endpoint_16_62_sources = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_w0 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 2 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_w2 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 2 2 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_p4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 4 237410996110500888 = some 237410996110500888 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 2 2 237410996110500888 237410996110500888 237410996110500888 endpoint_16_62_w0 endpoint_16_62_w2
private theorem endpoint_16_62_w4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 4 2 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_p6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 6 237410996110500888 = some 237410996110500888 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 4 2 237410996110500888 237410996110500888 237410996110500888 endpoint_16_62_p4 endpoint_16_62_w4
private theorem endpoint_16_62_w6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 6 2 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_p8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 8 237410996110500888 = some 237410996110500888 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 6 2 237410996110500888 237410996110500888 237410996110500888 endpoint_16_62_p6 endpoint_16_62_w6
private theorem endpoint_16_62_w8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 8 2 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_p10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 10 237410996110500888 = some 237410996110500888 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 8 2 237410996110500888 237410996110500888 237410996110500888 endpoint_16_62_p8 endpoint_16_62_w8
private theorem endpoint_16_62_w10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 10 2 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_p12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 12 237410996110500888 = some 237410996110500888 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 10 2 237410996110500888 237410996110500888 237410996110500888 endpoint_16_62_p10 endpoint_16_62_w10
private theorem endpoint_16_62_w12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 12 2 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_p14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 14 237410996110500888 = some 237410996110500888 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 12 2 237410996110500888 237410996110500888 237410996110500888 endpoint_16_62_p12 endpoint_16_62_w12
private theorem endpoint_16_62_w14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 14 1 237410996110500888 = some 237410996110500888 := by decide +kernel
private theorem endpoint_16_62_p15 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 15 237410996110500888 = some 237410996110500888 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 14 1 237410996110500888 237410996110500888 237410996110500888 endpoint_16_62_p14 endpoint_16_62_w14
def endpoint_16_62 : CertifiedEndpoint :=
  ⟨⟨16, 62, 2107⟩, 237410996110500888, .terminal ⟨contact15, contact15, contact12⟩ (finish_receipt_window endpoint_16_62_flag endpoint_16_62_sources 15 237410996110500888 237410996110500888 rfl endpoint_16_62_base endpoint_16_62_p15) (by decide)⟩
private def endpoint_16_63_flag : Flag := ⟨16, 63, 2036⟩
private def endpoint_16_63_sources : Sources := ⟨contact29, contact16, contact13⟩
private theorem endpoint_16_63_base : receiptBase endpoint_16_63_flag endpoint_16_63_sources = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_w0 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 2 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_w2 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 2 2 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_p4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 4 233812047983233659 = some 233812047983233659 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 2 2 233812047983233659 233812047983233659 233812047983233659 endpoint_16_63_w0 endpoint_16_63_w2
private theorem endpoint_16_63_w4 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 4 2 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_p6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 6 233812047983233659 = some 233812047983233659 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 4 2 233812047983233659 233812047983233659 233812047983233659 endpoint_16_63_p4 endpoint_16_63_w4
private theorem endpoint_16_63_w6 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 6 2 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_p8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 8 233812047983233659 = some 233812047983233659 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 6 2 233812047983233659 233812047983233659 233812047983233659 endpoint_16_63_p6 endpoint_16_63_w6
private theorem endpoint_16_63_w8 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 8 2 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_p10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 10 233812047983233659 = some 233812047983233659 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 8 2 233812047983233659 233812047983233659 233812047983233659 endpoint_16_63_p8 endpoint_16_63_w8
private theorem endpoint_16_63_w10 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 10 2 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_p12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 12 233812047983233659 = some 233812047983233659 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 10 2 233812047983233659 233812047983233659 233812047983233659 endpoint_16_63_p10 endpoint_16_63_w10
private theorem endpoint_16_63_w12 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 12 2 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_p14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 14 233812047983233659 = some 233812047983233659 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 12 2 233812047983233659 233812047983233659 233812047983233659 endpoint_16_63_p12 endpoint_16_63_w12
private theorem endpoint_16_63_w14 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 14 1 233812047983233659 = some 233812047983233659 := by decide +kernel
private theorem endpoint_16_63_p15 : receiptWindow endpoint_16_63_flag endpoint_16_63_sources 0 15 233812047983233659 = some 233812047983233659 :=
  join_receipt_window endpoint_16_63_flag endpoint_16_63_sources 0 14 1 233812047983233659 233812047983233659 233812047983233659 endpoint_16_63_p14 endpoint_16_63_w14
def endpoint_16_63 : CertifiedEndpoint :=
  ⟨⟨16, 63, 2036⟩, 233812047983233659, .terminal ⟨contact29, contact16, contact13⟩ (finish_receipt_window endpoint_16_63_flag endpoint_16_63_sources 15 233812047983233659 233812047983233659 rfl endpoint_16_63_base endpoint_16_63_p15) (by decide)⟩
private def endpoint_16_64_flag : Flag := ⟨16, 64, 1963⟩
private def endpoint_16_64_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_64_base : receiptBase endpoint_16_64_flag endpoint_16_64_sources = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_w0 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 2 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_w2 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 2 2 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_p4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 4 230783813759748772 = some 230783813759748772 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 2 2 230783813759748772 230783813759748772 230783813759748772 endpoint_16_64_w0 endpoint_16_64_w2
private theorem endpoint_16_64_w4 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 4 2 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_p6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 6 230783813759748772 = some 230783813759748772 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 4 2 230783813759748772 230783813759748772 230783813759748772 endpoint_16_64_p4 endpoint_16_64_w4
private theorem endpoint_16_64_w6 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 6 2 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_p8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 8 230783813759748772 = some 230783813759748772 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 6 2 230783813759748772 230783813759748772 230783813759748772 endpoint_16_64_p6 endpoint_16_64_w6
private theorem endpoint_16_64_w8 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 8 2 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_p10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 10 230783813759748772 = some 230783813759748772 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 8 2 230783813759748772 230783813759748772 230783813759748772 endpoint_16_64_p8 endpoint_16_64_w8
private theorem endpoint_16_64_w10 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 10 2 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_p12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 12 230783813759748772 = some 230783813759748772 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 10 2 230783813759748772 230783813759748772 230783813759748772 endpoint_16_64_p10 endpoint_16_64_w10
private theorem endpoint_16_64_w12 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 12 2 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_p14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 14 230783813759748772 = some 230783813759748772 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 12 2 230783813759748772 230783813759748772 230783813759748772 endpoint_16_64_p12 endpoint_16_64_w12
private theorem endpoint_16_64_w14 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 14 1 230783813759748772 = some 230783813759748772 := by decide +kernel
private theorem endpoint_16_64_p15 : receiptWindow endpoint_16_64_flag endpoint_16_64_sources 0 15 230783813759748772 = some 230783813759748772 :=
  join_receipt_window endpoint_16_64_flag endpoint_16_64_sources 0 14 1 230783813759748772 230783813759748772 230783813759748772 endpoint_16_64_p14 endpoint_16_64_w14
def endpoint_16_64 : CertifiedEndpoint :=
  ⟨⟨16, 64, 1963⟩, 230783813759748772, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_64_flag endpoint_16_64_sources 15 230783813759748772 230783813759748772 rfl endpoint_16_64_base endpoint_16_64_p15) (by decide)⟩
private def endpoint_16_65_flag : Flag := ⟨16, 65, 1888⟩
private def endpoint_16_65_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_65_base : receiptBase endpoint_16_65_flag endpoint_16_65_sources = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_w0 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 2 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_w2 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 2 2 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_p4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 4 225120613925359120 = some 225120613925359120 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 2 2 225120613925359120 225120613925359120 225120613925359120 endpoint_16_65_w0 endpoint_16_65_w2
private theorem endpoint_16_65_w4 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 4 2 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_p6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 6 225120613925359120 = some 225120613925359120 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 4 2 225120613925359120 225120613925359120 225120613925359120 endpoint_16_65_p4 endpoint_16_65_w4
private theorem endpoint_16_65_w6 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 6 2 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_p8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 8 225120613925359120 = some 225120613925359120 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 6 2 225120613925359120 225120613925359120 225120613925359120 endpoint_16_65_p6 endpoint_16_65_w6
private theorem endpoint_16_65_w8 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 8 2 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_p10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 10 225120613925359120 = some 225120613925359120 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 8 2 225120613925359120 225120613925359120 225120613925359120 endpoint_16_65_p8 endpoint_16_65_w8
private theorem endpoint_16_65_w10 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 10 2 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_p12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 12 225120613925359120 = some 225120613925359120 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 10 2 225120613925359120 225120613925359120 225120613925359120 endpoint_16_65_p10 endpoint_16_65_w10
private theorem endpoint_16_65_w12 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 12 2 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_p14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 14 225120613925359120 = some 225120613925359120 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 12 2 225120613925359120 225120613925359120 225120613925359120 endpoint_16_65_p12 endpoint_16_65_w12
private theorem endpoint_16_65_w14 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 14 1 225120613925359120 = some 225120613925359120 := by decide +kernel
private theorem endpoint_16_65_p15 : receiptWindow endpoint_16_65_flag endpoint_16_65_sources 0 15 225120613925359120 = some 225120613925359120 :=
  join_receipt_window endpoint_16_65_flag endpoint_16_65_sources 0 14 1 225120613925359120 225120613925359120 225120613925359120 endpoint_16_65_p14 endpoint_16_65_w14
def endpoint_16_65 : CertifiedEndpoint :=
  ⟨⟨16, 65, 1888⟩, 225120613925359120, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_65_flag endpoint_16_65_sources 15 225120613925359120 225120613925359120 rfl endpoint_16_65_base endpoint_16_65_p15) (by decide)⟩
private def endpoint_16_66_flag : Flag := ⟨16, 66, 1811⟩
private def endpoint_16_66_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_16_66_base : receiptBase endpoint_16_66_flag endpoint_16_66_sources = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_w0 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 2 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_w2 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 2 2 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_p4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 4 218973905528378700 = some 218973905528378700 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 2 2 218973905528378700 218973905528378700 218973905528378700 endpoint_16_66_w0 endpoint_16_66_w2
private theorem endpoint_16_66_w4 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 4 2 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_p6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 6 218973905528378700 = some 218973905528378700 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 4 2 218973905528378700 218973905528378700 218973905528378700 endpoint_16_66_p4 endpoint_16_66_w4
private theorem endpoint_16_66_w6 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 6 2 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_p8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 8 218973905528378700 = some 218973905528378700 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 6 2 218973905528378700 218973905528378700 218973905528378700 endpoint_16_66_p6 endpoint_16_66_w6
private theorem endpoint_16_66_w8 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 8 2 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_p10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 10 218973905528378700 = some 218973905528378700 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 8 2 218973905528378700 218973905528378700 218973905528378700 endpoint_16_66_p8 endpoint_16_66_w8
private theorem endpoint_16_66_w10 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 10 2 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_p12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 12 218973905528378700 = some 218973905528378700 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 10 2 218973905528378700 218973905528378700 218973905528378700 endpoint_16_66_p10 endpoint_16_66_w10
private theorem endpoint_16_66_w12 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 12 2 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_p14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 14 218973905528378700 = some 218973905528378700 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 12 2 218973905528378700 218973905528378700 218973905528378700 endpoint_16_66_p12 endpoint_16_66_w12
private theorem endpoint_16_66_w14 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 14 1 218973905528378700 = some 218973905528378700 := by decide +kernel
private theorem endpoint_16_66_p15 : receiptWindow endpoint_16_66_flag endpoint_16_66_sources 0 15 218973905528378700 = some 218973905528378700 :=
  join_receipt_window endpoint_16_66_flag endpoint_16_66_sources 0 14 1 218973905528378700 218973905528378700 218973905528378700 endpoint_16_66_p14 endpoint_16_66_w14
def endpoint_16_66 : CertifiedEndpoint :=
  ⟨⟨16, 66, 1811⟩, 218973905528378700, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_16_66_flag endpoint_16_66_sources 15 218973905528378700 218973905528378700 rfl endpoint_16_66_base endpoint_16_66_p15) (by decide)⟩
private def endpoint_16_67_flag : Flag := ⟨16, 67, 1732⟩
private def endpoint_16_67_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_67_base : receiptBase endpoint_16_67_flag endpoint_16_67_sources = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_w0 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 2 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_w2 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 2 2 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_p4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 4 214051556006235027 = some 214051556006235027 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 2 2 214051556006235027 214051556006235027 214051556006235027 endpoint_16_67_w0 endpoint_16_67_w2
private theorem endpoint_16_67_w4 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 4 2 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_p6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 6 214051556006235027 = some 214051556006235027 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 4 2 214051556006235027 214051556006235027 214051556006235027 endpoint_16_67_p4 endpoint_16_67_w4
private theorem endpoint_16_67_w6 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 6 2 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_p8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 8 214051556006235027 = some 214051556006235027 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 6 2 214051556006235027 214051556006235027 214051556006235027 endpoint_16_67_p6 endpoint_16_67_w6
private theorem endpoint_16_67_w8 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 8 2 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_p10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 10 214051556006235027 = some 214051556006235027 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 8 2 214051556006235027 214051556006235027 214051556006235027 endpoint_16_67_p8 endpoint_16_67_w8
private theorem endpoint_16_67_w10 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 10 2 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_p12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 12 214051556006235027 = some 214051556006235027 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 10 2 214051556006235027 214051556006235027 214051556006235027 endpoint_16_67_p10 endpoint_16_67_w10
private theorem endpoint_16_67_w12 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 12 2 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_p14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 14 214051556006235027 = some 214051556006235027 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 12 2 214051556006235027 214051556006235027 214051556006235027 endpoint_16_67_p12 endpoint_16_67_w12
private theorem endpoint_16_67_w14 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 14 1 214051556006235027 = some 214051556006235027 := by decide +kernel
private theorem endpoint_16_67_p15 : receiptWindow endpoint_16_67_flag endpoint_16_67_sources 0 15 214051556006235027 = some 214051556006235027 :=
  join_receipt_window endpoint_16_67_flag endpoint_16_67_sources 0 14 1 214051556006235027 214051556006235027 214051556006235027 endpoint_16_67_p14 endpoint_16_67_w14
def endpoint_16_67 : CertifiedEndpoint :=
  ⟨⟨16, 67, 1732⟩, 214051556006235027, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_67_flag endpoint_16_67_sources 15 214051556006235027 214051556006235027 rfl endpoint_16_67_base endpoint_16_67_p15) (by decide)⟩
private def endpoint_16_68_flag : Flag := ⟨16, 68, 1650⟩
private def endpoint_16_68_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_68_base : receiptBase endpoint_16_68_flag endpoint_16_68_sources = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_w0 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 2 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_w2 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 2 2 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_p4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 4 206712737012623083 = some 206712737012623083 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 2 2 206712737012623083 206712737012623083 206712737012623083 endpoint_16_68_w0 endpoint_16_68_w2
private theorem endpoint_16_68_w4 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 4 2 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_p6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 6 206712737012623083 = some 206712737012623083 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 4 2 206712737012623083 206712737012623083 206712737012623083 endpoint_16_68_p4 endpoint_16_68_w4
private theorem endpoint_16_68_w6 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 6 2 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_p8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 8 206712737012623083 = some 206712737012623083 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 6 2 206712737012623083 206712737012623083 206712737012623083 endpoint_16_68_p6 endpoint_16_68_w6
private theorem endpoint_16_68_w8 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 8 2 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_p10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 10 206712737012623083 = some 206712737012623083 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 8 2 206712737012623083 206712737012623083 206712737012623083 endpoint_16_68_p8 endpoint_16_68_w8
private theorem endpoint_16_68_w10 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 10 2 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_p12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 12 206712737012623083 = some 206712737012623083 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 10 2 206712737012623083 206712737012623083 206712737012623083 endpoint_16_68_p10 endpoint_16_68_w10
private theorem endpoint_16_68_w12 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 12 2 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_p14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 14 206712737012623083 = some 206712737012623083 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 12 2 206712737012623083 206712737012623083 206712737012623083 endpoint_16_68_p12 endpoint_16_68_w12
private theorem endpoint_16_68_w14 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 14 1 206712737012623083 = some 206712737012623083 := by decide +kernel
private theorem endpoint_16_68_p15 : receiptWindow endpoint_16_68_flag endpoint_16_68_sources 0 15 206712737012623083 = some 206712737012623083 :=
  join_receipt_window endpoint_16_68_flag endpoint_16_68_sources 0 14 1 206712737012623083 206712737012623083 206712737012623083 endpoint_16_68_p14 endpoint_16_68_w14
def endpoint_16_68 : CertifiedEndpoint :=
  ⟨⟨16, 68, 1650⟩, 206712737012623083, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_68_flag endpoint_16_68_sources 15 206712737012623083 206712737012623083 rfl endpoint_16_68_base endpoint_16_68_p15) (by decide)⟩
private def endpoint_16_69_flag : Flag := ⟨16, 69, 1566⟩
private def endpoint_16_69_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_16_69_base : receiptBase endpoint_16_69_flag endpoint_16_69_sources = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_w0 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 2 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_w2 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 2 2 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_p4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 4 198854635060927722 = some 198854635060927722 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 2 2 198854635060927722 198854635060927722 198854635060927722 endpoint_16_69_w0 endpoint_16_69_w2
private theorem endpoint_16_69_w4 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 4 2 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_p6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 6 198854635060927722 = some 198854635060927722 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 4 2 198854635060927722 198854635060927722 198854635060927722 endpoint_16_69_p4 endpoint_16_69_w4
private theorem endpoint_16_69_w6 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 6 2 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_p8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 8 198854635060927722 = some 198854635060927722 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 6 2 198854635060927722 198854635060927722 198854635060927722 endpoint_16_69_p6 endpoint_16_69_w6
private theorem endpoint_16_69_w8 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 8 2 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_p10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 10 198854635060927722 = some 198854635060927722 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 8 2 198854635060927722 198854635060927722 198854635060927722 endpoint_16_69_p8 endpoint_16_69_w8
private theorem endpoint_16_69_w10 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 10 2 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_p12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 12 198854635060927722 = some 198854635060927722 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 10 2 198854635060927722 198854635060927722 198854635060927722 endpoint_16_69_p10 endpoint_16_69_w10
private theorem endpoint_16_69_w12 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 12 2 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_p14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 14 198854635060927722 = some 198854635060927722 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 12 2 198854635060927722 198854635060927722 198854635060927722 endpoint_16_69_p12 endpoint_16_69_w12
private theorem endpoint_16_69_w14 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 14 1 198854635060927722 = some 198854635060927722 := by decide +kernel
private theorem endpoint_16_69_p15 : receiptWindow endpoint_16_69_flag endpoint_16_69_sources 0 15 198854635060927722 = some 198854635060927722 :=
  join_receipt_window endpoint_16_69_flag endpoint_16_69_sources 0 14 1 198854635060927722 198854635060927722 198854635060927722 endpoint_16_69_p14 endpoint_16_69_w14
def endpoint_16_69 : CertifiedEndpoint :=
  ⟨⟨16, 69, 1566⟩, 198854635060927722, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_16_69_flag endpoint_16_69_sources 15 198854635060927722 198854635060927722 rfl endpoint_16_69_base endpoint_16_69_p15) (by decide)⟩
private def endpoint_16_70_flag : Flag := ⟨16, 70, 1479⟩
private def endpoint_16_70_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_16_70_base : receiptBase endpoint_16_70_flag endpoint_16_70_sources = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_w0 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 2 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_w2 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 2 2 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_p4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 4 190694248062997678 = some 190694248062997678 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 2 2 190694248062997678 190694248062997678 190694248062997678 endpoint_16_70_w0 endpoint_16_70_w2
private theorem endpoint_16_70_w4 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 4 2 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_p6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 6 190694248062997678 = some 190694248062997678 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 4 2 190694248062997678 190694248062997678 190694248062997678 endpoint_16_70_p4 endpoint_16_70_w4
private theorem endpoint_16_70_w6 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 6 2 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_p8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 8 190694248062997678 = some 190694248062997678 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 6 2 190694248062997678 190694248062997678 190694248062997678 endpoint_16_70_p6 endpoint_16_70_w6
private theorem endpoint_16_70_w8 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 8 2 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_p10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 10 190694248062997678 = some 190694248062997678 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 8 2 190694248062997678 190694248062997678 190694248062997678 endpoint_16_70_p8 endpoint_16_70_w8
private theorem endpoint_16_70_w10 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 10 2 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_p12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 12 190694248062997678 = some 190694248062997678 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 10 2 190694248062997678 190694248062997678 190694248062997678 endpoint_16_70_p10 endpoint_16_70_w10
private theorem endpoint_16_70_w12 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 12 2 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_p14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 14 190694248062997678 = some 190694248062997678 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 12 2 190694248062997678 190694248062997678 190694248062997678 endpoint_16_70_p12 endpoint_16_70_w12
private theorem endpoint_16_70_w14 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 14 1 190694248062997678 = some 190694248062997678 := by decide +kernel
private theorem endpoint_16_70_p15 : receiptWindow endpoint_16_70_flag endpoint_16_70_sources 0 15 190694248062997678 = some 190694248062997678 :=
  join_receipt_window endpoint_16_70_flag endpoint_16_70_sources 0 14 1 190694248062997678 190694248062997678 190694248062997678 endpoint_16_70_p14 endpoint_16_70_w14
def endpoint_16_70 : CertifiedEndpoint :=
  ⟨⟨16, 70, 1479⟩, 190694248062997678, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_16_70_flag endpoint_16_70_sources 15 190694248062997678 190694248062997678 rfl endpoint_16_70_base endpoint_16_70_p15) (by decide)⟩
private def endpoint_16_71_flag : Flag := ⟨16, 71, 1390⟩
private def endpoint_16_71_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_16_71_base : receiptBase endpoint_16_71_flag endpoint_16_71_sources = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_w0 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 2 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_w2 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 2 2 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_p4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 4 182890972897858859 = some 182890972897858859 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 2 2 182890972897858859 182890972897858859 182890972897858859 endpoint_16_71_w0 endpoint_16_71_w2
private theorem endpoint_16_71_w4 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 4 2 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_p6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 6 182890972897858859 = some 182890972897858859 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 4 2 182890972897858859 182890972897858859 182890972897858859 endpoint_16_71_p4 endpoint_16_71_w4
private theorem endpoint_16_71_w6 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 6 2 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_p8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 8 182890972897858859 = some 182890972897858859 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 6 2 182890972897858859 182890972897858859 182890972897858859 endpoint_16_71_p6 endpoint_16_71_w6
private theorem endpoint_16_71_w8 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 8 2 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_p10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 10 182890972897858859 = some 182890972897858859 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 8 2 182890972897858859 182890972897858859 182890972897858859 endpoint_16_71_p8 endpoint_16_71_w8
private theorem endpoint_16_71_w10 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 10 2 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_p12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 12 182890972897858859 = some 182890972897858859 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 10 2 182890972897858859 182890972897858859 182890972897858859 endpoint_16_71_p10 endpoint_16_71_w10
private theorem endpoint_16_71_w12 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 12 2 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_p14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 14 182890972897858859 = some 182890972897858859 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 12 2 182890972897858859 182890972897858859 182890972897858859 endpoint_16_71_p12 endpoint_16_71_w12
private theorem endpoint_16_71_w14 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 14 1 182890972897858859 = some 182890972897858859 := by decide +kernel
private theorem endpoint_16_71_p15 : receiptWindow endpoint_16_71_flag endpoint_16_71_sources 0 15 182890972897858859 = some 182890972897858859 :=
  join_receipt_window endpoint_16_71_flag endpoint_16_71_sources 0 14 1 182890972897858859 182890972897858859 182890972897858859 endpoint_16_71_p14 endpoint_16_71_w14
def endpoint_16_71 : CertifiedEndpoint :=
  ⟨⟨16, 71, 1390⟩, 182890972897858859, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_16_71_flag endpoint_16_71_sources 15 182890972897858859 182890972897858859 rfl endpoint_16_71_base endpoint_16_71_p15) (by decide)⟩
private def endpoint_16_72_flag : Flag := ⟨16, 72, 1297⟩
private def endpoint_16_72_sources : Sources := ⟨contact31, contact21, contact22⟩
private theorem endpoint_16_72_base : receiptBase endpoint_16_72_flag endpoint_16_72_sources = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_w0 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 2 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_w2 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 2 2 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_p4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 4 173691400447668505 = some 173691400447668505 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 2 2 173691400447668505 173691400447668505 173691400447668505 endpoint_16_72_w0 endpoint_16_72_w2
private theorem endpoint_16_72_w4 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 4 2 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_p6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 6 173691400447668505 = some 173691400447668505 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 4 2 173691400447668505 173691400447668505 173691400447668505 endpoint_16_72_p4 endpoint_16_72_w4
private theorem endpoint_16_72_w6 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 6 2 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_p8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 8 173691400447668505 = some 173691400447668505 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 6 2 173691400447668505 173691400447668505 173691400447668505 endpoint_16_72_p6 endpoint_16_72_w6
private theorem endpoint_16_72_w8 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 8 2 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_p10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 10 173691400447668505 = some 173691400447668505 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 8 2 173691400447668505 173691400447668505 173691400447668505 endpoint_16_72_p8 endpoint_16_72_w8
private theorem endpoint_16_72_w10 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 10 2 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_p12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 12 173691400447668505 = some 173691400447668505 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 10 2 173691400447668505 173691400447668505 173691400447668505 endpoint_16_72_p10 endpoint_16_72_w10
private theorem endpoint_16_72_w12 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 12 2 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_p14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 14 173691400447668505 = some 173691400447668505 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 12 2 173691400447668505 173691400447668505 173691400447668505 endpoint_16_72_p12 endpoint_16_72_w12
private theorem endpoint_16_72_w14 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 14 1 173691400447668505 = some 173691400447668505 := by decide +kernel
private theorem endpoint_16_72_p15 : receiptWindow endpoint_16_72_flag endpoint_16_72_sources 0 15 173691400447668505 = some 173691400447668505 :=
  join_receipt_window endpoint_16_72_flag endpoint_16_72_sources 0 14 1 173691400447668505 173691400447668505 173691400447668505 endpoint_16_72_p14 endpoint_16_72_w14
def endpoint_16_72 : CertifiedEndpoint :=
  ⟨⟨16, 72, 1297⟩, 173691400447668505, .terminal ⟨contact31, contact21, contact22⟩ (finish_receipt_window endpoint_16_72_flag endpoint_16_72_sources 15 173691400447668505 173691400447668505 rfl endpoint_16_72_base endpoint_16_72_p15) (by decide)⟩
private def endpoint_16_73_flag : Flag := ⟨16, 73, 1202⟩
private def endpoint_16_73_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_73_base : receiptBase endpoint_16_73_flag endpoint_16_73_sources = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_w0 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 2 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_w2 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 2 2 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_p4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 4 163912545240554808 = some 163912545240554808 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 2 2 163912545240554808 163912545240554808 163912545240554808 endpoint_16_73_w0 endpoint_16_73_w2
private theorem endpoint_16_73_w4 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 4 2 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_p6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 6 163912545240554808 = some 163912545240554808 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 4 2 163912545240554808 163912545240554808 163912545240554808 endpoint_16_73_p4 endpoint_16_73_w4
private theorem endpoint_16_73_w6 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 6 2 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_p8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 8 163912545240554808 = some 163912545240554808 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 6 2 163912545240554808 163912545240554808 163912545240554808 endpoint_16_73_p6 endpoint_16_73_w6
private theorem endpoint_16_73_w8 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 8 2 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_p10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 10 163912545240554808 = some 163912545240554808 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 8 2 163912545240554808 163912545240554808 163912545240554808 endpoint_16_73_p8 endpoint_16_73_w8
private theorem endpoint_16_73_w10 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 10 2 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_p12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 12 163912545240554808 = some 163912545240554808 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 10 2 163912545240554808 163912545240554808 163912545240554808 endpoint_16_73_p10 endpoint_16_73_w10
private theorem endpoint_16_73_w12 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 12 2 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_p14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 14 163912545240554808 = some 163912545240554808 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 12 2 163912545240554808 163912545240554808 163912545240554808 endpoint_16_73_p12 endpoint_16_73_w12
private theorem endpoint_16_73_w14 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 14 1 163912545240554808 = some 163912545240554808 := by decide +kernel
private theorem endpoint_16_73_p15 : receiptWindow endpoint_16_73_flag endpoint_16_73_sources 0 15 163912545240554808 = some 163912545240554808 :=
  join_receipt_window endpoint_16_73_flag endpoint_16_73_sources 0 14 1 163912545240554808 163912545240554808 163912545240554808 endpoint_16_73_p14 endpoint_16_73_w14
def endpoint_16_73 : CertifiedEndpoint :=
  ⟨⟨16, 73, 1202⟩, 163912545240554808, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_73_flag endpoint_16_73_sources 15 163912545240554808 163912545240554808 rfl endpoint_16_73_base endpoint_16_73_p15) (by decide)⟩
private def endpoint_16_74_flag : Flag := ⟨16, 74, 1104⟩
private def endpoint_16_74_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_16_74_base : receiptBase endpoint_16_74_flag endpoint_16_74_sources = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_w0 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 2 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_w2 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 2 2 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_p4 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 4 152545219053244082 = some 152545219053244082 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 2 2 152545219053244082 152545219053244082 152545219053244082 endpoint_16_74_w0 endpoint_16_74_w2
private theorem endpoint_16_74_w4 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 4 2 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_p6 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 6 152545219053244082 = some 152545219053244082 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 4 2 152545219053244082 152545219053244082 152545219053244082 endpoint_16_74_p4 endpoint_16_74_w4
private theorem endpoint_16_74_w6 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 6 2 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_p8 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 8 152545219053244082 = some 152545219053244082 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 6 2 152545219053244082 152545219053244082 152545219053244082 endpoint_16_74_p6 endpoint_16_74_w6
private theorem endpoint_16_74_w8 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 8 2 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_p10 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 10 152545219053244082 = some 152545219053244082 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 8 2 152545219053244082 152545219053244082 152545219053244082 endpoint_16_74_p8 endpoint_16_74_w8
private theorem endpoint_16_74_w10 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 10 2 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_p12 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 12 152545219053244082 = some 152545219053244082 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 10 2 152545219053244082 152545219053244082 152545219053244082 endpoint_16_74_p10 endpoint_16_74_w10
private theorem endpoint_16_74_w12 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 12 2 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_p14 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 14 152545219053244082 = some 152545219053244082 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 12 2 152545219053244082 152545219053244082 152545219053244082 endpoint_16_74_p12 endpoint_16_74_w12
private theorem endpoint_16_74_w14 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 14 1 152545219053244082 = some 152545219053244082 := by decide +kernel
private theorem endpoint_16_74_p15 : receiptWindow endpoint_16_74_flag endpoint_16_74_sources 0 15 152545219053244082 = some 152545219053244082 :=
  join_receipt_window endpoint_16_74_flag endpoint_16_74_sources 0 14 1 152545219053244082 152545219053244082 152545219053244082 endpoint_16_74_p14 endpoint_16_74_w14
def endpoint_16_74 : CertifiedEndpoint :=
  ⟨⟨16, 74, 1104⟩, 152545219053244082, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_16_74_flag endpoint_16_74_sources 15 152545219053244082 152545219053244082 rfl endpoint_16_74_base endpoint_16_74_p15) (by decide)⟩
def endpoint_16_75 : CertifiedEndpoint :=
  ⟨⟨16, 75, 1002⟩, 255667410390235063, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_76 : CertifiedEndpoint :=
  ⟨⟨16, 76, 898⟩, 231274177008531670, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_77 : CertifiedEndpoint :=
  ⟨⟨16, 77, 791⟩, 205221670490343156, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_78 : CertifiedEndpoint :=
  ⟨⟨16, 78, 681⟩, 177473863754632603, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_79 : CertifiedEndpoint :=
  ⟨⟨16, 79, 567⟩, 147712508950812288, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_80 : CertifiedEndpoint :=
  ⟨⟨16, 80, 451⟩, 116462017527942801, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_81 : CertifiedEndpoint :=
  ⟨⟨16, 81, 331⟩, 83117917856881512, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_82 : CertifiedEndpoint :=
  ⟨⟨16, 82, 208⟩, 47926403626142308, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_83 : CertifiedEndpoint :=
  ⟨⟨16, 83, 83⟩, 11149680560255484, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_17 : CertifiedEndpoint :=
  ⟨⟨17, 17, 3854⟩, 152953578110570839, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_18 : CertifiedEndpoint :=
  ⟨⟨17, 18, 3824⟩, 157086856340963524, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_19 : CertifiedEndpoint :=
  ⟨⟨17, 19, 3794⟩, 161136122907328429, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_20 : CertifiedEndpoint :=
  ⟨⟨17, 20, 3763⟩, 175765014372429091, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_21 : CertifiedEndpoint :=
  ⟨⟨17, 21, 3732⟩, 190125480897528451, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_22 : CertifiedEndpoint :=
  ⟨⟨17, 22, 3700⟩, 204162124571713220, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_23 : CertifiedEndpoint :=
  ⟨⟨17, 23, 3668⟩, 217921821879229979, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_24 : CertifiedEndpoint :=
  ⟨⟨17, 24, 3635⟩, 231340653482498731, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_25 : CertifiedEndpoint :=
  ⟨⟨17, 25, 3602⟩, 244474017292432765, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_26 : CertifiedEndpoint :=
  ⟨⟨17, 26, 3568⟩, 257249472544785376, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_17_27_flag : Flag := ⟨17, 27, 3533⟩
private def endpoint_17_27_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_27_base : receiptBase endpoint_17_27_flag endpoint_17_27_sources = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_w0 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_w2 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 2 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_p4 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 4 194591328813099177 = some 194591328813099177 :=
  join_receipt_window endpoint_17_27_flag endpoint_17_27_sources 0 2 2 194591328813099177 194591328813099177 194591328813099177 endpoint_17_27_w0 endpoint_17_27_w2
private theorem endpoint_17_27_w4 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 4 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_p6 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 6 194591328813099177 = some 194591328813099177 :=
  join_receipt_window endpoint_17_27_flag endpoint_17_27_sources 0 4 2 194591328813099177 194591328813099177 194591328813099177 endpoint_17_27_p4 endpoint_17_27_w4
private theorem endpoint_17_27_w6 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 6 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_p8 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 8 194591328813099177 = some 194591328813099177 :=
  join_receipt_window endpoint_17_27_flag endpoint_17_27_sources 0 6 2 194591328813099177 194591328813099177 194591328813099177 endpoint_17_27_p6 endpoint_17_27_w6
private theorem endpoint_17_27_w8 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 8 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_p10 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 10 194591328813099177 = some 194591328813099177 :=
  join_receipt_window endpoint_17_27_flag endpoint_17_27_sources 0 8 2 194591328813099177 194591328813099177 194591328813099177 endpoint_17_27_p8 endpoint_17_27_w8
private theorem endpoint_17_27_w10 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 10 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_p12 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 12 194591328813099177 = some 194591328813099177 :=
  join_receipt_window endpoint_17_27_flag endpoint_17_27_sources 0 10 2 194591328813099177 194591328813099177 194591328813099177 endpoint_17_27_p10 endpoint_17_27_w10
private theorem endpoint_17_27_w12 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 12 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_p14 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 14 194591328813099177 = some 194591328813099177 :=
  join_receipt_window endpoint_17_27_flag endpoint_17_27_sources 0 12 2 194591328813099177 194591328813099177 194591328813099177 endpoint_17_27_p12 endpoint_17_27_w12
private theorem endpoint_17_27_w14 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 14 2 194591328813099177 = some 194591328813099177 := by decide +kernel
private theorem endpoint_17_27_p16 : receiptWindow endpoint_17_27_flag endpoint_17_27_sources 0 16 194591328813099177 = some 194591328813099177 :=
  join_receipt_window endpoint_17_27_flag endpoint_17_27_sources 0 14 2 194591328813099177 194591328813099177 194591328813099177 endpoint_17_27_p14 endpoint_17_27_w14
def endpoint_17_27 : CertifiedEndpoint :=
  ⟨⟨17, 27, 3533⟩, 194591328813099177, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_27_flag endpoint_17_27_sources 16 194591328813099177 194591328813099177 rfl endpoint_17_27_base endpoint_17_27_p16) (by decide)⟩
private def endpoint_17_28_flag : Flag := ⟨17, 28, 3498⟩
private def endpoint_17_28_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_28_base : receiptBase endpoint_17_28_flag endpoint_17_28_sources = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_w0 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_w2 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 2 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_p4 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 4 198423380477811800 = some 198423380477811800 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 2 2 198423380477811800 198423380477811800 198423380477811800 endpoint_17_28_w0 endpoint_17_28_w2
private theorem endpoint_17_28_w4 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 4 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_p6 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 6 198423380477811800 = some 198423380477811800 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 4 2 198423380477811800 198423380477811800 198423380477811800 endpoint_17_28_p4 endpoint_17_28_w4
private theorem endpoint_17_28_w6 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 6 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_p8 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 8 198423380477811800 = some 198423380477811800 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 6 2 198423380477811800 198423380477811800 198423380477811800 endpoint_17_28_p6 endpoint_17_28_w6
private theorem endpoint_17_28_w8 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 8 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_p10 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 10 198423380477811800 = some 198423380477811800 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 8 2 198423380477811800 198423380477811800 198423380477811800 endpoint_17_28_p8 endpoint_17_28_w8
private theorem endpoint_17_28_w10 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 10 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_p12 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 12 198423380477811800 = some 198423380477811800 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 10 2 198423380477811800 198423380477811800 198423380477811800 endpoint_17_28_p10 endpoint_17_28_w10
private theorem endpoint_17_28_w12 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 12 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_p14 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 14 198423380477811800 = some 198423380477811800 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 12 2 198423380477811800 198423380477811800 198423380477811800 endpoint_17_28_p12 endpoint_17_28_w12
private theorem endpoint_17_28_w14 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 14 2 198423380477811800 = some 198423380477811800 := by decide +kernel
private theorem endpoint_17_28_p16 : receiptWindow endpoint_17_28_flag endpoint_17_28_sources 0 16 198423380477811800 = some 198423380477811800 :=
  join_receipt_window endpoint_17_28_flag endpoint_17_28_sources 0 14 2 198423380477811800 198423380477811800 198423380477811800 endpoint_17_28_p14 endpoint_17_28_w14
def endpoint_17_28 : CertifiedEndpoint :=
  ⟨⟨17, 28, 3498⟩, 198423380477811800, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_28_flag endpoint_17_28_sources 16 198423380477811800 198423380477811800 rfl endpoint_17_28_base endpoint_17_28_p16) (by decide)⟩
private def endpoint_17_29_flag : Flag := ⟨17, 29, 3462⟩
private def endpoint_17_29_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_29_base : receiptBase endpoint_17_29_flag endpoint_17_29_sources = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_w0 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_w2 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 2 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_p4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 4 202083159106408481 = some 202083159106408481 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 2 2 202083159106408481 202083159106408481 202083159106408481 endpoint_17_29_w0 endpoint_17_29_w2
private theorem endpoint_17_29_w4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 4 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_p6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 6 202083159106408481 = some 202083159106408481 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 4 2 202083159106408481 202083159106408481 202083159106408481 endpoint_17_29_p4 endpoint_17_29_w4
private theorem endpoint_17_29_w6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 6 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_p8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 8 202083159106408481 = some 202083159106408481 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 6 2 202083159106408481 202083159106408481 202083159106408481 endpoint_17_29_p6 endpoint_17_29_w6
private theorem endpoint_17_29_w8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 8 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_p10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 10 202083159106408481 = some 202083159106408481 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 8 2 202083159106408481 202083159106408481 202083159106408481 endpoint_17_29_p8 endpoint_17_29_w8
private theorem endpoint_17_29_w10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 10 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_p12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 12 202083159106408481 = some 202083159106408481 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 10 2 202083159106408481 202083159106408481 202083159106408481 endpoint_17_29_p10 endpoint_17_29_w10
private theorem endpoint_17_29_w12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 12 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_p14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 14 202083159106408481 = some 202083159106408481 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 12 2 202083159106408481 202083159106408481 202083159106408481 endpoint_17_29_p12 endpoint_17_29_w12
private theorem endpoint_17_29_w14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 14 2 202083159106408481 = some 202083159106408481 := by decide +kernel
private theorem endpoint_17_29_p16 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 16 202083159106408481 = some 202083159106408481 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 14 2 202083159106408481 202083159106408481 202083159106408481 endpoint_17_29_p14 endpoint_17_29_w14
def endpoint_17_29 : CertifiedEndpoint :=
  ⟨⟨17, 29, 3462⟩, 202083159106408481, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_29_flag endpoint_17_29_sources 16 202083159106408481 202083159106408481 rfl endpoint_17_29_base endpoint_17_29_p16) (by decide)⟩
private def endpoint_17_30_flag : Flag := ⟨17, 30, 3425⟩
private def endpoint_17_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_30_base : receiptBase endpoint_17_30_flag endpoint_17_30_sources = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_w0 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_w2 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 2 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_p4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 4 205565827348139122 = some 205565827348139122 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 2 2 205565827348139122 205565827348139122 205565827348139122 endpoint_17_30_w0 endpoint_17_30_w2
private theorem endpoint_17_30_w4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 4 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_p6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 6 205565827348139122 = some 205565827348139122 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 4 2 205565827348139122 205565827348139122 205565827348139122 endpoint_17_30_p4 endpoint_17_30_w4
private theorem endpoint_17_30_w6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 6 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_p8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 8 205565827348139122 = some 205565827348139122 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 6 2 205565827348139122 205565827348139122 205565827348139122 endpoint_17_30_p6 endpoint_17_30_w6
private theorem endpoint_17_30_w8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 8 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_p10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 10 205565827348139122 = some 205565827348139122 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 8 2 205565827348139122 205565827348139122 205565827348139122 endpoint_17_30_p8 endpoint_17_30_w8
private theorem endpoint_17_30_w10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 10 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_p12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 12 205565827348139122 = some 205565827348139122 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 10 2 205565827348139122 205565827348139122 205565827348139122 endpoint_17_30_p10 endpoint_17_30_w10
private theorem endpoint_17_30_w12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 12 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_p14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 14 205565827348139122 = some 205565827348139122 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 12 2 205565827348139122 205565827348139122 205565827348139122 endpoint_17_30_p12 endpoint_17_30_w12
private theorem endpoint_17_30_w14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 14 2 205565827348139122 = some 205565827348139122 := by decide +kernel
private theorem endpoint_17_30_p16 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 16 205565827348139122 = some 205565827348139122 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 14 2 205565827348139122 205565827348139122 205565827348139122 endpoint_17_30_p14 endpoint_17_30_w14
def endpoint_17_30 : CertifiedEndpoint :=
  ⟨⟨17, 30, 3425⟩, 205565827348139122, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_30_flag endpoint_17_30_sources 16 205565827348139122 205565827348139122 rfl endpoint_17_30_base endpoint_17_30_p16) (by decide)⟩
private def endpoint_17_31_flag : Flag := ⟨17, 31, 3388⟩
private def endpoint_17_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_31_base : receiptBase endpoint_17_31_flag endpoint_17_31_sources = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_w0 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_w2 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 2 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_p4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 4 208927554621749267 = some 208927554621749267 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 2 2 208927554621749267 208927554621749267 208927554621749267 endpoint_17_31_w0 endpoint_17_31_w2
private theorem endpoint_17_31_w4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 4 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_p6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 6 208927554621749267 = some 208927554621749267 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 4 2 208927554621749267 208927554621749267 208927554621749267 endpoint_17_31_p4 endpoint_17_31_w4
private theorem endpoint_17_31_w6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 6 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_p8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 8 208927554621749267 = some 208927554621749267 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 6 2 208927554621749267 208927554621749267 208927554621749267 endpoint_17_31_p6 endpoint_17_31_w6
private theorem endpoint_17_31_w8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 8 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_p10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 10 208927554621749267 = some 208927554621749267 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 8 2 208927554621749267 208927554621749267 208927554621749267 endpoint_17_31_p8 endpoint_17_31_w8
private theorem endpoint_17_31_w10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 10 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_p12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 12 208927554621749267 = some 208927554621749267 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 10 2 208927554621749267 208927554621749267 208927554621749267 endpoint_17_31_p10 endpoint_17_31_w10
private theorem endpoint_17_31_w12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 12 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_p14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 14 208927554621749267 = some 208927554621749267 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 12 2 208927554621749267 208927554621749267 208927554621749267 endpoint_17_31_p12 endpoint_17_31_w12
private theorem endpoint_17_31_w14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 14 2 208927554621749267 = some 208927554621749267 := by decide +kernel
private theorem endpoint_17_31_p16 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 16 208927554621749267 = some 208927554621749267 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 14 2 208927554621749267 208927554621749267 208927554621749267 endpoint_17_31_p14 endpoint_17_31_w14
def endpoint_17_31 : CertifiedEndpoint :=
  ⟨⟨17, 31, 3388⟩, 208927554621749267, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_31_flag endpoint_17_31_sources 16 208927554621749267 208927554621749267 rfl endpoint_17_31_base endpoint_17_31_p16) (by decide)⟩
private def endpoint_17_32_flag : Flag := ⟨17, 32, 3350⟩
private def endpoint_17_32_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_32_base : receiptBase endpoint_17_32_flag endpoint_17_32_sources = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_w0 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_w2 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 2 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_p4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 4 212105721707493240 = some 212105721707493240 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 2 2 212105721707493240 212105721707493240 212105721707493240 endpoint_17_32_w0 endpoint_17_32_w2
private theorem endpoint_17_32_w4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 4 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_p6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 6 212105721707493240 = some 212105721707493240 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 4 2 212105721707493240 212105721707493240 212105721707493240 endpoint_17_32_p4 endpoint_17_32_w4
private theorem endpoint_17_32_w6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 6 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_p8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 8 212105721707493240 = some 212105721707493240 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 6 2 212105721707493240 212105721707493240 212105721707493240 endpoint_17_32_p6 endpoint_17_32_w6
private theorem endpoint_17_32_w8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 8 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_p10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 10 212105721707493240 = some 212105721707493240 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 8 2 212105721707493240 212105721707493240 212105721707493240 endpoint_17_32_p8 endpoint_17_32_w8
private theorem endpoint_17_32_w10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 10 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_p12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 12 212105721707493240 = some 212105721707493240 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 10 2 212105721707493240 212105721707493240 212105721707493240 endpoint_17_32_p10 endpoint_17_32_w10
private theorem endpoint_17_32_w12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 12 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_p14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 14 212105721707493240 = some 212105721707493240 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 12 2 212105721707493240 212105721707493240 212105721707493240 endpoint_17_32_p12 endpoint_17_32_w12
private theorem endpoint_17_32_w14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 14 2 212105721707493240 = some 212105721707493240 := by decide +kernel
private theorem endpoint_17_32_p16 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 16 212105721707493240 = some 212105721707493240 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 14 2 212105721707493240 212105721707493240 212105721707493240 endpoint_17_32_p14 endpoint_17_32_w14
def endpoint_17_32 : CertifiedEndpoint :=
  ⟨⟨17, 32, 3350⟩, 212105721707493240, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_32_flag endpoint_17_32_sources 16 212105721707493240 212105721707493240 rfl endpoint_17_32_base endpoint_17_32_p16) (by decide)⟩
private def endpoint_17_33_flag : Flag := ⟨17, 33, 3312⟩
private def endpoint_17_33_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_33_base : receiptBase endpoint_17_33_flag endpoint_17_33_sources = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_w0 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_w2 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 2 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_p4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 4 215159722924616652 = some 215159722924616652 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 2 2 215159722924616652 215159722924616652 215159722924616652 endpoint_17_33_w0 endpoint_17_33_w2
private theorem endpoint_17_33_w4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 4 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_p6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 6 215159722924616652 = some 215159722924616652 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 4 2 215159722924616652 215159722924616652 215159722924616652 endpoint_17_33_p4 endpoint_17_33_w4
private theorem endpoint_17_33_w6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 6 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_p8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 8 215159722924616652 = some 215159722924616652 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 6 2 215159722924616652 215159722924616652 215159722924616652 endpoint_17_33_p6 endpoint_17_33_w6
private theorem endpoint_17_33_w8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 8 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_p10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 10 215159722924616652 = some 215159722924616652 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 8 2 215159722924616652 215159722924616652 215159722924616652 endpoint_17_33_p8 endpoint_17_33_w8
private theorem endpoint_17_33_w10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 10 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_p12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 12 215159722924616652 = some 215159722924616652 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 10 2 215159722924616652 215159722924616652 215159722924616652 endpoint_17_33_p10 endpoint_17_33_w10
private theorem endpoint_17_33_w12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 12 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_p14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 14 215159722924616652 = some 215159722924616652 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 12 2 215159722924616652 215159722924616652 215159722924616652 endpoint_17_33_p12 endpoint_17_33_w12
private theorem endpoint_17_33_w14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 14 2 215159722924616652 = some 215159722924616652 := by decide +kernel
private theorem endpoint_17_33_p16 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 16 215159722924616652 = some 215159722924616652 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 14 2 215159722924616652 215159722924616652 215159722924616652 endpoint_17_33_p14 endpoint_17_33_w14
def endpoint_17_33 : CertifiedEndpoint :=
  ⟨⟨17, 33, 3312⟩, 215159722924616652, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_33_flag endpoint_17_33_sources 16 215159722924616652 215159722924616652 rfl endpoint_17_33_base endpoint_17_33_p16) (by decide)⟩
private def endpoint_17_34_flag : Flag := ⟨17, 34, 3273⟩
private def endpoint_17_34_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_17_34_base : receiptBase endpoint_17_34_flag endpoint_17_34_sources = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_w0 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_w2 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 2 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_p4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 4 217531925983397631 = some 217531925983397631 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 2 2 217531925983397631 217531925983397631 217531925983397631 endpoint_17_34_w0 endpoint_17_34_w2
private theorem endpoint_17_34_w4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 4 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_p6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 6 217531925983397631 = some 217531925983397631 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 4 2 217531925983397631 217531925983397631 217531925983397631 endpoint_17_34_p4 endpoint_17_34_w4
private theorem endpoint_17_34_w6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 6 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_p8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 8 217531925983397631 = some 217531925983397631 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 6 2 217531925983397631 217531925983397631 217531925983397631 endpoint_17_34_p6 endpoint_17_34_w6
private theorem endpoint_17_34_w8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 8 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_p10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 10 217531925983397631 = some 217531925983397631 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 8 2 217531925983397631 217531925983397631 217531925983397631 endpoint_17_34_p8 endpoint_17_34_w8
private theorem endpoint_17_34_w10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 10 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_p12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 12 217531925983397631 = some 217531925983397631 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 10 2 217531925983397631 217531925983397631 217531925983397631 endpoint_17_34_p10 endpoint_17_34_w10
private theorem endpoint_17_34_w12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 12 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_p14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 14 217531925983397631 = some 217531925983397631 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 12 2 217531925983397631 217531925983397631 217531925983397631 endpoint_17_34_p12 endpoint_17_34_w12
private theorem endpoint_17_34_w14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 14 2 217531925983397631 = some 217531925983397631 := by decide +kernel
private theorem endpoint_17_34_p16 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 16 217531925983397631 = some 217531925983397631 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 14 2 217531925983397631 217531925983397631 217531925983397631 endpoint_17_34_p14 endpoint_17_34_w14
def endpoint_17_34 : CertifiedEndpoint :=
  ⟨⟨17, 34, 3273⟩, 217531925983397631, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_17_34_flag endpoint_17_34_sources 16 217531925983397631 217531925983397631 rfl endpoint_17_34_base endpoint_17_34_p16) (by decide)⟩
private def endpoint_17_35_flag : Flag := ⟨17, 35, 3233⟩
private def endpoint_17_35_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_35_base : receiptBase endpoint_17_35_flag endpoint_17_35_sources = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_w0 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_w2 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 2 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_p4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 4 220692858041514464 = some 220692858041514464 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 2 2 220692858041514464 220692858041514464 220692858041514464 endpoint_17_35_w0 endpoint_17_35_w2
private theorem endpoint_17_35_w4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 4 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_p6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 6 220692858041514464 = some 220692858041514464 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 4 2 220692858041514464 220692858041514464 220692858041514464 endpoint_17_35_p4 endpoint_17_35_w4
private theorem endpoint_17_35_w6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 6 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_p8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 8 220692858041514464 = some 220692858041514464 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 6 2 220692858041514464 220692858041514464 220692858041514464 endpoint_17_35_p6 endpoint_17_35_w6
private theorem endpoint_17_35_w8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 8 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_p10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 10 220692858041514464 = some 220692858041514464 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 8 2 220692858041514464 220692858041514464 220692858041514464 endpoint_17_35_p8 endpoint_17_35_w8
private theorem endpoint_17_35_w10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 10 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_p12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 12 220692858041514464 = some 220692858041514464 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 10 2 220692858041514464 220692858041514464 220692858041514464 endpoint_17_35_p10 endpoint_17_35_w10
private theorem endpoint_17_35_w12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 12 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_p14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 14 220692858041514464 = some 220692858041514464 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 12 2 220692858041514464 220692858041514464 220692858041514464 endpoint_17_35_p12 endpoint_17_35_w12
private theorem endpoint_17_35_w14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 14 2 220692858041514464 = some 220692858041514464 := by decide +kernel
private theorem endpoint_17_35_p16 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 16 220692858041514464 = some 220692858041514464 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 14 2 220692858041514464 220692858041514464 220692858041514464 endpoint_17_35_p14 endpoint_17_35_w14
def endpoint_17_35 : CertifiedEndpoint :=
  ⟨⟨17, 35, 3233⟩, 220692858041514464, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_35_flag endpoint_17_35_sources 16 220692858041514464 220692858041514464 rfl endpoint_17_35_base endpoint_17_35_p16) (by decide)⟩
private def endpoint_17_36_flag : Flag := ⟨17, 36, 3192⟩
private def endpoint_17_36_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_36_base : receiptBase endpoint_17_36_flag endpoint_17_36_sources = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_w0 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_w2 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 2 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_p4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 4 223162317239788668 = some 223162317239788668 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 2 2 223162317239788668 223162317239788668 223162317239788668 endpoint_17_36_w0 endpoint_17_36_w2
private theorem endpoint_17_36_w4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 4 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_p6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 6 223162317239788668 = some 223162317239788668 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 4 2 223162317239788668 223162317239788668 223162317239788668 endpoint_17_36_p4 endpoint_17_36_w4
private theorem endpoint_17_36_w6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 6 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_p8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 8 223162317239788668 = some 223162317239788668 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 6 2 223162317239788668 223162317239788668 223162317239788668 endpoint_17_36_p6 endpoint_17_36_w6
private theorem endpoint_17_36_w8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 8 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_p10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 10 223162317239788668 = some 223162317239788668 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 8 2 223162317239788668 223162317239788668 223162317239788668 endpoint_17_36_p8 endpoint_17_36_w8
private theorem endpoint_17_36_w10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 10 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_p12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 12 223162317239788668 = some 223162317239788668 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 10 2 223162317239788668 223162317239788668 223162317239788668 endpoint_17_36_p10 endpoint_17_36_w10
private theorem endpoint_17_36_w12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 12 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_p14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 14 223162317239788668 = some 223162317239788668 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 12 2 223162317239788668 223162317239788668 223162317239788668 endpoint_17_36_p12 endpoint_17_36_w12
private theorem endpoint_17_36_w14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 14 2 223162317239788668 = some 223162317239788668 := by decide +kernel
private theorem endpoint_17_36_p16 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 16 223162317239788668 = some 223162317239788668 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 14 2 223162317239788668 223162317239788668 223162317239788668 endpoint_17_36_p14 endpoint_17_36_w14
def endpoint_17_36 : CertifiedEndpoint :=
  ⟨⟨17, 36, 3192⟩, 223162317239788668, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_36_flag endpoint_17_36_sources 16 223162317239788668 223162317239788668 rfl endpoint_17_36_base endpoint_17_36_p16) (by decide)⟩
private def endpoint_17_37_flag : Flag := ⟨17, 37, 3151⟩
private def endpoint_17_37_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_37_base : receiptBase endpoint_17_37_flag endpoint_17_37_sources = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_w0 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_w2 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 2 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_p4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 4 225497935867942113 = some 225497935867942113 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 2 2 225497935867942113 225497935867942113 225497935867942113 endpoint_17_37_w0 endpoint_17_37_w2
private theorem endpoint_17_37_w4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 4 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_p6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 6 225497935867942113 = some 225497935867942113 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 4 2 225497935867942113 225497935867942113 225497935867942113 endpoint_17_37_p4 endpoint_17_37_w4
private theorem endpoint_17_37_w6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 6 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_p8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 8 225497935867942113 = some 225497935867942113 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 6 2 225497935867942113 225497935867942113 225497935867942113 endpoint_17_37_p6 endpoint_17_37_w6
private theorem endpoint_17_37_w8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 8 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_p10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 10 225497935867942113 = some 225497935867942113 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 8 2 225497935867942113 225497935867942113 225497935867942113 endpoint_17_37_p8 endpoint_17_37_w8
private theorem endpoint_17_37_w10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 10 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_p12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 12 225497935867942113 = some 225497935867942113 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 10 2 225497935867942113 225497935867942113 225497935867942113 endpoint_17_37_p10 endpoint_17_37_w10
private theorem endpoint_17_37_w12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 12 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_p14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 14 225497935867942113 = some 225497935867942113 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 12 2 225497935867942113 225497935867942113 225497935867942113 endpoint_17_37_p12 endpoint_17_37_w12
private theorem endpoint_17_37_w14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 14 2 225497935867942113 = some 225497935867942113 := by decide +kernel
private theorem endpoint_17_37_p16 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 16 225497935867942113 = some 225497935867942113 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 14 2 225497935867942113 225497935867942113 225497935867942113 endpoint_17_37_p14 endpoint_17_37_w14
def endpoint_17_37 : CertifiedEndpoint :=
  ⟨⟨17, 37, 3151⟩, 225497935867942113, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_37_flag endpoint_17_37_sources 16 225497935867942113 225497935867942113 rfl endpoint_17_37_base endpoint_17_37_p16) (by decide)⟩
private def endpoint_17_38_flag : Flag := ⟨17, 38, 3108⟩
private def endpoint_17_38_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_38_base : receiptBase endpoint_17_38_flag endpoint_17_38_sources = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_w0 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_w2 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 2 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_p4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 4 227555126083483051 = some 227555126083483051 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 2 2 227555126083483051 227555126083483051 227555126083483051 endpoint_17_38_w0 endpoint_17_38_w2
private theorem endpoint_17_38_w4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 4 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_p6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 6 227555126083483051 = some 227555126083483051 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 4 2 227555126083483051 227555126083483051 227555126083483051 endpoint_17_38_p4 endpoint_17_38_w4
private theorem endpoint_17_38_w6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 6 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_p8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 8 227555126083483051 = some 227555126083483051 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 6 2 227555126083483051 227555126083483051 227555126083483051 endpoint_17_38_p6 endpoint_17_38_w6
private theorem endpoint_17_38_w8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 8 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_p10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 10 227555126083483051 = some 227555126083483051 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 8 2 227555126083483051 227555126083483051 227555126083483051 endpoint_17_38_p8 endpoint_17_38_w8
private theorem endpoint_17_38_w10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 10 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_p12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 12 227555126083483051 = some 227555126083483051 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 10 2 227555126083483051 227555126083483051 227555126083483051 endpoint_17_38_p10 endpoint_17_38_w10
private theorem endpoint_17_38_w12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 12 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_p14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 14 227555126083483051 = some 227555126083483051 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 12 2 227555126083483051 227555126083483051 227555126083483051 endpoint_17_38_p12 endpoint_17_38_w12
private theorem endpoint_17_38_w14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 14 2 227555126083483051 = some 227555126083483051 := by decide +kernel
private theorem endpoint_17_38_p16 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 16 227555126083483051 = some 227555126083483051 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 14 2 227555126083483051 227555126083483051 227555126083483051 endpoint_17_38_p14 endpoint_17_38_w14
def endpoint_17_38 : CertifiedEndpoint :=
  ⟨⟨17, 38, 3108⟩, 227555126083483051, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_38_flag endpoint_17_38_sources 16 227555126083483051 227555126083483051 rfl endpoint_17_38_base endpoint_17_38_p16) (by decide)⟩
private def endpoint_17_39_flag : Flag := ⟨17, 39, 3065⟩
private def endpoint_17_39_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_39_base : receiptBase endpoint_17_39_flag endpoint_17_39_sources = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_w0 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_w2 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 2 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_p4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 4 229472025927903098 = some 229472025927903098 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 2 2 229472025927903098 229472025927903098 229472025927903098 endpoint_17_39_w0 endpoint_17_39_w2
private theorem endpoint_17_39_w4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 4 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_p6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 6 229472025927903098 = some 229472025927903098 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 4 2 229472025927903098 229472025927903098 229472025927903098 endpoint_17_39_p4 endpoint_17_39_w4
private theorem endpoint_17_39_w6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 6 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_p8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 8 229472025927903098 = some 229472025927903098 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 6 2 229472025927903098 229472025927903098 229472025927903098 endpoint_17_39_p6 endpoint_17_39_w6
private theorem endpoint_17_39_w8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 8 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_p10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 10 229472025927903098 = some 229472025927903098 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 8 2 229472025927903098 229472025927903098 229472025927903098 endpoint_17_39_p8 endpoint_17_39_w8
private theorem endpoint_17_39_w10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 10 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_p12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 12 229472025927903098 = some 229472025927903098 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 10 2 229472025927903098 229472025927903098 229472025927903098 endpoint_17_39_p10 endpoint_17_39_w10
private theorem endpoint_17_39_w12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 12 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_p14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 14 229472025927903098 = some 229472025927903098 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 12 2 229472025927903098 229472025927903098 229472025927903098 endpoint_17_39_p12 endpoint_17_39_w12
private theorem endpoint_17_39_w14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 14 2 229472025927903098 = some 229472025927903098 := by decide +kernel
private theorem endpoint_17_39_p16 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 16 229472025927903098 = some 229472025927903098 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 14 2 229472025927903098 229472025927903098 229472025927903098 endpoint_17_39_p14 endpoint_17_39_w14
def endpoint_17_39 : CertifiedEndpoint :=
  ⟨⟨17, 39, 3065⟩, 229472025927903098, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_39_flag endpoint_17_39_sources 16 229472025927903098 229472025927903098 rfl endpoint_17_39_base endpoint_17_39_p16) (by decide)⟩
private def endpoint_17_40_flag : Flag := ⟨17, 40, 3021⟩
private def endpoint_17_40_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_40_base : receiptBase endpoint_17_40_flag endpoint_17_40_sources = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_w0 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_w2 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 2 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_p4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 4 231173116579456315 = some 231173116579456315 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 2 2 231173116579456315 231173116579456315 231173116579456315 endpoint_17_40_w0 endpoint_17_40_w2
private theorem endpoint_17_40_w4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 4 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_p6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 6 231173116579456315 = some 231173116579456315 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 4 2 231173116579456315 231173116579456315 231173116579456315 endpoint_17_40_p4 endpoint_17_40_w4
private theorem endpoint_17_40_w6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 6 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_p8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 8 231173116579456315 = some 231173116579456315 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 6 2 231173116579456315 231173116579456315 231173116579456315 endpoint_17_40_p6 endpoint_17_40_w6
private theorem endpoint_17_40_w8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 8 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_p10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 10 231173116579456315 = some 231173116579456315 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 8 2 231173116579456315 231173116579456315 231173116579456315 endpoint_17_40_p8 endpoint_17_40_w8
private theorem endpoint_17_40_w10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 10 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_p12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 12 231173116579456315 = some 231173116579456315 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 10 2 231173116579456315 231173116579456315 231173116579456315 endpoint_17_40_p10 endpoint_17_40_w10
private theorem endpoint_17_40_w12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 12 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_p14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 14 231173116579456315 = some 231173116579456315 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 12 2 231173116579456315 231173116579456315 231173116579456315 endpoint_17_40_p12 endpoint_17_40_w12
private theorem endpoint_17_40_w14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 14 2 231173116579456315 = some 231173116579456315 := by decide +kernel
private theorem endpoint_17_40_p16 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 16 231173116579456315 = some 231173116579456315 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 14 2 231173116579456315 231173116579456315 231173116579456315 endpoint_17_40_p14 endpoint_17_40_w14
def endpoint_17_40 : CertifiedEndpoint :=
  ⟨⟨17, 40, 3021⟩, 231173116579456315, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_40_flag endpoint_17_40_sources 16 231173116579456315 231173116579456315 rfl endpoint_17_40_base endpoint_17_40_p16) (by decide)⟩
private def endpoint_17_41_flag : Flag := ⟨17, 41, 2976⟩
private def endpoint_17_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_41_base : receiptBase endpoint_17_41_flag endpoint_17_41_sources = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_w0 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_w2 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 2 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_p4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 4 233370168794059256 = some 233370168794059256 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 2 2 233370168794059256 233370168794059256 233370168794059256 endpoint_17_41_w0 endpoint_17_41_w2
private theorem endpoint_17_41_w4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 4 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_p6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 6 233370168794059256 = some 233370168794059256 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 4 2 233370168794059256 233370168794059256 233370168794059256 endpoint_17_41_p4 endpoint_17_41_w4
private theorem endpoint_17_41_w6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 6 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_p8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 8 233370168794059256 = some 233370168794059256 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 6 2 233370168794059256 233370168794059256 233370168794059256 endpoint_17_41_p6 endpoint_17_41_w6
private theorem endpoint_17_41_w8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 8 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_p10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 10 233370168794059256 = some 233370168794059256 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 8 2 233370168794059256 233370168794059256 233370168794059256 endpoint_17_41_p8 endpoint_17_41_w8
private theorem endpoint_17_41_w10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 10 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_p12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 12 233370168794059256 = some 233370168794059256 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 10 2 233370168794059256 233370168794059256 233370168794059256 endpoint_17_41_p10 endpoint_17_41_w10
private theorem endpoint_17_41_w12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 12 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_p14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 14 233370168794059256 = some 233370168794059256 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 12 2 233370168794059256 233370168794059256 233370168794059256 endpoint_17_41_p12 endpoint_17_41_w12
private theorem endpoint_17_41_w14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 14 2 233370168794059256 = some 233370168794059256 := by decide +kernel
private theorem endpoint_17_41_p16 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 16 233370168794059256 = some 233370168794059256 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 14 2 233370168794059256 233370168794059256 233370168794059256 endpoint_17_41_p14 endpoint_17_41_w14
def endpoint_17_41 : CertifiedEndpoint :=
  ⟨⟨17, 41, 2976⟩, 233370168794059256, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_41_flag endpoint_17_41_sources 16 233370168794059256 233370168794059256 rfl endpoint_17_41_base endpoint_17_41_p16) (by decide)⟩
private def endpoint_17_42_flag : Flag := ⟨17, 42, 2931⟩
private def endpoint_17_42_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_42_base : receiptBase endpoint_17_42_flag endpoint_17_42_sources = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_w0 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_w2 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 2 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_p4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 4 234690826951696344 = some 234690826951696344 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 2 2 234690826951696344 234690826951696344 234690826951696344 endpoint_17_42_w0 endpoint_17_42_w2
private theorem endpoint_17_42_w4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 4 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_p6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 6 234690826951696344 = some 234690826951696344 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 4 2 234690826951696344 234690826951696344 234690826951696344 endpoint_17_42_p4 endpoint_17_42_w4
private theorem endpoint_17_42_w6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 6 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_p8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 8 234690826951696344 = some 234690826951696344 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 6 2 234690826951696344 234690826951696344 234690826951696344 endpoint_17_42_p6 endpoint_17_42_w6
private theorem endpoint_17_42_w8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 8 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_p10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 10 234690826951696344 = some 234690826951696344 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 8 2 234690826951696344 234690826951696344 234690826951696344 endpoint_17_42_p8 endpoint_17_42_w8
private theorem endpoint_17_42_w10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 10 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_p12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 12 234690826951696344 = some 234690826951696344 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 10 2 234690826951696344 234690826951696344 234690826951696344 endpoint_17_42_p10 endpoint_17_42_w10
private theorem endpoint_17_42_w12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 12 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_p14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 14 234690826951696344 = some 234690826951696344 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 12 2 234690826951696344 234690826951696344 234690826951696344 endpoint_17_42_p12 endpoint_17_42_w12
private theorem endpoint_17_42_w14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 14 2 234690826951696344 = some 234690826951696344 := by decide +kernel
private theorem endpoint_17_42_p16 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 16 234690826951696344 = some 234690826951696344 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 14 2 234690826951696344 234690826951696344 234690826951696344 endpoint_17_42_p14 endpoint_17_42_w14
def endpoint_17_42 : CertifiedEndpoint :=
  ⟨⟨17, 42, 2931⟩, 234690826951696344, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_42_flag endpoint_17_42_sources 16 234690826951696344 234690826951696344 rfl endpoint_17_42_base endpoint_17_42_p16) (by decide)⟩
private def endpoint_17_43_flag : Flag := ⟨17, 43, 2884⟩
private def endpoint_17_43_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_43_base : receiptBase endpoint_17_43_flag endpoint_17_43_sources = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_w0 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_w2 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 2 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_p4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 4 235703295943077784 = some 235703295943077784 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 2 2 235703295943077784 235703295943077784 235703295943077784 endpoint_17_43_w0 endpoint_17_43_w2
private theorem endpoint_17_43_w4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 4 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_p6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 6 235703295943077784 = some 235703295943077784 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 4 2 235703295943077784 235703295943077784 235703295943077784 endpoint_17_43_p4 endpoint_17_43_w4
private theorem endpoint_17_43_w6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 6 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_p8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 8 235703295943077784 = some 235703295943077784 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 6 2 235703295943077784 235703295943077784 235703295943077784 endpoint_17_43_p6 endpoint_17_43_w6
private theorem endpoint_17_43_w8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 8 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_p10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 10 235703295943077784 = some 235703295943077784 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 8 2 235703295943077784 235703295943077784 235703295943077784 endpoint_17_43_p8 endpoint_17_43_w8
private theorem endpoint_17_43_w10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 10 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_p12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 12 235703295943077784 = some 235703295943077784 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 10 2 235703295943077784 235703295943077784 235703295943077784 endpoint_17_43_p10 endpoint_17_43_w10
private theorem endpoint_17_43_w12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 12 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_p14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 14 235703295943077784 = some 235703295943077784 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 12 2 235703295943077784 235703295943077784 235703295943077784 endpoint_17_43_p12 endpoint_17_43_w12
private theorem endpoint_17_43_w14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 14 2 235703295943077784 = some 235703295943077784 := by decide +kernel
private theorem endpoint_17_43_p16 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 16 235703295943077784 = some 235703295943077784 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 14 2 235703295943077784 235703295943077784 235703295943077784 endpoint_17_43_p14 endpoint_17_43_w14
def endpoint_17_43 : CertifiedEndpoint :=
  ⟨⟨17, 43, 2884⟩, 235703295943077784, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_43_flag endpoint_17_43_sources 16 235703295943077784 235703295943077784 rfl endpoint_17_43_base endpoint_17_43_p16) (by decide)⟩
private def endpoint_17_44_flag : Flag := ⟨17, 44, 2836⟩
private def endpoint_17_44_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_44_base : receiptBase endpoint_17_44_flag endpoint_17_44_sources = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_w0 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_w2 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 2 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_p4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 4 236480150031292556 = some 236480150031292556 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 2 2 236480150031292556 236480150031292556 236480150031292556 endpoint_17_44_w0 endpoint_17_44_w2
private theorem endpoint_17_44_w4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 4 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_p6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 6 236480150031292556 = some 236480150031292556 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 4 2 236480150031292556 236480150031292556 236480150031292556 endpoint_17_44_p4 endpoint_17_44_w4
private theorem endpoint_17_44_w6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 6 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_p8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 8 236480150031292556 = some 236480150031292556 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 6 2 236480150031292556 236480150031292556 236480150031292556 endpoint_17_44_p6 endpoint_17_44_w6
private theorem endpoint_17_44_w8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 8 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_p10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 10 236480150031292556 = some 236480150031292556 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 8 2 236480150031292556 236480150031292556 236480150031292556 endpoint_17_44_p8 endpoint_17_44_w8
private theorem endpoint_17_44_w10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 10 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_p12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 12 236480150031292556 = some 236480150031292556 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 10 2 236480150031292556 236480150031292556 236480150031292556 endpoint_17_44_p10 endpoint_17_44_w10
private theorem endpoint_17_44_w12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 12 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_p14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 14 236480150031292556 = some 236480150031292556 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 12 2 236480150031292556 236480150031292556 236480150031292556 endpoint_17_44_p12 endpoint_17_44_w12
private theorem endpoint_17_44_w14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 14 2 236480150031292556 = some 236480150031292556 := by decide +kernel
private theorem endpoint_17_44_p16 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 16 236480150031292556 = some 236480150031292556 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 14 2 236480150031292556 236480150031292556 236480150031292556 endpoint_17_44_p14 endpoint_17_44_w14
def endpoint_17_44 : CertifiedEndpoint :=
  ⟨⟨17, 44, 2836⟩, 236480150031292556, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_44_flag endpoint_17_44_sources 16 236480150031292556 236480150031292556 rfl endpoint_17_44_base endpoint_17_44_p16) (by decide)⟩
private def endpoint_17_45_flag : Flag := ⟨17, 45, 2788⟩
private def endpoint_17_45_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_45_base : receiptBase endpoint_17_45_flag endpoint_17_45_sources = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_w0 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_w2 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 2 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_p4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 4 237100420534482221 = some 237100420534482221 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 2 2 237100420534482221 237100420534482221 237100420534482221 endpoint_17_45_w0 endpoint_17_45_w2
private theorem endpoint_17_45_w4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 4 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_p6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 6 237100420534482221 = some 237100420534482221 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 4 2 237100420534482221 237100420534482221 237100420534482221 endpoint_17_45_p4 endpoint_17_45_w4
private theorem endpoint_17_45_w6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 6 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_p8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 8 237100420534482221 = some 237100420534482221 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 6 2 237100420534482221 237100420534482221 237100420534482221 endpoint_17_45_p6 endpoint_17_45_w6
private theorem endpoint_17_45_w8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 8 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_p10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 10 237100420534482221 = some 237100420534482221 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 8 2 237100420534482221 237100420534482221 237100420534482221 endpoint_17_45_p8 endpoint_17_45_w8
private theorem endpoint_17_45_w10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 10 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_p12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 12 237100420534482221 = some 237100420534482221 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 10 2 237100420534482221 237100420534482221 237100420534482221 endpoint_17_45_p10 endpoint_17_45_w10
private theorem endpoint_17_45_w12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 12 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_p14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 14 237100420534482221 = some 237100420534482221 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 12 2 237100420534482221 237100420534482221 237100420534482221 endpoint_17_45_p12 endpoint_17_45_w12
private theorem endpoint_17_45_w14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 14 2 237100420534482221 = some 237100420534482221 := by decide +kernel
private theorem endpoint_17_45_p16 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 16 237100420534482221 = some 237100420534482221 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 14 2 237100420534482221 237100420534482221 237100420534482221 endpoint_17_45_p14 endpoint_17_45_w14
def endpoint_17_45 : CertifiedEndpoint :=
  ⟨⟨17, 45, 2788⟩, 237100420534482221, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_45_flag endpoint_17_45_sources 16 237100420534482221 237100420534482221 rfl endpoint_17_45_base endpoint_17_45_p16) (by decide)⟩
private def endpoint_17_46_flag : Flag := ⟨17, 46, 2738⟩
private def endpoint_17_46_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_46_base : receiptBase endpoint_17_46_flag endpoint_17_46_sources = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_w0 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_w2 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 2 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_p4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 4 237393130706258493 = some 237393130706258493 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 2 2 237393130706258493 237393130706258493 237393130706258493 endpoint_17_46_w0 endpoint_17_46_w2
private theorem endpoint_17_46_w4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 4 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_p6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 6 237393130706258493 = some 237393130706258493 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 4 2 237393130706258493 237393130706258493 237393130706258493 endpoint_17_46_p4 endpoint_17_46_w4
private theorem endpoint_17_46_w6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 6 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_p8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 8 237393130706258493 = some 237393130706258493 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 6 2 237393130706258493 237393130706258493 237393130706258493 endpoint_17_46_p6 endpoint_17_46_w6
private theorem endpoint_17_46_w8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 8 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_p10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 10 237393130706258493 = some 237393130706258493 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 8 2 237393130706258493 237393130706258493 237393130706258493 endpoint_17_46_p8 endpoint_17_46_w8
private theorem endpoint_17_46_w10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 10 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_p12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 12 237393130706258493 = some 237393130706258493 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 10 2 237393130706258493 237393130706258493 237393130706258493 endpoint_17_46_p10 endpoint_17_46_w10
private theorem endpoint_17_46_w12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 12 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_p14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 14 237393130706258493 = some 237393130706258493 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 12 2 237393130706258493 237393130706258493 237393130706258493 endpoint_17_46_p12 endpoint_17_46_w12
private theorem endpoint_17_46_w14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 14 2 237393130706258493 = some 237393130706258493 := by decide +kernel
private theorem endpoint_17_46_p16 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 16 237393130706258493 = some 237393130706258493 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 14 2 237393130706258493 237393130706258493 237393130706258493 endpoint_17_46_p14 endpoint_17_46_w14
def endpoint_17_46 : CertifiedEndpoint :=
  ⟨⟨17, 46, 2738⟩, 237393130706258493, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_46_flag endpoint_17_46_sources 16 237393130706258493 237393130706258493 rfl endpoint_17_46_base endpoint_17_46_p16) (by decide)⟩
private def endpoint_17_47_flag : Flag := ⟨17, 47, 2688⟩
private def endpoint_17_47_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_47_base : receiptBase endpoint_17_47_flag endpoint_17_47_sources = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_w0 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_w2 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 2 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_p4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 4 237522800237957078 = some 237522800237957078 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 2 2 237522800237957078 237522800237957078 237522800237957078 endpoint_17_47_w0 endpoint_17_47_w2
private theorem endpoint_17_47_w4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 4 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_p6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 6 237522800237957078 = some 237522800237957078 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 4 2 237522800237957078 237522800237957078 237522800237957078 endpoint_17_47_p4 endpoint_17_47_w4
private theorem endpoint_17_47_w6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 6 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_p8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 8 237522800237957078 = some 237522800237957078 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 6 2 237522800237957078 237522800237957078 237522800237957078 endpoint_17_47_p6 endpoint_17_47_w6
private theorem endpoint_17_47_w8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 8 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_p10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 10 237522800237957078 = some 237522800237957078 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 8 2 237522800237957078 237522800237957078 237522800237957078 endpoint_17_47_p8 endpoint_17_47_w8
private theorem endpoint_17_47_w10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 10 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_p12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 12 237522800237957078 = some 237522800237957078 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 10 2 237522800237957078 237522800237957078 237522800237957078 endpoint_17_47_p10 endpoint_17_47_w10
private theorem endpoint_17_47_w12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 12 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_p14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 14 237522800237957078 = some 237522800237957078 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 12 2 237522800237957078 237522800237957078 237522800237957078 endpoint_17_47_p12 endpoint_17_47_w12
private theorem endpoint_17_47_w14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 14 2 237522800237957078 = some 237522800237957078 := by decide +kernel
private theorem endpoint_17_47_p16 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 16 237522800237957078 = some 237522800237957078 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 14 2 237522800237957078 237522800237957078 237522800237957078 endpoint_17_47_p14 endpoint_17_47_w14
def endpoint_17_47 : CertifiedEndpoint :=
  ⟨⟨17, 47, 2688⟩, 237522800237957078, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_47_flag endpoint_17_47_sources 16 237522800237957078 237522800237957078 rfl endpoint_17_47_base endpoint_17_47_p16) (by decide)⟩
private def endpoint_17_48_flag : Flag := ⟨17, 48, 2636⟩
private def endpoint_17_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_48_base : receiptBase endpoint_17_48_flag endpoint_17_48_sources = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_w0 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_w2 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 2 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_p4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 4 237311995328137105 = some 237311995328137105 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 2 2 237311995328137105 237311995328137105 237311995328137105 endpoint_17_48_w0 endpoint_17_48_w2
private theorem endpoint_17_48_w4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 4 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_p6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 6 237311995328137105 = some 237311995328137105 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 4 2 237311995328137105 237311995328137105 237311995328137105 endpoint_17_48_p4 endpoint_17_48_w4
private theorem endpoint_17_48_w6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 6 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_p8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 8 237311995328137105 = some 237311995328137105 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 6 2 237311995328137105 237311995328137105 237311995328137105 endpoint_17_48_p6 endpoint_17_48_w6
private theorem endpoint_17_48_w8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 8 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_p10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 10 237311995328137105 = some 237311995328137105 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 8 2 237311995328137105 237311995328137105 237311995328137105 endpoint_17_48_p8 endpoint_17_48_w8
private theorem endpoint_17_48_w10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 10 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_p12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 12 237311995328137105 = some 237311995328137105 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 10 2 237311995328137105 237311995328137105 237311995328137105 endpoint_17_48_p10 endpoint_17_48_w10
private theorem endpoint_17_48_w12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 12 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_p14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 14 237311995328137105 = some 237311995328137105 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 12 2 237311995328137105 237311995328137105 237311995328137105 endpoint_17_48_p12 endpoint_17_48_w12
private theorem endpoint_17_48_w14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 14 2 237311995328137105 = some 237311995328137105 := by decide +kernel
private theorem endpoint_17_48_p16 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 16 237311995328137105 = some 237311995328137105 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 14 2 237311995328137105 237311995328137105 237311995328137105 endpoint_17_48_p14 endpoint_17_48_w14
def endpoint_17_48 : CertifiedEndpoint :=
  ⟨⟨17, 48, 2636⟩, 237311995328137105, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_48_flag endpoint_17_48_sources 16 237311995328137105 237311995328137105 rfl endpoint_17_48_base endpoint_17_48_p16) (by decide)⟩
private def endpoint_17_49_flag : Flag := ⟨17, 49, 2583⟩
private def endpoint_17_49_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_17_49_base : receiptBase endpoint_17_49_flag endpoint_17_49_sources = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_w0 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_w2 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 2 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_p4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 4 242602366423764937 = some 242602366423764937 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 2 2 242602366423764937 242602366423764937 242602366423764937 endpoint_17_49_w0 endpoint_17_49_w2
private theorem endpoint_17_49_w4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 4 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_p6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 6 242602366423764937 = some 242602366423764937 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 4 2 242602366423764937 242602366423764937 242602366423764937 endpoint_17_49_p4 endpoint_17_49_w4
private theorem endpoint_17_49_w6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 6 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_p8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 8 242602366423764937 = some 242602366423764937 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 6 2 242602366423764937 242602366423764937 242602366423764937 endpoint_17_49_p6 endpoint_17_49_w6
private theorem endpoint_17_49_w8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 8 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_p10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 10 242602366423764937 = some 242602366423764937 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 8 2 242602366423764937 242602366423764937 242602366423764937 endpoint_17_49_p8 endpoint_17_49_w8
private theorem endpoint_17_49_w10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 10 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_p12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 12 242602366423764937 = some 242602366423764937 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 10 2 242602366423764937 242602366423764937 242602366423764937 endpoint_17_49_p10 endpoint_17_49_w10
private theorem endpoint_17_49_w12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 12 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_p14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 14 242602366423764937 = some 242602366423764937 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 12 2 242602366423764937 242602366423764937 242602366423764937 endpoint_17_49_p12 endpoint_17_49_w12
private theorem endpoint_17_49_w14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 14 2 242602366423764937 = some 242602366423764937 := by decide +kernel
private theorem endpoint_17_49_p16 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 16 242602366423764937 = some 242602366423764937 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 14 2 242602366423764937 242602366423764937 242602366423764937 endpoint_17_49_p14 endpoint_17_49_w14
def endpoint_17_49 : CertifiedEndpoint :=
  ⟨⟨17, 49, 2583⟩, 242602366423764937, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_17_49_flag endpoint_17_49_sources 16 242602366423764937 242602366423764937 rfl endpoint_17_49_base endpoint_17_49_p16) (by decide)⟩
private def endpoint_17_50_flag : Flag := ⟨17, 50, 2529⟩
private def endpoint_17_50_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_50_base : receiptBase endpoint_17_50_flag endpoint_17_50_sources = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_w0 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_w2 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 2 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_p4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 4 242260575809434703 = some 242260575809434703 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 2 2 242260575809434703 242260575809434703 242260575809434703 endpoint_17_50_w0 endpoint_17_50_w2
private theorem endpoint_17_50_w4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 4 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_p6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 6 242260575809434703 = some 242260575809434703 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 4 2 242260575809434703 242260575809434703 242260575809434703 endpoint_17_50_p4 endpoint_17_50_w4
private theorem endpoint_17_50_w6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 6 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_p8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 8 242260575809434703 = some 242260575809434703 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 6 2 242260575809434703 242260575809434703 242260575809434703 endpoint_17_50_p6 endpoint_17_50_w6
private theorem endpoint_17_50_w8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 8 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_p10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 10 242260575809434703 = some 242260575809434703 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 8 2 242260575809434703 242260575809434703 242260575809434703 endpoint_17_50_p8 endpoint_17_50_w8
private theorem endpoint_17_50_w10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 10 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_p12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 12 242260575809434703 = some 242260575809434703 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 10 2 242260575809434703 242260575809434703 242260575809434703 endpoint_17_50_p10 endpoint_17_50_w10
private theorem endpoint_17_50_w12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 12 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_p14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 14 242260575809434703 = some 242260575809434703 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 12 2 242260575809434703 242260575809434703 242260575809434703 endpoint_17_50_p12 endpoint_17_50_w12
private theorem endpoint_17_50_w14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 14 2 242260575809434703 = some 242260575809434703 := by decide +kernel
private theorem endpoint_17_50_p16 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 16 242260575809434703 = some 242260575809434703 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 14 2 242260575809434703 242260575809434703 242260575809434703 endpoint_17_50_p14 endpoint_17_50_w14
def endpoint_17_50 : CertifiedEndpoint :=
  ⟨⟨17, 50, 2529⟩, 242260575809434703, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_50_flag endpoint_17_50_sources 16 242260575809434703 242260575809434703 rfl endpoint_17_50_base endpoint_17_50_p16) (by decide)⟩
private def endpoint_17_51_flag : Flag := ⟨17, 51, 2474⟩
private def endpoint_17_51_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_51_base : receiptBase endpoint_17_51_flag endpoint_17_51_sources = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_w0 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_w2 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 2 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_p4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 4 241268636480061740 = some 241268636480061740 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 2 2 241268636480061740 241268636480061740 241268636480061740 endpoint_17_51_w0 endpoint_17_51_w2
private theorem endpoint_17_51_w4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 4 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_p6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 6 241268636480061740 = some 241268636480061740 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 4 2 241268636480061740 241268636480061740 241268636480061740 endpoint_17_51_p4 endpoint_17_51_w4
private theorem endpoint_17_51_w6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 6 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_p8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 8 241268636480061740 = some 241268636480061740 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 6 2 241268636480061740 241268636480061740 241268636480061740 endpoint_17_51_p6 endpoint_17_51_w6
private theorem endpoint_17_51_w8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 8 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_p10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 10 241268636480061740 = some 241268636480061740 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 8 2 241268636480061740 241268636480061740 241268636480061740 endpoint_17_51_p8 endpoint_17_51_w8
private theorem endpoint_17_51_w10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 10 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_p12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 12 241268636480061740 = some 241268636480061740 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 10 2 241268636480061740 241268636480061740 241268636480061740 endpoint_17_51_p10 endpoint_17_51_w10
private theorem endpoint_17_51_w12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 12 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_p14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 14 241268636480061740 = some 241268636480061740 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 12 2 241268636480061740 241268636480061740 241268636480061740 endpoint_17_51_p12 endpoint_17_51_w12
private theorem endpoint_17_51_w14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 14 2 241268636480061740 = some 241268636480061740 := by decide +kernel
private theorem endpoint_17_51_p16 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 16 241268636480061740 = some 241268636480061740 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 14 2 241268636480061740 241268636480061740 241268636480061740 endpoint_17_51_p14 endpoint_17_51_w14
def endpoint_17_51 : CertifiedEndpoint :=
  ⟨⟨17, 51, 2474⟩, 241268636480061740, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_51_flag endpoint_17_51_sources 16 241268636480061740 241268636480061740 rfl endpoint_17_51_base endpoint_17_51_p16) (by decide)⟩
private def endpoint_17_52_flag : Flag := ⟨17, 52, 2418⟩
private def endpoint_17_52_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_52_base : receiptBase endpoint_17_52_flag endpoint_17_52_sources = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_w0 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_w2 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 2 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_p4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 4 240814564640670677 = some 240814564640670677 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 2 2 240814564640670677 240814564640670677 240814564640670677 endpoint_17_52_w0 endpoint_17_52_w2
private theorem endpoint_17_52_w4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 4 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_p6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 6 240814564640670677 = some 240814564640670677 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 4 2 240814564640670677 240814564640670677 240814564640670677 endpoint_17_52_p4 endpoint_17_52_w4
private theorem endpoint_17_52_w6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 6 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_p8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 8 240814564640670677 = some 240814564640670677 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 6 2 240814564640670677 240814564640670677 240814564640670677 endpoint_17_52_p6 endpoint_17_52_w6
private theorem endpoint_17_52_w8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 8 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_p10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 10 240814564640670677 = some 240814564640670677 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 8 2 240814564640670677 240814564640670677 240814564640670677 endpoint_17_52_p8 endpoint_17_52_w8
private theorem endpoint_17_52_w10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 10 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_p12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 12 240814564640670677 = some 240814564640670677 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 10 2 240814564640670677 240814564640670677 240814564640670677 endpoint_17_52_p10 endpoint_17_52_w10
private theorem endpoint_17_52_w12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 12 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_p14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 14 240814564640670677 = some 240814564640670677 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 12 2 240814564640670677 240814564640670677 240814564640670677 endpoint_17_52_p12 endpoint_17_52_w12
private theorem endpoint_17_52_w14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 14 2 240814564640670677 = some 240814564640670677 := by decide +kernel
private theorem endpoint_17_52_p16 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 16 240814564640670677 = some 240814564640670677 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 14 2 240814564640670677 240814564640670677 240814564640670677 endpoint_17_52_p14 endpoint_17_52_w14
def endpoint_17_52 : CertifiedEndpoint :=
  ⟨⟨17, 52, 2418⟩, 240814564640670677, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_52_flag endpoint_17_52_sources 16 240814564640670677 240814564640670677 rfl endpoint_17_52_base endpoint_17_52_p16) (by decide)⟩
private def endpoint_17_53_flag : Flag := ⟨17, 53, 2360⟩
private def endpoint_17_53_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_53_base : receiptBase endpoint_17_53_flag endpoint_17_53_sources = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_w0 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_w2 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 2 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_p4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 4 239158484833847021 = some 239158484833847021 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 2 2 239158484833847021 239158484833847021 239158484833847021 endpoint_17_53_w0 endpoint_17_53_w2
private theorem endpoint_17_53_w4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 4 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_p6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 6 239158484833847021 = some 239158484833847021 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 4 2 239158484833847021 239158484833847021 239158484833847021 endpoint_17_53_p4 endpoint_17_53_w4
private theorem endpoint_17_53_w6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 6 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_p8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 8 239158484833847021 = some 239158484833847021 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 6 2 239158484833847021 239158484833847021 239158484833847021 endpoint_17_53_p6 endpoint_17_53_w6
private theorem endpoint_17_53_w8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 8 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_p10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 10 239158484833847021 = some 239158484833847021 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 8 2 239158484833847021 239158484833847021 239158484833847021 endpoint_17_53_p8 endpoint_17_53_w8
private theorem endpoint_17_53_w10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 10 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_p12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 12 239158484833847021 = some 239158484833847021 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 10 2 239158484833847021 239158484833847021 239158484833847021 endpoint_17_53_p10 endpoint_17_53_w10
private theorem endpoint_17_53_w12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 12 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_p14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 14 239158484833847021 = some 239158484833847021 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 12 2 239158484833847021 239158484833847021 239158484833847021 endpoint_17_53_p12 endpoint_17_53_w12
private theorem endpoint_17_53_w14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 14 2 239158484833847021 = some 239158484833847021 := by decide +kernel
private theorem endpoint_17_53_p16 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 16 239158484833847021 = some 239158484833847021 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 14 2 239158484833847021 239158484833847021 239158484833847021 endpoint_17_53_p14 endpoint_17_53_w14
def endpoint_17_53 : CertifiedEndpoint :=
  ⟨⟨17, 53, 2360⟩, 239158484833847021, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_53_flag endpoint_17_53_sources 16 239158484833847021 239158484833847021 rfl endpoint_17_53_base endpoint_17_53_p16) (by decide)⟩
private def endpoint_17_54_flag : Flag := ⟨17, 54, 2301⟩
private def endpoint_17_54_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_54_base : receiptBase endpoint_17_54_flag endpoint_17_54_sources = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_w0 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_w2 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 2 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_p4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 4 237293146437650757 = some 237293146437650757 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 2 2 237293146437650757 237293146437650757 237293146437650757 endpoint_17_54_w0 endpoint_17_54_w2
private theorem endpoint_17_54_w4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 4 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_p6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 6 237293146437650757 = some 237293146437650757 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 4 2 237293146437650757 237293146437650757 237293146437650757 endpoint_17_54_p4 endpoint_17_54_w4
private theorem endpoint_17_54_w6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 6 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_p8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 8 237293146437650757 = some 237293146437650757 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 6 2 237293146437650757 237293146437650757 237293146437650757 endpoint_17_54_p6 endpoint_17_54_w6
private theorem endpoint_17_54_w8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 8 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_p10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 10 237293146437650757 = some 237293146437650757 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 8 2 237293146437650757 237293146437650757 237293146437650757 endpoint_17_54_p8 endpoint_17_54_w8
private theorem endpoint_17_54_w10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 10 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_p12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 12 237293146437650757 = some 237293146437650757 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 10 2 237293146437650757 237293146437650757 237293146437650757 endpoint_17_54_p10 endpoint_17_54_w10
private theorem endpoint_17_54_w12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 12 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_p14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 14 237293146437650757 = some 237293146437650757 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 12 2 237293146437650757 237293146437650757 237293146437650757 endpoint_17_54_p12 endpoint_17_54_w12
private theorem endpoint_17_54_w14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 14 2 237293146437650757 = some 237293146437650757 := by decide +kernel
private theorem endpoint_17_54_p16 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 16 237293146437650757 = some 237293146437650757 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 14 2 237293146437650757 237293146437650757 237293146437650757 endpoint_17_54_p14 endpoint_17_54_w14
def endpoint_17_54 : CertifiedEndpoint :=
  ⟨⟨17, 54, 2301⟩, 237293146437650757, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_54_flag endpoint_17_54_sources 16 237293146437650757 237293146437650757 rfl endpoint_17_54_base endpoint_17_54_p16) (by decide)⟩
private def endpoint_17_55_flag : Flag := ⟨17, 55, 2241⟩
private def endpoint_17_55_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_55_base : receiptBase endpoint_17_55_flag endpoint_17_55_sources = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_w0 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_w2 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 2 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_p4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 4 235011794062396242 = some 235011794062396242 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 2 2 235011794062396242 235011794062396242 235011794062396242 endpoint_17_55_w0 endpoint_17_55_w2
private theorem endpoint_17_55_w4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 4 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_p6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 6 235011794062396242 = some 235011794062396242 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 4 2 235011794062396242 235011794062396242 235011794062396242 endpoint_17_55_p4 endpoint_17_55_w4
private theorem endpoint_17_55_w6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 6 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_p8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 8 235011794062396242 = some 235011794062396242 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 6 2 235011794062396242 235011794062396242 235011794062396242 endpoint_17_55_p6 endpoint_17_55_w6
private theorem endpoint_17_55_w8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 8 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_p10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 10 235011794062396242 = some 235011794062396242 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 8 2 235011794062396242 235011794062396242 235011794062396242 endpoint_17_55_p8 endpoint_17_55_w8
private theorem endpoint_17_55_w10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 10 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_p12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 12 235011794062396242 = some 235011794062396242 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 10 2 235011794062396242 235011794062396242 235011794062396242 endpoint_17_55_p10 endpoint_17_55_w10
private theorem endpoint_17_55_w12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 12 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_p14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 14 235011794062396242 = some 235011794062396242 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 12 2 235011794062396242 235011794062396242 235011794062396242 endpoint_17_55_p12 endpoint_17_55_w12
private theorem endpoint_17_55_w14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 14 2 235011794062396242 = some 235011794062396242 := by decide +kernel
private theorem endpoint_17_55_p16 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 16 235011794062396242 = some 235011794062396242 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 14 2 235011794062396242 235011794062396242 235011794062396242 endpoint_17_55_p14 endpoint_17_55_w14
def endpoint_17_55 : CertifiedEndpoint :=
  ⟨⟨17, 55, 2241⟩, 235011794062396242, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_55_flag endpoint_17_55_sources 16 235011794062396242 235011794062396242 rfl endpoint_17_55_base endpoint_17_55_p16) (by decide)⟩
private def endpoint_17_56_flag : Flag := ⟨17, 56, 2179⟩
private def endpoint_17_56_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_56_base : receiptBase endpoint_17_56_flag endpoint_17_56_sources = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_w0 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_w2 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 2 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_p4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 4 233414537905101570 = some 233414537905101570 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 2 2 233414537905101570 233414537905101570 233414537905101570 endpoint_17_56_w0 endpoint_17_56_w2
private theorem endpoint_17_56_w4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 4 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_p6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 6 233414537905101570 = some 233414537905101570 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 4 2 233414537905101570 233414537905101570 233414537905101570 endpoint_17_56_p4 endpoint_17_56_w4
private theorem endpoint_17_56_w6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 6 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_p8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 8 233414537905101570 = some 233414537905101570 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 6 2 233414537905101570 233414537905101570 233414537905101570 endpoint_17_56_p6 endpoint_17_56_w6
private theorem endpoint_17_56_w8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 8 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_p10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 10 233414537905101570 = some 233414537905101570 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 8 2 233414537905101570 233414537905101570 233414537905101570 endpoint_17_56_p8 endpoint_17_56_w8
private theorem endpoint_17_56_w10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 10 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_p12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 12 233414537905101570 = some 233414537905101570 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 10 2 233414537905101570 233414537905101570 233414537905101570 endpoint_17_56_p10 endpoint_17_56_w10
private theorem endpoint_17_56_w12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 12 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_p14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 14 233414537905101570 = some 233414537905101570 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 12 2 233414537905101570 233414537905101570 233414537905101570 endpoint_17_56_p12 endpoint_17_56_w12
private theorem endpoint_17_56_w14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 14 2 233414537905101570 = some 233414537905101570 := by decide +kernel
private theorem endpoint_17_56_p16 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 16 233414537905101570 = some 233414537905101570 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 14 2 233414537905101570 233414537905101570 233414537905101570 endpoint_17_56_p14 endpoint_17_56_w14
def endpoint_17_56 : CertifiedEndpoint :=
  ⟨⟨17, 56, 2179⟩, 233414537905101570, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_56_flag endpoint_17_56_sources 16 233414537905101570 233414537905101570 rfl endpoint_17_56_base endpoint_17_56_p16) (by decide)⟩
private def endpoint_17_57_flag : Flag := ⟨17, 57, 2116⟩
private def endpoint_17_57_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_57_base : receiptBase endpoint_17_57_flag endpoint_17_57_sources = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_w0 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_w2 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 2 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_p4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 4 230387335519843152 = some 230387335519843152 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 2 2 230387335519843152 230387335519843152 230387335519843152 endpoint_17_57_w0 endpoint_17_57_w2
private theorem endpoint_17_57_w4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 4 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_p6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 6 230387335519843152 = some 230387335519843152 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 4 2 230387335519843152 230387335519843152 230387335519843152 endpoint_17_57_p4 endpoint_17_57_w4
private theorem endpoint_17_57_w6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 6 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_p8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 8 230387335519843152 = some 230387335519843152 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 6 2 230387335519843152 230387335519843152 230387335519843152 endpoint_17_57_p6 endpoint_17_57_w6
private theorem endpoint_17_57_w8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 8 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_p10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 10 230387335519843152 = some 230387335519843152 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 8 2 230387335519843152 230387335519843152 230387335519843152 endpoint_17_57_p8 endpoint_17_57_w8
private theorem endpoint_17_57_w10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 10 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_p12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 12 230387335519843152 = some 230387335519843152 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 10 2 230387335519843152 230387335519843152 230387335519843152 endpoint_17_57_p10 endpoint_17_57_w10
private theorem endpoint_17_57_w12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 12 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_p14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 14 230387335519843152 = some 230387335519843152 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 12 2 230387335519843152 230387335519843152 230387335519843152 endpoint_17_57_p12 endpoint_17_57_w12
private theorem endpoint_17_57_w14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 14 2 230387335519843152 = some 230387335519843152 := by decide +kernel
private theorem endpoint_17_57_p16 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 16 230387335519843152 = some 230387335519843152 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 14 2 230387335519843152 230387335519843152 230387335519843152 endpoint_17_57_p14 endpoint_17_57_w14
def endpoint_17_57 : CertifiedEndpoint :=
  ⟨⟨17, 57, 2116⟩, 230387335519843152, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_57_flag endpoint_17_57_sources 16 230387335519843152 230387335519843152 rfl endpoint_17_57_base endpoint_17_57_p16) (by decide)⟩
private def endpoint_17_58_flag : Flag := ⟨17, 58, 2051⟩
private def endpoint_17_58_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_58_base : receiptBase endpoint_17_58_flag endpoint_17_58_sources = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_w0 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_w2 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 2 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_p4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 4 226933601318902136 = some 226933601318902136 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 2 2 226933601318902136 226933601318902136 226933601318902136 endpoint_17_58_w0 endpoint_17_58_w2
private theorem endpoint_17_58_w4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 4 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_p6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 6 226933601318902136 = some 226933601318902136 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 4 2 226933601318902136 226933601318902136 226933601318902136 endpoint_17_58_p4 endpoint_17_58_w4
private theorem endpoint_17_58_w6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 6 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_p8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 8 226933601318902136 = some 226933601318902136 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 6 2 226933601318902136 226933601318902136 226933601318902136 endpoint_17_58_p6 endpoint_17_58_w6
private theorem endpoint_17_58_w8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 8 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_p10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 10 226933601318902136 = some 226933601318902136 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 8 2 226933601318902136 226933601318902136 226933601318902136 endpoint_17_58_p8 endpoint_17_58_w8
private theorem endpoint_17_58_w10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 10 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_p12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 12 226933601318902136 = some 226933601318902136 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 10 2 226933601318902136 226933601318902136 226933601318902136 endpoint_17_58_p10 endpoint_17_58_w10
private theorem endpoint_17_58_w12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 12 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_p14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 14 226933601318902136 = some 226933601318902136 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 12 2 226933601318902136 226933601318902136 226933601318902136 endpoint_17_58_p12 endpoint_17_58_w12
private theorem endpoint_17_58_w14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 14 2 226933601318902136 = some 226933601318902136 := by decide +kernel
private theorem endpoint_17_58_p16 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 16 226933601318902136 = some 226933601318902136 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 14 2 226933601318902136 226933601318902136 226933601318902136 endpoint_17_58_p14 endpoint_17_58_w14
def endpoint_17_58 : CertifiedEndpoint :=
  ⟨⟨17, 58, 2051⟩, 226933601318902136, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_58_flag endpoint_17_58_sources 16 226933601318902136 226933601318902136 rfl endpoint_17_58_base endpoint_17_58_p16) (by decide)⟩
private def endpoint_17_59_flag : Flag := ⟨17, 59, 1985⟩
private def endpoint_17_59_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_59_base : receiptBase endpoint_17_59_flag endpoint_17_59_sources = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_w0 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_w2 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 2 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_p4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 4 225955820098767499 = some 225955820098767499 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 2 2 225955820098767499 225955820098767499 225955820098767499 endpoint_17_59_w0 endpoint_17_59_w2
private theorem endpoint_17_59_w4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 4 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_p6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 6 225955820098767499 = some 225955820098767499 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 4 2 225955820098767499 225955820098767499 225955820098767499 endpoint_17_59_p4 endpoint_17_59_w4
private theorem endpoint_17_59_w6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 6 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_p8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 8 225955820098767499 = some 225955820098767499 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 6 2 225955820098767499 225955820098767499 225955820098767499 endpoint_17_59_p6 endpoint_17_59_w6
private theorem endpoint_17_59_w8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 8 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_p10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 10 225955820098767499 = some 225955820098767499 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 8 2 225955820098767499 225955820098767499 225955820098767499 endpoint_17_59_p8 endpoint_17_59_w8
private theorem endpoint_17_59_w10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 10 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_p12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 12 225955820098767499 = some 225955820098767499 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 10 2 225955820098767499 225955820098767499 225955820098767499 endpoint_17_59_p10 endpoint_17_59_w10
private theorem endpoint_17_59_w12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 12 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_p14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 14 225955820098767499 = some 225955820098767499 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 12 2 225955820098767499 225955820098767499 225955820098767499 endpoint_17_59_p12 endpoint_17_59_w12
private theorem endpoint_17_59_w14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 14 2 225955820098767499 = some 225955820098767499 := by decide +kernel
private theorem endpoint_17_59_p16 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 16 225955820098767499 = some 225955820098767499 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 14 2 225955820098767499 225955820098767499 225955820098767499 endpoint_17_59_p14 endpoint_17_59_w14
def endpoint_17_59 : CertifiedEndpoint :=
  ⟨⟨17, 59, 1985⟩, 225955820098767499, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_59_flag endpoint_17_59_sources 16 225955820098767499 225955820098767499 rfl endpoint_17_59_base endpoint_17_59_p16) (by decide)⟩
private def endpoint_17_60_flag : Flag := ⟨17, 60, 1917⟩
private def endpoint_17_60_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_60_base : receiptBase endpoint_17_60_flag endpoint_17_60_sources = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_w0 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_w2 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 2 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_p4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 4 221552723527440201 = some 221552723527440201 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 2 2 221552723527440201 221552723527440201 221552723527440201 endpoint_17_60_w0 endpoint_17_60_w2
private theorem endpoint_17_60_w4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 4 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_p6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 6 221552723527440201 = some 221552723527440201 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 4 2 221552723527440201 221552723527440201 221552723527440201 endpoint_17_60_p4 endpoint_17_60_w4
private theorem endpoint_17_60_w6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 6 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_p8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 8 221552723527440201 = some 221552723527440201 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 6 2 221552723527440201 221552723527440201 221552723527440201 endpoint_17_60_p6 endpoint_17_60_w6
private theorem endpoint_17_60_w8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 8 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_p10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 10 221552723527440201 = some 221552723527440201 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 8 2 221552723527440201 221552723527440201 221552723527440201 endpoint_17_60_p8 endpoint_17_60_w8
private theorem endpoint_17_60_w10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 10 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_p12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 12 221552723527440201 = some 221552723527440201 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 10 2 221552723527440201 221552723527440201 221552723527440201 endpoint_17_60_p10 endpoint_17_60_w10
private theorem endpoint_17_60_w12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 12 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_p14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 14 221552723527440201 = some 221552723527440201 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 12 2 221552723527440201 221552723527440201 221552723527440201 endpoint_17_60_p12 endpoint_17_60_w12
private theorem endpoint_17_60_w14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 14 2 221552723527440201 = some 221552723527440201 := by decide +kernel
private theorem endpoint_17_60_p16 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 16 221552723527440201 = some 221552723527440201 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 14 2 221552723527440201 221552723527440201 221552723527440201 endpoint_17_60_p14 endpoint_17_60_w14
def endpoint_17_60 : CertifiedEndpoint :=
  ⟨⟨17, 60, 1917⟩, 221552723527440201, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_60_flag endpoint_17_60_sources 16 221552723527440201 221552723527440201 rfl endpoint_17_60_base endpoint_17_60_p16) (by decide)⟩
private def endpoint_17_61_flag : Flag := ⟨17, 61, 1848⟩
private def endpoint_17_61_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_61_base : receiptBase endpoint_17_61_flag endpoint_17_61_sources = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_w0 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_w2 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 2 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_p4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 4 216802549188137830 = some 216802549188137830 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 2 2 216802549188137830 216802549188137830 216802549188137830 endpoint_17_61_w0 endpoint_17_61_w2
private theorem endpoint_17_61_w4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 4 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_p6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 6 216802549188137830 = some 216802549188137830 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 4 2 216802549188137830 216802549188137830 216802549188137830 endpoint_17_61_p4 endpoint_17_61_w4
private theorem endpoint_17_61_w6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 6 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_p8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 8 216802549188137830 = some 216802549188137830 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 6 2 216802549188137830 216802549188137830 216802549188137830 endpoint_17_61_p6 endpoint_17_61_w6
private theorem endpoint_17_61_w8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 8 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_p10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 10 216802549188137830 = some 216802549188137830 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 8 2 216802549188137830 216802549188137830 216802549188137830 endpoint_17_61_p8 endpoint_17_61_w8
private theorem endpoint_17_61_w10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 10 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_p12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 12 216802549188137830 = some 216802549188137830 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 10 2 216802549188137830 216802549188137830 216802549188137830 endpoint_17_61_p10 endpoint_17_61_w10
private theorem endpoint_17_61_w12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 12 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_p14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 14 216802549188137830 = some 216802549188137830 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 12 2 216802549188137830 216802549188137830 216802549188137830 endpoint_17_61_p12 endpoint_17_61_w12
private theorem endpoint_17_61_w14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 14 2 216802549188137830 = some 216802549188137830 := by decide +kernel
private theorem endpoint_17_61_p16 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 16 216802549188137830 = some 216802549188137830 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 14 2 216802549188137830 216802549188137830 216802549188137830 endpoint_17_61_p14 endpoint_17_61_w14
def endpoint_17_61 : CertifiedEndpoint :=
  ⟨⟨17, 61, 1848⟩, 216802549188137830, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_61_flag endpoint_17_61_sources 16 216802549188137830 216802549188137830 rfl endpoint_17_61_base endpoint_17_61_p16) (by decide)⟩
private def endpoint_17_62_flag : Flag := ⟨17, 62, 1777⟩
private def endpoint_17_62_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_62_base : receiptBase endpoint_17_62_flag endpoint_17_62_sources = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_w0 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_w2 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 2 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_p4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 4 211582627532603406 = some 211582627532603406 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 2 2 211582627532603406 211582627532603406 211582627532603406 endpoint_17_62_w0 endpoint_17_62_w2
private theorem endpoint_17_62_w4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 4 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_p6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 6 211582627532603406 = some 211582627532603406 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 4 2 211582627532603406 211582627532603406 211582627532603406 endpoint_17_62_p4 endpoint_17_62_w4
private theorem endpoint_17_62_w6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 6 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_p8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 8 211582627532603406 = some 211582627532603406 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 6 2 211582627532603406 211582627532603406 211582627532603406 endpoint_17_62_p6 endpoint_17_62_w6
private theorem endpoint_17_62_w8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 8 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_p10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 10 211582627532603406 = some 211582627532603406 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 8 2 211582627532603406 211582627532603406 211582627532603406 endpoint_17_62_p8 endpoint_17_62_w8
private theorem endpoint_17_62_w10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 10 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_p12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 12 211582627532603406 = some 211582627532603406 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 10 2 211582627532603406 211582627532603406 211582627532603406 endpoint_17_62_p10 endpoint_17_62_w10
private theorem endpoint_17_62_w12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 12 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_p14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 14 211582627532603406 = some 211582627532603406 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 12 2 211582627532603406 211582627532603406 211582627532603406 endpoint_17_62_p12 endpoint_17_62_w12
private theorem endpoint_17_62_w14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 14 2 211582627532603406 = some 211582627532603406 := by decide +kernel
private theorem endpoint_17_62_p16 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 16 211582627532603406 = some 211582627532603406 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 14 2 211582627532603406 211582627532603406 211582627532603406 endpoint_17_62_p14 endpoint_17_62_w14
def endpoint_17_62 : CertifiedEndpoint :=
  ⟨⟨17, 62, 1777⟩, 211582627532603406, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_62_flag endpoint_17_62_sources 16 211582627532603406 211582627532603406 rfl endpoint_17_62_base endpoint_17_62_p16) (by decide)⟩
private def endpoint_17_63_flag : Flag := ⟨17, 63, 1704⟩
private def endpoint_17_63_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_63_base : receiptBase endpoint_17_63_flag endpoint_17_63_sources = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_w0 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_w2 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 2 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_p4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 4 207575655840445372 = some 207575655840445372 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 2 2 207575655840445372 207575655840445372 207575655840445372 endpoint_17_63_w0 endpoint_17_63_w2
private theorem endpoint_17_63_w4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 4 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_p6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 6 207575655840445372 = some 207575655840445372 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 4 2 207575655840445372 207575655840445372 207575655840445372 endpoint_17_63_p4 endpoint_17_63_w4
private theorem endpoint_17_63_w6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 6 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_p8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 8 207575655840445372 = some 207575655840445372 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 6 2 207575655840445372 207575655840445372 207575655840445372 endpoint_17_63_p6 endpoint_17_63_w6
private theorem endpoint_17_63_w8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 8 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_p10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 10 207575655840445372 = some 207575655840445372 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 8 2 207575655840445372 207575655840445372 207575655840445372 endpoint_17_63_p8 endpoint_17_63_w8
private theorem endpoint_17_63_w10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 10 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_p12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 12 207575655840445372 = some 207575655840445372 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 10 2 207575655840445372 207575655840445372 207575655840445372 endpoint_17_63_p10 endpoint_17_63_w10
private theorem endpoint_17_63_w12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 12 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_p14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 14 207575655840445372 = some 207575655840445372 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 12 2 207575655840445372 207575655840445372 207575655840445372 endpoint_17_63_p12 endpoint_17_63_w12
private theorem endpoint_17_63_w14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 14 2 207575655840445372 = some 207575655840445372 := by decide +kernel
private theorem endpoint_17_63_p16 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 16 207575655840445372 = some 207575655840445372 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 14 2 207575655840445372 207575655840445372 207575655840445372 endpoint_17_63_p14 endpoint_17_63_w14
def endpoint_17_63 : CertifiedEndpoint :=
  ⟨⟨17, 63, 1704⟩, 207575655840445372, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_63_flag endpoint_17_63_sources 16 207575655840445372 207575655840445372 rfl endpoint_17_63_base endpoint_17_63_p16) (by decide)⟩
private def endpoint_17_64_flag : Flag := ⟨17, 64, 1629⟩
private def endpoint_17_64_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_64_base : receiptBase endpoint_17_64_flag endpoint_17_64_sources = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_w0 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_w2 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 2 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_p4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 4 201319786314609813 = some 201319786314609813 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 2 2 201319786314609813 201319786314609813 201319786314609813 endpoint_17_64_w0 endpoint_17_64_w2
private theorem endpoint_17_64_w4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 4 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_p6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 6 201319786314609813 = some 201319786314609813 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 4 2 201319786314609813 201319786314609813 201319786314609813 endpoint_17_64_p4 endpoint_17_64_w4
private theorem endpoint_17_64_w6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 6 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_p8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 8 201319786314609813 = some 201319786314609813 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 6 2 201319786314609813 201319786314609813 201319786314609813 endpoint_17_64_p6 endpoint_17_64_w6
private theorem endpoint_17_64_w8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 8 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_p10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 10 201319786314609813 = some 201319786314609813 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 8 2 201319786314609813 201319786314609813 201319786314609813 endpoint_17_64_p8 endpoint_17_64_w8
private theorem endpoint_17_64_w10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 10 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_p12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 12 201319786314609813 = some 201319786314609813 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 10 2 201319786314609813 201319786314609813 201319786314609813 endpoint_17_64_p10 endpoint_17_64_w10
private theorem endpoint_17_64_w12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 12 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_p14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 14 201319786314609813 = some 201319786314609813 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 12 2 201319786314609813 201319786314609813 201319786314609813 endpoint_17_64_p12 endpoint_17_64_w12
private theorem endpoint_17_64_w14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 14 2 201319786314609813 = some 201319786314609813 := by decide +kernel
private theorem endpoint_17_64_p16 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 16 201319786314609813 = some 201319786314609813 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 14 2 201319786314609813 201319786314609813 201319786314609813 endpoint_17_64_p14 endpoint_17_64_w14
def endpoint_17_64 : CertifiedEndpoint :=
  ⟨⟨17, 64, 1629⟩, 201319786314609813, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_64_flag endpoint_17_64_sources 16 201319786314609813 201319786314609813 rfl endpoint_17_64_base endpoint_17_64_p16) (by decide)⟩
private def endpoint_17_65_flag : Flag := ⟨17, 65, 1552⟩
private def endpoint_17_65_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_65_base : receiptBase endpoint_17_65_flag endpoint_17_65_sources = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_w0 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_w2 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 2 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_p4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 4 194560505595604974 = some 194560505595604974 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 2 2 194560505595604974 194560505595604974 194560505595604974 endpoint_17_65_w0 endpoint_17_65_w2
private theorem endpoint_17_65_w4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 4 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_p6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 6 194560505595604974 = some 194560505595604974 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 4 2 194560505595604974 194560505595604974 194560505595604974 endpoint_17_65_p4 endpoint_17_65_w4
private theorem endpoint_17_65_w6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 6 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_p8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 8 194560505595604974 = some 194560505595604974 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 6 2 194560505595604974 194560505595604974 194560505595604974 endpoint_17_65_p6 endpoint_17_65_w6
private theorem endpoint_17_65_w8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 8 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_p10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 10 194560505595604974 = some 194560505595604974 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 8 2 194560505595604974 194560505595604974 194560505595604974 endpoint_17_65_p8 endpoint_17_65_w8
private theorem endpoint_17_65_w10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 10 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_p12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 12 194560505595604974 = some 194560505595604974 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 10 2 194560505595604974 194560505595604974 194560505595604974 endpoint_17_65_p10 endpoint_17_65_w10
private theorem endpoint_17_65_w12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 12 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_p14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 14 194560505595604974 = some 194560505595604974 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 12 2 194560505595604974 194560505595604974 194560505595604974 endpoint_17_65_p12 endpoint_17_65_w12
private theorem endpoint_17_65_w14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 14 2 194560505595604974 = some 194560505595604974 := by decide +kernel
private theorem endpoint_17_65_p16 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 16 194560505595604974 = some 194560505595604974 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 14 2 194560505595604974 194560505595604974 194560505595604974 endpoint_17_65_p14 endpoint_17_65_w14
def endpoint_17_65 : CertifiedEndpoint :=
  ⟨⟨17, 65, 1552⟩, 194560505595604974, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_65_flag endpoint_17_65_sources 16 194560505595604974 194560505595604974 rfl endpoint_17_65_base endpoint_17_65_p16) (by decide)⟩
private def endpoint_17_66_flag : Flag := ⟨17, 66, 1474⟩
private def endpoint_17_66_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_66_base : receiptBase endpoint_17_66_flag endpoint_17_66_sources = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_w0 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_w2 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 2 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_p4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 4 187413054543265422 = some 187413054543265422 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 2 2 187413054543265422 187413054543265422 187413054543265422 endpoint_17_66_w0 endpoint_17_66_w2
private theorem endpoint_17_66_w4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 4 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_p6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 6 187413054543265422 = some 187413054543265422 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 4 2 187413054543265422 187413054543265422 187413054543265422 endpoint_17_66_p4 endpoint_17_66_w4
private theorem endpoint_17_66_w6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 6 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_p8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 8 187413054543265422 = some 187413054543265422 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 6 2 187413054543265422 187413054543265422 187413054543265422 endpoint_17_66_p6 endpoint_17_66_w6
private theorem endpoint_17_66_w8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 8 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_p10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 10 187413054543265422 = some 187413054543265422 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 8 2 187413054543265422 187413054543265422 187413054543265422 endpoint_17_66_p8 endpoint_17_66_w8
private theorem endpoint_17_66_w10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 10 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_p12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 12 187413054543265422 = some 187413054543265422 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 10 2 187413054543265422 187413054543265422 187413054543265422 endpoint_17_66_p10 endpoint_17_66_w10
private theorem endpoint_17_66_w12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 12 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_p14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 14 187413054543265422 = some 187413054543265422 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 12 2 187413054543265422 187413054543265422 187413054543265422 endpoint_17_66_p12 endpoint_17_66_w12
private theorem endpoint_17_66_w14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 14 2 187413054543265422 = some 187413054543265422 := by decide +kernel
private theorem endpoint_17_66_p16 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 16 187413054543265422 = some 187413054543265422 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 14 2 187413054543265422 187413054543265422 187413054543265422 endpoint_17_66_p14 endpoint_17_66_w14
def endpoint_17_66 : CertifiedEndpoint :=
  ⟨⟨17, 66, 1474⟩, 187413054543265422, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_66_flag endpoint_17_66_sources 16 187413054543265422 187413054543265422 rfl endpoint_17_66_base endpoint_17_66_p16) (by decide)⟩
private def endpoint_17_67_flag : Flag := ⟨17, 67, 1393⟩
private def endpoint_17_67_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_17_67_base : receiptBase endpoint_17_67_flag endpoint_17_67_sources = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_w0 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_w2 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 2 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_p4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 4 181274014496464009 = some 181274014496464009 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 2 2 181274014496464009 181274014496464009 181274014496464009 endpoint_17_67_w0 endpoint_17_67_w2
private theorem endpoint_17_67_w4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 4 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_p6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 6 181274014496464009 = some 181274014496464009 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 4 2 181274014496464009 181274014496464009 181274014496464009 endpoint_17_67_p4 endpoint_17_67_w4
private theorem endpoint_17_67_w6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 6 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_p8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 8 181274014496464009 = some 181274014496464009 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 6 2 181274014496464009 181274014496464009 181274014496464009 endpoint_17_67_p6 endpoint_17_67_w6
private theorem endpoint_17_67_w8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 8 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_p10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 10 181274014496464009 = some 181274014496464009 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 8 2 181274014496464009 181274014496464009 181274014496464009 endpoint_17_67_p8 endpoint_17_67_w8
private theorem endpoint_17_67_w10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 10 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_p12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 12 181274014496464009 = some 181274014496464009 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 10 2 181274014496464009 181274014496464009 181274014496464009 endpoint_17_67_p10 endpoint_17_67_w10
private theorem endpoint_17_67_w12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 12 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_p14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 14 181274014496464009 = some 181274014496464009 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 12 2 181274014496464009 181274014496464009 181274014496464009 endpoint_17_67_p12 endpoint_17_67_w12
private theorem endpoint_17_67_w14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 14 2 181274014496464009 = some 181274014496464009 := by decide +kernel
private theorem endpoint_17_67_p16 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 16 181274014496464009 = some 181274014496464009 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 14 2 181274014496464009 181274014496464009 181274014496464009 endpoint_17_67_p14 endpoint_17_67_w14
def endpoint_17_67 : CertifiedEndpoint :=
  ⟨⟨17, 67, 1393⟩, 181274014496464009, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_17_67_flag endpoint_17_67_sources 16 181274014496464009 181274014496464009 rfl endpoint_17_67_base endpoint_17_67_p16) (by decide)⟩
private def endpoint_17_68_flag : Flag := ⟨17, 68, 1310⟩
private def endpoint_17_68_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_17_68_base : receiptBase endpoint_17_68_flag endpoint_17_68_sources = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_w0 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_w2 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 2 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_p4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 4 173027659131895115 = some 173027659131895115 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 2 2 173027659131895115 173027659131895115 173027659131895115 endpoint_17_68_w0 endpoint_17_68_w2
private theorem endpoint_17_68_w4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 4 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_p6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 6 173027659131895115 = some 173027659131895115 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 4 2 173027659131895115 173027659131895115 173027659131895115 endpoint_17_68_p4 endpoint_17_68_w4
private theorem endpoint_17_68_w6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 6 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_p8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 8 173027659131895115 = some 173027659131895115 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 6 2 173027659131895115 173027659131895115 173027659131895115 endpoint_17_68_p6 endpoint_17_68_w6
private theorem endpoint_17_68_w8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 8 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_p10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 10 173027659131895115 = some 173027659131895115 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 8 2 173027659131895115 173027659131895115 173027659131895115 endpoint_17_68_p8 endpoint_17_68_w8
private theorem endpoint_17_68_w10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 10 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_p12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 12 173027659131895115 = some 173027659131895115 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 10 2 173027659131895115 173027659131895115 173027659131895115 endpoint_17_68_p10 endpoint_17_68_w10
private theorem endpoint_17_68_w12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 12 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_p14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 14 173027659131895115 = some 173027659131895115 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 12 2 173027659131895115 173027659131895115 173027659131895115 endpoint_17_68_p12 endpoint_17_68_w12
private theorem endpoint_17_68_w14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 14 2 173027659131895115 = some 173027659131895115 := by decide +kernel
private theorem endpoint_17_68_p16 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 16 173027659131895115 = some 173027659131895115 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 14 2 173027659131895115 173027659131895115 173027659131895115 endpoint_17_68_p14 endpoint_17_68_w14
def endpoint_17_68 : CertifiedEndpoint :=
  ⟨⟨17, 68, 1310⟩, 173027659131895115, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_17_68_flag endpoint_17_68_sources 16 173027659131895115 173027659131895115 rfl endpoint_17_68_base endpoint_17_68_p16) (by decide)⟩
private def endpoint_17_69_flag : Flag := ⟨17, 69, 1225⟩
private def endpoint_17_69_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_69_base : receiptBase endpoint_17_69_flag endpoint_17_69_sources = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_w0 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_w2 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 2 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_p4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 4 165566053501431807 = some 165566053501431807 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 2 2 165566053501431807 165566053501431807 165566053501431807 endpoint_17_69_w0 endpoint_17_69_w2
private theorem endpoint_17_69_w4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 4 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_p6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 6 165566053501431807 = some 165566053501431807 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 4 2 165566053501431807 165566053501431807 165566053501431807 endpoint_17_69_p4 endpoint_17_69_w4
private theorem endpoint_17_69_w6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 6 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_p8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 8 165566053501431807 = some 165566053501431807 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 6 2 165566053501431807 165566053501431807 165566053501431807 endpoint_17_69_p6 endpoint_17_69_w6
private theorem endpoint_17_69_w8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 8 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_p10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 10 165566053501431807 = some 165566053501431807 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 8 2 165566053501431807 165566053501431807 165566053501431807 endpoint_17_69_p8 endpoint_17_69_w8
private theorem endpoint_17_69_w10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 10 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_p12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 12 165566053501431807 = some 165566053501431807 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 10 2 165566053501431807 165566053501431807 165566053501431807 endpoint_17_69_p10 endpoint_17_69_w10
private theorem endpoint_17_69_w12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 12 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_p14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 14 165566053501431807 = some 165566053501431807 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 12 2 165566053501431807 165566053501431807 165566053501431807 endpoint_17_69_p12 endpoint_17_69_w12
private theorem endpoint_17_69_w14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 14 2 165566053501431807 = some 165566053501431807 := by decide +kernel
private theorem endpoint_17_69_p16 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 16 165566053501431807 = some 165566053501431807 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 14 2 165566053501431807 165566053501431807 165566053501431807 endpoint_17_69_p14 endpoint_17_69_w14
def endpoint_17_69 : CertifiedEndpoint :=
  ⟨⟨17, 69, 1225⟩, 165566053501431807, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_69_flag endpoint_17_69_sources 16 165566053501431807 165566053501431807 rfl endpoint_17_69_base endpoint_17_69_p16) (by decide)⟩
private def endpoint_17_70_flag : Flag := ⟨17, 70, 1137⟩
private def endpoint_17_70_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_70_base : receiptBase endpoint_17_70_flag endpoint_17_70_sources = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_w0 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_w2 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 2 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_p4 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 4 155797854370278032 = some 155797854370278032 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 2 2 155797854370278032 155797854370278032 155797854370278032 endpoint_17_70_w0 endpoint_17_70_w2
private theorem endpoint_17_70_w4 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 4 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_p6 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 6 155797854370278032 = some 155797854370278032 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 4 2 155797854370278032 155797854370278032 155797854370278032 endpoint_17_70_p4 endpoint_17_70_w4
private theorem endpoint_17_70_w6 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 6 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_p8 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 8 155797854370278032 = some 155797854370278032 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 6 2 155797854370278032 155797854370278032 155797854370278032 endpoint_17_70_p6 endpoint_17_70_w6
private theorem endpoint_17_70_w8 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 8 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_p10 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 10 155797854370278032 = some 155797854370278032 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 8 2 155797854370278032 155797854370278032 155797854370278032 endpoint_17_70_p8 endpoint_17_70_w8
private theorem endpoint_17_70_w10 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 10 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_p12 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 12 155797854370278032 = some 155797854370278032 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 10 2 155797854370278032 155797854370278032 155797854370278032 endpoint_17_70_p10 endpoint_17_70_w10
private theorem endpoint_17_70_w12 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 12 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_p14 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 14 155797854370278032 = some 155797854370278032 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 12 2 155797854370278032 155797854370278032 155797854370278032 endpoint_17_70_p12 endpoint_17_70_w12
private theorem endpoint_17_70_w14 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 14 2 155797854370278032 = some 155797854370278032 := by decide +kernel
private theorem endpoint_17_70_p16 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 16 155797854370278032 = some 155797854370278032 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 14 2 155797854370278032 155797854370278032 155797854370278032 endpoint_17_70_p14 endpoint_17_70_w14
def endpoint_17_70 : CertifiedEndpoint :=
  ⟨⟨17, 70, 1137⟩, 155797854370278032, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_70_flag endpoint_17_70_sources 16 155797854370278032 155797854370278032 rfl endpoint_17_70_base endpoint_17_70_p16) (by decide)⟩
private def endpoint_17_71_flag : Flag := ⟨17, 71, 1047⟩
private def endpoint_17_71_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_71_base : receiptBase endpoint_17_71_flag endpoint_17_71_sources = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_w0 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_w2 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 2 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_p4 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 4 145456979337251208 = some 145456979337251208 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 2 2 145456979337251208 145456979337251208 145456979337251208 endpoint_17_71_w0 endpoint_17_71_w2
private theorem endpoint_17_71_w4 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 4 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_p6 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 6 145456979337251208 = some 145456979337251208 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 4 2 145456979337251208 145456979337251208 145456979337251208 endpoint_17_71_p4 endpoint_17_71_w4
private theorem endpoint_17_71_w6 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 6 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_p8 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 8 145456979337251208 = some 145456979337251208 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 6 2 145456979337251208 145456979337251208 145456979337251208 endpoint_17_71_p6 endpoint_17_71_w6
private theorem endpoint_17_71_w8 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 8 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_p10 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 10 145456979337251208 = some 145456979337251208 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 8 2 145456979337251208 145456979337251208 145456979337251208 endpoint_17_71_p8 endpoint_17_71_w8
private theorem endpoint_17_71_w10 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 10 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_p12 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 12 145456979337251208 = some 145456979337251208 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 10 2 145456979337251208 145456979337251208 145456979337251208 endpoint_17_71_p10 endpoint_17_71_w10
private theorem endpoint_17_71_w12 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 12 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_p14 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 14 145456979337251208 = some 145456979337251208 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 12 2 145456979337251208 145456979337251208 145456979337251208 endpoint_17_71_p12 endpoint_17_71_w12
private theorem endpoint_17_71_w14 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 14 2 145456979337251208 = some 145456979337251208 := by decide +kernel
private theorem endpoint_17_71_p16 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 16 145456979337251208 = some 145456979337251208 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 14 2 145456979337251208 145456979337251208 145456979337251208 endpoint_17_71_p14 endpoint_17_71_w14
def endpoint_17_71 : CertifiedEndpoint :=
  ⟨⟨17, 71, 1047⟩, 145456979337251208, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_71_flag endpoint_17_71_sources 16 145456979337251208 145456979337251208 rfl endpoint_17_71_base endpoint_17_71_p16) (by decide)⟩
def endpoint_17_72 : CertifiedEndpoint :=
  ⟨⟨17, 72, 955⟩, 245531244449006515, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_73 : CertifiedEndpoint :=
  ⟨⟨17, 73, 860⟩, 223385366328828835, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_74 : CertifiedEndpoint :=
  ⟨⟨17, 74, 762⟩, 199594826949237450, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_75 : CertifiedEndpoint :=
  ⟨⟨17, 75, 661⟩, 174121279890232174, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_76 : CertifiedEndpoint :=
  ⟨⟨17, 76, 557⟩, 146926378731812821, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_77 : CertifiedEndpoint :=
  ⟨⟨17, 77, 450⟩, 117971777053979205, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_78 : CertifiedEndpoint :=
  ⟨⟨17, 78, 340⟩, 87219128436731140, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_79 : CertifiedEndpoint :=
  ⟨⟨17, 79, 226⟩, 54331827889153973, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_80 : CertifiedEndpoint :=
  ⟨⟨17, 80, 110⟩, 19863785419743098, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_18 : CertifiedEndpoint :=
  ⟨⟨18, 18, 3591⟩, 159144465917049723, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_19 : CertifiedEndpoint :=
  ⟨⟨18, 19, 3558⟩, 162934438483974052, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_20 : CertifiedEndpoint :=
  ⟨⟨18, 20, 3524⟩, 166578876699369156, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_21 : CertifiedEndpoint :=
  ⟨⟨18, 21, 3489⟩, 180590187457188762, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_22 : CertifiedEndpoint :=
  ⟨⟨18, 22, 3454⟩, 194280690560963342, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_23 : CertifiedEndpoint :=
  ⟨⟨18, 23, 3419⟩, 207650386010692896, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_24 : CertifiedEndpoint :=
  ⟨⟨18, 24, 3383⟩, 220633748109871877, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_25 : CertifiedEndpoint :=
  ⟨⟨18, 25, 3346⟩, 233217221605512467, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_26 : CertifiedEndpoint :=
  ⟨⟨18, 26, 3309⟩, 245461813776457607, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_27 : CertifiedEndpoint :=
  ⟨⟨18, 27, 3271⟩, 257288443673213932, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_18_28_flag : Flag := ⟨18, 28, 3232⟩
private def endpoint_18_28_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_28_base : receiptBase endpoint_18_28_flag endpoint_18_28_sources = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_w0 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_w2 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 2 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p4 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 4 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 2 2 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_w0 endpoint_18_28_w2
private theorem endpoint_18_28_w4 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 4 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p6 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 6 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 4 2 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_p4 endpoint_18_28_w4
private theorem endpoint_18_28_w6 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 6 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p8 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 8 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 6 2 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_p6 endpoint_18_28_w6
private theorem endpoint_18_28_w8 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 8 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p10 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 10 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 8 2 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_p8 endpoint_18_28_w8
private theorem endpoint_18_28_w10 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 10 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p12 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 12 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 10 2 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_p10 endpoint_18_28_w10
private theorem endpoint_18_28_w12 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 12 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p14 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 14 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 12 2 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_p12 endpoint_18_28_w12
private theorem endpoint_18_28_w14 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 14 2 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p16 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 16 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 14 2 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_p14 endpoint_18_28_w14
private theorem endpoint_18_28_w16 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 16 1 189993523030314153 = some 189993523030314153 := by decide +kernel
private theorem endpoint_18_28_p17 : receiptWindow endpoint_18_28_flag endpoint_18_28_sources 0 17 189993523030314153 = some 189993523030314153 :=
  join_receipt_window endpoint_18_28_flag endpoint_18_28_sources 0 16 1 189993523030314153 189993523030314153 189993523030314153 endpoint_18_28_p16 endpoint_18_28_w16
def endpoint_18_28 : CertifiedEndpoint :=
  ⟨⟨18, 28, 3232⟩, 189993523030314153, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_28_flag endpoint_18_28_sources 17 189993523030314153 189993523030314153 rfl endpoint_18_28_base endpoint_18_28_p17) (by decide)⟩
private def endpoint_18_29_flag : Flag := ⟨18, 29, 3193⟩
private def endpoint_18_29_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_29_base : receiptBase endpoint_18_29_flag endpoint_18_29_sources = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_w0 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_w2 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 2 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p4 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 4 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 2 2 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_w0 endpoint_18_29_w2
private theorem endpoint_18_29_w4 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 4 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p6 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 6 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 4 2 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_p4 endpoint_18_29_w4
private theorem endpoint_18_29_w6 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 6 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p8 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 8 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 6 2 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_p6 endpoint_18_29_w6
private theorem endpoint_18_29_w8 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 8 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p10 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 10 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 8 2 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_p8 endpoint_18_29_w8
private theorem endpoint_18_29_w10 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 10 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p12 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 12 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 10 2 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_p10 endpoint_18_29_w10
private theorem endpoint_18_29_w12 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 12 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p14 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 14 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 12 2 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_p12 endpoint_18_29_w12
private theorem endpoint_18_29_w14 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 14 2 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p16 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 16 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 14 2 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_p14 endpoint_18_29_w14
private theorem endpoint_18_29_w16 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 16 1 193199221739662131 = some 193199221739662131 := by decide +kernel
private theorem endpoint_18_29_p17 : receiptWindow endpoint_18_29_flag endpoint_18_29_sources 0 17 193199221739662131 = some 193199221739662131 :=
  join_receipt_window endpoint_18_29_flag endpoint_18_29_sources 0 16 1 193199221739662131 193199221739662131 193199221739662131 endpoint_18_29_p16 endpoint_18_29_w16
def endpoint_18_29 : CertifiedEndpoint :=
  ⟨⟨18, 29, 3193⟩, 193199221739662131, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_29_flag endpoint_18_29_sources 17 193199221739662131 193199221739662131 rfl endpoint_18_29_base endpoint_18_29_p17) (by decide)⟩
private def endpoint_18_30_flag : Flag := ⟨18, 30, 3153⟩
private def endpoint_18_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_30_base : receiptBase endpoint_18_30_flag endpoint_18_30_sources = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_w0 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_w2 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 2 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 4 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 2 2 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_w0 endpoint_18_30_w2
private theorem endpoint_18_30_w4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 4 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 6 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 4 2 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_p4 endpoint_18_30_w4
private theorem endpoint_18_30_w6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 6 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 8 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 6 2 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_p6 endpoint_18_30_w6
private theorem endpoint_18_30_w8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 8 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 10 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 8 2 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_p8 endpoint_18_30_w8
private theorem endpoint_18_30_w10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 10 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 12 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 10 2 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_p10 endpoint_18_30_w10
private theorem endpoint_18_30_w12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 12 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 14 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 12 2 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_p12 endpoint_18_30_w12
private theorem endpoint_18_30_w14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 14 2 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 16 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 14 2 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_p14 endpoint_18_30_w14
private theorem endpoint_18_30_w16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 16 1 196210567947917247 = some 196210567947917247 := by decide +kernel
private theorem endpoint_18_30_p17 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 17 196210567947917247 = some 196210567947917247 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 16 1 196210567947917247 196210567947917247 196210567947917247 endpoint_18_30_p16 endpoint_18_30_w16
def endpoint_18_30 : CertifiedEndpoint :=
  ⟨⟨18, 30, 3153⟩, 196210567947917247, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_30_flag endpoint_18_30_sources 17 196210567947917247 196210567947917247 rfl endpoint_18_30_base endpoint_18_30_p17) (by decide)⟩
private def endpoint_18_31_flag : Flag := ⟨18, 31, 3113⟩
private def endpoint_18_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_31_base : receiptBase endpoint_18_31_flag endpoint_18_31_sources = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_w0 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_w2 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 2 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 4 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 2 2 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_w0 endpoint_18_31_w2
private theorem endpoint_18_31_w4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 4 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 6 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 4 2 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_p4 endpoint_18_31_w4
private theorem endpoint_18_31_w6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 6 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 8 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 6 2 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_p6 endpoint_18_31_w6
private theorem endpoint_18_31_w8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 8 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 10 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 8 2 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_p8 endpoint_18_31_w8
private theorem endpoint_18_31_w10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 10 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 12 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 10 2 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_p10 endpoint_18_31_w10
private theorem endpoint_18_31_w12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 12 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 14 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 12 2 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_p12 endpoint_18_31_w12
private theorem endpoint_18_31_w14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 14 2 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 16 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 14 2 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_p14 endpoint_18_31_w14
private theorem endpoint_18_31_w16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 16 1 199085732124001397 = some 199085732124001397 := by decide +kernel
private theorem endpoint_18_31_p17 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 17 199085732124001397 = some 199085732124001397 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 16 1 199085732124001397 199085732124001397 199085732124001397 endpoint_18_31_p16 endpoint_18_31_w16
def endpoint_18_31 : CertifiedEndpoint :=
  ⟨⟨18, 31, 3113⟩, 199085732124001397, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_31_flag endpoint_18_31_sources 17 199085732124001397 199085732124001397 rfl endpoint_18_31_base endpoint_18_31_p17) (by decide)⟩
private def endpoint_18_32_flag : Flag := ⟨18, 32, 3072⟩
private def endpoint_18_32_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_32_base : receiptBase endpoint_18_32_flag endpoint_18_32_sources = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_w0 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_w2 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 2 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 4 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 2 2 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_w0 endpoint_18_32_w2
private theorem endpoint_18_32_w4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 4 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 6 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 4 2 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_p4 endpoint_18_32_w4
private theorem endpoint_18_32_w6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 6 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 8 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 6 2 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_p6 endpoint_18_32_w6
private theorem endpoint_18_32_w8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 8 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 10 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 8 2 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_p8 endpoint_18_32_w8
private theorem endpoint_18_32_w10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 10 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 12 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 10 2 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_p10 endpoint_18_32_w10
private theorem endpoint_18_32_w12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 12 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 14 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 12 2 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_p12 endpoint_18_32_w12
private theorem endpoint_18_32_w14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 14 2 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 16 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 14 2 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_p14 endpoint_18_32_w14
private theorem endpoint_18_32_w16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 16 1 202027953563092132 = some 202027953563092132 := by decide +kernel
private theorem endpoint_18_32_p17 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 17 202027953563092132 = some 202027953563092132 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 16 1 202027953563092132 202027953563092132 202027953563092132 endpoint_18_32_p16 endpoint_18_32_w16
def endpoint_18_32 : CertifiedEndpoint :=
  ⟨⟨18, 32, 3072⟩, 202027953563092132, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_32_flag endpoint_18_32_sources 17 202027953563092132 202027953563092132 rfl endpoint_18_32_base endpoint_18_32_p17) (by decide)⟩
private def endpoint_18_33_flag : Flag := ⟨18, 33, 3030⟩
private def endpoint_18_33_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_33_base : receiptBase endpoint_18_33_flag endpoint_18_33_sources = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_w0 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_w2 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 2 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 4 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 2 2 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_w0 endpoint_18_33_w2
private theorem endpoint_18_33_w4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 4 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 6 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 4 2 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_p4 endpoint_18_33_w4
private theorem endpoint_18_33_w6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 6 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 8 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 6 2 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_p6 endpoint_18_33_w6
private theorem endpoint_18_33_w8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 8 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 10 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 8 2 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_p8 endpoint_18_33_w8
private theorem endpoint_18_33_w10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 10 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 12 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 10 2 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_p10 endpoint_18_33_w10
private theorem endpoint_18_33_w12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 12 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 14 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 12 2 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_p12 endpoint_18_33_w12
private theorem endpoint_18_33_w14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 14 2 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 16 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 14 2 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_p14 endpoint_18_33_w14
private theorem endpoint_18_33_w16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 16 1 204511008757862790 = some 204511008757862790 := by decide +kernel
private theorem endpoint_18_33_p17 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 17 204511008757862790 = some 204511008757862790 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 16 1 204511008757862790 204511008757862790 204511008757862790 endpoint_18_33_p16 endpoint_18_33_w16
def endpoint_18_33 : CertifiedEndpoint :=
  ⟨⟨18, 33, 3030⟩, 204511008757862790, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_33_flag endpoint_18_33_sources 17 204511008757862790 204511008757862790 rfl endpoint_18_33_base endpoint_18_33_p17) (by decide)⟩
private def endpoint_18_34_flag : Flag := ⟨18, 34, 2987⟩
private def endpoint_18_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_34_base : receiptBase endpoint_18_34_flag endpoint_18_34_sources = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_w0 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_w2 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 2 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 4 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 2 2 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_w0 endpoint_18_34_w2
private theorem endpoint_18_34_w4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 4 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 6 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 4 2 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_p4 endpoint_18_34_w4
private theorem endpoint_18_34_w6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 6 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 8 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 6 2 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_p6 endpoint_18_34_w6
private theorem endpoint_18_34_w8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 8 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 10 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 8 2 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_p8 endpoint_18_34_w8
private theorem endpoint_18_34_w10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 10 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 12 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 10 2 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_p10 endpoint_18_34_w10
private theorem endpoint_18_34_w12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 12 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 14 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 12 2 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_p12 endpoint_18_34_w12
private theorem endpoint_18_34_w14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 14 2 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 16 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 14 2 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_p14 endpoint_18_34_w14
private theorem endpoint_18_34_w16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 16 1 207242773404638591 = some 207242773404638591 := by decide +kernel
private theorem endpoint_18_34_p17 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 17 207242773404638591 = some 207242773404638591 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 16 1 207242773404638591 207242773404638591 207242773404638591 endpoint_18_34_p16 endpoint_18_34_w16
def endpoint_18_34 : CertifiedEndpoint :=
  ⟨⟨18, 34, 2987⟩, 207242773404638591, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_34_flag endpoint_18_34_sources 17 207242773404638591 207242773404638591 rfl endpoint_18_34_base endpoint_18_34_p17) (by decide)⟩
private def endpoint_18_35_flag : Flag := ⟨18, 35, 2944⟩
private def endpoint_18_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_35_base : receiptBase endpoint_18_35_flag endpoint_18_35_sources = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_w0 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_w2 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 2 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 4 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 2 2 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_w0 endpoint_18_35_w2
private theorem endpoint_18_35_w4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 4 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 6 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 4 2 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_p4 endpoint_18_35_w4
private theorem endpoint_18_35_w6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 6 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 8 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 6 2 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_p6 endpoint_18_35_w6
private theorem endpoint_18_35_w8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 8 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 10 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 8 2 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_p8 endpoint_18_35_w8
private theorem endpoint_18_35_w10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 10 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 12 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 10 2 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_p10 endpoint_18_35_w10
private theorem endpoint_18_35_w12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 12 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 14 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 12 2 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_p12 endpoint_18_35_w12
private theorem endpoint_18_35_w14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 14 2 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 16 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 14 2 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_p14 endpoint_18_35_w14
private theorem endpoint_18_35_w16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 16 1 209340484099121809 = some 209340484099121809 := by decide +kernel
private theorem endpoint_18_35_p17 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 17 209340484099121809 = some 209340484099121809 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 16 1 209340484099121809 209340484099121809 209340484099121809 endpoint_18_35_p16 endpoint_18_35_w16
def endpoint_18_35 : CertifiedEndpoint :=
  ⟨⟨18, 35, 2944⟩, 209340484099121809, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_35_flag endpoint_18_35_sources 17 209340484099121809 209340484099121809 rfl endpoint_18_35_base endpoint_18_35_p17) (by decide)⟩
private def endpoint_18_36_flag : Flag := ⟨18, 36, 2900⟩
private def endpoint_18_36_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_36_base : receiptBase endpoint_18_36_flag endpoint_18_36_sources = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_w0 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_w2 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 2 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 4 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 2 2 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_w0 endpoint_18_36_w2
private theorem endpoint_18_36_w4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 4 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 6 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 4 2 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_p4 endpoint_18_36_w4
private theorem endpoint_18_36_w6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 6 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 8 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 6 2 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_p6 endpoint_18_36_w6
private theorem endpoint_18_36_w8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 8 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 10 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 8 2 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_p8 endpoint_18_36_w8
private theorem endpoint_18_36_w10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 10 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 12 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 10 2 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_p10 endpoint_18_36_w10
private theorem endpoint_18_36_w12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 12 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 14 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 12 2 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_p12 endpoint_18_36_w12
private theorem endpoint_18_36_w14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 14 2 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 16 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 14 2 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_p14 endpoint_18_36_w14
private theorem endpoint_18_36_w16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 16 1 211219865979774398 = some 211219865979774398 := by decide +kernel
private theorem endpoint_18_36_p17 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 17 211219865979774398 = some 211219865979774398 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 16 1 211219865979774398 211219865979774398 211219865979774398 endpoint_18_36_p16 endpoint_18_36_w16
def endpoint_18_36 : CertifiedEndpoint :=
  ⟨⟨18, 36, 2900⟩, 211219865979774398, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_36_flag endpoint_18_36_sources 17 211219865979774398 211219865979774398 rfl endpoint_18_36_base endpoint_18_36_p17) (by decide)⟩
private def endpoint_18_37_flag : Flag := ⟨18, 37, 2855⟩
private def endpoint_18_37_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_37_base : receiptBase endpoint_18_37_flag endpoint_18_37_sources = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_w0 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_w2 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 2 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 4 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 2 2 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_w0 endpoint_18_37_w2
private theorem endpoint_18_37_w4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 4 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 6 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 4 2 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_p4 endpoint_18_37_w4
private theorem endpoint_18_37_w6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 6 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 8 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 6 2 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_p6 endpoint_18_37_w6
private theorem endpoint_18_37_w8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 8 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 10 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 8 2 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_p8 endpoint_18_37_w8
private theorem endpoint_18_37_w10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 10 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 12 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 10 2 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_p10 endpoint_18_37_w10
private theorem endpoint_18_37_w12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 12 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 14 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 12 2 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_p12 endpoint_18_37_w12
private theorem endpoint_18_37_w14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 14 2 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 16 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 14 2 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_p14 endpoint_18_37_w14
private theorem endpoint_18_37_w16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 16 1 212875870093730988 = some 212875870093730988 := by decide +kernel
private theorem endpoint_18_37_p17 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 17 212875870093730988 = some 212875870093730988 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 16 1 212875870093730988 212875870093730988 212875870093730988 endpoint_18_37_p16 endpoint_18_37_w16
def endpoint_18_37 : CertifiedEndpoint :=
  ⟨⟨18, 37, 2855⟩, 212875870093730988, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_37_flag endpoint_18_37_sources 17 212875870093730988 212875870093730988 rfl endpoint_18_37_base endpoint_18_37_p17) (by decide)⟩
private def endpoint_18_38_flag : Flag := ⟨18, 38, 2809⟩
private def endpoint_18_38_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_38_base : receiptBase endpoint_18_38_flag endpoint_18_38_sources = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_w0 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_w2 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 2 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 4 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 2 2 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_w0 endpoint_18_38_w2
private theorem endpoint_18_38_w4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 4 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 6 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 4 2 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_p4 endpoint_18_38_w4
private theorem endpoint_18_38_w6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 6 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 8 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 6 2 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_p6 endpoint_18_38_w6
private theorem endpoint_18_38_w8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 8 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 10 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 8 2 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_p8 endpoint_18_38_w8
private theorem endpoint_18_38_w10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 10 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 12 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 10 2 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_p10 endpoint_18_38_w10
private theorem endpoint_18_38_w12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 12 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 14 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 12 2 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_p12 endpoint_18_38_w12
private theorem endpoint_18_38_w14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 14 2 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 16 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 14 2 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_p14 endpoint_18_38_w14
private theorem endpoint_18_38_w16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 16 1 214303447488126205 = some 214303447488126205 := by decide +kernel
private theorem endpoint_18_38_p17 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 17 214303447488126205 = some 214303447488126205 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 16 1 214303447488126205 214303447488126205 214303447488126205 endpoint_18_38_p16 endpoint_18_38_w16
def endpoint_18_38 : CertifiedEndpoint :=
  ⟨⟨18, 38, 2809⟩, 214303447488126205, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_38_flag endpoint_18_38_sources 17 214303447488126205 214303447488126205 rfl endpoint_18_38_base endpoint_18_38_p17) (by decide)⟩
private def endpoint_18_39_flag : Flag := ⟨18, 39, 2763⟩
private def endpoint_18_39_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_39_base : receiptBase endpoint_18_39_flag endpoint_18_39_sources = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_w0 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_w2 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 2 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 4 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 2 2 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_w0 endpoint_18_39_w2
private theorem endpoint_18_39_w4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 4 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 6 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 4 2 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_p4 endpoint_18_39_w4
private theorem endpoint_18_39_w6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 6 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 8 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 6 2 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_p6 endpoint_18_39_w6
private theorem endpoint_18_39_w8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 8 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 10 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 8 2 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_p8 endpoint_18_39_w8
private theorem endpoint_18_39_w10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 10 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 12 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 10 2 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_p10 endpoint_18_39_w10
private theorem endpoint_18_39_w12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 12 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 14 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 12 2 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_p12 endpoint_18_39_w12
private theorem endpoint_18_39_w14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 14 2 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 16 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 14 2 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_p14 endpoint_18_39_w14
private theorem endpoint_18_39_w16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 16 1 215574507343694882 = some 215574507343694882 := by decide +kernel
private theorem endpoint_18_39_p17 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 17 215574507343694882 = some 215574507343694882 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 16 1 215574507343694882 215574507343694882 215574507343694882 endpoint_18_39_p16 endpoint_18_39_w16
def endpoint_18_39 : CertifiedEndpoint :=
  ⟨⟨18, 39, 2763⟩, 215574507343694882, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_39_flag endpoint_18_39_sources 17 215574507343694882 215574507343694882 rfl endpoint_18_39_base endpoint_18_39_p17) (by decide)⟩
private def endpoint_18_40_flag : Flag := ⟨18, 40, 2715⟩
private def endpoint_18_40_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_40_base : receiptBase endpoint_18_40_flag endpoint_18_40_sources = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_w0 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_w2 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 2 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 4 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 2 2 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_w0 endpoint_18_40_w2
private theorem endpoint_18_40_w4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 4 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 6 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 4 2 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_p4 endpoint_18_40_w4
private theorem endpoint_18_40_w6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 6 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 8 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 6 2 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_p6 endpoint_18_40_w6
private theorem endpoint_18_40_w8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 8 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 10 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 8 2 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_p8 endpoint_18_40_w8
private theorem endpoint_18_40_w10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 10 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 12 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 10 2 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_p10 endpoint_18_40_w10
private theorem endpoint_18_40_w12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 12 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 14 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 12 2 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_p12 endpoint_18_40_w12
private theorem endpoint_18_40_w14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 14 2 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 16 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 14 2 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_p14 endpoint_18_40_w14
private theorem endpoint_18_40_w16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 16 1 216531767424659695 = some 216531767424659695 := by decide +kernel
private theorem endpoint_18_40_p17 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 17 216531767424659695 = some 216531767424659695 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 16 1 216531767424659695 216531767424659695 216531767424659695 endpoint_18_40_p16 endpoint_18_40_w16
def endpoint_18_40 : CertifiedEndpoint :=
  ⟨⟨18, 40, 2715⟩, 216531767424659695, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_40_flag endpoint_18_40_sources 17 216531767424659695 216531767424659695 rfl endpoint_18_40_base endpoint_18_40_p17) (by decide)⟩
private def endpoint_18_41_flag : Flag := ⟨18, 41, 2667⟩
private def endpoint_18_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_41_base : receiptBase endpoint_18_41_flag endpoint_18_41_sources = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_w0 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_w2 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 2 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 4 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 2 2 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_w0 endpoint_18_41_w2
private theorem endpoint_18_41_w4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 4 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 6 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 4 2 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_p4 endpoint_18_41_w4
private theorem endpoint_18_41_w6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 6 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 8 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 6 2 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_p6 endpoint_18_41_w6
private theorem endpoint_18_41_w8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 8 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 10 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 8 2 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_p8 endpoint_18_41_w8
private theorem endpoint_18_41_w10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 10 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 12 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 10 2 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_p10 endpoint_18_41_w10
private theorem endpoint_18_41_w12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 12 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 14 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 12 2 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_p12 endpoint_18_41_w12
private theorem endpoint_18_41_w14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 14 2 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 16 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 14 2 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_p14 endpoint_18_41_w14
private theorem endpoint_18_41_w16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 16 1 217325778029644138 = some 217325778029644138 := by decide +kernel
private theorem endpoint_18_41_p17 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 17 217325778029644138 = some 217325778029644138 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 16 1 217325778029644138 217325778029644138 217325778029644138 endpoint_18_41_p16 endpoint_18_41_w16
def endpoint_18_41 : CertifiedEndpoint :=
  ⟨⟨18, 41, 2667⟩, 217325778029644138, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_41_flag endpoint_18_41_sources 17 217325778029644138 217325778029644138 rfl endpoint_18_41_base endpoint_18_41_p17) (by decide)⟩
private def endpoint_18_42_flag : Flag := ⟨18, 42, 2618⟩
private def endpoint_18_42_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_18_42_base : receiptBase endpoint_18_42_flag endpoint_18_42_sources = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_w0 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_w2 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 2 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 4 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 2 2 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_w0 endpoint_18_42_w2
private theorem endpoint_18_42_w4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 4 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 6 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 4 2 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_p4 endpoint_18_42_w4
private theorem endpoint_18_42_w6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 6 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 8 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 6 2 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_p6 endpoint_18_42_w6
private theorem endpoint_18_42_w8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 8 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 10 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 8 2 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_p8 endpoint_18_42_w8
private theorem endpoint_18_42_w10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 10 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 12 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 10 2 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_p10 endpoint_18_42_w10
private theorem endpoint_18_42_w12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 12 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 14 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 12 2 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_p12 endpoint_18_42_w12
private theorem endpoint_18_42_w14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 14 2 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 16 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 14 2 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_p14 endpoint_18_42_w14
private theorem endpoint_18_42_w16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 16 1 223139178114730534 = some 223139178114730534 := by decide +kernel
private theorem endpoint_18_42_p17 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 17 223139178114730534 = some 223139178114730534 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 16 1 223139178114730534 223139178114730534 223139178114730534 endpoint_18_42_p16 endpoint_18_42_w16
def endpoint_18_42 : CertifiedEndpoint :=
  ⟨⟨18, 42, 2618⟩, 223139178114730534, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_18_42_flag endpoint_18_42_sources 17 223139178114730534 223139178114730534 rfl endpoint_18_42_base endpoint_18_42_p17) (by decide)⟩
private def endpoint_18_43_flag : Flag := ⟨18, 43, 2568⟩
private def endpoint_18_43_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_43_base : receiptBase endpoint_18_43_flag endpoint_18_43_sources = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_w0 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_w2 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 2 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 4 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 2 2 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_w0 endpoint_18_43_w2
private theorem endpoint_18_43_w4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 4 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 6 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 4 2 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_p4 endpoint_18_43_w4
private theorem endpoint_18_43_w6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 6 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 8 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 6 2 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_p6 endpoint_18_43_w6
private theorem endpoint_18_43_w8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 8 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 10 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 8 2 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_p8 endpoint_18_43_w8
private theorem endpoint_18_43_w10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 10 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 12 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 10 2 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_p10 endpoint_18_43_w10
private theorem endpoint_18_43_w12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 12 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 14 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 12 2 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_p12 endpoint_18_43_w12
private theorem endpoint_18_43_w14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 14 2 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 16 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 14 2 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_p14 endpoint_18_43_w14
private theorem endpoint_18_43_w16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 16 1 223988103394266027 = some 223988103394266027 := by decide +kernel
private theorem endpoint_18_43_p17 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 17 223988103394266027 = some 223988103394266027 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 16 1 223988103394266027 223988103394266027 223988103394266027 endpoint_18_43_p16 endpoint_18_43_w16
def endpoint_18_43 : CertifiedEndpoint :=
  ⟨⟨18, 43, 2568⟩, 223988103394266027, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_43_flag endpoint_18_43_sources 17 223988103394266027 223988103394266027 rfl endpoint_18_43_base endpoint_18_43_p17) (by decide)⟩
private def endpoint_18_44_flag : Flag := ⟨18, 44, 2517⟩
private def endpoint_18_44_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_44_base : receiptBase endpoint_18_44_flag endpoint_18_44_sources = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_w0 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_w2 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 2 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 4 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 2 2 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_w0 endpoint_18_44_w2
private theorem endpoint_18_44_w4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 4 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 6 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 4 2 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_p4 endpoint_18_44_w4
private theorem endpoint_18_44_w6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 6 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 8 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 6 2 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_p6 endpoint_18_44_w6
private theorem endpoint_18_44_w8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 8 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 10 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 8 2 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_p8 endpoint_18_44_w8
private theorem endpoint_18_44_w10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 10 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 12 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 10 2 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_p10 endpoint_18_44_w10
private theorem endpoint_18_44_w12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 12 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 14 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 12 2 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_p12 endpoint_18_44_w12
private theorem endpoint_18_44_w14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 14 2 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 16 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 14 2 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_p14 endpoint_18_44_w14
private theorem endpoint_18_44_w16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 16 1 224091682388603070 = some 224091682388603070 := by decide +kernel
private theorem endpoint_18_44_p17 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 17 224091682388603070 = some 224091682388603070 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 16 1 224091682388603070 224091682388603070 224091682388603070 endpoint_18_44_p16 endpoint_18_44_w16
def endpoint_18_44 : CertifiedEndpoint :=
  ⟨⟨18, 44, 2517⟩, 224091682388603070, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_44_flag endpoint_18_44_sources 17 224091682388603070 224091682388603070 rfl endpoint_18_44_base endpoint_18_44_p17) (by decide)⟩
private def endpoint_18_45_flag : Flag := ⟨18, 45, 2465⟩
private def endpoint_18_45_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_45_base : receiptBase endpoint_18_45_flag endpoint_18_45_sources = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_w0 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_w2 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 2 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 4 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 2 2 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_w0 endpoint_18_45_w2
private theorem endpoint_18_45_w4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 4 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 6 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 4 2 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_p4 endpoint_18_45_w4
private theorem endpoint_18_45_w6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 6 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 8 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 6 2 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_p6 endpoint_18_45_w6
private theorem endpoint_18_45_w8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 8 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 10 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 8 2 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_p8 endpoint_18_45_w8
private theorem endpoint_18_45_w10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 10 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 12 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 10 2 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_p10 endpoint_18_45_w10
private theorem endpoint_18_45_w12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 12 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 14 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 12 2 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_p12 endpoint_18_45_w12
private theorem endpoint_18_45_w14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 14 2 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 16 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 14 2 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_p14 endpoint_18_45_w14
private theorem endpoint_18_45_w16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 16 1 224557672151753986 = some 224557672151753986 := by decide +kernel
private theorem endpoint_18_45_p17 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 17 224557672151753986 = some 224557672151753986 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 16 1 224557672151753986 224557672151753986 224557672151753986 endpoint_18_45_p16 endpoint_18_45_w16
def endpoint_18_45 : CertifiedEndpoint :=
  ⟨⟨18, 45, 2465⟩, 224557672151753986, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_45_flag endpoint_18_45_sources 17 224557672151753986 224557672151753986 rfl endpoint_18_45_base endpoint_18_45_p17) (by decide)⟩
private def endpoint_18_46_flag : Flag := ⟨18, 46, 2412⟩
private def endpoint_18_46_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_46_base : receiptBase endpoint_18_46_flag endpoint_18_46_sources = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_w0 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_w2 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 2 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 4 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 2 2 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_w0 endpoint_18_46_w2
private theorem endpoint_18_46_w4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 4 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 6 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 4 2 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_p4 endpoint_18_46_w4
private theorem endpoint_18_46_w6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 6 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 8 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 6 2 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_p6 endpoint_18_46_w6
private theorem endpoint_18_46_w8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 8 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 10 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 8 2 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_p8 endpoint_18_46_w8
private theorem endpoint_18_46_w10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 10 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 12 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 10 2 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_p10 endpoint_18_46_w10
private theorem endpoint_18_46_w12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 12 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 14 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 12 2 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_p12 endpoint_18_46_w12
private theorem endpoint_18_46_w14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 14 2 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 16 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 14 2 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_p14 endpoint_18_46_w14
private theorem endpoint_18_46_w16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 16 1 224091711105157910 = some 224091711105157910 := by decide +kernel
private theorem endpoint_18_46_p17 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 17 224091711105157910 = some 224091711105157910 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 16 1 224091711105157910 224091711105157910 224091711105157910 endpoint_18_46_p16 endpoint_18_46_w16
def endpoint_18_46 : CertifiedEndpoint :=
  ⟨⟨18, 46, 2412⟩, 224091711105157910, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_46_flag endpoint_18_46_sources 17 224091711105157910 224091711105157910 rfl endpoint_18_46_base endpoint_18_46_p17) (by decide)⟩

def endpointBlock11 : List CertifiedEndpoint := [
  endpoint_16_53, endpoint_16_54, endpoint_16_55, endpoint_16_56, endpoint_16_57, endpoint_16_58, endpoint_16_59,
  endpoint_16_60, endpoint_16_61, endpoint_16_62, endpoint_16_63, endpoint_16_64, endpoint_16_65, endpoint_16_66,
  endpoint_16_67, endpoint_16_68, endpoint_16_69, endpoint_16_70, endpoint_16_71, endpoint_16_72, endpoint_16_73,
  endpoint_16_74, endpoint_16_75, endpoint_16_76, endpoint_16_77, endpoint_16_78, endpoint_16_79, endpoint_16_80,
  endpoint_16_81, endpoint_16_82, endpoint_16_83, endpoint_17_17, endpoint_17_18, endpoint_17_19, endpoint_17_20,
  endpoint_17_21, endpoint_17_22, endpoint_17_23, endpoint_17_24, endpoint_17_25, endpoint_17_26, endpoint_17_27,
  endpoint_17_28, endpoint_17_29, endpoint_17_30, endpoint_17_31, endpoint_17_32, endpoint_17_33, endpoint_17_34,
  endpoint_17_35, endpoint_17_36, endpoint_17_37, endpoint_17_38, endpoint_17_39, endpoint_17_40, endpoint_17_41,
  endpoint_17_42, endpoint_17_43, endpoint_17_44, endpoint_17_45, endpoint_17_46, endpoint_17_47, endpoint_17_48,
  endpoint_17_49, endpoint_17_50, endpoint_17_51, endpoint_17_52, endpoint_17_53, endpoint_17_54, endpoint_17_55,
  endpoint_17_56, endpoint_17_57, endpoint_17_58, endpoint_17_59, endpoint_17_60, endpoint_17_61, endpoint_17_62,
  endpoint_17_63, endpoint_17_64, endpoint_17_65, endpoint_17_66, endpoint_17_67, endpoint_17_68, endpoint_17_69,
  endpoint_17_70, endpoint_17_71, endpoint_17_72, endpoint_17_73, endpoint_17_74, endpoint_17_75, endpoint_17_76,
  endpoint_17_77, endpoint_17_78, endpoint_17_79, endpoint_17_80, endpoint_18_18, endpoint_18_19, endpoint_18_20,
  endpoint_18_21, endpoint_18_22, endpoint_18_23, endpoint_18_24, endpoint_18_25, endpoint_18_26, endpoint_18_27,
  endpoint_18_28, endpoint_18_29, endpoint_18_30, endpoint_18_31, endpoint_18_32, endpoint_18_33, endpoint_18_34,
  endpoint_18_35, endpoint_18_36, endpoint_18_37, endpoint_18_38, endpoint_18_39, endpoint_18_40, endpoint_18_41,
  endpoint_18_42, endpoint_18_43, endpoint_18_44, endpoint_18_45, endpoint_18_46
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
