import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_11_46_flag : Flag := ⟨11, 46, 3808⟩
private def endpoint_11_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_46_base : receiptBase endpoint_11_46_flag endpoint_11_46_sources = some 238900547176618604 := by decide +kernel
private theorem endpoint_11_46_w0 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 2 238900547176618604 = some 238900547176618604 := by decide +kernel
private theorem endpoint_11_46_w2 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 2 2 238900547176618604 = some 238900547176618604 := by decide +kernel
private theorem endpoint_11_46_p4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 4 238900547176618604 = some 238900547176618604 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 2 2 238900547176618604 238900547176618604 238900547176618604 endpoint_11_46_w0 endpoint_11_46_w2
private theorem endpoint_11_46_w4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 4 2 238900547176618604 = some 238900547176618604 := by decide +kernel
private theorem endpoint_11_46_p6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 6 238900547176618604 = some 238900547176618604 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 4 2 238900547176618604 238900547176618604 238900547176618604 endpoint_11_46_p4 endpoint_11_46_w4
private theorem endpoint_11_46_w6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 6 2 238900547176618604 = some 238900547176618604 := by decide +kernel
private theorem endpoint_11_46_p8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 8 238900547176618604 = some 238900547176618604 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 6 2 238900547176618604 238900547176618604 238900547176618604 endpoint_11_46_p6 endpoint_11_46_w6
private theorem endpoint_11_46_w8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 8 2 238900547176618604 = some 238900547176618604 := by decide +kernel
private theorem endpoint_11_46_p10 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 10 238900547176618604 = some 238900547176618604 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 8 2 238900547176618604 238900547176618604 238900547176618604 endpoint_11_46_p8 endpoint_11_46_w8
def endpoint_11_46 : CertifiedEndpoint :=
  ⟨⟨11, 46, 3808⟩, 238900547176618604, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_46_flag endpoint_11_46_sources 10 238900547176618604 238900547176618604 rfl endpoint_11_46_base endpoint_11_46_p10) (by decide)⟩
private def endpoint_11_47_flag : Flag := ⟨11, 47, 3773⟩
private def endpoint_11_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_47_base : receiptBase endpoint_11_47_flag endpoint_11_47_sources = some 241131222967383692 := by decide +kernel
private theorem endpoint_11_47_w0 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 2 241131222967383692 = some 241131222967383692 := by decide +kernel
private theorem endpoint_11_47_w2 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 2 2 241131222967383692 = some 241131222967383692 := by decide +kernel
private theorem endpoint_11_47_p4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 4 241131222967383692 = some 241131222967383692 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 2 2 241131222967383692 241131222967383692 241131222967383692 endpoint_11_47_w0 endpoint_11_47_w2
private theorem endpoint_11_47_w4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 4 2 241131222967383692 = some 241131222967383692 := by decide +kernel
private theorem endpoint_11_47_p6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 6 241131222967383692 = some 241131222967383692 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 4 2 241131222967383692 241131222967383692 241131222967383692 endpoint_11_47_p4 endpoint_11_47_w4
private theorem endpoint_11_47_w6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 6 2 241131222967383692 = some 241131222967383692 := by decide +kernel
private theorem endpoint_11_47_p8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 8 241131222967383692 = some 241131222967383692 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 6 2 241131222967383692 241131222967383692 241131222967383692 endpoint_11_47_p6 endpoint_11_47_w6
private theorem endpoint_11_47_w8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 8 2 241131222967383692 = some 241131222967383692 := by decide +kernel
private theorem endpoint_11_47_p10 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 10 241131222967383692 = some 241131222967383692 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 8 2 241131222967383692 241131222967383692 241131222967383692 endpoint_11_47_p8 endpoint_11_47_w8
def endpoint_11_47 : CertifiedEndpoint :=
  ⟨⟨11, 47, 3773⟩, 241131222967383692, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_47_flag endpoint_11_47_sources 10 241131222967383692 241131222967383692 rfl endpoint_11_47_base endpoint_11_47_p10) (by decide)⟩
private def endpoint_11_48_flag : Flag := ⟨11, 48, 3737⟩
private def endpoint_11_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_48_base : receiptBase endpoint_11_48_flag endpoint_11_48_sources = some 243216244587676107 := by decide +kernel
private theorem endpoint_11_48_w0 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 2 243216244587676107 = some 243216244587676107 := by decide +kernel
private theorem endpoint_11_48_w2 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 2 2 243216244587676107 = some 243216244587676107 := by decide +kernel
private theorem endpoint_11_48_p4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 4 243216244587676107 = some 243216244587676107 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 2 2 243216244587676107 243216244587676107 243216244587676107 endpoint_11_48_w0 endpoint_11_48_w2
private theorem endpoint_11_48_w4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 4 2 243216244587676107 = some 243216244587676107 := by decide +kernel
private theorem endpoint_11_48_p6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 6 243216244587676107 = some 243216244587676107 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 4 2 243216244587676107 243216244587676107 243216244587676107 endpoint_11_48_p4 endpoint_11_48_w4
private theorem endpoint_11_48_w6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 6 2 243216244587676107 = some 243216244587676107 := by decide +kernel
private theorem endpoint_11_48_p8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 8 243216244587676107 = some 243216244587676107 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 6 2 243216244587676107 243216244587676107 243216244587676107 endpoint_11_48_p6 endpoint_11_48_w6
private theorem endpoint_11_48_w8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 8 2 243216244587676107 = some 243216244587676107 := by decide +kernel
private theorem endpoint_11_48_p10 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 10 243216244587676107 = some 243216244587676107 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 8 2 243216244587676107 243216244587676107 243216244587676107 endpoint_11_48_p8 endpoint_11_48_w8
def endpoint_11_48 : CertifiedEndpoint :=
  ⟨⟨11, 48, 3737⟩, 243216244587676107, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_48_flag endpoint_11_48_sources 10 243216244587676107 243216244587676107 rfl endpoint_11_48_base endpoint_11_48_p10) (by decide)⟩
private def endpoint_11_49_flag : Flag := ⟨11, 49, 3700⟩
private def endpoint_11_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_49_base : receiptBase endpoint_11_49_flag endpoint_11_49_sources = some 245152168203723518 := by decide +kernel
private theorem endpoint_11_49_w0 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 2 245152168203723518 = some 245152168203723518 := by decide +kernel
private theorem endpoint_11_49_w2 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 2 2 245152168203723518 = some 245152168203723518 := by decide +kernel
private theorem endpoint_11_49_p4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 4 245152168203723518 = some 245152168203723518 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 2 2 245152168203723518 245152168203723518 245152168203723518 endpoint_11_49_w0 endpoint_11_49_w2
private theorem endpoint_11_49_w4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 4 2 245152168203723518 = some 245152168203723518 := by decide +kernel
private theorem endpoint_11_49_p6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 6 245152168203723518 = some 245152168203723518 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 4 2 245152168203723518 245152168203723518 245152168203723518 endpoint_11_49_p4 endpoint_11_49_w4
private theorem endpoint_11_49_w6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 6 2 245152168203723518 = some 245152168203723518 := by decide +kernel
private theorem endpoint_11_49_p8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 8 245152168203723518 = some 245152168203723518 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 6 2 245152168203723518 245152168203723518 245152168203723518 endpoint_11_49_p6 endpoint_11_49_w6
private theorem endpoint_11_49_w8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 8 2 245152168203723518 = some 245152168203723518 := by decide +kernel
private theorem endpoint_11_49_p10 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 10 245152168203723518 = some 245152168203723518 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 8 2 245152168203723518 245152168203723518 245152168203723518 endpoint_11_49_p8 endpoint_11_49_w8
def endpoint_11_49 : CertifiedEndpoint :=
  ⟨⟨11, 49, 3700⟩, 245152168203723518, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_49_flag endpoint_11_49_sources 10 245152168203723518 245152168203723518 rfl endpoint_11_49_base endpoint_11_49_p10) (by decide)⟩
private def endpoint_11_50_flag : Flag := ⟨11, 50, 3662⟩
private def endpoint_11_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_50_base : receiptBase endpoint_11_50_flag endpoint_11_50_sources = some 246935549981753594 := by decide +kernel
private theorem endpoint_11_50_w0 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 2 246935549981753594 = some 246935549981753594 := by decide +kernel
private theorem endpoint_11_50_w2 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 2 2 246935549981753594 = some 246935549981753594 := by decide +kernel
private theorem endpoint_11_50_p4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 4 246935549981753594 = some 246935549981753594 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 2 2 246935549981753594 246935549981753594 246935549981753594 endpoint_11_50_w0 endpoint_11_50_w2
private theorem endpoint_11_50_w4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 4 2 246935549981753594 = some 246935549981753594 := by decide +kernel
private theorem endpoint_11_50_p6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 6 246935549981753594 = some 246935549981753594 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 4 2 246935549981753594 246935549981753594 246935549981753594 endpoint_11_50_p4 endpoint_11_50_w4
private theorem endpoint_11_50_w6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 6 2 246935549981753594 = some 246935549981753594 := by decide +kernel
private theorem endpoint_11_50_p8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 8 246935549981753594 = some 246935549981753594 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 6 2 246935549981753594 246935549981753594 246935549981753594 endpoint_11_50_p6 endpoint_11_50_w6
private theorem endpoint_11_50_w8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 8 2 246935549981753594 = some 246935549981753594 := by decide +kernel
private theorem endpoint_11_50_p10 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 10 246935549981753594 = some 246935549981753594 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 8 2 246935549981753594 246935549981753594 246935549981753594 endpoint_11_50_p8 endpoint_11_50_w8
def endpoint_11_50 : CertifiedEndpoint :=
  ⟨⟨11, 50, 3662⟩, 246935549981753594, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_50_flag endpoint_11_50_sources 10 246935549981753594 246935549981753594 rfl endpoint_11_50_base endpoint_11_50_p10) (by decide)⟩
private def endpoint_11_51_flag : Flag := ⟨11, 51, 3623⟩
private def endpoint_11_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_51_base : receiptBase endpoint_11_51_flag endpoint_11_51_sources = some 249205919818814739 := by decide +kernel
private theorem endpoint_11_51_w0 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 2 249205919818814739 = some 249205919818814739 := by decide +kernel
private theorem endpoint_11_51_w2 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 2 2 249205919818814739 = some 249205919818814739 := by decide +kernel
private theorem endpoint_11_51_p4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 4 249205919818814739 = some 249205919818814739 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 2 2 249205919818814739 249205919818814739 249205919818814739 endpoint_11_51_w0 endpoint_11_51_w2
private theorem endpoint_11_51_w4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 4 2 249205919818814739 = some 249205919818814739 := by decide +kernel
private theorem endpoint_11_51_p6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 6 249205919818814739 = some 249205919818814739 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 4 2 249205919818814739 249205919818814739 249205919818814739 endpoint_11_51_p4 endpoint_11_51_w4
private theorem endpoint_11_51_w6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 6 2 249205919818814739 = some 249205919818814739 := by decide +kernel
private theorem endpoint_11_51_p8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 8 249205919818814739 = some 249205919818814739 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 6 2 249205919818814739 249205919818814739 249205919818814739 endpoint_11_51_p6 endpoint_11_51_w6
private theorem endpoint_11_51_w8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 8 2 249205919818814739 = some 249205919818814739 := by decide +kernel
private theorem endpoint_11_51_p10 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 10 249205919818814739 = some 249205919818814739 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 8 2 249205919818814739 249205919818814739 249205919818814739 endpoint_11_51_p8 endpoint_11_51_w8
def endpoint_11_51 : CertifiedEndpoint :=
  ⟨⟨11, 51, 3623⟩, 249205919818814739, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_51_flag endpoint_11_51_sources 10 249205919818814739 249205919818814739 rfl endpoint_11_51_base endpoint_11_51_p10) (by decide)⟩
private def endpoint_11_52_flag : Flag := ⟨11, 52, 3583⟩
private def endpoint_11_52_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_52_base : receiptBase endpoint_11_52_flag endpoint_11_52_sources = some 250682395778363612 := by decide +kernel
private theorem endpoint_11_52_w0 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 2 250682395778363612 = some 250682395778363612 := by decide +kernel
private theorem endpoint_11_52_w2 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 2 2 250682395778363612 = some 250682395778363612 := by decide +kernel
private theorem endpoint_11_52_p4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 4 250682395778363612 = some 250682395778363612 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 2 2 250682395778363612 250682395778363612 250682395778363612 endpoint_11_52_w0 endpoint_11_52_w2
private theorem endpoint_11_52_w4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 4 2 250682395778363612 = some 250682395778363612 := by decide +kernel
private theorem endpoint_11_52_p6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 6 250682395778363612 = some 250682395778363612 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 4 2 250682395778363612 250682395778363612 250682395778363612 endpoint_11_52_p4 endpoint_11_52_w4
private theorem endpoint_11_52_w6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 6 2 250682395778363612 = some 250682395778363612 := by decide +kernel
private theorem endpoint_11_52_p8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 8 250682395778363612 = some 250682395778363612 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 6 2 250682395778363612 250682395778363612 250682395778363612 endpoint_11_52_p6 endpoint_11_52_w6
private theorem endpoint_11_52_w8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 8 2 250682395778363612 = some 250682395778363612 := by decide +kernel
private theorem endpoint_11_52_p10 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 10 250682395778363612 = some 250682395778363612 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 8 2 250682395778363612 250682395778363612 250682395778363612 endpoint_11_52_p8 endpoint_11_52_w8
def endpoint_11_52 : CertifiedEndpoint :=
  ⟨⟨11, 52, 3583⟩, 250682395778363612, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_52_flag endpoint_11_52_sources 10 250682395778363612 250682395778363612 rfl endpoint_11_52_base endpoint_11_52_p10) (by decide)⟩
private def endpoint_11_53_flag : Flag := ⟨11, 53, 3542⟩
private def endpoint_11_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_53_base : receiptBase endpoint_11_53_flag endpoint_11_53_sources = some 251995440354137367 := by decide +kernel
private theorem endpoint_11_53_w0 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 2 251995440354137367 = some 251995440354137367 := by decide +kernel
private theorem endpoint_11_53_w2 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 2 2 251995440354137367 = some 251995440354137367 := by decide +kernel
private theorem endpoint_11_53_p4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 4 251995440354137367 = some 251995440354137367 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 2 2 251995440354137367 251995440354137367 251995440354137367 endpoint_11_53_w0 endpoint_11_53_w2
private theorem endpoint_11_53_w4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 4 2 251995440354137367 = some 251995440354137367 := by decide +kernel
private theorem endpoint_11_53_p6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 6 251995440354137367 = some 251995440354137367 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 4 2 251995440354137367 251995440354137367 251995440354137367 endpoint_11_53_p4 endpoint_11_53_w4
private theorem endpoint_11_53_w6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 6 2 251995440354137367 = some 251995440354137367 := by decide +kernel
private theorem endpoint_11_53_p8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 8 251995440354137367 = some 251995440354137367 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 6 2 251995440354137367 251995440354137367 251995440354137367 endpoint_11_53_p6 endpoint_11_53_w6
private theorem endpoint_11_53_w8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 8 2 251995440354137367 = some 251995440354137367 := by decide +kernel
private theorem endpoint_11_53_p10 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 10 251995440354137367 = some 251995440354137367 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 8 2 251995440354137367 251995440354137367 251995440354137367 endpoint_11_53_p8 endpoint_11_53_w8
def endpoint_11_53 : CertifiedEndpoint :=
  ⟨⟨11, 53, 3542⟩, 251995440354137367, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_53_flag endpoint_11_53_sources 10 251995440354137367 251995440354137367 rfl endpoint_11_53_base endpoint_11_53_p10) (by decide)⟩
private def endpoint_11_54_flag : Flag := ⟨11, 54, 3499⟩
private def endpoint_11_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_54_base : receiptBase endpoint_11_54_flag endpoint_11_54_sources = some 255858255762719415 := by decide +kernel
private theorem endpoint_11_54_w0 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 2 255858255762719415 = some 255858255762719415 := by decide +kernel
private theorem endpoint_11_54_w2 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 2 2 255858255762719415 = some 255858255762719415 := by decide +kernel
private theorem endpoint_11_54_p4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 4 255858255762719415 = some 255858255762719415 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 2 2 255858255762719415 255858255762719415 255858255762719415 endpoint_11_54_w0 endpoint_11_54_w2
private theorem endpoint_11_54_w4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 4 2 255858255762719415 = some 255858255762719415 := by decide +kernel
private theorem endpoint_11_54_p6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 6 255858255762719415 = some 255858255762719415 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 4 2 255858255762719415 255858255762719415 255858255762719415 endpoint_11_54_p4 endpoint_11_54_w4
private theorem endpoint_11_54_w6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 6 2 255858255762719415 = some 255858255762719415 := by decide +kernel
private theorem endpoint_11_54_p8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 8 255858255762719415 = some 255858255762719415 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 6 2 255858255762719415 255858255762719415 255858255762719415 endpoint_11_54_p6 endpoint_11_54_w6
private theorem endpoint_11_54_w8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 8 2 255858255762719415 = some 255858255762719415 := by decide +kernel
private theorem endpoint_11_54_p10 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 10 255858255762719415 = some 255858255762719415 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 8 2 255858255762719415 255858255762719415 255858255762719415 endpoint_11_54_p8 endpoint_11_54_w8
def endpoint_11_54 : CertifiedEndpoint :=
  ⟨⟨11, 54, 3499⟩, 255858255762719415, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_54_flag endpoint_11_54_sources 10 255858255762719415 255858255762719415 rfl endpoint_11_54_base endpoint_11_54_p10) (by decide)⟩
private def endpoint_11_55_flag : Flag := ⟨11, 55, 3456⟩
private def endpoint_11_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_55_base : receiptBase endpoint_11_55_flag endpoint_11_55_sources = some 256790242194899160 := by decide +kernel
private theorem endpoint_11_55_w0 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 2 256790242194899160 = some 256790242194899160 := by decide +kernel
private theorem endpoint_11_55_w2 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 2 2 256790242194899160 = some 256790242194899160 := by decide +kernel
private theorem endpoint_11_55_p4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 4 256790242194899160 = some 256790242194899160 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 2 2 256790242194899160 256790242194899160 256790242194899160 endpoint_11_55_w0 endpoint_11_55_w2
private theorem endpoint_11_55_w4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 4 2 256790242194899160 = some 256790242194899160 := by decide +kernel
private theorem endpoint_11_55_p6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 6 256790242194899160 = some 256790242194899160 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 4 2 256790242194899160 256790242194899160 256790242194899160 endpoint_11_55_p4 endpoint_11_55_w4
private theorem endpoint_11_55_w6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 6 2 256790242194899160 = some 256790242194899160 := by decide +kernel
private theorem endpoint_11_55_p8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 8 256790242194899160 = some 256790242194899160 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 6 2 256790242194899160 256790242194899160 256790242194899160 endpoint_11_55_p6 endpoint_11_55_w6
private theorem endpoint_11_55_w8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 8 2 256790242194899160 = some 256790242194899160 := by decide +kernel
private theorem endpoint_11_55_p10 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 10 256790242194899160 = some 256790242194899160 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 8 2 256790242194899160 256790242194899160 256790242194899160 endpoint_11_55_p8 endpoint_11_55_w8
def endpoint_11_55 : CertifiedEndpoint :=
  ⟨⟨11, 55, 3456⟩, 256790242194899160, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_55_flag endpoint_11_55_sources 10 256790242194899160 256790242194899160 rfl endpoint_11_55_base endpoint_11_55_p10) (by decide)⟩
private def endpoint_11_56_flag : Flag := ⟨11, 56, 3411⟩
private def endpoint_11_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_56_base : receiptBase endpoint_11_56_flag endpoint_11_56_sources = some 257472470654655844 := by decide +kernel
private theorem endpoint_11_56_w0 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 2 257472470654655844 = some 257472470654655844 := by decide +kernel
private theorem endpoint_11_56_w2 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 2 2 257472470654655844 = some 257472470654655844 := by decide +kernel
private theorem endpoint_11_56_p4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 4 257472470654655844 = some 257472470654655844 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 2 2 257472470654655844 257472470654655844 257472470654655844 endpoint_11_56_w0 endpoint_11_56_w2
private theorem endpoint_11_56_w4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 4 2 257472470654655844 = some 257472470654655844 := by decide +kernel
private theorem endpoint_11_56_p6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 6 257472470654655844 = some 257472470654655844 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 4 2 257472470654655844 257472470654655844 257472470654655844 endpoint_11_56_p4 endpoint_11_56_w4
private theorem endpoint_11_56_w6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 6 2 257472470654655844 = some 257472470654655844 := by decide +kernel
private theorem endpoint_11_56_p8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 8 257472470654655844 = some 257472470654655844 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 6 2 257472470654655844 257472470654655844 257472470654655844 endpoint_11_56_p6 endpoint_11_56_w6
private theorem endpoint_11_56_w8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 8 2 257472470654655844 = some 257472470654655844 := by decide +kernel
private theorem endpoint_11_56_p10 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 10 257472470654655844 = some 257472470654655844 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 8 2 257472470654655844 257472470654655844 257472470654655844 endpoint_11_56_p8 endpoint_11_56_w8
def endpoint_11_56 : CertifiedEndpoint :=
  ⟨⟨11, 56, 3411⟩, 257472470654655844, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_56_flag endpoint_11_56_sources 10 257472470654655844 257472470654655844 rfl endpoint_11_56_base endpoint_11_56_p10) (by decide)⟩
private def endpoint_11_57_flag : Flag := ⟨11, 57, 3364⟩
private def endpoint_11_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_57_base : receiptBase endpoint_11_57_flag endpoint_11_57_sources = some 257897999501969656 := by decide +kernel
private theorem endpoint_11_57_w0 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 2 257897999501969656 = some 257897999501969656 := by decide +kernel
private theorem endpoint_11_57_w2 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 2 2 257897999501969656 = some 257897999501969656 := by decide +kernel
private theorem endpoint_11_57_p4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 4 257897999501969656 = some 257897999501969656 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 2 2 257897999501969656 257897999501969656 257897999501969656 endpoint_11_57_w0 endpoint_11_57_w2
private theorem endpoint_11_57_w4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 4 2 257897999501969656 = some 257897999501969656 := by decide +kernel
private theorem endpoint_11_57_p6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 6 257897999501969656 = some 257897999501969656 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 4 2 257897999501969656 257897999501969656 257897999501969656 endpoint_11_57_p4 endpoint_11_57_w4
private theorem endpoint_11_57_w6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 6 2 257897999501969656 = some 257897999501969656 := by decide +kernel
private theorem endpoint_11_57_p8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 8 257897999501969656 = some 257897999501969656 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 6 2 257897999501969656 257897999501969656 257897999501969656 endpoint_11_57_p6 endpoint_11_57_w6
private theorem endpoint_11_57_w8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 8 2 257897999501969656 = some 257897999501969656 := by decide +kernel
private theorem endpoint_11_57_p10 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 10 257897999501969656 = some 257897999501969656 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 8 2 257897999501969656 257897999501969656 257897999501969656 endpoint_11_57_p8 endpoint_11_57_w8
def endpoint_11_57 : CertifiedEndpoint :=
  ⟨⟨11, 57, 3364⟩, 257897999501969656, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_57_flag endpoint_11_57_sources 10 257897999501969656 257897999501969656 rfl endpoint_11_57_base endpoint_11_57_p10) (by decide)⟩
private def endpoint_11_58_flag : Flag := ⟨11, 58, 3315⟩
private def endpoint_11_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_58_base : receiptBase endpoint_11_58_flag endpoint_11_58_sources = some 258059887096820785 := by decide +kernel
private theorem endpoint_11_58_w0 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 2 258059887096820785 = some 258059887096820785 := by decide +kernel
private theorem endpoint_11_58_w2 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 2 2 258059887096820785 = some 258059887096820785 := by decide +kernel
private theorem endpoint_11_58_p4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 4 258059887096820785 = some 258059887096820785 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 2 2 258059887096820785 258059887096820785 258059887096820785 endpoint_11_58_w0 endpoint_11_58_w2
private theorem endpoint_11_58_w4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 4 2 258059887096820785 = some 258059887096820785 := by decide +kernel
private theorem endpoint_11_58_p6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 6 258059887096820785 = some 258059887096820785 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 4 2 258059887096820785 258059887096820785 258059887096820785 endpoint_11_58_p4 endpoint_11_58_w4
private theorem endpoint_11_58_w6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 6 2 258059887096820785 = some 258059887096820785 := by decide +kernel
private theorem endpoint_11_58_p8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 8 258059887096820785 = some 258059887096820785 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 6 2 258059887096820785 258059887096820785 258059887096820785 endpoint_11_58_p6 endpoint_11_58_w6
private theorem endpoint_11_58_w8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 8 2 258059887096820785 = some 258059887096820785 := by decide +kernel
private theorem endpoint_11_58_p10 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 10 258059887096820785 = some 258059887096820785 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 8 2 258059887096820785 258059887096820785 258059887096820785 endpoint_11_58_p8 endpoint_11_58_w8
def endpoint_11_58 : CertifiedEndpoint :=
  ⟨⟨11, 58, 3315⟩, 258059887096820785, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_58_flag endpoint_11_58_sources 10 258059887096820785 258059887096820785 rfl endpoint_11_58_base endpoint_11_58_p10) (by decide)⟩
private def endpoint_11_59_flag : Flag := ⟨11, 59, 3265⟩
private def endpoint_11_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_59_base : receiptBase endpoint_11_59_flag endpoint_11_59_sources = some 258029214715267218 := by decide +kernel
private theorem endpoint_11_59_w0 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 2 258029214715267218 = some 258029214715267218 := by decide +kernel
private theorem endpoint_11_59_w2 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 2 2 258029214715267218 = some 258029214715267218 := by decide +kernel
private theorem endpoint_11_59_p4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 4 258029214715267218 = some 258029214715267218 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 2 2 258029214715267218 258029214715267218 258029214715267218 endpoint_11_59_w0 endpoint_11_59_w2
private theorem endpoint_11_59_w4 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 4 2 258029214715267218 = some 258029214715267218 := by decide +kernel
private theorem endpoint_11_59_p6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 6 258029214715267218 = some 258029214715267218 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 4 2 258029214715267218 258029214715267218 258029214715267218 endpoint_11_59_p4 endpoint_11_59_w4
private theorem endpoint_11_59_w6 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 6 2 258029214715267218 = some 258029214715267218 := by decide +kernel
private theorem endpoint_11_59_p8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 8 258029214715267218 = some 258029214715267218 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 6 2 258029214715267218 258029214715267218 258029214715267218 endpoint_11_59_p6 endpoint_11_59_w6
private theorem endpoint_11_59_w8 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 8 2 258029214715267218 = some 258029214715267218 := by decide +kernel
private theorem endpoint_11_59_p10 : receiptWindow endpoint_11_59_flag endpoint_11_59_sources 0 10 258029214715267218 = some 258029214715267218 :=
  join_receipt_window endpoint_11_59_flag endpoint_11_59_sources 0 8 2 258029214715267218 258029214715267218 258029214715267218 endpoint_11_59_p8 endpoint_11_59_w8
def endpoint_11_59 : CertifiedEndpoint :=
  ⟨⟨11, 59, 3265⟩, 258029214715267218, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_59_flag endpoint_11_59_sources 10 258029214715267218 258029214715267218 rfl endpoint_11_59_base endpoint_11_59_p10) (by decide)⟩
private def endpoint_11_60_flag : Flag := ⟨11, 60, 3212⟩
private def endpoint_11_60_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_60_base : receiptBase endpoint_11_60_flag endpoint_11_60_sources = some 258833853869101627 := by decide +kernel
private theorem endpoint_11_60_w0 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 2 258833853869101627 = some 258833853869101627 := by decide +kernel
private theorem endpoint_11_60_w2 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 2 2 258833853869101627 = some 258833853869101627 := by decide +kernel
private theorem endpoint_11_60_p4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 4 258833853869101627 = some 258833853869101627 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 2 2 258833853869101627 258833853869101627 258833853869101627 endpoint_11_60_w0 endpoint_11_60_w2
private theorem endpoint_11_60_w4 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 4 2 258833853869101627 = some 258833853869101627 := by decide +kernel
private theorem endpoint_11_60_p6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 6 258833853869101627 = some 258833853869101627 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 4 2 258833853869101627 258833853869101627 258833853869101627 endpoint_11_60_p4 endpoint_11_60_w4
private theorem endpoint_11_60_w6 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 6 2 258833853869101627 = some 258833853869101627 := by decide +kernel
private theorem endpoint_11_60_p8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 8 258833853869101627 = some 258833853869101627 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 6 2 258833853869101627 258833853869101627 258833853869101627 endpoint_11_60_p6 endpoint_11_60_w6
private theorem endpoint_11_60_w8 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 8 2 258833853869101627 = some 258833853869101627 := by decide +kernel
private theorem endpoint_11_60_p10 : receiptWindow endpoint_11_60_flag endpoint_11_60_sources 0 10 258833853869101627 = some 258833853869101627 :=
  join_receipt_window endpoint_11_60_flag endpoint_11_60_sources 0 8 2 258833853869101627 258833853869101627 258833853869101627 endpoint_11_60_p8 endpoint_11_60_w8
def endpoint_11_60 : CertifiedEndpoint :=
  ⟨⟨11, 60, 3212⟩, 258833853869101627, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_60_flag endpoint_11_60_sources 10 258833853869101627 258833853869101627 rfl endpoint_11_60_base endpoint_11_60_p10) (by decide)⟩
private def endpoint_11_61_flag : Flag := ⟨11, 61, 3157⟩
private def endpoint_11_61_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_11_61_base : receiptBase endpoint_11_61_flag endpoint_11_61_sources = some 258163959604105000 := by decide +kernel
private theorem endpoint_11_61_w0 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 2 258163959604105000 = some 258163959604105000 := by decide +kernel
private theorem endpoint_11_61_w2 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 2 2 258163959604105000 = some 258163959604105000 := by decide +kernel
private theorem endpoint_11_61_p4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 4 258163959604105000 = some 258163959604105000 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 2 2 258163959604105000 258163959604105000 258163959604105000 endpoint_11_61_w0 endpoint_11_61_w2
private theorem endpoint_11_61_w4 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 4 2 258163959604105000 = some 258163959604105000 := by decide +kernel
private theorem endpoint_11_61_p6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 6 258163959604105000 = some 258163959604105000 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 4 2 258163959604105000 258163959604105000 258163959604105000 endpoint_11_61_p4 endpoint_11_61_w4
private theorem endpoint_11_61_w6 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 6 2 258163959604105000 = some 258163959604105000 := by decide +kernel
private theorem endpoint_11_61_p8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 8 258163959604105000 = some 258163959604105000 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 6 2 258163959604105000 258163959604105000 258163959604105000 endpoint_11_61_p6 endpoint_11_61_w6
private theorem endpoint_11_61_w8 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 8 2 258163959604105000 = some 258163959604105000 := by decide +kernel
private theorem endpoint_11_61_p10 : receiptWindow endpoint_11_61_flag endpoint_11_61_sources 0 10 258163959604105000 = some 258163959604105000 :=
  join_receipt_window endpoint_11_61_flag endpoint_11_61_sources 0 8 2 258163959604105000 258163959604105000 258163959604105000 endpoint_11_61_p8 endpoint_11_61_w8
def endpoint_11_61 : CertifiedEndpoint :=
  ⟨⟨11, 61, 3157⟩, 258163959604105000, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_11_61_flag endpoint_11_61_sources 10 258163959604105000 258163959604105000 rfl endpoint_11_61_base endpoint_11_61_p10) (by decide)⟩
private def endpoint_11_62_flag : Flag := ⟨11, 62, 3099⟩
private def endpoint_11_62_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_62_base : receiptBase endpoint_11_62_flag endpoint_11_62_sources = some 258367632165699546 := by decide +kernel
private theorem endpoint_11_62_w0 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 2 258367632165699546 = some 258367632165699546 := by decide +kernel
private theorem endpoint_11_62_w2 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 2 2 258367632165699546 = some 258367632165699546 := by decide +kernel
private theorem endpoint_11_62_p4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 4 258367632165699546 = some 258367632165699546 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 2 2 258367632165699546 258367632165699546 258367632165699546 endpoint_11_62_w0 endpoint_11_62_w2
private theorem endpoint_11_62_w4 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 4 2 258367632165699546 = some 258367632165699546 := by decide +kernel
private theorem endpoint_11_62_p6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 6 258367632165699546 = some 258367632165699546 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 4 2 258367632165699546 258367632165699546 258367632165699546 endpoint_11_62_p4 endpoint_11_62_w4
private theorem endpoint_11_62_w6 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 6 2 258367632165699546 = some 258367632165699546 := by decide +kernel
private theorem endpoint_11_62_p8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 8 258367632165699546 = some 258367632165699546 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 6 2 258367632165699546 258367632165699546 258367632165699546 endpoint_11_62_p6 endpoint_11_62_w6
private theorem endpoint_11_62_w8 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 8 2 258367632165699546 = some 258367632165699546 := by decide +kernel
private theorem endpoint_11_62_p10 : receiptWindow endpoint_11_62_flag endpoint_11_62_sources 0 10 258367632165699546 = some 258367632165699546 :=
  join_receipt_window endpoint_11_62_flag endpoint_11_62_sources 0 8 2 258367632165699546 258367632165699546 258367632165699546 endpoint_11_62_p8 endpoint_11_62_w8
def endpoint_11_62 : CertifiedEndpoint :=
  ⟨⟨11, 62, 3099⟩, 258367632165699546, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_62_flag endpoint_11_62_sources 10 258367632165699546 258367632165699546 rfl endpoint_11_62_base endpoint_11_62_p10) (by decide)⟩
private def endpoint_11_63_flag : Flag := ⟨11, 63, 3038⟩
private def endpoint_11_63_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_11_63_base : receiptBase endpoint_11_63_flag endpoint_11_63_sources = some 256932767416474439 := by decide +kernel
private theorem endpoint_11_63_w0 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 2 256932767416474439 = some 256932767416474439 := by decide +kernel
private theorem endpoint_11_63_w2 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 2 2 256932767416474439 = some 256932767416474439 := by decide +kernel
private theorem endpoint_11_63_p4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 4 256932767416474439 = some 256932767416474439 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 2 2 256932767416474439 256932767416474439 256932767416474439 endpoint_11_63_w0 endpoint_11_63_w2
private theorem endpoint_11_63_w4 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 4 2 256932767416474439 = some 256932767416474439 := by decide +kernel
private theorem endpoint_11_63_p6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 6 256932767416474439 = some 256932767416474439 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 4 2 256932767416474439 256932767416474439 256932767416474439 endpoint_11_63_p4 endpoint_11_63_w4
private theorem endpoint_11_63_w6 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 6 2 256932767416474439 = some 256932767416474439 := by decide +kernel
private theorem endpoint_11_63_p8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 8 256932767416474439 = some 256932767416474439 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 6 2 256932767416474439 256932767416474439 256932767416474439 endpoint_11_63_p6 endpoint_11_63_w6
private theorem endpoint_11_63_w8 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 8 2 256932767416474439 = some 256932767416474439 := by decide +kernel
private theorem endpoint_11_63_p10 : receiptWindow endpoint_11_63_flag endpoint_11_63_sources 0 10 256932767416474439 = some 256932767416474439 :=
  join_receipt_window endpoint_11_63_flag endpoint_11_63_sources 0 8 2 256932767416474439 256932767416474439 256932767416474439 endpoint_11_63_p8 endpoint_11_63_w8
def endpoint_11_63 : CertifiedEndpoint :=
  ⟨⟨11, 63, 3038⟩, 256932767416474439, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_11_63_flag endpoint_11_63_sources 10 256932767416474439 256932767416474439 rfl endpoint_11_63_base endpoint_11_63_p10) (by decide)⟩
private def endpoint_11_64_flag : Flag := ⟨11, 64, 2974⟩
private def endpoint_11_64_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_11_64_base : receiptBase endpoint_11_64_flag endpoint_11_64_sources = some 256386719295353606 := by decide +kernel
private theorem endpoint_11_64_w0 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 2 256386719295353606 = some 256386719295353606 := by decide +kernel
private theorem endpoint_11_64_w2 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 2 2 256386719295353606 = some 256386719295353606 := by decide +kernel
private theorem endpoint_11_64_p4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 4 256386719295353606 = some 256386719295353606 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 2 2 256386719295353606 256386719295353606 256386719295353606 endpoint_11_64_w0 endpoint_11_64_w2
private theorem endpoint_11_64_w4 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 4 2 256386719295353606 = some 256386719295353606 := by decide +kernel
private theorem endpoint_11_64_p6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 6 256386719295353606 = some 256386719295353606 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 4 2 256386719295353606 256386719295353606 256386719295353606 endpoint_11_64_p4 endpoint_11_64_w4
private theorem endpoint_11_64_w6 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 6 2 256386719295353606 = some 256386719295353606 := by decide +kernel
private theorem endpoint_11_64_p8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 8 256386719295353606 = some 256386719295353606 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 6 2 256386719295353606 256386719295353606 256386719295353606 endpoint_11_64_p6 endpoint_11_64_w6
private theorem endpoint_11_64_w8 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 8 2 256386719295353606 = some 256386719295353606 := by decide +kernel
private theorem endpoint_11_64_p10 : receiptWindow endpoint_11_64_flag endpoint_11_64_sources 0 10 256386719295353606 = some 256386719295353606 :=
  join_receipt_window endpoint_11_64_flag endpoint_11_64_sources 0 8 2 256386719295353606 256386719295353606 256386719295353606 endpoint_11_64_p8 endpoint_11_64_w8
def endpoint_11_64 : CertifiedEndpoint :=
  ⟨⟨11, 64, 2974⟩, 256386719295353606, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_11_64_flag endpoint_11_64_sources 10 256386719295353606 256386719295353606 rfl endpoint_11_64_base endpoint_11_64_p10) (by decide)⟩
private def endpoint_11_65_flag : Flag := ⟨11, 65, 2908⟩
private def endpoint_11_65_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_11_65_base : receiptBase endpoint_11_65_flag endpoint_11_65_sources = some 255541498328362041 := by decide +kernel
private theorem endpoint_11_65_w0 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 2 255541498328362041 = some 255541498328362041 := by decide +kernel
private theorem endpoint_11_65_w2 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 2 2 255541498328362041 = some 255541498328362041 := by decide +kernel
private theorem endpoint_11_65_p4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 4 255541498328362041 = some 255541498328362041 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 2 2 255541498328362041 255541498328362041 255541498328362041 endpoint_11_65_w0 endpoint_11_65_w2
private theorem endpoint_11_65_w4 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 4 2 255541498328362041 = some 255541498328362041 := by decide +kernel
private theorem endpoint_11_65_p6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 6 255541498328362041 = some 255541498328362041 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 4 2 255541498328362041 255541498328362041 255541498328362041 endpoint_11_65_p4 endpoint_11_65_w4
private theorem endpoint_11_65_w6 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 6 2 255541498328362041 = some 255541498328362041 := by decide +kernel
private theorem endpoint_11_65_p8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 8 255541498328362041 = some 255541498328362041 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 6 2 255541498328362041 255541498328362041 255541498328362041 endpoint_11_65_p6 endpoint_11_65_w6
private theorem endpoint_11_65_w8 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 8 2 255541498328362041 = some 255541498328362041 := by decide +kernel
private theorem endpoint_11_65_p10 : receiptWindow endpoint_11_65_flag endpoint_11_65_sources 0 10 255541498328362041 = some 255541498328362041 :=
  join_receipt_window endpoint_11_65_flag endpoint_11_65_sources 0 8 2 255541498328362041 255541498328362041 255541498328362041 endpoint_11_65_p8 endpoint_11_65_w8
def endpoint_11_65 : CertifiedEndpoint :=
  ⟨⟨11, 65, 2908⟩, 255541498328362041, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_11_65_flag endpoint_11_65_sources 10 255541498328362041 255541498328362041 rfl endpoint_11_65_base endpoint_11_65_p10) (by decide)⟩
private def endpoint_11_66_flag : Flag := ⟨11, 66, 2838⟩
private def endpoint_11_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_66_base : receiptBase endpoint_11_66_flag endpoint_11_66_sources = some 254046833806644552 := by decide +kernel
private theorem endpoint_11_66_w0 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 2 254046833806644552 = some 254046833806644552 := by decide +kernel
private theorem endpoint_11_66_w2 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 2 2 254046833806644552 = some 254046833806644552 := by decide +kernel
private theorem endpoint_11_66_p4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 4 254046833806644552 = some 254046833806644552 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 2 2 254046833806644552 254046833806644552 254046833806644552 endpoint_11_66_w0 endpoint_11_66_w2
private theorem endpoint_11_66_w4 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 4 2 254046833806644552 = some 254046833806644552 := by decide +kernel
private theorem endpoint_11_66_p6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 6 254046833806644552 = some 254046833806644552 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 4 2 254046833806644552 254046833806644552 254046833806644552 endpoint_11_66_p4 endpoint_11_66_w4
private theorem endpoint_11_66_w6 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 6 2 254046833806644552 = some 254046833806644552 := by decide +kernel
private theorem endpoint_11_66_p8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 8 254046833806644552 = some 254046833806644552 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 6 2 254046833806644552 254046833806644552 254046833806644552 endpoint_11_66_p6 endpoint_11_66_w6
private theorem endpoint_11_66_w8 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 8 2 254046833806644552 = some 254046833806644552 := by decide +kernel
private theorem endpoint_11_66_p10 : receiptWindow endpoint_11_66_flag endpoint_11_66_sources 0 10 254046833806644552 = some 254046833806644552 :=
  join_receipt_window endpoint_11_66_flag endpoint_11_66_sources 0 8 2 254046833806644552 254046833806644552 254046833806644552 endpoint_11_66_p8 endpoint_11_66_w8
def endpoint_11_66 : CertifiedEndpoint :=
  ⟨⟨11, 66, 2838⟩, 254046833806644552, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_66_flag endpoint_11_66_sources 10 254046833806644552 254046833806644552 rfl endpoint_11_66_base endpoint_11_66_p10) (by decide)⟩
private def endpoint_11_67_flag : Flag := ⟨11, 67, 2766⟩
private def endpoint_11_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_67_base : receiptBase endpoint_11_67_flag endpoint_11_67_sources = some 251002835633440837 := by decide +kernel
private theorem endpoint_11_67_w0 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 2 251002835633440837 = some 251002835633440837 := by decide +kernel
private theorem endpoint_11_67_w2 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 2 2 251002835633440837 = some 251002835633440837 := by decide +kernel
private theorem endpoint_11_67_p4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 4 251002835633440837 = some 251002835633440837 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 2 2 251002835633440837 251002835633440837 251002835633440837 endpoint_11_67_w0 endpoint_11_67_w2
private theorem endpoint_11_67_w4 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 4 2 251002835633440837 = some 251002835633440837 := by decide +kernel
private theorem endpoint_11_67_p6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 6 251002835633440837 = some 251002835633440837 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 4 2 251002835633440837 251002835633440837 251002835633440837 endpoint_11_67_p4 endpoint_11_67_w4
private theorem endpoint_11_67_w6 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 6 2 251002835633440837 = some 251002835633440837 := by decide +kernel
private theorem endpoint_11_67_p8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 8 251002835633440837 = some 251002835633440837 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 6 2 251002835633440837 251002835633440837 251002835633440837 endpoint_11_67_p6 endpoint_11_67_w6
private theorem endpoint_11_67_w8 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 8 2 251002835633440837 = some 251002835633440837 := by decide +kernel
private theorem endpoint_11_67_p10 : receiptWindow endpoint_11_67_flag endpoint_11_67_sources 0 10 251002835633440837 = some 251002835633440837 :=
  join_receipt_window endpoint_11_67_flag endpoint_11_67_sources 0 8 2 251002835633440837 251002835633440837 251002835633440837 endpoint_11_67_p8 endpoint_11_67_w8
def endpoint_11_67 : CertifiedEndpoint :=
  ⟨⟨11, 67, 2766⟩, 251002835633440837, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_67_flag endpoint_11_67_sources 10 251002835633440837 251002835633440837 rfl endpoint_11_67_base endpoint_11_67_p10) (by decide)⟩
private def endpoint_11_68_flag : Flag := ⟨11, 68, 2691⟩
private def endpoint_11_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_68_base : receiptBase endpoint_11_68_flag endpoint_11_68_sources = some 247511603972756565 := by decide +kernel
private theorem endpoint_11_68_w0 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 2 247511603972756565 = some 247511603972756565 := by decide +kernel
private theorem endpoint_11_68_w2 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 2 2 247511603972756565 = some 247511603972756565 := by decide +kernel
private theorem endpoint_11_68_p4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 4 247511603972756565 = some 247511603972756565 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 2 2 247511603972756565 247511603972756565 247511603972756565 endpoint_11_68_w0 endpoint_11_68_w2
private theorem endpoint_11_68_w4 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 4 2 247511603972756565 = some 247511603972756565 := by decide +kernel
private theorem endpoint_11_68_p6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 6 247511603972756565 = some 247511603972756565 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 4 2 247511603972756565 247511603972756565 247511603972756565 endpoint_11_68_p4 endpoint_11_68_w4
private theorem endpoint_11_68_w6 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 6 2 247511603972756565 = some 247511603972756565 := by decide +kernel
private theorem endpoint_11_68_p8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 8 247511603972756565 = some 247511603972756565 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 6 2 247511603972756565 247511603972756565 247511603972756565 endpoint_11_68_p6 endpoint_11_68_w6
private theorem endpoint_11_68_w8 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 8 2 247511603972756565 = some 247511603972756565 := by decide +kernel
private theorem endpoint_11_68_p10 : receiptWindow endpoint_11_68_flag endpoint_11_68_sources 0 10 247511603972756565 = some 247511603972756565 :=
  join_receipt_window endpoint_11_68_flag endpoint_11_68_sources 0 8 2 247511603972756565 247511603972756565 247511603972756565 endpoint_11_68_p8 endpoint_11_68_w8
def endpoint_11_68 : CertifiedEndpoint :=
  ⟨⟨11, 68, 2691⟩, 247511603972756565, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_68_flag endpoint_11_68_sources 10 247511603972756565 247511603972756565 rfl endpoint_11_68_base endpoint_11_68_p10) (by decide)⟩
private def endpoint_11_69_flag : Flag := ⟨11, 69, 2612⟩
private def endpoint_11_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_11_69_base : receiptBase endpoint_11_69_flag endpoint_11_69_sources = some 243470135385499954 := by decide +kernel
private theorem endpoint_11_69_w0 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 2 243470135385499954 = some 243470135385499954 := by decide +kernel
private theorem endpoint_11_69_w2 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 2 2 243470135385499954 = some 243470135385499954 := by decide +kernel
private theorem endpoint_11_69_p4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 4 243470135385499954 = some 243470135385499954 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 2 2 243470135385499954 243470135385499954 243470135385499954 endpoint_11_69_w0 endpoint_11_69_w2
private theorem endpoint_11_69_w4 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 4 2 243470135385499954 = some 243470135385499954 := by decide +kernel
private theorem endpoint_11_69_p6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 6 243470135385499954 = some 243470135385499954 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 4 2 243470135385499954 243470135385499954 243470135385499954 endpoint_11_69_p4 endpoint_11_69_w4
private theorem endpoint_11_69_w6 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 6 2 243470135385499954 = some 243470135385499954 := by decide +kernel
private theorem endpoint_11_69_p8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 8 243470135385499954 = some 243470135385499954 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 6 2 243470135385499954 243470135385499954 243470135385499954 endpoint_11_69_p6 endpoint_11_69_w6
private theorem endpoint_11_69_w8 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 8 2 243470135385499954 = some 243470135385499954 := by decide +kernel
private theorem endpoint_11_69_p10 : receiptWindow endpoint_11_69_flag endpoint_11_69_sources 0 10 243470135385499954 = some 243470135385499954 :=
  join_receipt_window endpoint_11_69_flag endpoint_11_69_sources 0 8 2 243470135385499954 243470135385499954 243470135385499954 endpoint_11_69_p8 endpoint_11_69_w8
def endpoint_11_69 : CertifiedEndpoint :=
  ⟨⟨11, 69, 2612⟩, 243470135385499954, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_11_69_flag endpoint_11_69_sources 10 243470135385499954 243470135385499954 rfl endpoint_11_69_base endpoint_11_69_p10) (by decide)⟩
private def endpoint_11_70_flag : Flag := ⟨11, 70, 2531⟩
private def endpoint_11_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_70_base : receiptBase endpoint_11_70_flag endpoint_11_70_sources = some 244318074700802622 := by decide +kernel
private theorem endpoint_11_70_w0 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 2 244318074700802622 = some 244318074700802622 := by decide +kernel
private theorem endpoint_11_70_w2 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 2 2 244318074700802622 = some 244318074700802622 := by decide +kernel
private theorem endpoint_11_70_p4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 4 244318074700802622 = some 244318074700802622 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 2 2 244318074700802622 244318074700802622 244318074700802622 endpoint_11_70_w0 endpoint_11_70_w2
private theorem endpoint_11_70_w4 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 4 2 244318074700802622 = some 244318074700802622 := by decide +kernel
private theorem endpoint_11_70_p6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 6 244318074700802622 = some 244318074700802622 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 4 2 244318074700802622 244318074700802622 244318074700802622 endpoint_11_70_p4 endpoint_11_70_w4
private theorem endpoint_11_70_w6 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 6 2 244318074700802622 = some 244318074700802622 := by decide +kernel
private theorem endpoint_11_70_p8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 8 244318074700802622 = some 244318074700802622 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 6 2 244318074700802622 244318074700802622 244318074700802622 endpoint_11_70_p6 endpoint_11_70_w6
private theorem endpoint_11_70_w8 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 8 2 244318074700802622 = some 244318074700802622 := by decide +kernel
private theorem endpoint_11_70_p10 : receiptWindow endpoint_11_70_flag endpoint_11_70_sources 0 10 244318074700802622 = some 244318074700802622 :=
  join_receipt_window endpoint_11_70_flag endpoint_11_70_sources 0 8 2 244318074700802622 244318074700802622 244318074700802622 endpoint_11_70_p8 endpoint_11_70_w8
def endpoint_11_70 : CertifiedEndpoint :=
  ⟨⟨11, 70, 2531⟩, 244318074700802622, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_70_flag endpoint_11_70_sources 10 244318074700802622 244318074700802622 rfl endpoint_11_70_base endpoint_11_70_p10) (by decide)⟩
private def endpoint_11_71_flag : Flag := ⟨11, 71, 2447⟩
private def endpoint_11_71_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_71_base : receiptBase endpoint_11_71_flag endpoint_11_71_sources = some 239368686487896458 := by decide +kernel
private theorem endpoint_11_71_w0 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 2 239368686487896458 = some 239368686487896458 := by decide +kernel
private theorem endpoint_11_71_w2 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 2 2 239368686487896458 = some 239368686487896458 := by decide +kernel
private theorem endpoint_11_71_p4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 4 239368686487896458 = some 239368686487896458 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 2 2 239368686487896458 239368686487896458 239368686487896458 endpoint_11_71_w0 endpoint_11_71_w2
private theorem endpoint_11_71_w4 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 4 2 239368686487896458 = some 239368686487896458 := by decide +kernel
private theorem endpoint_11_71_p6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 6 239368686487896458 = some 239368686487896458 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 4 2 239368686487896458 239368686487896458 239368686487896458 endpoint_11_71_p4 endpoint_11_71_w4
private theorem endpoint_11_71_w6 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 6 2 239368686487896458 = some 239368686487896458 := by decide +kernel
private theorem endpoint_11_71_p8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 8 239368686487896458 = some 239368686487896458 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 6 2 239368686487896458 239368686487896458 239368686487896458 endpoint_11_71_p6 endpoint_11_71_w6
private theorem endpoint_11_71_w8 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 8 2 239368686487896458 = some 239368686487896458 := by decide +kernel
private theorem endpoint_11_71_p10 : receiptWindow endpoint_11_71_flag endpoint_11_71_sources 0 10 239368686487896458 = some 239368686487896458 :=
  join_receipt_window endpoint_11_71_flag endpoint_11_71_sources 0 8 2 239368686487896458 239368686487896458 239368686487896458 endpoint_11_71_p8 endpoint_11_71_w8
def endpoint_11_71 : CertifiedEndpoint :=
  ⟨⟨11, 71, 2447⟩, 239368686487896458, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_71_flag endpoint_11_71_sources 10 239368686487896458 239368686487896458 rfl endpoint_11_71_base endpoint_11_71_p10) (by decide)⟩
private def endpoint_11_72_flag : Flag := ⟨11, 72, 2359⟩
private def endpoint_11_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_11_72_base : receiptBase endpoint_11_72_flag endpoint_11_72_sources = some 233828076482453064 := by decide +kernel
private theorem endpoint_11_72_w0 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 2 233828076482453064 = some 233828076482453064 := by decide +kernel
private theorem endpoint_11_72_w2 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 2 2 233828076482453064 = some 233828076482453064 := by decide +kernel
private theorem endpoint_11_72_p4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 4 233828076482453064 = some 233828076482453064 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 2 2 233828076482453064 233828076482453064 233828076482453064 endpoint_11_72_w0 endpoint_11_72_w2
private theorem endpoint_11_72_w4 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 4 2 233828076482453064 = some 233828076482453064 := by decide +kernel
private theorem endpoint_11_72_p6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 6 233828076482453064 = some 233828076482453064 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 4 2 233828076482453064 233828076482453064 233828076482453064 endpoint_11_72_p4 endpoint_11_72_w4
private theorem endpoint_11_72_w6 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 6 2 233828076482453064 = some 233828076482453064 := by decide +kernel
private theorem endpoint_11_72_p8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 8 233828076482453064 = some 233828076482453064 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 6 2 233828076482453064 233828076482453064 233828076482453064 endpoint_11_72_p6 endpoint_11_72_w6
private theorem endpoint_11_72_w8 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 8 2 233828076482453064 = some 233828076482453064 := by decide +kernel
private theorem endpoint_11_72_p10 : receiptWindow endpoint_11_72_flag endpoint_11_72_sources 0 10 233828076482453064 = some 233828076482453064 :=
  join_receipt_window endpoint_11_72_flag endpoint_11_72_sources 0 8 2 233828076482453064 233828076482453064 233828076482453064 endpoint_11_72_p8 endpoint_11_72_w8
def endpoint_11_72 : CertifiedEndpoint :=
  ⟨⟨11, 72, 2359⟩, 233828076482453064, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_11_72_flag endpoint_11_72_sources 10 233828076482453064 233828076482453064 rfl endpoint_11_72_base endpoint_11_72_p10) (by decide)⟩
private def endpoint_11_73_flag : Flag := ⟨11, 73, 2269⟩
private def endpoint_11_73_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_73_base : receiptBase endpoint_11_73_flag endpoint_11_73_sources = some 229550545554857961 := by decide +kernel
private theorem endpoint_11_73_w0 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 2 229550545554857961 = some 229550545554857961 := by decide +kernel
private theorem endpoint_11_73_w2 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 2 2 229550545554857961 = some 229550545554857961 := by decide +kernel
private theorem endpoint_11_73_p4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 4 229550545554857961 = some 229550545554857961 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 2 2 229550545554857961 229550545554857961 229550545554857961 endpoint_11_73_w0 endpoint_11_73_w2
private theorem endpoint_11_73_w4 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 4 2 229550545554857961 = some 229550545554857961 := by decide +kernel
private theorem endpoint_11_73_p6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 6 229550545554857961 = some 229550545554857961 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 4 2 229550545554857961 229550545554857961 229550545554857961 endpoint_11_73_p4 endpoint_11_73_w4
private theorem endpoint_11_73_w6 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 6 2 229550545554857961 = some 229550545554857961 := by decide +kernel
private theorem endpoint_11_73_p8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 8 229550545554857961 = some 229550545554857961 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 6 2 229550545554857961 229550545554857961 229550545554857961 endpoint_11_73_p6 endpoint_11_73_w6
private theorem endpoint_11_73_w8 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 8 2 229550545554857961 = some 229550545554857961 := by decide +kernel
private theorem endpoint_11_73_p10 : receiptWindow endpoint_11_73_flag endpoint_11_73_sources 0 10 229550545554857961 = some 229550545554857961 :=
  join_receipt_window endpoint_11_73_flag endpoint_11_73_sources 0 8 2 229550545554857961 229550545554857961 229550545554857961 endpoint_11_73_p8 endpoint_11_73_w8
def endpoint_11_73 : CertifiedEndpoint :=
  ⟨⟨11, 73, 2269⟩, 229550545554857961, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_73_flag endpoint_11_73_sources 10 229550545554857961 229550545554857961 rfl endpoint_11_73_base endpoint_11_73_p10) (by decide)⟩
private def endpoint_11_74_flag : Flag := ⟨11, 74, 2176⟩
private def endpoint_11_74_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_11_74_base : receiptBase endpoint_11_74_flag endpoint_11_74_sources = some 222936847688258611 := by decide +kernel
private theorem endpoint_11_74_w0 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 2 222936847688258611 = some 222936847688258611 := by decide +kernel
private theorem endpoint_11_74_w2 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 2 2 222936847688258611 = some 222936847688258611 := by decide +kernel
private theorem endpoint_11_74_p4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 4 222936847688258611 = some 222936847688258611 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 2 2 222936847688258611 222936847688258611 222936847688258611 endpoint_11_74_w0 endpoint_11_74_w2
private theorem endpoint_11_74_w4 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 4 2 222936847688258611 = some 222936847688258611 := by decide +kernel
private theorem endpoint_11_74_p6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 6 222936847688258611 = some 222936847688258611 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 4 2 222936847688258611 222936847688258611 222936847688258611 endpoint_11_74_p4 endpoint_11_74_w4
private theorem endpoint_11_74_w6 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 6 2 222936847688258611 = some 222936847688258611 := by decide +kernel
private theorem endpoint_11_74_p8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 8 222936847688258611 = some 222936847688258611 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 6 2 222936847688258611 222936847688258611 222936847688258611 endpoint_11_74_p6 endpoint_11_74_w6
private theorem endpoint_11_74_w8 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 8 2 222936847688258611 = some 222936847688258611 := by decide +kernel
private theorem endpoint_11_74_p10 : receiptWindow endpoint_11_74_flag endpoint_11_74_sources 0 10 222936847688258611 = some 222936847688258611 :=
  join_receipt_window endpoint_11_74_flag endpoint_11_74_sources 0 8 2 222936847688258611 222936847688258611 222936847688258611 endpoint_11_74_p8 endpoint_11_74_w8
def endpoint_11_74 : CertifiedEndpoint :=
  ⟨⟨11, 74, 2176⟩, 222936847688258611, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_11_74_flag endpoint_11_74_sources 10 222936847688258611 222936847688258611 rfl endpoint_11_74_base endpoint_11_74_p10) (by decide)⟩
private def endpoint_11_75_flag : Flag := ⟨11, 75, 2079⟩
private def endpoint_11_75_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_75_base : receiptBase endpoint_11_75_flag endpoint_11_75_sources = some 217447090784815043 := by decide +kernel
private theorem endpoint_11_75_w0 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 2 217447090784815043 = some 217447090784815043 := by decide +kernel
private theorem endpoint_11_75_w2 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 2 2 217447090784815043 = some 217447090784815043 := by decide +kernel
private theorem endpoint_11_75_p4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 4 217447090784815043 = some 217447090784815043 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 2 2 217447090784815043 217447090784815043 217447090784815043 endpoint_11_75_w0 endpoint_11_75_w2
private theorem endpoint_11_75_w4 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 4 2 217447090784815043 = some 217447090784815043 := by decide +kernel
private theorem endpoint_11_75_p6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 6 217447090784815043 = some 217447090784815043 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 4 2 217447090784815043 217447090784815043 217447090784815043 endpoint_11_75_p4 endpoint_11_75_w4
private theorem endpoint_11_75_w6 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 6 2 217447090784815043 = some 217447090784815043 := by decide +kernel
private theorem endpoint_11_75_p8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 8 217447090784815043 = some 217447090784815043 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 6 2 217447090784815043 217447090784815043 217447090784815043 endpoint_11_75_p6 endpoint_11_75_w6
private theorem endpoint_11_75_w8 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 8 2 217447090784815043 = some 217447090784815043 := by decide +kernel
private theorem endpoint_11_75_p10 : receiptWindow endpoint_11_75_flag endpoint_11_75_sources 0 10 217447090784815043 = some 217447090784815043 :=
  join_receipt_window endpoint_11_75_flag endpoint_11_75_sources 0 8 2 217447090784815043 217447090784815043 217447090784815043 endpoint_11_75_p8 endpoint_11_75_w8
def endpoint_11_75 : CertifiedEndpoint :=
  ⟨⟨11, 75, 2079⟩, 217447090784815043, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_75_flag endpoint_11_75_sources 10 217447090784815043 217447090784815043 rfl endpoint_11_75_base endpoint_11_75_p10) (by decide)⟩
private def endpoint_11_76_flag : Flag := ⟨11, 76, 1980⟩
private def endpoint_11_76_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_11_76_base : receiptBase endpoint_11_76_flag endpoint_11_76_sources = some 209678047186930963 := by decide +kernel
private theorem endpoint_11_76_w0 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 2 209678047186930963 = some 209678047186930963 := by decide +kernel
private theorem endpoint_11_76_w2 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 2 2 209678047186930963 = some 209678047186930963 := by decide +kernel
private theorem endpoint_11_76_p4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 4 209678047186930963 = some 209678047186930963 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 2 2 209678047186930963 209678047186930963 209678047186930963 endpoint_11_76_w0 endpoint_11_76_w2
private theorem endpoint_11_76_w4 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 4 2 209678047186930963 = some 209678047186930963 := by decide +kernel
private theorem endpoint_11_76_p6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 6 209678047186930963 = some 209678047186930963 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 4 2 209678047186930963 209678047186930963 209678047186930963 endpoint_11_76_p4 endpoint_11_76_w4
private theorem endpoint_11_76_w6 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 6 2 209678047186930963 = some 209678047186930963 := by decide +kernel
private theorem endpoint_11_76_p8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 8 209678047186930963 = some 209678047186930963 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 6 2 209678047186930963 209678047186930963 209678047186930963 endpoint_11_76_p6 endpoint_11_76_w6
private theorem endpoint_11_76_w8 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 8 2 209678047186930963 = some 209678047186930963 := by decide +kernel
private theorem endpoint_11_76_p10 : receiptWindow endpoint_11_76_flag endpoint_11_76_sources 0 10 209678047186930963 = some 209678047186930963 :=
  join_receipt_window endpoint_11_76_flag endpoint_11_76_sources 0 8 2 209678047186930963 209678047186930963 209678047186930963 endpoint_11_76_p8 endpoint_11_76_w8
def endpoint_11_76 : CertifiedEndpoint :=
  ⟨⟨11, 76, 1980⟩, 209678047186930963, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_11_76_flag endpoint_11_76_sources 10 209678047186930963 209678047186930963 rfl endpoint_11_76_base endpoint_11_76_p10) (by decide)⟩
private def endpoint_11_77_flag : Flag := ⟨11, 77, 1877⟩
private def endpoint_11_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_77_base : receiptBase endpoint_11_77_flag endpoint_11_77_sources = some 202946963864905020 := by decide +kernel
private theorem endpoint_11_77_w0 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 2 202946963864905020 = some 202946963864905020 := by decide +kernel
private theorem endpoint_11_77_w2 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 2 2 202946963864905020 = some 202946963864905020 := by decide +kernel
private theorem endpoint_11_77_p4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 4 202946963864905020 = some 202946963864905020 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 2 2 202946963864905020 202946963864905020 202946963864905020 endpoint_11_77_w0 endpoint_11_77_w2
private theorem endpoint_11_77_w4 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 4 2 202946963864905020 = some 202946963864905020 := by decide +kernel
private theorem endpoint_11_77_p6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 6 202946963864905020 = some 202946963864905020 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 4 2 202946963864905020 202946963864905020 202946963864905020 endpoint_11_77_p4 endpoint_11_77_w4
private theorem endpoint_11_77_w6 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 6 2 202946963864905020 = some 202946963864905020 := by decide +kernel
private theorem endpoint_11_77_p8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 8 202946963864905020 = some 202946963864905020 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 6 2 202946963864905020 202946963864905020 202946963864905020 endpoint_11_77_p6 endpoint_11_77_w6
private theorem endpoint_11_77_w8 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 8 2 202946963864905020 = some 202946963864905020 := by decide +kernel
private theorem endpoint_11_77_p10 : receiptWindow endpoint_11_77_flag endpoint_11_77_sources 0 10 202946963864905020 = some 202946963864905020 :=
  join_receipt_window endpoint_11_77_flag endpoint_11_77_sources 0 8 2 202946963864905020 202946963864905020 202946963864905020 endpoint_11_77_p8 endpoint_11_77_w8
def endpoint_11_77 : CertifiedEndpoint :=
  ⟨⟨11, 77, 1877⟩, 202946963864905020, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_77_flag endpoint_11_77_sources 10 202946963864905020 202946963864905020 rfl endpoint_11_77_base endpoint_11_77_p10) (by decide)⟩
private def endpoint_11_78_flag : Flag := ⟨11, 78, 1771⟩
private def endpoint_11_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_78_base : receiptBase endpoint_11_78_flag endpoint_11_78_sources = some 193811991820146846 := by decide +kernel
private theorem endpoint_11_78_w0 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 2 193811991820146846 = some 193811991820146846 := by decide +kernel
private theorem endpoint_11_78_w2 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 2 2 193811991820146846 = some 193811991820146846 := by decide +kernel
private theorem endpoint_11_78_p4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 4 193811991820146846 = some 193811991820146846 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 2 2 193811991820146846 193811991820146846 193811991820146846 endpoint_11_78_w0 endpoint_11_78_w2
private theorem endpoint_11_78_w4 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 4 2 193811991820146846 = some 193811991820146846 := by decide +kernel
private theorem endpoint_11_78_p6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 6 193811991820146846 = some 193811991820146846 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 4 2 193811991820146846 193811991820146846 193811991820146846 endpoint_11_78_p4 endpoint_11_78_w4
private theorem endpoint_11_78_w6 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 6 2 193811991820146846 = some 193811991820146846 := by decide +kernel
private theorem endpoint_11_78_p8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 8 193811991820146846 = some 193811991820146846 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 6 2 193811991820146846 193811991820146846 193811991820146846 endpoint_11_78_p6 endpoint_11_78_w6
private theorem endpoint_11_78_w8 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 8 2 193811991820146846 = some 193811991820146846 := by decide +kernel
private theorem endpoint_11_78_p10 : receiptWindow endpoint_11_78_flag endpoint_11_78_sources 0 10 193811991820146846 = some 193811991820146846 :=
  join_receipt_window endpoint_11_78_flag endpoint_11_78_sources 0 8 2 193811991820146846 193811991820146846 193811991820146846 endpoint_11_78_p8 endpoint_11_78_w8
def endpoint_11_78 : CertifiedEndpoint :=
  ⟨⟨11, 78, 1771⟩, 193811991820146846, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_78_flag endpoint_11_78_sources 10 193811991820146846 193811991820146846 rfl endpoint_11_78_base endpoint_11_78_p10) (by decide)⟩
private def endpoint_11_79_flag : Flag := ⟨11, 79, 1663⟩
private def endpoint_11_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_11_79_base : receiptBase endpoint_11_79_flag endpoint_11_79_sources = some 184191513598429338 := by decide +kernel
private theorem endpoint_11_79_w0 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 2 184191513598429338 = some 184191513598429338 := by decide +kernel
private theorem endpoint_11_79_w2 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 2 2 184191513598429338 = some 184191513598429338 := by decide +kernel
private theorem endpoint_11_79_p4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 4 184191513598429338 = some 184191513598429338 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 2 2 184191513598429338 184191513598429338 184191513598429338 endpoint_11_79_w0 endpoint_11_79_w2
private theorem endpoint_11_79_w4 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 4 2 184191513598429338 = some 184191513598429338 := by decide +kernel
private theorem endpoint_11_79_p6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 6 184191513598429338 = some 184191513598429338 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 4 2 184191513598429338 184191513598429338 184191513598429338 endpoint_11_79_p4 endpoint_11_79_w4
private theorem endpoint_11_79_w6 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 6 2 184191513598429338 = some 184191513598429338 := by decide +kernel
private theorem endpoint_11_79_p8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 8 184191513598429338 = some 184191513598429338 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 6 2 184191513598429338 184191513598429338 184191513598429338 endpoint_11_79_p6 endpoint_11_79_w6
private theorem endpoint_11_79_w8 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 8 2 184191513598429338 = some 184191513598429338 := by decide +kernel
private theorem endpoint_11_79_p10 : receiptWindow endpoint_11_79_flag endpoint_11_79_sources 0 10 184191513598429338 = some 184191513598429338 :=
  join_receipt_window endpoint_11_79_flag endpoint_11_79_sources 0 8 2 184191513598429338 184191513598429338 184191513598429338 endpoint_11_79_p8 endpoint_11_79_w8
def endpoint_11_79 : CertifiedEndpoint :=
  ⟨⟨11, 79, 1663⟩, 184191513598429338, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_11_79_flag endpoint_11_79_sources 10 184191513598429338 184191513598429338 rfl endpoint_11_79_base endpoint_11_79_p10) (by decide)⟩
private def endpoint_11_80_flag : Flag := ⟨11, 80, 1551⟩
private def endpoint_11_80_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_80_base : receiptBase endpoint_11_80_flag endpoint_11_80_sources = some 176949844167998758 := by decide +kernel
private theorem endpoint_11_80_w0 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 2 176949844167998758 = some 176949844167998758 := by decide +kernel
private theorem endpoint_11_80_w2 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 2 2 176949844167998758 = some 176949844167998758 := by decide +kernel
private theorem endpoint_11_80_p4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 4 176949844167998758 = some 176949844167998758 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 2 2 176949844167998758 176949844167998758 176949844167998758 endpoint_11_80_w0 endpoint_11_80_w2
private theorem endpoint_11_80_w4 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 4 2 176949844167998758 = some 176949844167998758 := by decide +kernel
private theorem endpoint_11_80_p6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 6 176949844167998758 = some 176949844167998758 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 4 2 176949844167998758 176949844167998758 176949844167998758 endpoint_11_80_p4 endpoint_11_80_w4
private theorem endpoint_11_80_w6 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 6 2 176949844167998758 = some 176949844167998758 := by decide +kernel
private theorem endpoint_11_80_p8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 8 176949844167998758 = some 176949844167998758 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 6 2 176949844167998758 176949844167998758 176949844167998758 endpoint_11_80_p6 endpoint_11_80_w6
private theorem endpoint_11_80_w8 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 8 2 176949844167998758 = some 176949844167998758 := by decide +kernel
private theorem endpoint_11_80_p10 : receiptWindow endpoint_11_80_flag endpoint_11_80_sources 0 10 176949844167998758 = some 176949844167998758 :=
  join_receipt_window endpoint_11_80_flag endpoint_11_80_sources 0 8 2 176949844167998758 176949844167998758 176949844167998758 endpoint_11_80_p8 endpoint_11_80_w8
def endpoint_11_80 : CertifiedEndpoint :=
  ⟨⟨11, 80, 1551⟩, 176949844167998758, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_80_flag endpoint_11_80_sources 10 176949844167998758 176949844167998758 rfl endpoint_11_80_base endpoint_11_80_p10) (by decide)⟩
private def endpoint_11_81_flag : Flag := ⟨11, 81, 1436⟩
private def endpoint_11_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_11_81_base : receiptBase endpoint_11_81_flag endpoint_11_81_sources = some 165729495730209634 := by decide +kernel
private theorem endpoint_11_81_w0 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 2 165729495730209634 = some 165729495730209634 := by decide +kernel
private theorem endpoint_11_81_w2 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 2 2 165729495730209634 = some 165729495730209634 := by decide +kernel
private theorem endpoint_11_81_p4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 4 165729495730209634 = some 165729495730209634 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 2 2 165729495730209634 165729495730209634 165729495730209634 endpoint_11_81_w0 endpoint_11_81_w2
private theorem endpoint_11_81_w4 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 4 2 165729495730209634 = some 165729495730209634 := by decide +kernel
private theorem endpoint_11_81_p6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 6 165729495730209634 = some 165729495730209634 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 4 2 165729495730209634 165729495730209634 165729495730209634 endpoint_11_81_p4 endpoint_11_81_w4
private theorem endpoint_11_81_w6 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 6 2 165729495730209634 = some 165729495730209634 := by decide +kernel
private theorem endpoint_11_81_p8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 8 165729495730209634 = some 165729495730209634 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 6 2 165729495730209634 165729495730209634 165729495730209634 endpoint_11_81_p6 endpoint_11_81_w6
private theorem endpoint_11_81_w8 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 8 2 165729495730209634 = some 165729495730209634 := by decide +kernel
private theorem endpoint_11_81_p10 : receiptWindow endpoint_11_81_flag endpoint_11_81_sources 0 10 165729495730209634 = some 165729495730209634 :=
  join_receipt_window endpoint_11_81_flag endpoint_11_81_sources 0 8 2 165729495730209634 165729495730209634 165729495730209634 endpoint_11_81_p8 endpoint_11_81_w8
def endpoint_11_81 : CertifiedEndpoint :=
  ⟨⟨11, 81, 1436⟩, 165729495730209634, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_11_81_flag endpoint_11_81_sources 10 165729495730209634 165729495730209634 rfl endpoint_11_81_base endpoint_11_81_p10) (by decide)⟩
def endpoint_11_82 : CertifiedEndpoint :=
  ⟨⟨11, 82, 1317⟩, 262645040469504777, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_83 : CertifiedEndpoint :=
  ⟨⟨11, 83, 1196⟩, 240704153298525683, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_84 : CertifiedEndpoint :=
  ⟨⟨11, 84, 1072⟩, 217468429795842208, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_85 : CertifiedEndpoint :=
  ⟨⟨11, 85, 944⟩, 192698986453293007, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_86 : CertifiedEndpoint :=
  ⟨⟨11, 86, 813⟩, 166580417031882585, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_87 : CertifiedEndpoint :=
  ⟨⟨11, 87, 679⟩, 139088291145390364, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_88 : CertifiedEndpoint :=
  ⟨⟨11, 88, 542⟩, 110198178407595766, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_89 : CertifiedEndpoint :=
  ⟨⟨11, 89, 402⟩, 79885648432278213, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_90 : CertifiedEndpoint :=
  ⟨⟨11, 90, 259⟩, 48126270833217127, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_91 : CertifiedEndpoint :=
  ⟨⟨11, 91, 112⟩, 14664875178104111, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_12 : CertifiedEndpoint :=
  ⟨⟨12, 12, 4621⟩, 93892562659997901, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_13 : CertifiedEndpoint :=
  ⟨⟨12, 13, 4599⟩, 97895272294426354, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_14 : CertifiedEndpoint :=
  ⟨⟨12, 14, 4576⟩, 101832971631570388, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_15 : CertifiedEndpoint :=
  ⟨⟨12, 15, 4553⟩, 114809362197168386, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_16 : CertifiedEndpoint :=
  ⟨⟨12, 16, 4530⟩, 127646059753472966, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_17 : CertifiedEndpoint :=
  ⟨⟨12, 17, 4506⟩, 140311847664280319, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_18 : CertifiedEndpoint :=
  ⟨⟨12, 18, 4482⟩, 152831998182420066, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_19 : CertifiedEndpoint :=
  ⟨⟨12, 19, 4459⟩, 165243672327470204, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_20 : CertifiedEndpoint :=
  ⟨⟨12, 20, 4434⟩, 177435387040696742, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_21 : CertifiedEndpoint :=
  ⟨⟨12, 21, 4410⟩, 189518625380833671, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_22 : CertifiedEndpoint :=
  ⟨⟨12, 22, 4385⟩, 201410148733663715, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_23 : CertifiedEndpoint :=
  ⟨⟨12, 23, 4360⟩, 213150090310451965, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_24 : CertifiedEndpoint :=
  ⟨⟨12, 24, 4335⟩, 224738450111198421, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_25 : CertifiedEndpoint :=
  ⟨⟨12, 25, 4309⟩, 236120233966202522, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_26 : CertifiedEndpoint :=
  ⟨⟨12, 26, 4283⟩, 247344491661790641, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_27 : CertifiedEndpoint :=
  ⟨⟨12, 27, 4257⟩, 258411223197962778, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_12_28_flag : Flag := ⟨12, 28, 4230⟩
private def endpoint_12_28_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_28_base : receiptBase endpoint_12_28_flag endpoint_12_28_sources = some 185199753627964807 := by decide +kernel
private theorem endpoint_12_28_w0 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 2 185199753627964807 = some 185199753627964807 := by decide +kernel
private theorem endpoint_12_28_w2 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 2 2 185199753627964807 = some 185199753627964807 := by decide +kernel
private theorem endpoint_12_28_p4 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 4 185199753627964807 = some 185199753627964807 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 2 2 185199753627964807 185199753627964807 185199753627964807 endpoint_12_28_w0 endpoint_12_28_w2
private theorem endpoint_12_28_w4 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 4 2 185199753627964807 = some 185199753627964807 := by decide +kernel
private theorem endpoint_12_28_p6 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 6 185199753627964807 = some 185199753627964807 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 4 2 185199753627964807 185199753627964807 185199753627964807 endpoint_12_28_p4 endpoint_12_28_w4
private theorem endpoint_12_28_w6 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 6 2 185199753627964807 = some 185199753627964807 := by decide +kernel
private theorem endpoint_12_28_p8 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 8 185199753627964807 = some 185199753627964807 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 6 2 185199753627964807 185199753627964807 185199753627964807 endpoint_12_28_p6 endpoint_12_28_w6
private theorem endpoint_12_28_w8 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 8 2 185199753627964807 = some 185199753627964807 := by decide +kernel
private theorem endpoint_12_28_p10 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 10 185199753627964807 = some 185199753627964807 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 8 2 185199753627964807 185199753627964807 185199753627964807 endpoint_12_28_p8 endpoint_12_28_w8
private theorem endpoint_12_28_w10 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 10 1 185199753627964807 = some 185199753627964807 := by decide +kernel
private theorem endpoint_12_28_p11 : receiptWindow endpoint_12_28_flag endpoint_12_28_sources 0 11 185199753627964807 = some 185199753627964807 :=
  join_receipt_window endpoint_12_28_flag endpoint_12_28_sources 0 10 1 185199753627964807 185199753627964807 185199753627964807 endpoint_12_28_p10 endpoint_12_28_w10
def endpoint_12_28 : CertifiedEndpoint :=
  ⟨⟨12, 28, 4230⟩, 185199753627964807, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_28_flag endpoint_12_28_sources 11 185199753627964807 185199753627964807 rfl endpoint_12_28_base endpoint_12_28_p11) (by decide)⟩
private def endpoint_12_29_flag : Flag := ⟨12, 29, 4204⟩
private def endpoint_12_29_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_29_base : receiptBase endpoint_12_29_flag endpoint_12_29_sources = some 189312926504983968 := by decide +kernel
private theorem endpoint_12_29_w0 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 2 189312926504983968 = some 189312926504983968 := by decide +kernel
private theorem endpoint_12_29_w2 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 2 2 189312926504983968 = some 189312926504983968 := by decide +kernel
private theorem endpoint_12_29_p4 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 4 189312926504983968 = some 189312926504983968 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 2 2 189312926504983968 189312926504983968 189312926504983968 endpoint_12_29_w0 endpoint_12_29_w2
private theorem endpoint_12_29_w4 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 4 2 189312926504983968 = some 189312926504983968 := by decide +kernel
private theorem endpoint_12_29_p6 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 6 189312926504983968 = some 189312926504983968 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 4 2 189312926504983968 189312926504983968 189312926504983968 endpoint_12_29_p4 endpoint_12_29_w4
private theorem endpoint_12_29_w6 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 6 2 189312926504983968 = some 189312926504983968 := by decide +kernel
private theorem endpoint_12_29_p8 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 8 189312926504983968 = some 189312926504983968 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 6 2 189312926504983968 189312926504983968 189312926504983968 endpoint_12_29_p6 endpoint_12_29_w6
private theorem endpoint_12_29_w8 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 8 2 189312926504983968 = some 189312926504983968 := by decide +kernel
private theorem endpoint_12_29_p10 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 10 189312926504983968 = some 189312926504983968 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 8 2 189312926504983968 189312926504983968 189312926504983968 endpoint_12_29_p8 endpoint_12_29_w8
private theorem endpoint_12_29_w10 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 10 1 189312926504983968 = some 189312926504983968 := by decide +kernel
private theorem endpoint_12_29_p11 : receiptWindow endpoint_12_29_flag endpoint_12_29_sources 0 11 189312926504983968 = some 189312926504983968 :=
  join_receipt_window endpoint_12_29_flag endpoint_12_29_sources 0 10 1 189312926504983968 189312926504983968 189312926504983968 endpoint_12_29_p10 endpoint_12_29_w10
def endpoint_12_29 : CertifiedEndpoint :=
  ⟨⟨12, 29, 4204⟩, 189312926504983968, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_29_flag endpoint_12_29_sources 11 189312926504983968 189312926504983968 rfl endpoint_12_29_base endpoint_12_29_p11) (by decide)⟩
private def endpoint_12_30_flag : Flag := ⟨12, 30, 4176⟩
private def endpoint_12_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_30_base : receiptBase endpoint_12_30_flag endpoint_12_30_sources = some 193270052537224327 := by decide +kernel
private theorem endpoint_12_30_w0 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 2 193270052537224327 = some 193270052537224327 := by decide +kernel
private theorem endpoint_12_30_w2 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 2 2 193270052537224327 = some 193270052537224327 := by decide +kernel
private theorem endpoint_12_30_p4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 4 193270052537224327 = some 193270052537224327 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 2 2 193270052537224327 193270052537224327 193270052537224327 endpoint_12_30_w0 endpoint_12_30_w2
private theorem endpoint_12_30_w4 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 4 2 193270052537224327 = some 193270052537224327 := by decide +kernel
private theorem endpoint_12_30_p6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 6 193270052537224327 = some 193270052537224327 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 4 2 193270052537224327 193270052537224327 193270052537224327 endpoint_12_30_p4 endpoint_12_30_w4
private theorem endpoint_12_30_w6 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 6 2 193270052537224327 = some 193270052537224327 := by decide +kernel
private theorem endpoint_12_30_p8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 8 193270052537224327 = some 193270052537224327 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 6 2 193270052537224327 193270052537224327 193270052537224327 endpoint_12_30_p6 endpoint_12_30_w6
private theorem endpoint_12_30_w8 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 8 2 193270052537224327 = some 193270052537224327 := by decide +kernel
private theorem endpoint_12_30_p10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 10 193270052537224327 = some 193270052537224327 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 8 2 193270052537224327 193270052537224327 193270052537224327 endpoint_12_30_p8 endpoint_12_30_w8
private theorem endpoint_12_30_w10 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 10 1 193270052537224327 = some 193270052537224327 := by decide +kernel
private theorem endpoint_12_30_p11 : receiptWindow endpoint_12_30_flag endpoint_12_30_sources 0 11 193270052537224327 = some 193270052537224327 :=
  join_receipt_window endpoint_12_30_flag endpoint_12_30_sources 0 10 1 193270052537224327 193270052537224327 193270052537224327 endpoint_12_30_p10 endpoint_12_30_w10
def endpoint_12_30 : CertifiedEndpoint :=
  ⟨⟨12, 30, 4176⟩, 193270052537224327, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_30_flag endpoint_12_30_sources 11 193270052537224327 193270052537224327 rfl endpoint_12_30_base endpoint_12_30_p11) (by decide)⟩
private def endpoint_12_31_flag : Flag := ⟨12, 31, 4149⟩
private def endpoint_12_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_31_base : receiptBase endpoint_12_31_flag endpoint_12_31_sources = some 197204449215614240 := by decide +kernel
private theorem endpoint_12_31_w0 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 2 197204449215614240 = some 197204449215614240 := by decide +kernel
private theorem endpoint_12_31_w2 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 2 2 197204449215614240 = some 197204449215614240 := by decide +kernel
private theorem endpoint_12_31_p4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 4 197204449215614240 = some 197204449215614240 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 2 2 197204449215614240 197204449215614240 197204449215614240 endpoint_12_31_w0 endpoint_12_31_w2
private theorem endpoint_12_31_w4 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 4 2 197204449215614240 = some 197204449215614240 := by decide +kernel
private theorem endpoint_12_31_p6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 6 197204449215614240 = some 197204449215614240 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 4 2 197204449215614240 197204449215614240 197204449215614240 endpoint_12_31_p4 endpoint_12_31_w4
private theorem endpoint_12_31_w6 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 6 2 197204449215614240 = some 197204449215614240 := by decide +kernel
private theorem endpoint_12_31_p8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 8 197204449215614240 = some 197204449215614240 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 6 2 197204449215614240 197204449215614240 197204449215614240 endpoint_12_31_p6 endpoint_12_31_w6
private theorem endpoint_12_31_w8 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 8 2 197204449215614240 = some 197204449215614240 := by decide +kernel
private theorem endpoint_12_31_p10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 10 197204449215614240 = some 197204449215614240 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 8 2 197204449215614240 197204449215614240 197204449215614240 endpoint_12_31_p8 endpoint_12_31_w8
private theorem endpoint_12_31_w10 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 10 1 197204449215614240 = some 197204449215614240 := by decide +kernel
private theorem endpoint_12_31_p11 : receiptWindow endpoint_12_31_flag endpoint_12_31_sources 0 11 197204449215614240 = some 197204449215614240 :=
  join_receipt_window endpoint_12_31_flag endpoint_12_31_sources 0 10 1 197204449215614240 197204449215614240 197204449215614240 endpoint_12_31_p10 endpoint_12_31_w10
def endpoint_12_31 : CertifiedEndpoint :=
  ⟨⟨12, 31, 4149⟩, 197204449215614240, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_31_flag endpoint_12_31_sources 11 197204449215614240 197204449215614240 rfl endpoint_12_31_base endpoint_12_31_p11) (by decide)⟩
private def endpoint_12_32_flag : Flag := ⟨12, 32, 4120⟩
private def endpoint_12_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_32_base : receiptBase endpoint_12_32_flag endpoint_12_32_sources = some 200975472065455728 := by decide +kernel
private theorem endpoint_12_32_w0 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 2 200975472065455728 = some 200975472065455728 := by decide +kernel
private theorem endpoint_12_32_w2 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 2 2 200975472065455728 = some 200975472065455728 := by decide +kernel
private theorem endpoint_12_32_p4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 4 200975472065455728 = some 200975472065455728 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 2 2 200975472065455728 200975472065455728 200975472065455728 endpoint_12_32_w0 endpoint_12_32_w2
private theorem endpoint_12_32_w4 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 4 2 200975472065455728 = some 200975472065455728 := by decide +kernel
private theorem endpoint_12_32_p6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 6 200975472065455728 = some 200975472065455728 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 4 2 200975472065455728 200975472065455728 200975472065455728 endpoint_12_32_p4 endpoint_12_32_w4
private theorem endpoint_12_32_w6 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 6 2 200975472065455728 = some 200975472065455728 := by decide +kernel
private theorem endpoint_12_32_p8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 8 200975472065455728 = some 200975472065455728 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 6 2 200975472065455728 200975472065455728 200975472065455728 endpoint_12_32_p6 endpoint_12_32_w6
private theorem endpoint_12_32_w8 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 8 2 200975472065455728 = some 200975472065455728 := by decide +kernel
private theorem endpoint_12_32_p10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 10 200975472065455728 = some 200975472065455728 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 8 2 200975472065455728 200975472065455728 200975472065455728 endpoint_12_32_p8 endpoint_12_32_w8
private theorem endpoint_12_32_w10 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 10 1 200975472065455728 = some 200975472065455728 := by decide +kernel
private theorem endpoint_12_32_p11 : receiptWindow endpoint_12_32_flag endpoint_12_32_sources 0 11 200975472065455728 = some 200975472065455728 :=
  join_receipt_window endpoint_12_32_flag endpoint_12_32_sources 0 10 1 200975472065455728 200975472065455728 200975472065455728 endpoint_12_32_p10 endpoint_12_32_w10
def endpoint_12_32 : CertifiedEndpoint :=
  ⟨⟨12, 32, 4120⟩, 200975472065455728, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_32_flag endpoint_12_32_sources 11 200975472065455728 200975472065455728 rfl endpoint_12_32_base endpoint_12_32_p11) (by decide)⟩
private def endpoint_12_33_flag : Flag := ⟨12, 33, 4092⟩
private def endpoint_12_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_33_base : receiptBase endpoint_12_33_flag endpoint_12_33_sources = some 204723765561446770 := by decide +kernel
private theorem endpoint_12_33_w0 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 2 204723765561446770 = some 204723765561446770 := by decide +kernel
private theorem endpoint_12_33_w2 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 2 2 204723765561446770 = some 204723765561446770 := by decide +kernel
private theorem endpoint_12_33_p4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 4 204723765561446770 = some 204723765561446770 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 2 2 204723765561446770 204723765561446770 204723765561446770 endpoint_12_33_w0 endpoint_12_33_w2
private theorem endpoint_12_33_w4 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 4 2 204723765561446770 = some 204723765561446770 := by decide +kernel
private theorem endpoint_12_33_p6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 6 204723765561446770 = some 204723765561446770 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 4 2 204723765561446770 204723765561446770 204723765561446770 endpoint_12_33_p4 endpoint_12_33_w4
private theorem endpoint_12_33_w6 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 6 2 204723765561446770 = some 204723765561446770 := by decide +kernel
private theorem endpoint_12_33_p8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 8 204723765561446770 = some 204723765561446770 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 6 2 204723765561446770 204723765561446770 204723765561446770 endpoint_12_33_p6 endpoint_12_33_w6
private theorem endpoint_12_33_w8 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 8 2 204723765561446770 = some 204723765561446770 := by decide +kernel
private theorem endpoint_12_33_p10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 10 204723765561446770 = some 204723765561446770 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 8 2 204723765561446770 204723765561446770 204723765561446770 endpoint_12_33_p8 endpoint_12_33_w8
private theorem endpoint_12_33_w10 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 10 1 204723765561446770 = some 204723765561446770 := by decide +kernel
private theorem endpoint_12_33_p11 : receiptWindow endpoint_12_33_flag endpoint_12_33_sources 0 11 204723765561446770 = some 204723765561446770 :=
  join_receipt_window endpoint_12_33_flag endpoint_12_33_sources 0 10 1 204723765561446770 204723765561446770 204723765561446770 endpoint_12_33_p10 endpoint_12_33_w10
def endpoint_12_33 : CertifiedEndpoint :=
  ⟨⟨12, 33, 4092⟩, 204723765561446770, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_33_flag endpoint_12_33_sources 11 204723765561446770 204723765561446770 rfl endpoint_12_33_base endpoint_12_33_p11) (by decide)⟩
private def endpoint_12_34_flag : Flag := ⟨12, 34, 4063⟩
private def endpoint_12_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_34_base : receiptBase endpoint_12_34_flag endpoint_12_34_sources = some 208351903228570568 := by decide +kernel
private theorem endpoint_12_34_w0 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 2 208351903228570568 = some 208351903228570568 := by decide +kernel
private theorem endpoint_12_34_w2 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 2 2 208351903228570568 = some 208351903228570568 := by decide +kernel
private theorem endpoint_12_34_p4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 4 208351903228570568 = some 208351903228570568 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 2 2 208351903228570568 208351903228570568 208351903228570568 endpoint_12_34_w0 endpoint_12_34_w2
private theorem endpoint_12_34_w4 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 4 2 208351903228570568 = some 208351903228570568 := by decide +kernel
private theorem endpoint_12_34_p6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 6 208351903228570568 = some 208351903228570568 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 4 2 208351903228570568 208351903228570568 208351903228570568 endpoint_12_34_p4 endpoint_12_34_w4
private theorem endpoint_12_34_w6 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 6 2 208351903228570568 = some 208351903228570568 := by decide +kernel
private theorem endpoint_12_34_p8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 8 208351903228570568 = some 208351903228570568 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 6 2 208351903228570568 208351903228570568 208351903228570568 endpoint_12_34_p6 endpoint_12_34_w6
private theorem endpoint_12_34_w8 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 8 2 208351903228570568 = some 208351903228570568 := by decide +kernel
private theorem endpoint_12_34_p10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 10 208351903228570568 = some 208351903228570568 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 8 2 208351903228570568 208351903228570568 208351903228570568 endpoint_12_34_p8 endpoint_12_34_w8
private theorem endpoint_12_34_w10 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 10 1 208351903228570568 = some 208351903228570568 := by decide +kernel
private theorem endpoint_12_34_p11 : receiptWindow endpoint_12_34_flag endpoint_12_34_sources 0 11 208351903228570568 = some 208351903228570568 :=
  join_receipt_window endpoint_12_34_flag endpoint_12_34_sources 0 10 1 208351903228570568 208351903228570568 208351903228570568 endpoint_12_34_p10 endpoint_12_34_w10
def endpoint_12_34 : CertifiedEndpoint :=
  ⟨⟨12, 34, 4063⟩, 208351903228570568, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_34_flag endpoint_12_34_sources 11 208351903228570568 208351903228570568 rfl endpoint_12_34_base endpoint_12_34_p11) (by decide)⟩
private def endpoint_12_35_flag : Flag := ⟨12, 35, 4034⟩
private def endpoint_12_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_35_base : receiptBase endpoint_12_35_flag endpoint_12_35_sources = some 211907987722354719 := by decide +kernel
private theorem endpoint_12_35_w0 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 2 211907987722354719 = some 211907987722354719 := by decide +kernel
private theorem endpoint_12_35_w2 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 2 2 211907987722354719 = some 211907987722354719 := by decide +kernel
private theorem endpoint_12_35_p4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 4 211907987722354719 = some 211907987722354719 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 2 2 211907987722354719 211907987722354719 211907987722354719 endpoint_12_35_w0 endpoint_12_35_w2
private theorem endpoint_12_35_w4 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 4 2 211907987722354719 = some 211907987722354719 := by decide +kernel
private theorem endpoint_12_35_p6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 6 211907987722354719 = some 211907987722354719 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 4 2 211907987722354719 211907987722354719 211907987722354719 endpoint_12_35_p4 endpoint_12_35_w4
private theorem endpoint_12_35_w6 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 6 2 211907987722354719 = some 211907987722354719 := by decide +kernel
private theorem endpoint_12_35_p8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 8 211907987722354719 = some 211907987722354719 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 6 2 211907987722354719 211907987722354719 211907987722354719 endpoint_12_35_p6 endpoint_12_35_w6
private theorem endpoint_12_35_w8 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 8 2 211907987722354719 = some 211907987722354719 := by decide +kernel
private theorem endpoint_12_35_p10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 10 211907987722354719 = some 211907987722354719 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 8 2 211907987722354719 211907987722354719 211907987722354719 endpoint_12_35_p8 endpoint_12_35_w8
private theorem endpoint_12_35_w10 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 10 1 211907987722354719 = some 211907987722354719 := by decide +kernel
private theorem endpoint_12_35_p11 : receiptWindow endpoint_12_35_flag endpoint_12_35_sources 0 11 211907987722354719 = some 211907987722354719 :=
  join_receipt_window endpoint_12_35_flag endpoint_12_35_sources 0 10 1 211907987722354719 211907987722354719 211907987722354719 endpoint_12_35_p10 endpoint_12_35_w10
def endpoint_12_35 : CertifiedEndpoint :=
  ⟨⟨12, 35, 4034⟩, 211907987722354719, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_35_flag endpoint_12_35_sources 11 211907987722354719 211907987722354719 rfl endpoint_12_35_base endpoint_12_35_p11) (by decide)⟩
private def endpoint_12_36_flag : Flag := ⟨12, 36, 4004⟩
private def endpoint_12_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_36_base : receiptBase endpoint_12_36_flag endpoint_12_36_sources = some 215339031731425211 := by decide +kernel
private theorem endpoint_12_36_w0 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 2 215339031731425211 = some 215339031731425211 := by decide +kernel
private theorem endpoint_12_36_w2 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 2 2 215339031731425211 = some 215339031731425211 := by decide +kernel
private theorem endpoint_12_36_p4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 4 215339031731425211 = some 215339031731425211 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 2 2 215339031731425211 215339031731425211 215339031731425211 endpoint_12_36_w0 endpoint_12_36_w2
private theorem endpoint_12_36_w4 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 4 2 215339031731425211 = some 215339031731425211 := by decide +kernel
private theorem endpoint_12_36_p6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 6 215339031731425211 = some 215339031731425211 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 4 2 215339031731425211 215339031731425211 215339031731425211 endpoint_12_36_p4 endpoint_12_36_w4
private theorem endpoint_12_36_w6 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 6 2 215339031731425211 = some 215339031731425211 := by decide +kernel
private theorem endpoint_12_36_p8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 8 215339031731425211 = some 215339031731425211 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 6 2 215339031731425211 215339031731425211 215339031731425211 endpoint_12_36_p6 endpoint_12_36_w6
private theorem endpoint_12_36_w8 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 8 2 215339031731425211 = some 215339031731425211 := by decide +kernel
private theorem endpoint_12_36_p10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 10 215339031731425211 = some 215339031731425211 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 8 2 215339031731425211 215339031731425211 215339031731425211 endpoint_12_36_p8 endpoint_12_36_w8
private theorem endpoint_12_36_w10 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 10 1 215339031731425211 = some 215339031731425211 := by decide +kernel
private theorem endpoint_12_36_p11 : receiptWindow endpoint_12_36_flag endpoint_12_36_sources 0 11 215339031731425211 = some 215339031731425211 :=
  join_receipt_window endpoint_12_36_flag endpoint_12_36_sources 0 10 1 215339031731425211 215339031731425211 215339031731425211 endpoint_12_36_p10 endpoint_12_36_w10
def endpoint_12_36 : CertifiedEndpoint :=
  ⟨⟨12, 36, 4004⟩, 215339031731425211, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_36_flag endpoint_12_36_sources 11 215339031731425211 215339031731425211 rfl endpoint_12_36_base endpoint_12_36_p11) (by decide)⟩
private def endpoint_12_37_flag : Flag := ⟨12, 37, 3974⟩
private def endpoint_12_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_37_base : receiptBase endpoint_12_37_flag endpoint_12_37_sources = some 218695580239232848 := by decide +kernel
private theorem endpoint_12_37_w0 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 2 218695580239232848 = some 218695580239232848 := by decide +kernel
private theorem endpoint_12_37_w2 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 2 2 218695580239232848 = some 218695580239232848 := by decide +kernel
private theorem endpoint_12_37_p4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 4 218695580239232848 = some 218695580239232848 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 2 2 218695580239232848 218695580239232848 218695580239232848 endpoint_12_37_w0 endpoint_12_37_w2
private theorem endpoint_12_37_w4 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 4 2 218695580239232848 = some 218695580239232848 := by decide +kernel
private theorem endpoint_12_37_p6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 6 218695580239232848 = some 218695580239232848 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 4 2 218695580239232848 218695580239232848 218695580239232848 endpoint_12_37_p4 endpoint_12_37_w4
private theorem endpoint_12_37_w6 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 6 2 218695580239232848 = some 218695580239232848 := by decide +kernel
private theorem endpoint_12_37_p8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 8 218695580239232848 = some 218695580239232848 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 6 2 218695580239232848 218695580239232848 218695580239232848 endpoint_12_37_p6 endpoint_12_37_w6
private theorem endpoint_12_37_w8 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 8 2 218695580239232848 = some 218695580239232848 := by decide +kernel
private theorem endpoint_12_37_p10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 10 218695580239232848 = some 218695580239232848 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 8 2 218695580239232848 218695580239232848 218695580239232848 endpoint_12_37_p8 endpoint_12_37_w8
private theorem endpoint_12_37_w10 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 10 1 218695580239232848 = some 218695580239232848 := by decide +kernel
private theorem endpoint_12_37_p11 : receiptWindow endpoint_12_37_flag endpoint_12_37_sources 0 11 218695580239232848 = some 218695580239232848 :=
  join_receipt_window endpoint_12_37_flag endpoint_12_37_sources 0 10 1 218695580239232848 218695580239232848 218695580239232848 endpoint_12_37_p10 endpoint_12_37_w10
def endpoint_12_37 : CertifiedEndpoint :=
  ⟨⟨12, 37, 3974⟩, 218695580239232848, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_37_flag endpoint_12_37_sources 11 218695580239232848 218695580239232848 rfl endpoint_12_37_base endpoint_12_37_p11) (by decide)⟩
private def endpoint_12_38_flag : Flag := ⟨12, 38, 3943⟩
private def endpoint_12_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_12_38_base : receiptBase endpoint_12_38_flag endpoint_12_38_sources = some 221922203606480410 := by decide +kernel
private theorem endpoint_12_38_w0 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 2 221922203606480410 = some 221922203606480410 := by decide +kernel
private theorem endpoint_12_38_w2 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 2 2 221922203606480410 = some 221922203606480410 := by decide +kernel
private theorem endpoint_12_38_p4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 4 221922203606480410 = some 221922203606480410 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 2 2 221922203606480410 221922203606480410 221922203606480410 endpoint_12_38_w0 endpoint_12_38_w2
private theorem endpoint_12_38_w4 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 4 2 221922203606480410 = some 221922203606480410 := by decide +kernel
private theorem endpoint_12_38_p6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 6 221922203606480410 = some 221922203606480410 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 4 2 221922203606480410 221922203606480410 221922203606480410 endpoint_12_38_p4 endpoint_12_38_w4
private theorem endpoint_12_38_w6 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 6 2 221922203606480410 = some 221922203606480410 := by decide +kernel
private theorem endpoint_12_38_p8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 8 221922203606480410 = some 221922203606480410 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 6 2 221922203606480410 221922203606480410 221922203606480410 endpoint_12_38_p6 endpoint_12_38_w6
private theorem endpoint_12_38_w8 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 8 2 221922203606480410 = some 221922203606480410 := by decide +kernel
private theorem endpoint_12_38_p10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 10 221922203606480410 = some 221922203606480410 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 8 2 221922203606480410 221922203606480410 221922203606480410 endpoint_12_38_p8 endpoint_12_38_w8
private theorem endpoint_12_38_w10 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 10 1 221922203606480410 = some 221922203606480410 := by decide +kernel
private theorem endpoint_12_38_p11 : receiptWindow endpoint_12_38_flag endpoint_12_38_sources 0 11 221922203606480410 = some 221922203606480410 :=
  join_receipt_window endpoint_12_38_flag endpoint_12_38_sources 0 10 1 221922203606480410 221922203606480410 221922203606480410 endpoint_12_38_p10 endpoint_12_38_w10
def endpoint_12_38 : CertifiedEndpoint :=
  ⟨⟨12, 38, 3943⟩, 221922203606480410, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_12_38_flag endpoint_12_38_sources 11 221922203606480410 221922203606480410 rfl endpoint_12_38_base endpoint_12_38_p11) (by decide)⟩
private def endpoint_12_39_flag : Flag := ⟨12, 39, 3911⟩
private def endpoint_12_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_39_base : receiptBase endpoint_12_39_flag endpoint_12_39_sources = some 225938599237455632 := by decide +kernel
private theorem endpoint_12_39_w0 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 2 225938599237455632 = some 225938599237455632 := by decide +kernel
private theorem endpoint_12_39_w2 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 2 2 225938599237455632 = some 225938599237455632 := by decide +kernel
private theorem endpoint_12_39_p4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 4 225938599237455632 = some 225938599237455632 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 2 2 225938599237455632 225938599237455632 225938599237455632 endpoint_12_39_w0 endpoint_12_39_w2
private theorem endpoint_12_39_w4 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 4 2 225938599237455632 = some 225938599237455632 := by decide +kernel
private theorem endpoint_12_39_p6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 6 225938599237455632 = some 225938599237455632 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 4 2 225938599237455632 225938599237455632 225938599237455632 endpoint_12_39_p4 endpoint_12_39_w4
private theorem endpoint_12_39_w6 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 6 2 225938599237455632 = some 225938599237455632 := by decide +kernel
private theorem endpoint_12_39_p8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 8 225938599237455632 = some 225938599237455632 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 6 2 225938599237455632 225938599237455632 225938599237455632 endpoint_12_39_p6 endpoint_12_39_w6
private theorem endpoint_12_39_w8 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 8 2 225938599237455632 = some 225938599237455632 := by decide +kernel
private theorem endpoint_12_39_p10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 10 225938599237455632 = some 225938599237455632 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 8 2 225938599237455632 225938599237455632 225938599237455632 endpoint_12_39_p8 endpoint_12_39_w8
private theorem endpoint_12_39_w10 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 10 1 225938599237455632 = some 225938599237455632 := by decide +kernel
private theorem endpoint_12_39_p11 : receiptWindow endpoint_12_39_flag endpoint_12_39_sources 0 11 225938599237455632 = some 225938599237455632 :=
  join_receipt_window endpoint_12_39_flag endpoint_12_39_sources 0 10 1 225938599237455632 225938599237455632 225938599237455632 endpoint_12_39_p10 endpoint_12_39_w10
def endpoint_12_39 : CertifiedEndpoint :=
  ⟨⟨12, 39, 3911⟩, 225938599237455632, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_39_flag endpoint_12_39_sources 11 225938599237455632 225938599237455632 rfl endpoint_12_39_base endpoint_12_39_p11) (by decide)⟩
private def endpoint_12_40_flag : Flag := ⟨12, 40, 3880⟩
private def endpoint_12_40_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_40_base : receiptBase endpoint_12_40_flag endpoint_12_40_sources = some 228973712472263791 := by decide +kernel
private theorem endpoint_12_40_w0 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 2 228973712472263791 = some 228973712472263791 := by decide +kernel
private theorem endpoint_12_40_w2 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 2 2 228973712472263791 = some 228973712472263791 := by decide +kernel
private theorem endpoint_12_40_p4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 4 228973712472263791 = some 228973712472263791 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 2 2 228973712472263791 228973712472263791 228973712472263791 endpoint_12_40_w0 endpoint_12_40_w2
private theorem endpoint_12_40_w4 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 4 2 228973712472263791 = some 228973712472263791 := by decide +kernel
private theorem endpoint_12_40_p6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 6 228973712472263791 = some 228973712472263791 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 4 2 228973712472263791 228973712472263791 228973712472263791 endpoint_12_40_p4 endpoint_12_40_w4
private theorem endpoint_12_40_w6 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 6 2 228973712472263791 = some 228973712472263791 := by decide +kernel
private theorem endpoint_12_40_p8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 8 228973712472263791 = some 228973712472263791 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 6 2 228973712472263791 228973712472263791 228973712472263791 endpoint_12_40_p6 endpoint_12_40_w6
private theorem endpoint_12_40_w8 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 8 2 228973712472263791 = some 228973712472263791 := by decide +kernel
private theorem endpoint_12_40_p10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 10 228973712472263791 = some 228973712472263791 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 8 2 228973712472263791 228973712472263791 228973712472263791 endpoint_12_40_p8 endpoint_12_40_w8
private theorem endpoint_12_40_w10 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 10 1 228973712472263791 = some 228973712472263791 := by decide +kernel
private theorem endpoint_12_40_p11 : receiptWindow endpoint_12_40_flag endpoint_12_40_sources 0 11 228973712472263791 = some 228973712472263791 :=
  join_receipt_window endpoint_12_40_flag endpoint_12_40_sources 0 10 1 228973712472263791 228973712472263791 228973712472263791 endpoint_12_40_p10 endpoint_12_40_w10
def endpoint_12_40 : CertifiedEndpoint :=
  ⟨⟨12, 40, 3880⟩, 228973712472263791, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_40_flag endpoint_12_40_sources 11 228973712472263791 228973712472263791 rfl endpoint_12_40_base endpoint_12_40_p11) (by decide)⟩
private def endpoint_12_41_flag : Flag := ⟨12, 41, 3847⟩
private def endpoint_12_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_41_base : receiptBase endpoint_12_41_flag endpoint_12_41_sources = some 231813355305701199 := by decide +kernel
private theorem endpoint_12_41_w0 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 2 231813355305701199 = some 231813355305701199 := by decide +kernel
private theorem endpoint_12_41_w2 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 2 2 231813355305701199 = some 231813355305701199 := by decide +kernel
private theorem endpoint_12_41_p4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 4 231813355305701199 = some 231813355305701199 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 2 2 231813355305701199 231813355305701199 231813355305701199 endpoint_12_41_w0 endpoint_12_41_w2
private theorem endpoint_12_41_w4 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 4 2 231813355305701199 = some 231813355305701199 := by decide +kernel
private theorem endpoint_12_41_p6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 6 231813355305701199 = some 231813355305701199 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 4 2 231813355305701199 231813355305701199 231813355305701199 endpoint_12_41_p4 endpoint_12_41_w4
private theorem endpoint_12_41_w6 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 6 2 231813355305701199 = some 231813355305701199 := by decide +kernel
private theorem endpoint_12_41_p8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 8 231813355305701199 = some 231813355305701199 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 6 2 231813355305701199 231813355305701199 231813355305701199 endpoint_12_41_p6 endpoint_12_41_w6
private theorem endpoint_12_41_w8 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 8 2 231813355305701199 = some 231813355305701199 := by decide +kernel
private theorem endpoint_12_41_p10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 10 231813355305701199 = some 231813355305701199 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 8 2 231813355305701199 231813355305701199 231813355305701199 endpoint_12_41_p8 endpoint_12_41_w8
private theorem endpoint_12_41_w10 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 10 1 231813355305701199 = some 231813355305701199 := by decide +kernel
private theorem endpoint_12_41_p11 : receiptWindow endpoint_12_41_flag endpoint_12_41_sources 0 11 231813355305701199 = some 231813355305701199 :=
  join_receipt_window endpoint_12_41_flag endpoint_12_41_sources 0 10 1 231813355305701199 231813355305701199 231813355305701199 endpoint_12_41_p10 endpoint_12_41_w10
def endpoint_12_41 : CertifiedEndpoint :=
  ⟨⟨12, 41, 3847⟩, 231813355305701199, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_41_flag endpoint_12_41_sources 11 231813355305701199 231813355305701199 rfl endpoint_12_41_base endpoint_12_41_p11) (by decide)⟩
private def endpoint_12_42_flag : Flag := ⟨12, 42, 3814⟩
private def endpoint_12_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_42_base : receiptBase endpoint_12_42_flag endpoint_12_42_sources = some 234571481576360659 := by decide +kernel
private theorem endpoint_12_42_w0 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 2 234571481576360659 = some 234571481576360659 := by decide +kernel
private theorem endpoint_12_42_w2 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 2 2 234571481576360659 = some 234571481576360659 := by decide +kernel
private theorem endpoint_12_42_p4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 4 234571481576360659 = some 234571481576360659 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 2 2 234571481576360659 234571481576360659 234571481576360659 endpoint_12_42_w0 endpoint_12_42_w2
private theorem endpoint_12_42_w4 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 4 2 234571481576360659 = some 234571481576360659 := by decide +kernel
private theorem endpoint_12_42_p6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 6 234571481576360659 = some 234571481576360659 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 4 2 234571481576360659 234571481576360659 234571481576360659 endpoint_12_42_p4 endpoint_12_42_w4
private theorem endpoint_12_42_w6 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 6 2 234571481576360659 = some 234571481576360659 := by decide +kernel
private theorem endpoint_12_42_p8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 8 234571481576360659 = some 234571481576360659 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 6 2 234571481576360659 234571481576360659 234571481576360659 endpoint_12_42_p6 endpoint_12_42_w6
private theorem endpoint_12_42_w8 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 8 2 234571481576360659 = some 234571481576360659 := by decide +kernel
private theorem endpoint_12_42_p10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 10 234571481576360659 = some 234571481576360659 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 8 2 234571481576360659 234571481576360659 234571481576360659 endpoint_12_42_p8 endpoint_12_42_w8
private theorem endpoint_12_42_w10 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 10 1 234571481576360659 = some 234571481576360659 := by decide +kernel
private theorem endpoint_12_42_p11 : receiptWindow endpoint_12_42_flag endpoint_12_42_sources 0 11 234571481576360659 = some 234571481576360659 :=
  join_receipt_window endpoint_12_42_flag endpoint_12_42_sources 0 10 1 234571481576360659 234571481576360659 234571481576360659 endpoint_12_42_p10 endpoint_12_42_w10
def endpoint_12_42 : CertifiedEndpoint :=
  ⟨⟨12, 42, 3814⟩, 234571481576360659, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_42_flag endpoint_12_42_sources 11 234571481576360659 234571481576360659 rfl endpoint_12_42_base endpoint_12_42_p11) (by decide)⟩
private def endpoint_12_43_flag : Flag := ⟨12, 43, 3780⟩
private def endpoint_12_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_43_base : receiptBase endpoint_12_43_flag endpoint_12_43_sources = some 237186247704481414 := by decide +kernel
private theorem endpoint_12_43_w0 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 2 237186247704481414 = some 237186247704481414 := by decide +kernel
private theorem endpoint_12_43_w2 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 2 2 237186247704481414 = some 237186247704481414 := by decide +kernel
private theorem endpoint_12_43_p4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 4 237186247704481414 = some 237186247704481414 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 2 2 237186247704481414 237186247704481414 237186247704481414 endpoint_12_43_w0 endpoint_12_43_w2
private theorem endpoint_12_43_w4 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 4 2 237186247704481414 = some 237186247704481414 := by decide +kernel
private theorem endpoint_12_43_p6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 6 237186247704481414 = some 237186247704481414 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 4 2 237186247704481414 237186247704481414 237186247704481414 endpoint_12_43_p4 endpoint_12_43_w4
private theorem endpoint_12_43_w6 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 6 2 237186247704481414 = some 237186247704481414 := by decide +kernel
private theorem endpoint_12_43_p8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 8 237186247704481414 = some 237186247704481414 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 6 2 237186247704481414 237186247704481414 237186247704481414 endpoint_12_43_p6 endpoint_12_43_w6
private theorem endpoint_12_43_w8 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 8 2 237186247704481414 = some 237186247704481414 := by decide +kernel
private theorem endpoint_12_43_p10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 10 237186247704481414 = some 237186247704481414 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 8 2 237186247704481414 237186247704481414 237186247704481414 endpoint_12_43_p8 endpoint_12_43_w8
private theorem endpoint_12_43_w10 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 10 1 237186247704481414 = some 237186247704481414 := by decide +kernel
private theorem endpoint_12_43_p11 : receiptWindow endpoint_12_43_flag endpoint_12_43_sources 0 11 237186247704481414 = some 237186247704481414 :=
  join_receipt_window endpoint_12_43_flag endpoint_12_43_sources 0 10 1 237186247704481414 237186247704481414 237186247704481414 endpoint_12_43_p10 endpoint_12_43_w10
def endpoint_12_43 : CertifiedEndpoint :=
  ⟨⟨12, 43, 3780⟩, 237186247704481414, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_43_flag endpoint_12_43_sources 11 237186247704481414 237186247704481414 rfl endpoint_12_43_base endpoint_12_43_p11) (by decide)⟩
private def endpoint_12_44_flag : Flag := ⟨12, 44, 3746⟩
private def endpoint_12_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_44_base : receiptBase endpoint_12_44_flag endpoint_12_44_sources = some 239717063939592044 := by decide +kernel
private theorem endpoint_12_44_w0 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 2 239717063939592044 = some 239717063939592044 := by decide +kernel
private theorem endpoint_12_44_w2 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 2 2 239717063939592044 = some 239717063939592044 := by decide +kernel
private theorem endpoint_12_44_p4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 4 239717063939592044 = some 239717063939592044 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 2 2 239717063939592044 239717063939592044 239717063939592044 endpoint_12_44_w0 endpoint_12_44_w2
private theorem endpoint_12_44_w4 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 4 2 239717063939592044 = some 239717063939592044 := by decide +kernel
private theorem endpoint_12_44_p6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 6 239717063939592044 = some 239717063939592044 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 4 2 239717063939592044 239717063939592044 239717063939592044 endpoint_12_44_p4 endpoint_12_44_w4
private theorem endpoint_12_44_w6 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 6 2 239717063939592044 = some 239717063939592044 := by decide +kernel
private theorem endpoint_12_44_p8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 8 239717063939592044 = some 239717063939592044 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 6 2 239717063939592044 239717063939592044 239717063939592044 endpoint_12_44_p6 endpoint_12_44_w6
private theorem endpoint_12_44_w8 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 8 2 239717063939592044 = some 239717063939592044 := by decide +kernel
private theorem endpoint_12_44_p10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 10 239717063939592044 = some 239717063939592044 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 8 2 239717063939592044 239717063939592044 239717063939592044 endpoint_12_44_p8 endpoint_12_44_w8
private theorem endpoint_12_44_w10 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 10 1 239717063939592044 = some 239717063939592044 := by decide +kernel
private theorem endpoint_12_44_p11 : receiptWindow endpoint_12_44_flag endpoint_12_44_sources 0 11 239717063939592044 = some 239717063939592044 :=
  join_receipt_window endpoint_12_44_flag endpoint_12_44_sources 0 10 1 239717063939592044 239717063939592044 239717063939592044 endpoint_12_44_p10 endpoint_12_44_w10
def endpoint_12_44 : CertifiedEndpoint :=
  ⟨⟨12, 44, 3746⟩, 239717063939592044, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_44_flag endpoint_12_44_sources 11 239717063939592044 239717063939592044 rfl endpoint_12_44_base endpoint_12_44_p11) (by decide)⟩
private def endpoint_12_45_flag : Flag := ⟨12, 45, 3711⟩
private def endpoint_12_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_45_base : receiptBase endpoint_12_45_flag endpoint_12_45_sources = some 242099653371699615 := by decide +kernel
private theorem endpoint_12_45_w0 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 2 242099653371699615 = some 242099653371699615 := by decide +kernel
private theorem endpoint_12_45_w2 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 2 2 242099653371699615 = some 242099653371699615 := by decide +kernel
private theorem endpoint_12_45_p4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 4 242099653371699615 = some 242099653371699615 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 2 2 242099653371699615 242099653371699615 242099653371699615 endpoint_12_45_w0 endpoint_12_45_w2
private theorem endpoint_12_45_w4 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 4 2 242099653371699615 = some 242099653371699615 := by decide +kernel
private theorem endpoint_12_45_p6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 6 242099653371699615 = some 242099653371699615 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 4 2 242099653371699615 242099653371699615 242099653371699615 endpoint_12_45_p4 endpoint_12_45_w4
private theorem endpoint_12_45_w6 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 6 2 242099653371699615 = some 242099653371699615 := by decide +kernel
private theorem endpoint_12_45_p8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 8 242099653371699615 = some 242099653371699615 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 6 2 242099653371699615 242099653371699615 242099653371699615 endpoint_12_45_p6 endpoint_12_45_w6
private theorem endpoint_12_45_w8 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 8 2 242099653371699615 = some 242099653371699615 := by decide +kernel
private theorem endpoint_12_45_p10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 10 242099653371699615 = some 242099653371699615 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 8 2 242099653371699615 242099653371699615 242099653371699615 endpoint_12_45_p8 endpoint_12_45_w8
private theorem endpoint_12_45_w10 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 10 1 242099653371699615 = some 242099653371699615 := by decide +kernel
private theorem endpoint_12_45_p11 : receiptWindow endpoint_12_45_flag endpoint_12_45_sources 0 11 242099653371699615 = some 242099653371699615 :=
  join_receipt_window endpoint_12_45_flag endpoint_12_45_sources 0 10 1 242099653371699615 242099653371699615 242099653371699615 endpoint_12_45_p10 endpoint_12_45_w10
def endpoint_12_45 : CertifiedEndpoint :=
  ⟨⟨12, 45, 3711⟩, 242099653371699615, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_45_flag endpoint_12_45_sources 11 242099653371699615 242099653371699615 rfl endpoint_12_45_base endpoint_12_45_p11) (by decide)⟩
private def endpoint_12_46_flag : Flag := ⟨12, 46, 3675⟩
private def endpoint_12_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_46_base : receiptBase endpoint_12_46_flag endpoint_12_46_sources = some 244330366005455859 := by decide +kernel
private theorem endpoint_12_46_w0 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 2 244330366005455859 = some 244330366005455859 := by decide +kernel
private theorem endpoint_12_46_w2 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 2 2 244330366005455859 = some 244330366005455859 := by decide +kernel
private theorem endpoint_12_46_p4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 4 244330366005455859 = some 244330366005455859 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 2 2 244330366005455859 244330366005455859 244330366005455859 endpoint_12_46_w0 endpoint_12_46_w2
private theorem endpoint_12_46_w4 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 4 2 244330366005455859 = some 244330366005455859 := by decide +kernel
private theorem endpoint_12_46_p6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 6 244330366005455859 = some 244330366005455859 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 4 2 244330366005455859 244330366005455859 244330366005455859 endpoint_12_46_p4 endpoint_12_46_w4
private theorem endpoint_12_46_w6 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 6 2 244330366005455859 = some 244330366005455859 := by decide +kernel
private theorem endpoint_12_46_p8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 8 244330366005455859 = some 244330366005455859 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 6 2 244330366005455859 244330366005455859 244330366005455859 endpoint_12_46_p6 endpoint_12_46_w6
private theorem endpoint_12_46_w8 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 8 2 244330366005455859 = some 244330366005455859 := by decide +kernel
private theorem endpoint_12_46_p10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 10 244330366005455859 = some 244330366005455859 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 8 2 244330366005455859 244330366005455859 244330366005455859 endpoint_12_46_p8 endpoint_12_46_w8
private theorem endpoint_12_46_w10 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 10 1 244330366005455859 = some 244330366005455859 := by decide +kernel
private theorem endpoint_12_46_p11 : receiptWindow endpoint_12_46_flag endpoint_12_46_sources 0 11 244330366005455859 = some 244330366005455859 :=
  join_receipt_window endpoint_12_46_flag endpoint_12_46_sources 0 10 1 244330366005455859 244330366005455859 244330366005455859 endpoint_12_46_p10 endpoint_12_46_w10
def endpoint_12_46 : CertifiedEndpoint :=
  ⟨⟨12, 46, 3675⟩, 244330366005455859, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_46_flag endpoint_12_46_sources 11 244330366005455859 244330366005455859 rfl endpoint_12_46_base endpoint_12_46_p11) (by decide)⟩
private def endpoint_12_47_flag : Flag := ⟨12, 47, 3638⟩
private def endpoint_12_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_12_47_base : receiptBase endpoint_12_47_flag endpoint_12_47_sources = some 246405551845512512 := by decide +kernel
private theorem endpoint_12_47_w0 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 2 246405551845512512 = some 247062970166887563 := by decide +kernel
private theorem endpoint_12_47_w2 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 2 2 247062970166887563 = some 247062970166887563 := by decide +kernel
private theorem endpoint_12_47_p4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 4 246405551845512512 = some 247062970166887563 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 2 2 246405551845512512 247062970166887563 247062970166887563 endpoint_12_47_w0 endpoint_12_47_w2
private theorem endpoint_12_47_w4 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 4 2 247062970166887563 = some 247062970166887563 := by decide +kernel
private theorem endpoint_12_47_p6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 6 246405551845512512 = some 247062970166887563 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 4 2 246405551845512512 247062970166887563 247062970166887563 endpoint_12_47_p4 endpoint_12_47_w4
private theorem endpoint_12_47_w6 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 6 2 247062970166887563 = some 247062970166887563 := by decide +kernel
private theorem endpoint_12_47_p8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 8 246405551845512512 = some 247062970166887563 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 6 2 246405551845512512 247062970166887563 247062970166887563 endpoint_12_47_p6 endpoint_12_47_w6
private theorem endpoint_12_47_w8 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 8 2 247062970166887563 = some 247062970166887563 := by decide +kernel
private theorem endpoint_12_47_p10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 10 246405551845512512 = some 247062970166887563 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 8 2 246405551845512512 247062970166887563 247062970166887563 endpoint_12_47_p8 endpoint_12_47_w8
private theorem endpoint_12_47_w10 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 10 1 247062970166887563 = some 247062970166887563 := by decide +kernel
private theorem endpoint_12_47_p11 : receiptWindow endpoint_12_47_flag endpoint_12_47_sources 0 11 246405551845512512 = some 247062970166887563 :=
  join_receipt_window endpoint_12_47_flag endpoint_12_47_sources 0 10 1 246405551845512512 247062970166887563 247062970166887563 endpoint_12_47_p10 endpoint_12_47_w10
def endpoint_12_47 : CertifiedEndpoint :=
  ⟨⟨12, 47, 3638⟩, 247062970166887563, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_12_47_flag endpoint_12_47_sources 11 246405551845512512 247062970166887563 rfl endpoint_12_47_base endpoint_12_47_p11) (by decide)⟩
private def endpoint_12_48_flag : Flag := ⟨12, 48, 3600⟩
private def endpoint_12_48_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_48_base : receiptBase endpoint_12_48_flag endpoint_12_48_sources = some 248896992630748301 := by decide +kernel
private theorem endpoint_12_48_w0 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 2 248896992630748301 = some 248896992630748301 := by decide +kernel
private theorem endpoint_12_48_w2 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 2 2 248896992630748301 = some 248896992630748301 := by decide +kernel
private theorem endpoint_12_48_p4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 4 248896992630748301 = some 248896992630748301 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 2 2 248896992630748301 248896992630748301 248896992630748301 endpoint_12_48_w0 endpoint_12_48_w2
private theorem endpoint_12_48_w4 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 4 2 248896992630748301 = some 248896992630748301 := by decide +kernel
private theorem endpoint_12_48_p6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 6 248896992630748301 = some 248896992630748301 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 4 2 248896992630748301 248896992630748301 248896992630748301 endpoint_12_48_p4 endpoint_12_48_w4
private theorem endpoint_12_48_w6 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 6 2 248896992630748301 = some 248896992630748301 := by decide +kernel
private theorem endpoint_12_48_p8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 8 248896992630748301 = some 248896992630748301 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 6 2 248896992630748301 248896992630748301 248896992630748301 endpoint_12_48_p6 endpoint_12_48_w6
private theorem endpoint_12_48_w8 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 8 2 248896992630748301 = some 248896992630748301 := by decide +kernel
private theorem endpoint_12_48_p10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 10 248896992630748301 = some 248896992630748301 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 8 2 248896992630748301 248896992630748301 248896992630748301 endpoint_12_48_p8 endpoint_12_48_w8
private theorem endpoint_12_48_w10 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 10 1 248896992630748301 = some 248896992630748301 := by decide +kernel
private theorem endpoint_12_48_p11 : receiptWindow endpoint_12_48_flag endpoint_12_48_sources 0 11 248896992630748301 = some 248896992630748301 :=
  join_receipt_window endpoint_12_48_flag endpoint_12_48_sources 0 10 1 248896992630748301 248896992630748301 248896992630748301 endpoint_12_48_p10 endpoint_12_48_w10
def endpoint_12_48 : CertifiedEndpoint :=
  ⟨⟨12, 48, 3600⟩, 248896992630748301, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_48_flag endpoint_12_48_sources 11 248896992630748301 248896992630748301 rfl endpoint_12_48_base endpoint_12_48_p11) (by decide)⟩
private def endpoint_12_49_flag : Flag := ⟨12, 49, 3562⟩
private def endpoint_12_49_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_49_base : receiptBase endpoint_12_49_flag endpoint_12_49_sources = some 250728808821089565 := by decide +kernel
private theorem endpoint_12_49_w0 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 2 250728808821089565 = some 250728808821089565 := by decide +kernel
private theorem endpoint_12_49_w2 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 2 2 250728808821089565 = some 250728808821089565 := by decide +kernel
private theorem endpoint_12_49_p4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 4 250728808821089565 = some 250728808821089565 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 2 2 250728808821089565 250728808821089565 250728808821089565 endpoint_12_49_w0 endpoint_12_49_w2
private theorem endpoint_12_49_w4 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 4 2 250728808821089565 = some 250728808821089565 := by decide +kernel
private theorem endpoint_12_49_p6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 6 250728808821089565 = some 250728808821089565 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 4 2 250728808821089565 250728808821089565 250728808821089565 endpoint_12_49_p4 endpoint_12_49_w4
private theorem endpoint_12_49_w6 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 6 2 250728808821089565 = some 250728808821089565 := by decide +kernel
private theorem endpoint_12_49_p8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 8 250728808821089565 = some 250728808821089565 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 6 2 250728808821089565 250728808821089565 250728808821089565 endpoint_12_49_p6 endpoint_12_49_w6
private theorem endpoint_12_49_w8 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 8 2 250728808821089565 = some 250728808821089565 := by decide +kernel
private theorem endpoint_12_49_p10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 10 250728808821089565 = some 250728808821089565 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 8 2 250728808821089565 250728808821089565 250728808821089565 endpoint_12_49_p8 endpoint_12_49_w8
private theorem endpoint_12_49_w10 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 10 1 250728808821089565 = some 250728808821089565 := by decide +kernel
private theorem endpoint_12_49_p11 : receiptWindow endpoint_12_49_flag endpoint_12_49_sources 0 11 250728808821089565 = some 250728808821089565 :=
  join_receipt_window endpoint_12_49_flag endpoint_12_49_sources 0 10 1 250728808821089565 250728808821089565 250728808821089565 endpoint_12_49_p10 endpoint_12_49_w10
def endpoint_12_49 : CertifiedEndpoint :=
  ⟨⟨12, 49, 3562⟩, 250728808821089565, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_49_flag endpoint_12_49_sources 11 250728808821089565 250728808821089565 rfl endpoint_12_49_base endpoint_12_49_p11) (by decide)⟩
private def endpoint_12_50_flag : Flag := ⟨12, 50, 3522⟩
private def endpoint_12_50_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_50_base : receiptBase endpoint_12_50_flag endpoint_12_50_sources = some 252325528270968886 := by decide +kernel
private theorem endpoint_12_50_w0 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 2 252325528270968886 = some 252457565226946308 := by decide +kernel
private theorem endpoint_12_50_w2 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 2 2 252457565226946308 = some 252457565226946308 := by decide +kernel
private theorem endpoint_12_50_p4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 4 252325528270968886 = some 252457565226946308 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 2 2 252325528270968886 252457565226946308 252457565226946308 endpoint_12_50_w0 endpoint_12_50_w2
private theorem endpoint_12_50_w4 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 4 2 252457565226946308 = some 252457565226946308 := by decide +kernel
private theorem endpoint_12_50_p6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 6 252325528270968886 = some 252457565226946308 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 4 2 252325528270968886 252457565226946308 252457565226946308 endpoint_12_50_p4 endpoint_12_50_w4
private theorem endpoint_12_50_w6 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 6 2 252457565226946308 = some 252457565226946308 := by decide +kernel
private theorem endpoint_12_50_p8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 8 252325528270968886 = some 252457565226946308 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 6 2 252325528270968886 252457565226946308 252457565226946308 endpoint_12_50_p6 endpoint_12_50_w6
private theorem endpoint_12_50_w8 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 8 2 252457565226946308 = some 252457565226946308 := by decide +kernel
private theorem endpoint_12_50_p10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 10 252325528270968886 = some 252457565226946308 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 8 2 252325528270968886 252457565226946308 252457565226946308 endpoint_12_50_p8 endpoint_12_50_w8
private theorem endpoint_12_50_w10 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 10 1 252457565226946308 = some 252457565226946308 := by decide +kernel
private theorem endpoint_12_50_p11 : receiptWindow endpoint_12_50_flag endpoint_12_50_sources 0 11 252325528270968886 = some 252457565226946308 :=
  join_receipt_window endpoint_12_50_flag endpoint_12_50_sources 0 10 1 252325528270968886 252457565226946308 252457565226946308 endpoint_12_50_p10 endpoint_12_50_w10
def endpoint_12_50 : CertifiedEndpoint :=
  ⟨⟨12, 50, 3522⟩, 252457565226946308, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_50_flag endpoint_12_50_sources 11 252325528270968886 252457565226946308 rfl endpoint_12_50_base endpoint_12_50_p11) (by decide)⟩
private def endpoint_12_51_flag : Flag := ⟨12, 51, 3481⟩
private def endpoint_12_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_12_51_base : receiptBase endpoint_12_51_flag endpoint_12_51_sources = some 253751576402408312 := by decide +kernel
private theorem endpoint_12_51_w0 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 2 253751576402408312 = some 256677364126172658 := by decide +kernel
private theorem endpoint_12_51_w2 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 2 2 256677364126172658 = some 256677364126172658 := by decide +kernel
private theorem endpoint_12_51_p4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 4 253751576402408312 = some 256677364126172658 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 2 2 253751576402408312 256677364126172658 256677364126172658 endpoint_12_51_w0 endpoint_12_51_w2
private theorem endpoint_12_51_w4 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 4 2 256677364126172658 = some 256677364126172658 := by decide +kernel
private theorem endpoint_12_51_p6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 6 253751576402408312 = some 256677364126172658 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 4 2 253751576402408312 256677364126172658 256677364126172658 endpoint_12_51_p4 endpoint_12_51_w4
private theorem endpoint_12_51_w6 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 6 2 256677364126172658 = some 256677364126172658 := by decide +kernel
private theorem endpoint_12_51_p8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 8 253751576402408312 = some 256677364126172658 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 6 2 253751576402408312 256677364126172658 256677364126172658 endpoint_12_51_p6 endpoint_12_51_w6
private theorem endpoint_12_51_w8 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 8 2 256677364126172658 = some 256677364126172658 := by decide +kernel
private theorem endpoint_12_51_p10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 10 253751576402408312 = some 256677364126172658 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 8 2 253751576402408312 256677364126172658 256677364126172658 endpoint_12_51_p8 endpoint_12_51_w8
private theorem endpoint_12_51_w10 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 10 1 256677364126172658 = some 256677364126172658 := by decide +kernel
private theorem endpoint_12_51_p11 : receiptWindow endpoint_12_51_flag endpoint_12_51_sources 0 11 253751576402408312 = some 256677364126172658 :=
  join_receipt_window endpoint_12_51_flag endpoint_12_51_sources 0 10 1 253751576402408312 256677364126172658 256677364126172658 endpoint_12_51_p10 endpoint_12_51_w10
def endpoint_12_51 : CertifiedEndpoint :=
  ⟨⟨12, 51, 3481⟩, 256677364126172658, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_12_51_flag endpoint_12_51_sources 11 253751576402408312 256677364126172658 rfl endpoint_12_51_base endpoint_12_51_p11) (by decide)⟩
private def endpoint_12_52_flag : Flag := ⟨12, 52, 3439⟩
private def endpoint_12_52_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_12_52_base : receiptBase endpoint_12_52_flag endpoint_12_52_sources = some 255966274295760274 := by decide +kernel
private theorem endpoint_12_52_w0 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 2 255966274295760274 = some 256555512058310428 := by decide +kernel
private theorem endpoint_12_52_w2 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 2 2 256555512058310428 = some 256555512058310428 := by decide +kernel
private theorem endpoint_12_52_p4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 4 255966274295760274 = some 256555512058310428 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 2 2 255966274295760274 256555512058310428 256555512058310428 endpoint_12_52_w0 endpoint_12_52_w2
private theorem endpoint_12_52_w4 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 4 2 256555512058310428 = some 256555512058310428 := by decide +kernel
private theorem endpoint_12_52_p6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 6 255966274295760274 = some 256555512058310428 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 4 2 255966274295760274 256555512058310428 256555512058310428 endpoint_12_52_p4 endpoint_12_52_w4
private theorem endpoint_12_52_w6 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 6 2 256555512058310428 = some 256555512058310428 := by decide +kernel
private theorem endpoint_12_52_p8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 8 255966274295760274 = some 256555512058310428 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 6 2 255966274295760274 256555512058310428 256555512058310428 endpoint_12_52_p6 endpoint_12_52_w6
private theorem endpoint_12_52_w8 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 8 2 256555512058310428 = some 256555512058310428 := by decide +kernel
private theorem endpoint_12_52_p10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 10 255966274295760274 = some 256555512058310428 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 8 2 255966274295760274 256555512058310428 256555512058310428 endpoint_12_52_p8 endpoint_12_52_w8
private theorem endpoint_12_52_w10 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 10 1 256555512058310428 = some 256555512058310428 := by decide +kernel
private theorem endpoint_12_52_p11 : receiptWindow endpoint_12_52_flag endpoint_12_52_sources 0 11 255966274295760274 = some 256555512058310428 :=
  join_receipt_window endpoint_12_52_flag endpoint_12_52_sources 0 10 1 255966274295760274 256555512058310428 256555512058310428 endpoint_12_52_p10 endpoint_12_52_w10
def endpoint_12_52 : CertifiedEndpoint :=
  ⟨⟨12, 52, 3439⟩, 256555512058310428, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_12_52_flag endpoint_12_52_sources 11 255966274295760274 256555512058310428 rfl endpoint_12_52_base endpoint_12_52_p11) (by decide)⟩
private def endpoint_12_53_flag : Flag := ⟨12, 53, 3396⟩
private def endpoint_12_53_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_53_base : receiptBase endpoint_12_53_flag endpoint_12_53_sources = some 258947156959075521 := by decide +kernel
private theorem endpoint_12_53_w0 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 2 258947156959075521 = some 258947156959075521 := by decide +kernel
private theorem endpoint_12_53_w2 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 2 2 258947156959075521 = some 258947156959075521 := by decide +kernel
private theorem endpoint_12_53_p4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 4 258947156959075521 = some 258947156959075521 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 2 2 258947156959075521 258947156959075521 258947156959075521 endpoint_12_53_w0 endpoint_12_53_w2
private theorem endpoint_12_53_w4 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 4 2 258947156959075521 = some 258947156959075521 := by decide +kernel
private theorem endpoint_12_53_p6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 6 258947156959075521 = some 258947156959075521 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 4 2 258947156959075521 258947156959075521 258947156959075521 endpoint_12_53_p4 endpoint_12_53_w4
private theorem endpoint_12_53_w6 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 6 2 258947156959075521 = some 258947156959075521 := by decide +kernel
private theorem endpoint_12_53_p8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 8 258947156959075521 = some 258947156959075521 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 6 2 258947156959075521 258947156959075521 258947156959075521 endpoint_12_53_p6 endpoint_12_53_w6
private theorem endpoint_12_53_w8 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 8 2 258947156959075521 = some 258947156959075521 := by decide +kernel
private theorem endpoint_12_53_p10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 10 258947156959075521 = some 258947156959075521 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 8 2 258947156959075521 258947156959075521 258947156959075521 endpoint_12_53_p8 endpoint_12_53_w8
private theorem endpoint_12_53_w10 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 10 1 258947156959075521 = some 258947156959075521 := by decide +kernel
private theorem endpoint_12_53_p11 : receiptWindow endpoint_12_53_flag endpoint_12_53_sources 0 11 258947156959075521 = some 258947156959075521 :=
  join_receipt_window endpoint_12_53_flag endpoint_12_53_sources 0 10 1 258947156959075521 258947156959075521 258947156959075521 endpoint_12_53_p10 endpoint_12_53_w10
def endpoint_12_53 : CertifiedEndpoint :=
  ⟨⟨12, 53, 3396⟩, 258947156959075521, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_53_flag endpoint_12_53_sources 11 258947156959075521 258947156959075521 rfl endpoint_12_53_base endpoint_12_53_p11) (by decide)⟩
private def endpoint_12_54_flag : Flag := ⟨12, 54, 3352⟩
private def endpoint_12_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_54_base : receiptBase endpoint_12_54_flag endpoint_12_54_sources = some 259790634390537703 := by decide +kernel
private theorem endpoint_12_54_w0 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 2 259790634390537703 = some 259790634390537703 := by decide +kernel
private theorem endpoint_12_54_w2 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 2 2 259790634390537703 = some 259790634390537703 := by decide +kernel
private theorem endpoint_12_54_p4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 4 259790634390537703 = some 259790634390537703 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 2 2 259790634390537703 259790634390537703 259790634390537703 endpoint_12_54_w0 endpoint_12_54_w2
private theorem endpoint_12_54_w4 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 4 2 259790634390537703 = some 259790634390537703 := by decide +kernel
private theorem endpoint_12_54_p6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 6 259790634390537703 = some 259790634390537703 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 4 2 259790634390537703 259790634390537703 259790634390537703 endpoint_12_54_p4 endpoint_12_54_w4
private theorem endpoint_12_54_w6 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 6 2 259790634390537703 = some 259790634390537703 := by decide +kernel
private theorem endpoint_12_54_p8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 8 259790634390537703 = some 259790634390537703 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 6 2 259790634390537703 259790634390537703 259790634390537703 endpoint_12_54_p6 endpoint_12_54_w6
private theorem endpoint_12_54_w8 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 8 2 259790634390537703 = some 259790634390537703 := by decide +kernel
private theorem endpoint_12_54_p10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 10 259790634390537703 = some 259790634390537703 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 8 2 259790634390537703 259790634390537703 259790634390537703 endpoint_12_54_p8 endpoint_12_54_w8
private theorem endpoint_12_54_w10 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 10 1 259790634390537703 = some 259790634390537703 := by decide +kernel
private theorem endpoint_12_54_p11 : receiptWindow endpoint_12_54_flag endpoint_12_54_sources 0 11 259790634390537703 = some 259790634390537703 :=
  join_receipt_window endpoint_12_54_flag endpoint_12_54_sources 0 10 1 259790634390537703 259790634390537703 259790634390537703 endpoint_12_54_p10 endpoint_12_54_w10
def endpoint_12_54 : CertifiedEndpoint :=
  ⟨⟨12, 54, 3352⟩, 259790634390537703, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_54_flag endpoint_12_54_sources 11 259790634390537703 259790634390537703 rfl endpoint_12_54_base endpoint_12_54_p11) (by decide)⟩
private def endpoint_12_55_flag : Flag := ⟨12, 55, 3306⟩
private def endpoint_12_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_55_base : receiptBase endpoint_12_55_flag endpoint_12_55_sources = some 260369584801965335 := by decide +kernel
private theorem endpoint_12_55_w0 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 2 260369584801965335 = some 260497735640356437 := by decide +kernel
private theorem endpoint_12_55_w2 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 2 2 260497735640356437 = some 260497735640356437 := by decide +kernel
private theorem endpoint_12_55_p4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 4 260369584801965335 = some 260497735640356437 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 2 2 260369584801965335 260497735640356437 260497735640356437 endpoint_12_55_w0 endpoint_12_55_w2
private theorem endpoint_12_55_w4 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 4 2 260497735640356437 = some 260497735640356437 := by decide +kernel
private theorem endpoint_12_55_p6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 6 260369584801965335 = some 260497735640356437 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 4 2 260369584801965335 260497735640356437 260497735640356437 endpoint_12_55_p4 endpoint_12_55_w4
private theorem endpoint_12_55_w6 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 6 2 260497735640356437 = some 260497735640356437 := by decide +kernel
private theorem endpoint_12_55_p8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 8 260369584801965335 = some 260497735640356437 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 6 2 260369584801965335 260497735640356437 260497735640356437 endpoint_12_55_p6 endpoint_12_55_w6
private theorem endpoint_12_55_w8 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 8 2 260497735640356437 = some 260497735640356437 := by decide +kernel
private theorem endpoint_12_55_p10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 10 260369584801965335 = some 260497735640356437 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 8 2 260369584801965335 260497735640356437 260497735640356437 endpoint_12_55_p8 endpoint_12_55_w8
private theorem endpoint_12_55_w10 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 10 1 260497735640356437 = some 260497735640356437 := by decide +kernel
private theorem endpoint_12_55_p11 : receiptWindow endpoint_12_55_flag endpoint_12_55_sources 0 11 260369584801965335 = some 260497735640356437 :=
  join_receipt_window endpoint_12_55_flag endpoint_12_55_sources 0 10 1 260369584801965335 260497735640356437 260497735640356437 endpoint_12_55_p10 endpoint_12_55_w10
def endpoint_12_55 : CertifiedEndpoint :=
  ⟨⟨12, 55, 3306⟩, 260497735640356437, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_55_flag endpoint_12_55_sources 11 260369584801965335 260497735640356437 rfl endpoint_12_55_base endpoint_12_55_p11) (by decide)⟩
private def endpoint_12_56_flag : Flag := ⟨12, 56, 3258⟩
private def endpoint_12_56_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_12_56_base : receiptBase endpoint_12_56_flag endpoint_12_56_sources = some 260676654230186733 := by decide +kernel
private theorem endpoint_12_56_w0 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 2 260676654230186733 = some 263784188690523136 := by decide +kernel
private theorem endpoint_12_56_w2 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 2 2 263784188690523136 = some 263784188690523136 := by decide +kernel
private theorem endpoint_12_56_p4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 4 260676654230186733 = some 263784188690523136 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 2 2 260676654230186733 263784188690523136 263784188690523136 endpoint_12_56_w0 endpoint_12_56_w2
private theorem endpoint_12_56_w4 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 4 2 263784188690523136 = some 263784188690523136 := by decide +kernel
private theorem endpoint_12_56_p6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 6 260676654230186733 = some 263784188690523136 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 4 2 260676654230186733 263784188690523136 263784188690523136 endpoint_12_56_p4 endpoint_12_56_w4
private theorem endpoint_12_56_w6 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 6 2 263784188690523136 = some 263784188690523136 := by decide +kernel
private theorem endpoint_12_56_p8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 8 260676654230186733 = some 263784188690523136 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 6 2 260676654230186733 263784188690523136 263784188690523136 endpoint_12_56_p6 endpoint_12_56_w6
private theorem endpoint_12_56_w8 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 8 2 263784188690523136 = some 263784188690523136 := by decide +kernel
private theorem endpoint_12_56_p10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 10 260676654230186733 = some 263784188690523136 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 8 2 260676654230186733 263784188690523136 263784188690523136 endpoint_12_56_p8 endpoint_12_56_w8
private theorem endpoint_12_56_w10 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 10 1 263784188690523136 = some 263784188690523136 := by decide +kernel
private theorem endpoint_12_56_p11 : receiptWindow endpoint_12_56_flag endpoint_12_56_sources 0 11 260676654230186733 = some 263784188690523136 :=
  join_receipt_window endpoint_12_56_flag endpoint_12_56_sources 0 10 1 260676654230186733 263784188690523136 263784188690523136 endpoint_12_56_p10 endpoint_12_56_w10
def endpoint_12_56 : CertifiedEndpoint :=
  ⟨⟨12, 56, 3258⟩, 263784188690523136, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_12_56_flag endpoint_12_56_sources 11 260676654230186733 263784188690523136 rfl endpoint_12_56_base endpoint_12_56_p11) (by decide)⟩
private def endpoint_12_57_flag : Flag := ⟨12, 57, 3209⟩
private def endpoint_12_57_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_57_base : receiptBase endpoint_12_57_flag endpoint_12_57_sources = some 261859098578300771 := by decide +kernel
private theorem endpoint_12_57_w0 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 2 261859098578300771 = some 261859098578300771 := by decide +kernel
private theorem endpoint_12_57_w2 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 2 2 261859098578300771 = some 261859098578300771 := by decide +kernel
private theorem endpoint_12_57_p4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 4 261859098578300771 = some 261859098578300771 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 2 2 261859098578300771 261859098578300771 261859098578300771 endpoint_12_57_w0 endpoint_12_57_w2
private theorem endpoint_12_57_w4 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 4 2 261859098578300771 = some 261859098578300771 := by decide +kernel
private theorem endpoint_12_57_p6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 6 261859098578300771 = some 261859098578300771 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 4 2 261859098578300771 261859098578300771 261859098578300771 endpoint_12_57_p4 endpoint_12_57_w4
private theorem endpoint_12_57_w6 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 6 2 261859098578300771 = some 261859098578300771 := by decide +kernel
private theorem endpoint_12_57_p8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 8 261859098578300771 = some 261859098578300771 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 6 2 261859098578300771 261859098578300771 261859098578300771 endpoint_12_57_p6 endpoint_12_57_w6
private theorem endpoint_12_57_w8 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 8 2 261859098578300771 = some 261859098578300771 := by decide +kernel
private theorem endpoint_12_57_p10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 10 261859098578300771 = some 261859098578300771 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 8 2 261859098578300771 261859098578300771 261859098578300771 endpoint_12_57_p8 endpoint_12_57_w8
private theorem endpoint_12_57_w10 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 10 1 261859098578300771 = some 261859098578300771 := by decide +kernel
private theorem endpoint_12_57_p11 : receiptWindow endpoint_12_57_flag endpoint_12_57_sources 0 11 261859098578300771 = some 261859098578300771 :=
  join_receipt_window endpoint_12_57_flag endpoint_12_57_sources 0 10 1 261859098578300771 261859098578300771 261859098578300771 endpoint_12_57_p10 endpoint_12_57_w10
def endpoint_12_57 : CertifiedEndpoint :=
  ⟨⟨12, 57, 3209⟩, 261859098578300771, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_57_flag endpoint_12_57_sources 11 261859098578300771 261859098578300771 rfl endpoint_12_57_base endpoint_12_57_p11) (by decide)⟩
private def endpoint_12_58_flag : Flag := ⟨12, 58, 3158⟩
private def endpoint_12_58_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_58_base : receiptBase endpoint_12_58_flag endpoint_12_58_sources = some 261685848317548048 := by decide +kernel
private theorem endpoint_12_58_w0 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 2 261685848317548048 = some 262030524718461888 := by decide +kernel
private theorem endpoint_12_58_w2 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 2 2 262030524718461888 = some 262030524718461888 := by decide +kernel
private theorem endpoint_12_58_p4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 4 261685848317548048 = some 262030524718461888 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 2 2 261685848317548048 262030524718461888 262030524718461888 endpoint_12_58_w0 endpoint_12_58_w2
private theorem endpoint_12_58_w4 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 4 2 262030524718461888 = some 262030524718461888 := by decide +kernel
private theorem endpoint_12_58_p6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 6 261685848317548048 = some 262030524718461888 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 4 2 261685848317548048 262030524718461888 262030524718461888 endpoint_12_58_p4 endpoint_12_58_w4
private theorem endpoint_12_58_w6 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 6 2 262030524718461888 = some 262030524718461888 := by decide +kernel
private theorem endpoint_12_58_p8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 8 261685848317548048 = some 262030524718461888 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 6 2 261685848317548048 262030524718461888 262030524718461888 endpoint_12_58_p6 endpoint_12_58_w6
private theorem endpoint_12_58_w8 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 8 2 262030524718461888 = some 262030524718461888 := by decide +kernel
private theorem endpoint_12_58_p10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 10 261685848317548048 = some 262030524718461888 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 8 2 261685848317548048 262030524718461888 262030524718461888 endpoint_12_58_p8 endpoint_12_58_w8
private theorem endpoint_12_58_w10 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 10 1 262030524718461888 = some 262030524718461888 := by decide +kernel
private theorem endpoint_12_58_p11 : receiptWindow endpoint_12_58_flag endpoint_12_58_sources 0 11 261685848317548048 = some 262030524718461888 :=
  join_receipt_window endpoint_12_58_flag endpoint_12_58_sources 0 10 1 261685848317548048 262030524718461888 262030524718461888 endpoint_12_58_p10 endpoint_12_58_w10
def endpoint_12_58 : CertifiedEndpoint :=
  ⟨⟨12, 58, 3158⟩, 262030524718461888, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_58_flag endpoint_12_58_sources 11 261685848317548048 262030524718461888 rfl endpoint_12_58_base endpoint_12_58_p11) (by decide)⟩
private def endpoint_12_59_flag : Flag := ⟨12, 59, 3104⟩
private def endpoint_12_59_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_12_59_base : receiptBase endpoint_12_59_flag endpoint_12_59_sources = some 261136295885705925 := by decide +kernel
private theorem endpoint_12_59_w0 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 2 261136295885705925 = some 264621914135061559 := by decide +kernel
private theorem endpoint_12_59_w2 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 2 2 264621914135061559 = some 264621914135061559 := by decide +kernel
private theorem endpoint_12_59_p4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 4 261136295885705925 = some 264621914135061559 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 2 2 261136295885705925 264621914135061559 264621914135061559 endpoint_12_59_w0 endpoint_12_59_w2
private theorem endpoint_12_59_w4 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 4 2 264621914135061559 = some 264621914135061559 := by decide +kernel
private theorem endpoint_12_59_p6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 6 261136295885705925 = some 264621914135061559 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 4 2 261136295885705925 264621914135061559 264621914135061559 endpoint_12_59_p4 endpoint_12_59_w4
private theorem endpoint_12_59_w6 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 6 2 264621914135061559 = some 264621914135061559 := by decide +kernel
private theorem endpoint_12_59_p8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 8 261136295885705925 = some 264621914135061559 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 6 2 261136295885705925 264621914135061559 264621914135061559 endpoint_12_59_p6 endpoint_12_59_w6
private theorem endpoint_12_59_w8 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 8 2 264621914135061559 = some 264621914135061559 := by decide +kernel
private theorem endpoint_12_59_p10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 10 261136295885705925 = some 264621914135061559 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 8 2 261136295885705925 264621914135061559 264621914135061559 endpoint_12_59_p8 endpoint_12_59_w8
private theorem endpoint_12_59_w10 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 10 1 264621914135061559 = some 264621914135061559 := by decide +kernel
private theorem endpoint_12_59_p11 : receiptWindow endpoint_12_59_flag endpoint_12_59_sources 0 11 261136295885705925 = some 264621914135061559 :=
  join_receipt_window endpoint_12_59_flag endpoint_12_59_sources 0 10 1 261136295885705925 264621914135061559 264621914135061559 endpoint_12_59_p10 endpoint_12_59_w10
def endpoint_12_59 : CertifiedEndpoint :=
  ⟨⟨12, 59, 3104⟩, 264621914135061559, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_12_59_flag endpoint_12_59_sources 11 261136295885705925 264621914135061559 rfl endpoint_12_59_base endpoint_12_59_p11) (by decide)⟩
private def endpoint_12_60_flag : Flag := ⟨12, 60, 3048⟩
private def endpoint_12_60_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_60_base : receiptBase endpoint_12_60_flag endpoint_12_60_sources = some 261424309414645285 := by decide +kernel
private theorem endpoint_12_60_w0 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 2 261424309414645285 = some 261424309414645285 := by decide +kernel
private theorem endpoint_12_60_w2 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 2 2 261424309414645285 = some 261424309414645285 := by decide +kernel
private theorem endpoint_12_60_p4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 4 261424309414645285 = some 261424309414645285 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 2 2 261424309414645285 261424309414645285 261424309414645285 endpoint_12_60_w0 endpoint_12_60_w2
private theorem endpoint_12_60_w4 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 4 2 261424309414645285 = some 261424309414645285 := by decide +kernel
private theorem endpoint_12_60_p6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 6 261424309414645285 = some 261424309414645285 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 4 2 261424309414645285 261424309414645285 261424309414645285 endpoint_12_60_p4 endpoint_12_60_w4
private theorem endpoint_12_60_w6 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 6 2 261424309414645285 = some 261424309414645285 := by decide +kernel
private theorem endpoint_12_60_p8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 8 261424309414645285 = some 261424309414645285 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 6 2 261424309414645285 261424309414645285 261424309414645285 endpoint_12_60_p6 endpoint_12_60_w6
private theorem endpoint_12_60_w8 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 8 2 261424309414645285 = some 261424309414645285 := by decide +kernel
private theorem endpoint_12_60_p10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 10 261424309414645285 = some 261424309414645285 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 8 2 261424309414645285 261424309414645285 261424309414645285 endpoint_12_60_p8 endpoint_12_60_w8
private theorem endpoint_12_60_w10 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 10 1 261424309414645285 = some 261424309414645285 := by decide +kernel
private theorem endpoint_12_60_p11 : receiptWindow endpoint_12_60_flag endpoint_12_60_sources 0 11 261424309414645285 = some 261424309414645285 :=
  join_receipt_window endpoint_12_60_flag endpoint_12_60_sources 0 10 1 261424309414645285 261424309414645285 261424309414645285 endpoint_12_60_p10 endpoint_12_60_w10
def endpoint_12_60 : CertifiedEndpoint :=
  ⟨⟨12, 60, 3048⟩, 261424309414645285, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_60_flag endpoint_12_60_sources 11 261424309414645285 261424309414645285 rfl endpoint_12_60_base endpoint_12_60_p11) (by decide)⟩
private def endpoint_12_61_flag : Flag := ⟨12, 61, 2990⟩
private def endpoint_12_61_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_12_61_base : receiptBase endpoint_12_61_flag endpoint_12_61_sources = some 260259390785881577 := by decide +kernel
private theorem endpoint_12_61_w0 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 2 260259390785881577 = some 263363033733773012 := by decide +kernel
private theorem endpoint_12_61_w2 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 2 2 263363033733773012 = some 263363033733773012 := by decide +kernel
private theorem endpoint_12_61_p4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 4 260259390785881577 = some 263363033733773012 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 2 2 260259390785881577 263363033733773012 263363033733773012 endpoint_12_61_w0 endpoint_12_61_w2
private theorem endpoint_12_61_w4 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 4 2 263363033733773012 = some 263363033733773012 := by decide +kernel
private theorem endpoint_12_61_p6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 6 260259390785881577 = some 263363033733773012 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 4 2 260259390785881577 263363033733773012 263363033733773012 endpoint_12_61_p4 endpoint_12_61_w4
private theorem endpoint_12_61_w6 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 6 2 263363033733773012 = some 263363033733773012 := by decide +kernel
private theorem endpoint_12_61_p8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 8 260259390785881577 = some 263363033733773012 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 6 2 260259390785881577 263363033733773012 263363033733773012 endpoint_12_61_p6 endpoint_12_61_w6
private theorem endpoint_12_61_w8 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 8 2 263363033733773012 = some 263363033733773012 := by decide +kernel
private theorem endpoint_12_61_p10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 10 260259390785881577 = some 263363033733773012 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 8 2 260259390785881577 263363033733773012 263363033733773012 endpoint_12_61_p8 endpoint_12_61_w8
private theorem endpoint_12_61_w10 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 10 1 263363033733773012 = some 263363033733773012 := by decide +kernel
private theorem endpoint_12_61_p11 : receiptWindow endpoint_12_61_flag endpoint_12_61_sources 0 11 260259390785881577 = some 263363033733773012 :=
  join_receipt_window endpoint_12_61_flag endpoint_12_61_sources 0 10 1 260259390785881577 263363033733773012 263363033733773012 endpoint_12_61_p10 endpoint_12_61_w10
def endpoint_12_61 : CertifiedEndpoint :=
  ⟨⟨12, 61, 2990⟩, 263363033733773012, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_12_61_flag endpoint_12_61_sources 11 260259390785881577 263363033733773012 rfl endpoint_12_61_base endpoint_12_61_p11) (by decide)⟩
private def endpoint_12_62_flag : Flag := ⟨12, 62, 2929⟩
private def endpoint_12_62_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_12_62_base : receiptBase endpoint_12_62_flag endpoint_12_62_sources = some 259872880627089250 := by decide +kernel
private theorem endpoint_12_62_w0 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 2 259872880627089250 = some 261160096968510892 := by decide +kernel
private theorem endpoint_12_62_w2 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 2 2 261160096968510892 = some 261160096968510892 := by decide +kernel
private theorem endpoint_12_62_p4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 4 259872880627089250 = some 261160096968510892 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 2 2 259872880627089250 261160096968510892 261160096968510892 endpoint_12_62_w0 endpoint_12_62_w2
private theorem endpoint_12_62_w4 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 4 2 261160096968510892 = some 261160096968510892 := by decide +kernel
private theorem endpoint_12_62_p6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 6 259872880627089250 = some 261160096968510892 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 4 2 259872880627089250 261160096968510892 261160096968510892 endpoint_12_62_p4 endpoint_12_62_w4
private theorem endpoint_12_62_w6 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 6 2 261160096968510892 = some 261160096968510892 := by decide +kernel
private theorem endpoint_12_62_p8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 8 259872880627089250 = some 261160096968510892 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 6 2 259872880627089250 261160096968510892 261160096968510892 endpoint_12_62_p6 endpoint_12_62_w6
private theorem endpoint_12_62_w8 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 8 2 261160096968510892 = some 261160096968510892 := by decide +kernel
private theorem endpoint_12_62_p10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 10 259872880627089250 = some 261160096968510892 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 8 2 259872880627089250 261160096968510892 261160096968510892 endpoint_12_62_p8 endpoint_12_62_w8
private theorem endpoint_12_62_w10 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 10 1 261160096968510892 = some 261160096968510892 := by decide +kernel
private theorem endpoint_12_62_p11 : receiptWindow endpoint_12_62_flag endpoint_12_62_sources 0 11 259872880627089250 = some 261160096968510892 :=
  join_receipt_window endpoint_12_62_flag endpoint_12_62_sources 0 10 1 259872880627089250 261160096968510892 261160096968510892 endpoint_12_62_p10 endpoint_12_62_w10
def endpoint_12_62 : CertifiedEndpoint :=
  ⟨⟨12, 62, 2929⟩, 261160096968510892, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_12_62_flag endpoint_12_62_sources 11 259872880627089250 261160096968510892 rfl endpoint_12_62_base endpoint_12_62_p11) (by decide)⟩
private def endpoint_12_63_flag : Flag := ⟨12, 63, 2865⟩
private def endpoint_12_63_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_12_63_base : receiptBase endpoint_12_63_flag endpoint_12_63_sources = some 259097759234043836 := by decide +kernel
private theorem endpoint_12_63_w0 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 2 259097759234043836 = some 260097141708156768 := by decide +kernel
private theorem endpoint_12_63_w2 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 2 2 260097141708156768 = some 260097141708156768 := by decide +kernel
private theorem endpoint_12_63_p4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 4 259097759234043836 = some 260097141708156768 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 2 2 259097759234043836 260097141708156768 260097141708156768 endpoint_12_63_w0 endpoint_12_63_w2
private theorem endpoint_12_63_w4 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 4 2 260097141708156768 = some 260097141708156768 := by decide +kernel
private theorem endpoint_12_63_p6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 6 259097759234043836 = some 260097141708156768 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 4 2 259097759234043836 260097141708156768 260097141708156768 endpoint_12_63_p4 endpoint_12_63_w4
private theorem endpoint_12_63_w6 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 6 2 260097141708156768 = some 260097141708156768 := by decide +kernel
private theorem endpoint_12_63_p8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 8 259097759234043836 = some 260097141708156768 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 6 2 259097759234043836 260097141708156768 260097141708156768 endpoint_12_63_p6 endpoint_12_63_w6
private theorem endpoint_12_63_w8 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 8 2 260097141708156768 = some 260097141708156768 := by decide +kernel
private theorem endpoint_12_63_p10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 10 259097759234043836 = some 260097141708156768 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 8 2 259097759234043836 260097141708156768 260097141708156768 endpoint_12_63_p8 endpoint_12_63_w8
private theorem endpoint_12_63_w10 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 10 1 260097141708156768 = some 260097141708156768 := by decide +kernel
private theorem endpoint_12_63_p11 : receiptWindow endpoint_12_63_flag endpoint_12_63_sources 0 11 259097759234043836 = some 260097141708156768 :=
  join_receipt_window endpoint_12_63_flag endpoint_12_63_sources 0 10 1 259097759234043836 260097141708156768 260097141708156768 endpoint_12_63_p10 endpoint_12_63_w10
def endpoint_12_63 : CertifiedEndpoint :=
  ⟨⟨12, 63, 2865⟩, 260097141708156768, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_12_63_flag endpoint_12_63_sources 11 259097759234043836 260097141708156768 rfl endpoint_12_63_base endpoint_12_63_p11) (by decide)⟩
private def endpoint_12_64_flag : Flag := ⟨12, 64, 2799⟩
private def endpoint_12_64_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_64_base : receiptBase endpoint_12_64_flag endpoint_12_64_sources = some 257842019829338790 := by decide +kernel
private theorem endpoint_12_64_w0 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 2 257842019829338790 = some 257842019829338790 := by decide +kernel
private theorem endpoint_12_64_w2 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 2 2 257842019829338790 = some 257842019829338790 := by decide +kernel
private theorem endpoint_12_64_p4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 4 257842019829338790 = some 257842019829338790 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 2 2 257842019829338790 257842019829338790 257842019829338790 endpoint_12_64_w0 endpoint_12_64_w2
private theorem endpoint_12_64_w4 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 4 2 257842019829338790 = some 257842019829338790 := by decide +kernel
private theorem endpoint_12_64_p6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 6 257842019829338790 = some 257842019829338790 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 4 2 257842019829338790 257842019829338790 257842019829338790 endpoint_12_64_p4 endpoint_12_64_w4
private theorem endpoint_12_64_w6 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 6 2 257842019829338790 = some 257842019829338790 := by decide +kernel
private theorem endpoint_12_64_p8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 8 257842019829338790 = some 257842019829338790 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 6 2 257842019829338790 257842019829338790 257842019829338790 endpoint_12_64_p6 endpoint_12_64_w6
private theorem endpoint_12_64_w8 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 8 2 257842019829338790 = some 257842019829338790 := by decide +kernel
private theorem endpoint_12_64_p10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 10 257842019829338790 = some 257842019829338790 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 8 2 257842019829338790 257842019829338790 257842019829338790 endpoint_12_64_p8 endpoint_12_64_w8
private theorem endpoint_12_64_w10 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 10 1 257842019829338790 = some 257842019829338790 := by decide +kernel
private theorem endpoint_12_64_p11 : receiptWindow endpoint_12_64_flag endpoint_12_64_sources 0 11 257842019829338790 = some 257842019829338790 :=
  join_receipt_window endpoint_12_64_flag endpoint_12_64_sources 0 10 1 257842019829338790 257842019829338790 257842019829338790 endpoint_12_64_p10 endpoint_12_64_w10
def endpoint_12_64 : CertifiedEndpoint :=
  ⟨⟨12, 64, 2799⟩, 257842019829338790, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_64_flag endpoint_12_64_sources 11 257842019829338790 257842019829338790 rfl endpoint_12_64_base endpoint_12_64_p11) (by decide)⟩
private def endpoint_12_65_flag : Flag := ⟨12, 65, 2729⟩
private def endpoint_12_65_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_65_base : receiptBase endpoint_12_65_flag endpoint_12_65_sources = some 254949875114275960 := by decide +kernel
private theorem endpoint_12_65_w0 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 2 254949875114275960 = some 254949875114275960 := by decide +kernel
private theorem endpoint_12_65_w2 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 2 2 254949875114275960 = some 254949875114275960 := by decide +kernel
private theorem endpoint_12_65_p4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 4 254949875114275960 = some 254949875114275960 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 2 2 254949875114275960 254949875114275960 254949875114275960 endpoint_12_65_w0 endpoint_12_65_w2
private theorem endpoint_12_65_w4 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 4 2 254949875114275960 = some 254949875114275960 := by decide +kernel
private theorem endpoint_12_65_p6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 6 254949875114275960 = some 254949875114275960 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 4 2 254949875114275960 254949875114275960 254949875114275960 endpoint_12_65_p4 endpoint_12_65_w4
private theorem endpoint_12_65_w6 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 6 2 254949875114275960 = some 254949875114275960 := by decide +kernel
private theorem endpoint_12_65_p8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 8 254949875114275960 = some 254949875114275960 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 6 2 254949875114275960 254949875114275960 254949875114275960 endpoint_12_65_p6 endpoint_12_65_w6
private theorem endpoint_12_65_w8 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 8 2 254949875114275960 = some 254949875114275960 := by decide +kernel
private theorem endpoint_12_65_p10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 10 254949875114275960 = some 254949875114275960 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 8 2 254949875114275960 254949875114275960 254949875114275960 endpoint_12_65_p8 endpoint_12_65_w8
private theorem endpoint_12_65_w10 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 10 1 254949875114275960 = some 254949875114275960 := by decide +kernel
private theorem endpoint_12_65_p11 : receiptWindow endpoint_12_65_flag endpoint_12_65_sources 0 11 254949875114275960 = some 254949875114275960 :=
  join_receipt_window endpoint_12_65_flag endpoint_12_65_sources 0 10 1 254949875114275960 254949875114275960 254949875114275960 endpoint_12_65_p10 endpoint_12_65_w10
def endpoint_12_65 : CertifiedEndpoint :=
  ⟨⟨12, 65, 2729⟩, 254949875114275960, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_65_flag endpoint_12_65_sources 11 254949875114275960 254949875114275960 rfl endpoint_12_65_base endpoint_12_65_p11) (by decide)⟩
private def endpoint_12_66_flag : Flag := ⟨12, 66, 2657⟩
private def endpoint_12_66_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_66_base : receiptBase endpoint_12_66_flag endpoint_12_66_sources = some 251691332107371176 := by decide +kernel
private theorem endpoint_12_66_w0 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 2 251691332107371176 = some 255265460636499684 := by decide +kernel
private theorem endpoint_12_66_w2 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 2 2 255265460636499684 = some 255265460636499684 := by decide +kernel
private theorem endpoint_12_66_p4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 4 251691332107371176 = some 255265460636499684 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 2 2 251691332107371176 255265460636499684 255265460636499684 endpoint_12_66_w0 endpoint_12_66_w2
private theorem endpoint_12_66_w4 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 4 2 255265460636499684 = some 255265460636499684 := by decide +kernel
private theorem endpoint_12_66_p6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 6 251691332107371176 = some 255265460636499684 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 4 2 251691332107371176 255265460636499684 255265460636499684 endpoint_12_66_p4 endpoint_12_66_w4
private theorem endpoint_12_66_w6 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 6 2 255265460636499684 = some 255265460636499684 := by decide +kernel
private theorem endpoint_12_66_p8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 8 251691332107371176 = some 255265460636499684 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 6 2 251691332107371176 255265460636499684 255265460636499684 endpoint_12_66_p6 endpoint_12_66_w6
private theorem endpoint_12_66_w8 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 8 2 255265460636499684 = some 255265460636499684 := by decide +kernel
private theorem endpoint_12_66_p10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 10 251691332107371176 = some 255265460636499684 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 8 2 251691332107371176 255265460636499684 255265460636499684 endpoint_12_66_p8 endpoint_12_66_w8
private theorem endpoint_12_66_w10 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 10 1 255265460636499684 = some 255265460636499684 := by decide +kernel
private theorem endpoint_12_66_p11 : receiptWindow endpoint_12_66_flag endpoint_12_66_sources 0 11 251691332107371176 = some 255265460636499684 :=
  join_receipt_window endpoint_12_66_flag endpoint_12_66_sources 0 10 1 251691332107371176 255265460636499684 255265460636499684 endpoint_12_66_p10 endpoint_12_66_w10
def endpoint_12_66 : CertifiedEndpoint :=
  ⟨⟨12, 66, 2657⟩, 255265460636499684, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_66_flag endpoint_12_66_sources 11 251691332107371176 255265460636499684 rfl endpoint_12_66_base endpoint_12_66_p11) (by decide)⟩
private def endpoint_12_67_flag : Flag := ⟨12, 67, 2582⟩
private def endpoint_12_67_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_12_67_base : receiptBase endpoint_12_67_flag endpoint_12_67_sources = some 247963878644826263 := by decide +kernel
private theorem endpoint_12_67_w0 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 2 247963878644826263 = some 255542155940367018 := by decide +kernel
private theorem endpoint_12_67_w2 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 2 2 255542155940367018 = some 255542155940367018 := by decide +kernel
private theorem endpoint_12_67_p4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 4 247963878644826263 = some 255542155940367018 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 2 2 247963878644826263 255542155940367018 255542155940367018 endpoint_12_67_w0 endpoint_12_67_w2
private theorem endpoint_12_67_w4 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 4 2 255542155940367018 = some 255542155940367018 := by decide +kernel
private theorem endpoint_12_67_p6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 6 247963878644826263 = some 255542155940367018 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 4 2 247963878644826263 255542155940367018 255542155940367018 endpoint_12_67_p4 endpoint_12_67_w4
private theorem endpoint_12_67_w6 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 6 2 255542155940367018 = some 255542155940367018 := by decide +kernel
private theorem endpoint_12_67_p8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 8 247963878644826263 = some 255542155940367018 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 6 2 247963878644826263 255542155940367018 255542155940367018 endpoint_12_67_p6 endpoint_12_67_w6
private theorem endpoint_12_67_w8 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 8 2 255542155940367018 = some 255542155940367018 := by decide +kernel
private theorem endpoint_12_67_p10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 10 247963878644826263 = some 255542155940367018 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 8 2 247963878644826263 255542155940367018 255542155940367018 endpoint_12_67_p8 endpoint_12_67_w8
private theorem endpoint_12_67_w10 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 10 1 255542155940367018 = some 255542155940367018 := by decide +kernel
private theorem endpoint_12_67_p11 : receiptWindow endpoint_12_67_flag endpoint_12_67_sources 0 11 247963878644826263 = some 255542155940367018 :=
  join_receipt_window endpoint_12_67_flag endpoint_12_67_sources 0 10 1 247963878644826263 255542155940367018 255542155940367018 endpoint_12_67_p10 endpoint_12_67_w10
def endpoint_12_67 : CertifiedEndpoint :=
  ⟨⟨12, 67, 2582⟩, 255542155940367018, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_12_67_flag endpoint_12_67_sources 11 247963878644826263 255542155940367018 rfl endpoint_12_67_base endpoint_12_67_p11) (by decide)⟩
private def endpoint_12_68_flag : Flag := ⟨12, 68, 2504⟩
private def endpoint_12_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_68_base : receiptBase endpoint_12_68_flag endpoint_12_68_sources = some 249314584023669036 := by decide +kernel
private theorem endpoint_12_68_w0 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 2 249314584023669036 = some 249314584023669036 := by decide +kernel
private theorem endpoint_12_68_w2 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 2 2 249314584023669036 = some 249314584023669036 := by decide +kernel
private theorem endpoint_12_68_p4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 4 249314584023669036 = some 249314584023669036 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 2 2 249314584023669036 249314584023669036 249314584023669036 endpoint_12_68_w0 endpoint_12_68_w2
private theorem endpoint_12_68_w4 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 4 2 249314584023669036 = some 249314584023669036 := by decide +kernel
private theorem endpoint_12_68_p6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 6 249314584023669036 = some 249314584023669036 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 4 2 249314584023669036 249314584023669036 249314584023669036 endpoint_12_68_p4 endpoint_12_68_w4
private theorem endpoint_12_68_w6 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 6 2 249314584023669036 = some 249314584023669036 := by decide +kernel
private theorem endpoint_12_68_p8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 8 249314584023669036 = some 249314584023669036 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 6 2 249314584023669036 249314584023669036 249314584023669036 endpoint_12_68_p6 endpoint_12_68_w6
private theorem endpoint_12_68_w8 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 8 2 249314584023669036 = some 249314584023669036 := by decide +kernel
private theorem endpoint_12_68_p10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 10 249314584023669036 = some 249314584023669036 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 8 2 249314584023669036 249314584023669036 249314584023669036 endpoint_12_68_p8 endpoint_12_68_w8
private theorem endpoint_12_68_w10 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 10 1 249314584023669036 = some 249314584023669036 := by decide +kernel
private theorem endpoint_12_68_p11 : receiptWindow endpoint_12_68_flag endpoint_12_68_sources 0 11 249314584023669036 = some 249314584023669036 :=
  join_receipt_window endpoint_12_68_flag endpoint_12_68_sources 0 10 1 249314584023669036 249314584023669036 249314584023669036 endpoint_12_68_p10 endpoint_12_68_w10
def endpoint_12_68 : CertifiedEndpoint :=
  ⟨⟨12, 68, 2504⟩, 249314584023669036, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_68_flag endpoint_12_68_sources 11 249314584023669036 249314584023669036 rfl endpoint_12_68_base endpoint_12_68_p11) (by decide)⟩
private def endpoint_12_69_flag : Flag := ⟨12, 69, 2424⟩
private def endpoint_12_69_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_69_base : receiptBase endpoint_12_69_flag endpoint_12_69_sources = some 244663129701125686 := by decide +kernel
private theorem endpoint_12_69_w0 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 2 244663129701125686 = some 244663129701125686 := by decide +kernel
private theorem endpoint_12_69_w2 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 2 2 244663129701125686 = some 244663129701125686 := by decide +kernel
private theorem endpoint_12_69_p4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 4 244663129701125686 = some 244663129701125686 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 2 2 244663129701125686 244663129701125686 244663129701125686 endpoint_12_69_w0 endpoint_12_69_w2
private theorem endpoint_12_69_w4 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 4 2 244663129701125686 = some 244663129701125686 := by decide +kernel
private theorem endpoint_12_69_p6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 6 244663129701125686 = some 244663129701125686 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 4 2 244663129701125686 244663129701125686 244663129701125686 endpoint_12_69_p4 endpoint_12_69_w4
private theorem endpoint_12_69_w6 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 6 2 244663129701125686 = some 244663129701125686 := by decide +kernel
private theorem endpoint_12_69_p8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 8 244663129701125686 = some 244663129701125686 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 6 2 244663129701125686 244663129701125686 244663129701125686 endpoint_12_69_p6 endpoint_12_69_w6
private theorem endpoint_12_69_w8 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 8 2 244663129701125686 = some 244663129701125686 := by decide +kernel
private theorem endpoint_12_69_p10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 10 244663129701125686 = some 244663129701125686 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 8 2 244663129701125686 244663129701125686 244663129701125686 endpoint_12_69_p8 endpoint_12_69_w8
private theorem endpoint_12_69_w10 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 10 1 244663129701125686 = some 244663129701125686 := by decide +kernel
private theorem endpoint_12_69_p11 : receiptWindow endpoint_12_69_flag endpoint_12_69_sources 0 11 244663129701125686 = some 244663129701125686 :=
  join_receipt_window endpoint_12_69_flag endpoint_12_69_sources 0 10 1 244663129701125686 244663129701125686 244663129701125686 endpoint_12_69_p10 endpoint_12_69_w10
def endpoint_12_69 : CertifiedEndpoint :=
  ⟨⟨12, 69, 2424⟩, 244663129701125686, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_69_flag endpoint_12_69_sources 11 244663129701125686 244663129701125686 rfl endpoint_12_69_base endpoint_12_69_p11) (by decide)⟩
private def endpoint_12_70_flag : Flag := ⟨12, 70, 2340⟩
private def endpoint_12_70_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_12_70_base : receiptBase endpoint_12_70_flag endpoint_12_70_sources = some 239407033628276823 := by decide +kernel
private theorem endpoint_12_70_w0 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 2 239407033628276823 = some 242107661671543326 := by decide +kernel
private theorem endpoint_12_70_w2 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 2 2 242107661671543326 = some 242107661671543326 := by decide +kernel
private theorem endpoint_12_70_p4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 4 239407033628276823 = some 242107661671543326 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 2 2 239407033628276823 242107661671543326 242107661671543326 endpoint_12_70_w0 endpoint_12_70_w2
private theorem endpoint_12_70_w4 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 4 2 242107661671543326 = some 242107661671543326 := by decide +kernel
private theorem endpoint_12_70_p6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 6 239407033628276823 = some 242107661671543326 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 4 2 239407033628276823 242107661671543326 242107661671543326 endpoint_12_70_p4 endpoint_12_70_w4
private theorem endpoint_12_70_w6 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 6 2 242107661671543326 = some 242107661671543326 := by decide +kernel
private theorem endpoint_12_70_p8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 8 239407033628276823 = some 242107661671543326 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 6 2 239407033628276823 242107661671543326 242107661671543326 endpoint_12_70_p6 endpoint_12_70_w6
private theorem endpoint_12_70_w8 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 8 2 242107661671543326 = some 242107661671543326 := by decide +kernel
private theorem endpoint_12_70_p10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 10 239407033628276823 = some 242107661671543326 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 8 2 239407033628276823 242107661671543326 242107661671543326 endpoint_12_70_p8 endpoint_12_70_w8
private theorem endpoint_12_70_w10 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 10 1 242107661671543326 = some 242107661671543326 := by decide +kernel
private theorem endpoint_12_70_p11 : receiptWindow endpoint_12_70_flag endpoint_12_70_sources 0 11 239407033628276823 = some 242107661671543326 :=
  join_receipt_window endpoint_12_70_flag endpoint_12_70_sources 0 10 1 239407033628276823 242107661671543326 242107661671543326 endpoint_12_70_p10 endpoint_12_70_w10
def endpoint_12_70 : CertifiedEndpoint :=
  ⟨⟨12, 70, 2340⟩, 242107661671543326, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_12_70_flag endpoint_12_70_sources 11 239407033628276823 242107661671543326 rfl endpoint_12_70_base endpoint_12_70_p11) (by decide)⟩
private def endpoint_12_71_flag : Flag := ⟨12, 71, 2253⟩
private def endpoint_12_71_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_12_71_base : receiptBase endpoint_12_71_flag endpoint_12_71_sources = some 235101671619945097 := by decide +kernel
private theorem endpoint_12_71_w0 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 2 235101671619945097 = some 235101671619945097 := by decide +kernel
private theorem endpoint_12_71_w2 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 2 2 235101671619945097 = some 235101671619945097 := by decide +kernel
private theorem endpoint_12_71_p4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 4 235101671619945097 = some 235101671619945097 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 2 2 235101671619945097 235101671619945097 235101671619945097 endpoint_12_71_w0 endpoint_12_71_w2
private theorem endpoint_12_71_w4 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 4 2 235101671619945097 = some 235101671619945097 := by decide +kernel
private theorem endpoint_12_71_p6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 6 235101671619945097 = some 235101671619945097 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 4 2 235101671619945097 235101671619945097 235101671619945097 endpoint_12_71_p4 endpoint_12_71_w4
private theorem endpoint_12_71_w6 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 6 2 235101671619945097 = some 235101671619945097 := by decide +kernel
private theorem endpoint_12_71_p8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 8 235101671619945097 = some 235101671619945097 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 6 2 235101671619945097 235101671619945097 235101671619945097 endpoint_12_71_p6 endpoint_12_71_w6
private theorem endpoint_12_71_w8 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 8 2 235101671619945097 = some 235101671619945097 := by decide +kernel
private theorem endpoint_12_71_p10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 10 235101671619945097 = some 235101671619945097 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 8 2 235101671619945097 235101671619945097 235101671619945097 endpoint_12_71_p8 endpoint_12_71_w8
private theorem endpoint_12_71_w10 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 10 1 235101671619945097 = some 235101671619945097 := by decide +kernel
private theorem endpoint_12_71_p11 : receiptWindow endpoint_12_71_flag endpoint_12_71_sources 0 11 235101671619945097 = some 235101671619945097 :=
  join_receipt_window endpoint_12_71_flag endpoint_12_71_sources 0 10 1 235101671619945097 235101671619945097 235101671619945097 endpoint_12_71_p10 endpoint_12_71_w10
def endpoint_12_71 : CertifiedEndpoint :=
  ⟨⟨12, 71, 2253⟩, 235101671619945097, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_12_71_flag endpoint_12_71_sources 11 235101671619945097 235101671619945097 rfl endpoint_12_71_base endpoint_12_71_p11) (by decide)⟩
private def endpoint_12_72_flag : Flag := ⟨12, 72, 2164⟩
private def endpoint_12_72_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_12_72_base : receiptBase endpoint_12_72_flag endpoint_12_72_sources = some 228853997429904286 := by decide +kernel
private theorem endpoint_12_72_w0 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 2 228853997429904286 = some 228853997429904286 := by decide +kernel
private theorem endpoint_12_72_w2 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 2 2 228853997429904286 = some 228853997429904286 := by decide +kernel
private theorem endpoint_12_72_p4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 4 228853997429904286 = some 228853997429904286 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 2 2 228853997429904286 228853997429904286 228853997429904286 endpoint_12_72_w0 endpoint_12_72_w2
private theorem endpoint_12_72_w4 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 4 2 228853997429904286 = some 228853997429904286 := by decide +kernel
private theorem endpoint_12_72_p6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 6 228853997429904286 = some 228853997429904286 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 4 2 228853997429904286 228853997429904286 228853997429904286 endpoint_12_72_p4 endpoint_12_72_w4
private theorem endpoint_12_72_w6 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 6 2 228853997429904286 = some 228853997429904286 := by decide +kernel
private theorem endpoint_12_72_p8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 8 228853997429904286 = some 228853997429904286 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 6 2 228853997429904286 228853997429904286 228853997429904286 endpoint_12_72_p6 endpoint_12_72_w6
private theorem endpoint_12_72_w8 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 8 2 228853997429904286 = some 228853997429904286 := by decide +kernel
private theorem endpoint_12_72_p10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 10 228853997429904286 = some 228853997429904286 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 8 2 228853997429904286 228853997429904286 228853997429904286 endpoint_12_72_p8 endpoint_12_72_w8
private theorem endpoint_12_72_w10 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 10 1 228853997429904286 = some 228853997429904286 := by decide +kernel
private theorem endpoint_12_72_p11 : receiptWindow endpoint_12_72_flag endpoint_12_72_sources 0 11 228853997429904286 = some 228853997429904286 :=
  join_receipt_window endpoint_12_72_flag endpoint_12_72_sources 0 10 1 228853997429904286 228853997429904286 228853997429904286 endpoint_12_72_p10 endpoint_12_72_w10
def endpoint_12_72 : CertifiedEndpoint :=
  ⟨⟨12, 72, 2164⟩, 228853997429904286, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_12_72_flag endpoint_12_72_sources 11 228853997429904286 228853997429904286 rfl endpoint_12_72_base endpoint_12_72_p11) (by decide)⟩
private def endpoint_12_73_flag : Flag := ⟨12, 73, 2071⟩
private def endpoint_12_73_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_73_base : receiptBase endpoint_12_73_flag endpoint_12_73_sources = some 223500069032347568 := by decide +kernel
private theorem endpoint_12_73_w0 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 2 223500069032347568 = some 223500069032347568 := by decide +kernel
private theorem endpoint_12_73_w2 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 2 2 223500069032347568 = some 223500069032347568 := by decide +kernel
private theorem endpoint_12_73_p4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 4 223500069032347568 = some 223500069032347568 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 2 2 223500069032347568 223500069032347568 223500069032347568 endpoint_12_73_w0 endpoint_12_73_w2
private theorem endpoint_12_73_w4 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 4 2 223500069032347568 = some 223500069032347568 := by decide +kernel
private theorem endpoint_12_73_p6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 6 223500069032347568 = some 223500069032347568 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 4 2 223500069032347568 223500069032347568 223500069032347568 endpoint_12_73_p4 endpoint_12_73_w4
private theorem endpoint_12_73_w6 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 6 2 223500069032347568 = some 223500069032347568 := by decide +kernel
private theorem endpoint_12_73_p8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 8 223500069032347568 = some 223500069032347568 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 6 2 223500069032347568 223500069032347568 223500069032347568 endpoint_12_73_p6 endpoint_12_73_w6
private theorem endpoint_12_73_w8 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 8 2 223500069032347568 = some 223500069032347568 := by decide +kernel
private theorem endpoint_12_73_p10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 10 223500069032347568 = some 223500069032347568 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 8 2 223500069032347568 223500069032347568 223500069032347568 endpoint_12_73_p8 endpoint_12_73_w8
private theorem endpoint_12_73_w10 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 10 1 223500069032347568 = some 223500069032347568 := by decide +kernel
private theorem endpoint_12_73_p11 : receiptWindow endpoint_12_73_flag endpoint_12_73_sources 0 11 223500069032347568 = some 223500069032347568 :=
  join_receipt_window endpoint_12_73_flag endpoint_12_73_sources 0 10 1 223500069032347568 223500069032347568 223500069032347568 endpoint_12_73_p10 endpoint_12_73_w10
def endpoint_12_73 : CertifiedEndpoint :=
  ⟨⟨12, 73, 2071⟩, 223500069032347568, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_73_flag endpoint_12_73_sources 11 223500069032347568 223500069032347568 rfl endpoint_12_73_base endpoint_12_73_p11) (by decide)⟩
private def endpoint_12_74_flag : Flag := ⟨12, 74, 1976⟩
private def endpoint_12_74_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_12_74_base : receiptBase endpoint_12_74_flag endpoint_12_74_sources = some 215979559754799618 := by decide +kernel
private theorem endpoint_12_74_w0 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 2 215979559754799618 = some 216517680388357832 := by decide +kernel
private theorem endpoint_12_74_w2 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 2 2 216517680388357832 = some 216517680388357832 := by decide +kernel
private theorem endpoint_12_74_p4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 4 215979559754799618 = some 216517680388357832 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 2 2 215979559754799618 216517680388357832 216517680388357832 endpoint_12_74_w0 endpoint_12_74_w2
private theorem endpoint_12_74_w4 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 4 2 216517680388357832 = some 216517680388357832 := by decide +kernel
private theorem endpoint_12_74_p6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 6 215979559754799618 = some 216517680388357832 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 4 2 215979559754799618 216517680388357832 216517680388357832 endpoint_12_74_p4 endpoint_12_74_w4
private theorem endpoint_12_74_w6 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 6 2 216517680388357832 = some 216517680388357832 := by decide +kernel
private theorem endpoint_12_74_p8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 8 215979559754799618 = some 216517680388357832 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 6 2 215979559754799618 216517680388357832 216517680388357832 endpoint_12_74_p6 endpoint_12_74_w6
private theorem endpoint_12_74_w8 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 8 2 216517680388357832 = some 216517680388357832 := by decide +kernel
private theorem endpoint_12_74_p10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 10 215979559754799618 = some 216517680388357832 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 8 2 215979559754799618 216517680388357832 216517680388357832 endpoint_12_74_p8 endpoint_12_74_w8
private theorem endpoint_12_74_w10 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 10 1 216517680388357832 = some 216517680388357832 := by decide +kernel
private theorem endpoint_12_74_p11 : receiptWindow endpoint_12_74_flag endpoint_12_74_sources 0 11 215979559754799618 = some 216517680388357832 :=
  join_receipt_window endpoint_12_74_flag endpoint_12_74_sources 0 10 1 215979559754799618 216517680388357832 216517680388357832 endpoint_12_74_p10 endpoint_12_74_w10
def endpoint_12_74 : CertifiedEndpoint :=
  ⟨⟨12, 74, 1976⟩, 216517680388357832, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_12_74_flag endpoint_12_74_sources 11 215979559754799618 216517680388357832 rfl endpoint_12_74_base endpoint_12_74_p11) (by decide)⟩
private def endpoint_12_75_flag : Flag := ⟨12, 75, 1877⟩
private def endpoint_12_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_75_base : receiptBase endpoint_12_75_flag endpoint_12_75_sources = some 209410769170387824 := by decide +kernel
private theorem endpoint_12_75_w0 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 2 209410769170387824 = some 209410769170387824 := by decide +kernel
private theorem endpoint_12_75_w2 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 2 2 209410769170387824 = some 209410769170387824 := by decide +kernel
private theorem endpoint_12_75_p4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 4 209410769170387824 = some 209410769170387824 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 2 2 209410769170387824 209410769170387824 209410769170387824 endpoint_12_75_w0 endpoint_12_75_w2
private theorem endpoint_12_75_w4 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 4 2 209410769170387824 = some 209410769170387824 := by decide +kernel
private theorem endpoint_12_75_p6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 6 209410769170387824 = some 209410769170387824 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 4 2 209410769170387824 209410769170387824 209410769170387824 endpoint_12_75_p4 endpoint_12_75_w4
private theorem endpoint_12_75_w6 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 6 2 209410769170387824 = some 209410769170387824 := by decide +kernel
private theorem endpoint_12_75_p8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 8 209410769170387824 = some 209410769170387824 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 6 2 209410769170387824 209410769170387824 209410769170387824 endpoint_12_75_p6 endpoint_12_75_w6
private theorem endpoint_12_75_w8 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 8 2 209410769170387824 = some 209410769170387824 := by decide +kernel
private theorem endpoint_12_75_p10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 10 209410769170387824 = some 209410769170387824 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 8 2 209410769170387824 209410769170387824 209410769170387824 endpoint_12_75_p8 endpoint_12_75_w8
private theorem endpoint_12_75_w10 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 10 1 209410769170387824 = some 209410769170387824 := by decide +kernel
private theorem endpoint_12_75_p11 : receiptWindow endpoint_12_75_flag endpoint_12_75_sources 0 11 209410769170387824 = some 209410769170387824 :=
  join_receipt_window endpoint_12_75_flag endpoint_12_75_sources 0 10 1 209410769170387824 209410769170387824 209410769170387824 endpoint_12_75_p10 endpoint_12_75_w10
def endpoint_12_75 : CertifiedEndpoint :=
  ⟨⟨12, 75, 1877⟩, 209410769170387824, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_75_flag endpoint_12_75_sources 11 209410769170387824 209410769170387824 rfl endpoint_12_75_base endpoint_12_75_p11) (by decide)⟩
private def endpoint_12_76_flag : Flag := ⟨12, 76, 1775⟩
private def endpoint_12_76_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_76_base : receiptBase endpoint_12_76_flag endpoint_12_76_sources = some 200500659648089891 := by decide +kernel
private theorem endpoint_12_76_w0 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 2 200500659648089891 = some 200500659648089891 := by decide +kernel
private theorem endpoint_12_76_w2 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 2 2 200500659648089891 = some 200500659648089891 := by decide +kernel
private theorem endpoint_12_76_p4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 4 200500659648089891 = some 200500659648089891 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 2 2 200500659648089891 200500659648089891 200500659648089891 endpoint_12_76_w0 endpoint_12_76_w2
private theorem endpoint_12_76_w4 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 4 2 200500659648089891 = some 200500659648089891 := by decide +kernel
private theorem endpoint_12_76_p6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 6 200500659648089891 = some 200500659648089891 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 4 2 200500659648089891 200500659648089891 200500659648089891 endpoint_12_76_p4 endpoint_12_76_w4
private theorem endpoint_12_76_w6 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 6 2 200500659648089891 = some 200500659648089891 := by decide +kernel
private theorem endpoint_12_76_p8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 8 200500659648089891 = some 200500659648089891 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 6 2 200500659648089891 200500659648089891 200500659648089891 endpoint_12_76_p6 endpoint_12_76_w6
private theorem endpoint_12_76_w8 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 8 2 200500659648089891 = some 200500659648089891 := by decide +kernel
private theorem endpoint_12_76_p10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 10 200500659648089891 = some 200500659648089891 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 8 2 200500659648089891 200500659648089891 200500659648089891 endpoint_12_76_p8 endpoint_12_76_w8
private theorem endpoint_12_76_w10 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 10 1 200500659648089891 = some 200500659648089891 := by decide +kernel
private theorem endpoint_12_76_p11 : receiptWindow endpoint_12_76_flag endpoint_12_76_sources 0 11 200500659648089891 = some 200500659648089891 :=
  join_receipt_window endpoint_12_76_flag endpoint_12_76_sources 0 10 1 200500659648089891 200500659648089891 200500659648089891 endpoint_12_76_p10 endpoint_12_76_w10
def endpoint_12_76 : CertifiedEndpoint :=
  ⟨⟨12, 76, 1775⟩, 200500659648089891, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_76_flag endpoint_12_76_sources 11 200500659648089891 200500659648089891 rfl endpoint_12_76_base endpoint_12_76_p11) (by decide)⟩
private def endpoint_12_77_flag : Flag := ⟨12, 77, 1670⟩
private def endpoint_12_77_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_12_77_base : receiptBase endpoint_12_77_flag endpoint_12_77_sources = some 190981213178982309 := by decide +kernel
private theorem endpoint_12_77_w0 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 2 190981213178982309 = some 192111766517586591 := by decide +kernel
private theorem endpoint_12_77_w2 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 2 2 192111766517586591 = some 192111766517586591 := by decide +kernel
private theorem endpoint_12_77_p4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 4 190981213178982309 = some 192111766517586591 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 2 2 190981213178982309 192111766517586591 192111766517586591 endpoint_12_77_w0 endpoint_12_77_w2
private theorem endpoint_12_77_w4 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 4 2 192111766517586591 = some 192111766517586591 := by decide +kernel
private theorem endpoint_12_77_p6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 6 190981213178982309 = some 192111766517586591 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 4 2 190981213178982309 192111766517586591 192111766517586591 endpoint_12_77_p4 endpoint_12_77_w4
private theorem endpoint_12_77_w6 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 6 2 192111766517586591 = some 192111766517586591 := by decide +kernel
private theorem endpoint_12_77_p8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 8 190981213178982309 = some 192111766517586591 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 6 2 190981213178982309 192111766517586591 192111766517586591 endpoint_12_77_p6 endpoint_12_77_w6
private theorem endpoint_12_77_w8 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 8 2 192111766517586591 = some 192111766517586591 := by decide +kernel
private theorem endpoint_12_77_p10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 10 190981213178982309 = some 192111766517586591 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 8 2 190981213178982309 192111766517586591 192111766517586591 endpoint_12_77_p8 endpoint_12_77_w8
private theorem endpoint_12_77_w10 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 10 1 192111766517586591 = some 192111766517586591 := by decide +kernel
private theorem endpoint_12_77_p11 : receiptWindow endpoint_12_77_flag endpoint_12_77_sources 0 11 190981213178982309 = some 192111766517586591 :=
  join_receipt_window endpoint_12_77_flag endpoint_12_77_sources 0 10 1 190981213178982309 192111766517586591 192111766517586591 endpoint_12_77_p10 endpoint_12_77_w10
def endpoint_12_77 : CertifiedEndpoint :=
  ⟨⟨12, 77, 1670⟩, 192111766517586591, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_12_77_flag endpoint_12_77_sources 11 190981213178982309 192111766517586591 rfl endpoint_12_77_base endpoint_12_77_p11) (by decide)⟩
private def endpoint_12_78_flag : Flag := ⟨12, 78, 1562⟩
private def endpoint_12_78_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_78_base : receiptBase endpoint_12_78_flag endpoint_12_78_sources = some 183845111533471144 := by decide +kernel
private theorem endpoint_12_78_w0 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 2 183845111533471144 = some 183845111533471144 := by decide +kernel
private theorem endpoint_12_78_w2 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 2 2 183845111533471144 = some 183845111533471144 := by decide +kernel
private theorem endpoint_12_78_p4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 4 183845111533471144 = some 183845111533471144 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 2 2 183845111533471144 183845111533471144 183845111533471144 endpoint_12_78_w0 endpoint_12_78_w2
private theorem endpoint_12_78_w4 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 4 2 183845111533471144 = some 183845111533471144 := by decide +kernel
private theorem endpoint_12_78_p6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 6 183845111533471144 = some 183845111533471144 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 4 2 183845111533471144 183845111533471144 183845111533471144 endpoint_12_78_p4 endpoint_12_78_w4
private theorem endpoint_12_78_w6 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 6 2 183845111533471144 = some 183845111533471144 := by decide +kernel
private theorem endpoint_12_78_p8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 8 183845111533471144 = some 183845111533471144 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 6 2 183845111533471144 183845111533471144 183845111533471144 endpoint_12_78_p6 endpoint_12_78_w6
private theorem endpoint_12_78_w8 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 8 2 183845111533471144 = some 183845111533471144 := by decide +kernel
private theorem endpoint_12_78_p10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 10 183845111533471144 = some 183845111533471144 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 8 2 183845111533471144 183845111533471144 183845111533471144 endpoint_12_78_p8 endpoint_12_78_w8
private theorem endpoint_12_78_w10 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 10 1 183845111533471144 = some 183845111533471144 := by decide +kernel
private theorem endpoint_12_78_p11 : receiptWindow endpoint_12_78_flag endpoint_12_78_sources 0 11 183845111533471144 = some 183845111533471144 :=
  join_receipt_window endpoint_12_78_flag endpoint_12_78_sources 0 10 1 183845111533471144 183845111533471144 183845111533471144 endpoint_12_78_p10 endpoint_12_78_w10
def endpoint_12_78 : CertifiedEndpoint :=
  ⟨⟨12, 78, 1562⟩, 183845111533471144, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_78_flag endpoint_12_78_sources 11 183845111533471144 183845111533471144 rfl endpoint_12_78_base endpoint_12_78_p11) (by decide)⟩
private def endpoint_12_79_flag : Flag := ⟨12, 79, 1451⟩
private def endpoint_12_79_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_12_79_base : receiptBase endpoint_12_79_flag endpoint_12_79_sources = some 172819398726523099 := by decide +kernel
private theorem endpoint_12_79_w0 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 2 172819398726523099 = some 172819398726523099 := by decide +kernel
private theorem endpoint_12_79_w2 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 2 2 172819398726523099 = some 172819398726523099 := by decide +kernel
private theorem endpoint_12_79_p4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 4 172819398726523099 = some 172819398726523099 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 2 2 172819398726523099 172819398726523099 172819398726523099 endpoint_12_79_w0 endpoint_12_79_w2
private theorem endpoint_12_79_w4 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 4 2 172819398726523099 = some 172819398726523099 := by decide +kernel
private theorem endpoint_12_79_p6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 6 172819398726523099 = some 172819398726523099 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 4 2 172819398726523099 172819398726523099 172819398726523099 endpoint_12_79_p4 endpoint_12_79_w4
private theorem endpoint_12_79_w6 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 6 2 172819398726523099 = some 172819398726523099 := by decide +kernel
private theorem endpoint_12_79_p8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 8 172819398726523099 = some 172819398726523099 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 6 2 172819398726523099 172819398726523099 172819398726523099 endpoint_12_79_p6 endpoint_12_79_w6
private theorem endpoint_12_79_w8 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 8 2 172819398726523099 = some 172819398726523099 := by decide +kernel
private theorem endpoint_12_79_p10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 10 172819398726523099 = some 172819398726523099 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 8 2 172819398726523099 172819398726523099 172819398726523099 endpoint_12_79_p8 endpoint_12_79_w8
private theorem endpoint_12_79_w10 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 10 1 172819398726523099 = some 172819398726523099 := by decide +kernel
private theorem endpoint_12_79_p11 : receiptWindow endpoint_12_79_flag endpoint_12_79_sources 0 11 172819398726523099 = some 172819398726523099 :=
  join_receipt_window endpoint_12_79_flag endpoint_12_79_sources 0 10 1 172819398726523099 172819398726523099 172819398726523099 endpoint_12_79_p10 endpoint_12_79_w10
def endpoint_12_79 : CertifiedEndpoint :=
  ⟨⟨12, 79, 1451⟩, 172819398726523099, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_12_79_flag endpoint_12_79_sources 11 172819398726523099 172819398726523099 rfl endpoint_12_79_base endpoint_12_79_p11) (by decide)⟩
private def endpoint_12_80_flag : Flag := ⟨12, 80, 1337⟩
private def endpoint_12_80_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_12_80_base : receiptBase endpoint_12_80_flag endpoint_12_80_sources = some 161524080509230742 := by decide +kernel
private theorem endpoint_12_80_w0 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 2 161524080509230742 = some 161524080509230742 := by decide +kernel
private theorem endpoint_12_80_w2 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 2 2 161524080509230742 = some 161524080509230742 := by decide +kernel
private theorem endpoint_12_80_p4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 4 161524080509230742 = some 161524080509230742 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 2 2 161524080509230742 161524080509230742 161524080509230742 endpoint_12_80_w0 endpoint_12_80_w2
private theorem endpoint_12_80_w4 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 4 2 161524080509230742 = some 161524080509230742 := by decide +kernel
private theorem endpoint_12_80_p6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 6 161524080509230742 = some 161524080509230742 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 4 2 161524080509230742 161524080509230742 161524080509230742 endpoint_12_80_p4 endpoint_12_80_w4
private theorem endpoint_12_80_w6 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 6 2 161524080509230742 = some 161524080509230742 := by decide +kernel
private theorem endpoint_12_80_p8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 8 161524080509230742 = some 161524080509230742 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 6 2 161524080509230742 161524080509230742 161524080509230742 endpoint_12_80_p6 endpoint_12_80_w6
private theorem endpoint_12_80_w8 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 8 2 161524080509230742 = some 161524080509230742 := by decide +kernel
private theorem endpoint_12_80_p10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 10 161524080509230742 = some 161524080509230742 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 8 2 161524080509230742 161524080509230742 161524080509230742 endpoint_12_80_p8 endpoint_12_80_w8
private theorem endpoint_12_80_w10 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 10 1 161524080509230742 = some 161524080509230742 := by decide +kernel
private theorem endpoint_12_80_p11 : receiptWindow endpoint_12_80_flag endpoint_12_80_sources 0 11 161524080509230742 = some 161524080509230742 :=
  join_receipt_window endpoint_12_80_flag endpoint_12_80_sources 0 10 1 161524080509230742 161524080509230742 161524080509230742 endpoint_12_80_p10 endpoint_12_80_w10
def endpoint_12_80 : CertifiedEndpoint :=
  ⟨⟨12, 80, 1337⟩, 161524080509230742, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_12_80_flag endpoint_12_80_sources 11 161524080509230742 161524080509230742 rfl endpoint_12_80_base endpoint_12_80_p11) (by decide)⟩
def endpoint_12_81 : CertifiedEndpoint :=
  ⟨⟨12, 81, 1220⟩, 260481914896136681, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_82 : CertifiedEndpoint :=
  ⟨⟨12, 82, 1100⟩, 236936663628102920, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_83 : CertifiedEndpoint :=
  ⟨⟨12, 83, 977⟩, 211992970300823466, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_84 : CertifiedEndpoint :=
  ⟨⟨12, 84, 850⟩, 185393731709875366, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_85 : CertifiedEndpoint :=
  ⟨⟨12, 85, 721⟩, 157569932896865894, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock08 : List CertifiedEndpoint := [
  endpoint_11_46, endpoint_11_47, endpoint_11_48, endpoint_11_49, endpoint_11_50, endpoint_11_51, endpoint_11_52,
  endpoint_11_53, endpoint_11_54, endpoint_11_55, endpoint_11_56, endpoint_11_57, endpoint_11_58, endpoint_11_59,
  endpoint_11_60, endpoint_11_61, endpoint_11_62, endpoint_11_63, endpoint_11_64, endpoint_11_65, endpoint_11_66,
  endpoint_11_67, endpoint_11_68, endpoint_11_69, endpoint_11_70, endpoint_11_71, endpoint_11_72, endpoint_11_73,
  endpoint_11_74, endpoint_11_75, endpoint_11_76, endpoint_11_77, endpoint_11_78, endpoint_11_79, endpoint_11_80,
  endpoint_11_81, endpoint_11_82, endpoint_11_83, endpoint_11_84, endpoint_11_85, endpoint_11_86, endpoint_11_87,
  endpoint_11_88, endpoint_11_89, endpoint_11_90, endpoint_11_91, endpoint_12_12, endpoint_12_13, endpoint_12_14,
  endpoint_12_15, endpoint_12_16, endpoint_12_17, endpoint_12_18, endpoint_12_19, endpoint_12_20, endpoint_12_21,
  endpoint_12_22, endpoint_12_23, endpoint_12_24, endpoint_12_25, endpoint_12_26, endpoint_12_27, endpoint_12_28,
  endpoint_12_29, endpoint_12_30, endpoint_12_31, endpoint_12_32, endpoint_12_33, endpoint_12_34, endpoint_12_35,
  endpoint_12_36, endpoint_12_37, endpoint_12_38, endpoint_12_39, endpoint_12_40, endpoint_12_41, endpoint_12_42,
  endpoint_12_43, endpoint_12_44, endpoint_12_45, endpoint_12_46, endpoint_12_47, endpoint_12_48, endpoint_12_49,
  endpoint_12_50, endpoint_12_51, endpoint_12_52, endpoint_12_53, endpoint_12_54, endpoint_12_55, endpoint_12_56,
  endpoint_12_57, endpoint_12_58, endpoint_12_59, endpoint_12_60, endpoint_12_61, endpoint_12_62, endpoint_12_63,
  endpoint_12_64, endpoint_12_65, endpoint_12_66, endpoint_12_67, endpoint_12_68, endpoint_12_69, endpoint_12_70,
  endpoint_12_71, endpoint_12_72, endpoint_12_73, endpoint_12_74, endpoint_12_75, endpoint_12_76, endpoint_12_77,
  endpoint_12_78, endpoint_12_79, endpoint_12_80, endpoint_12_81, endpoint_12_82, endpoint_12_83, endpoint_12_84,
  endpoint_12_85
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
