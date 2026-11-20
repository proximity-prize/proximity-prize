import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_10_18 : CertifiedEndpoint :=
  ⟨⟨10, 18, 4775⟩, 146328775098210125, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_19 : CertifiedEndpoint :=
  ⟨⟨10, 19, 4752⟩, 157251434232698217, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_20 : CertifiedEndpoint :=
  ⟨⟨10, 20, 4729⟩, 168058624564842579, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_21 : CertifiedEndpoint :=
  ⟨⟨10, 21, 4706⟩, 178750346094643211, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_22 : CertifiedEndpoint :=
  ⟨⟨10, 22, 4682⟩, 189286053284275202, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_23 : CertifiedEndpoint :=
  ⟨⟨10, 23, 4658⟩, 199701378105506283, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_24 : CertifiedEndpoint :=
  ⟨⟨10, 24, 4634⟩, 209996320558336454, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_25 : CertifiedEndpoint :=
  ⟨⟨10, 25, 4610⟩, 220170880642765715, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_26 : CertifiedEndpoint :=
  ⟨⟨10, 26, 4585⟩, 230174685688854795, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_27 : CertifiedEndpoint :=
  ⟨⟨10, 27, 4560⟩, 240053194800485785, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_28 : CertifiedEndpoint :=
  ⟨⟨10, 28, 4535⟩, 249806407977658685, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_29 : CertifiedEndpoint :=
  ⟨⟨10, 29, 4509⟩, 259376582201348454, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_10_30_flag : Flag := ⟨10, 30, 4484⟩
private def endpoint_10_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_30_base : receiptBase endpoint_10_30_flag endpoint_10_30_sources = some 184292071296374813 := by decide +kernel
private theorem endpoint_10_30_w0 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 0 2 184292071296374813 = some 184292071296374813 := by decide +kernel
private theorem endpoint_10_30_w2 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 2 2 184292071296374813 = some 184292071296374813 := by decide +kernel
private theorem endpoint_10_30_p4 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 0 4 184292071296374813 = some 184292071296374813 :=
  join_receipt_window endpoint_10_30_flag endpoint_10_30_sources 0 2 2 184292071296374813 184292071296374813 184292071296374813 endpoint_10_30_w0 endpoint_10_30_w2
private theorem endpoint_10_30_w4 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 4 2 184292071296374813 = some 184292071296374813 := by decide +kernel
private theorem endpoint_10_30_p6 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 0 6 184292071296374813 = some 184292071296374813 :=
  join_receipt_window endpoint_10_30_flag endpoint_10_30_sources 0 4 2 184292071296374813 184292071296374813 184292071296374813 endpoint_10_30_p4 endpoint_10_30_w4
private theorem endpoint_10_30_w6 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 6 2 184292071296374813 = some 184292071296374813 := by decide +kernel
private theorem endpoint_10_30_p8 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 0 8 184292071296374813 = some 184292071296374813 :=
  join_receipt_window endpoint_10_30_flag endpoint_10_30_sources 0 6 2 184292071296374813 184292071296374813 184292071296374813 endpoint_10_30_p6 endpoint_10_30_w6
private theorem endpoint_10_30_w8 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 8 1 184292071296374813 = some 184292071296374813 := by decide +kernel
private theorem endpoint_10_30_p9 : receiptWindow endpoint_10_30_flag endpoint_10_30_sources 0 9 184292071296374813 = some 184292071296374813 :=
  join_receipt_window endpoint_10_30_flag endpoint_10_30_sources 0 8 1 184292071296374813 184292071296374813 184292071296374813 endpoint_10_30_p8 endpoint_10_30_w8
def endpoint_10_30 : CertifiedEndpoint :=
  ⟨⟨10, 30, 4484⟩, 184292071296374813, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_30_flag endpoint_10_30_sources 9 184292071296374813 184292071296374813 rfl endpoint_10_30_base endpoint_10_30_p9) (by decide)⟩
private def endpoint_10_31_flag : Flag := ⟨10, 31, 4457⟩
private def endpoint_10_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_31_base : receiptBase endpoint_10_31_flag endpoint_10_31_sources = some 188107840634227854 := by decide +kernel
private theorem endpoint_10_31_w0 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 2 188107840634227854 = some 188107840634227854 := by decide +kernel
private theorem endpoint_10_31_w2 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 2 2 188107840634227854 = some 188107840634227854 := by decide +kernel
private theorem endpoint_10_31_p4 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 4 188107840634227854 = some 188107840634227854 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 2 2 188107840634227854 188107840634227854 188107840634227854 endpoint_10_31_w0 endpoint_10_31_w2
private theorem endpoint_10_31_w4 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 4 2 188107840634227854 = some 188107840634227854 := by decide +kernel
private theorem endpoint_10_31_p6 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 6 188107840634227854 = some 188107840634227854 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 4 2 188107840634227854 188107840634227854 188107840634227854 endpoint_10_31_p4 endpoint_10_31_w4
private theorem endpoint_10_31_w6 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 6 2 188107840634227854 = some 188107840634227854 := by decide +kernel
private theorem endpoint_10_31_p8 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 8 188107840634227854 = some 188107840634227854 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 6 2 188107840634227854 188107840634227854 188107840634227854 endpoint_10_31_p6 endpoint_10_31_w6
private theorem endpoint_10_31_w8 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 8 1 188107840634227854 = some 188107840634227854 := by decide +kernel
private theorem endpoint_10_31_p9 : receiptWindow endpoint_10_31_flag endpoint_10_31_sources 0 9 188107840634227854 = some 188107840634227854 :=
  join_receipt_window endpoint_10_31_flag endpoint_10_31_sources 0 8 1 188107840634227854 188107840634227854 188107840634227854 endpoint_10_31_p8 endpoint_10_31_w8
def endpoint_10_31 : CertifiedEndpoint :=
  ⟨⟨10, 31, 4457⟩, 188107840634227854, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_31_flag endpoint_10_31_sources 9 188107840634227854 188107840634227854 rfl endpoint_10_31_base endpoint_10_31_p9) (by decide)⟩
private def endpoint_10_32_flag : Flag := ⟨10, 32, 4431⟩
private def endpoint_10_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_32_base : receiptBase endpoint_10_32_flag endpoint_10_32_sources = some 191906765607202706 := by decide +kernel
private theorem endpoint_10_32_w0 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 2 191906765607202706 = some 191906765607202706 := by decide +kernel
private theorem endpoint_10_32_w2 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 2 2 191906765607202706 = some 191906765607202706 := by decide +kernel
private theorem endpoint_10_32_p4 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 4 191906765607202706 = some 191906765607202706 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 2 2 191906765607202706 191906765607202706 191906765607202706 endpoint_10_32_w0 endpoint_10_32_w2
private theorem endpoint_10_32_w4 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 4 2 191906765607202706 = some 191906765607202706 := by decide +kernel
private theorem endpoint_10_32_p6 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 6 191906765607202706 = some 191906765607202706 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 4 2 191906765607202706 191906765607202706 191906765607202706 endpoint_10_32_p4 endpoint_10_32_w4
private theorem endpoint_10_32_w6 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 6 2 191906765607202706 = some 191906765607202706 := by decide +kernel
private theorem endpoint_10_32_p8 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 8 191906765607202706 = some 191906765607202706 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 6 2 191906765607202706 191906765607202706 191906765607202706 endpoint_10_32_p6 endpoint_10_32_w6
private theorem endpoint_10_32_w8 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 8 1 191906765607202706 = some 191906765607202706 := by decide +kernel
private theorem endpoint_10_32_p9 : receiptWindow endpoint_10_32_flag endpoint_10_32_sources 0 9 191906765607202706 = some 191906765607202706 :=
  join_receipt_window endpoint_10_32_flag endpoint_10_32_sources 0 8 1 191906765607202706 191906765607202706 191906765607202706 endpoint_10_32_p8 endpoint_10_32_w8
def endpoint_10_32 : CertifiedEndpoint :=
  ⟨⟨10, 32, 4431⟩, 191906765607202706, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_32_flag endpoint_10_32_sources 9 191906765607202706 191906765607202706 rfl endpoint_10_32_base endpoint_10_32_p9) (by decide)⟩
private def endpoint_10_33_flag : Flag := ⟨10, 33, 4404⟩
private def endpoint_10_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_33_base : receiptBase endpoint_10_33_flag endpoint_10_33_sources = some 195604400148463355 := by decide +kernel
private theorem endpoint_10_33_w0 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 2 195604400148463355 = some 195604400148463355 := by decide +kernel
private theorem endpoint_10_33_w2 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 2 2 195604400148463355 = some 195604400148463355 := by decide +kernel
private theorem endpoint_10_33_p4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 4 195604400148463355 = some 195604400148463355 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 2 2 195604400148463355 195604400148463355 195604400148463355 endpoint_10_33_w0 endpoint_10_33_w2
private theorem endpoint_10_33_w4 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 4 2 195604400148463355 = some 195604400148463355 := by decide +kernel
private theorem endpoint_10_33_p6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 6 195604400148463355 = some 195604400148463355 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 4 2 195604400148463355 195604400148463355 195604400148463355 endpoint_10_33_p4 endpoint_10_33_w4
private theorem endpoint_10_33_w6 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 6 2 195604400148463355 = some 195604400148463355 := by decide +kernel
private theorem endpoint_10_33_p8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 8 195604400148463355 = some 195604400148463355 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 6 2 195604400148463355 195604400148463355 195604400148463355 endpoint_10_33_p6 endpoint_10_33_w6
private theorem endpoint_10_33_w8 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 8 1 195604400148463355 = some 195604400148463355 := by decide +kernel
private theorem endpoint_10_33_p9 : receiptWindow endpoint_10_33_flag endpoint_10_33_sources 0 9 195604400148463355 = some 195604400148463355 :=
  join_receipt_window endpoint_10_33_flag endpoint_10_33_sources 0 8 1 195604400148463355 195604400148463355 195604400148463355 endpoint_10_33_p8 endpoint_10_33_w8
def endpoint_10_33 : CertifiedEndpoint :=
  ⟨⟨10, 33, 4404⟩, 195604400148463355, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_33_flag endpoint_10_33_sources 9 195604400148463355 195604400148463355 rfl endpoint_10_33_base endpoint_10_33_p9) (by decide)⟩
private def endpoint_10_34_flag : Flag := ⟨10, 34, 4377⟩
private def endpoint_10_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_34_base : receiptBase endpoint_10_34_flag endpoint_10_34_sources = some 199242425429971924 := by decide +kernel
private theorem endpoint_10_34_w0 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 2 199242425429971924 = some 199242425429971924 := by decide +kernel
private theorem endpoint_10_34_w2 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 2 2 199242425429971924 = some 199242425429971924 := by decide +kernel
private theorem endpoint_10_34_p4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 4 199242425429971924 = some 199242425429971924 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 2 2 199242425429971924 199242425429971924 199242425429971924 endpoint_10_34_w0 endpoint_10_34_w2
private theorem endpoint_10_34_w4 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 4 2 199242425429971924 = some 199242425429971924 := by decide +kernel
private theorem endpoint_10_34_p6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 6 199242425429971924 = some 199242425429971924 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 4 2 199242425429971924 199242425429971924 199242425429971924 endpoint_10_34_p4 endpoint_10_34_w4
private theorem endpoint_10_34_w6 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 6 2 199242425429971924 = some 199242425429971924 := by decide +kernel
private theorem endpoint_10_34_p8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 8 199242425429971924 = some 199242425429971924 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 6 2 199242425429971924 199242425429971924 199242425429971924 endpoint_10_34_p6 endpoint_10_34_w6
private theorem endpoint_10_34_w8 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 8 1 199242425429971924 = some 199242425429971924 := by decide +kernel
private theorem endpoint_10_34_p9 : receiptWindow endpoint_10_34_flag endpoint_10_34_sources 0 9 199242425429971924 = some 199242425429971924 :=
  join_receipt_window endpoint_10_34_flag endpoint_10_34_sources 0 8 1 199242425429971924 199242425429971924 199242425429971924 endpoint_10_34_p8 endpoint_10_34_w8
def endpoint_10_34 : CertifiedEndpoint :=
  ⟨⟨10, 34, 4377⟩, 199242425429971924, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_34_flag endpoint_10_34_sources 9 199242425429971924 199242425429971924 rfl endpoint_10_34_base endpoint_10_34_p9) (by decide)⟩
private def endpoint_10_35_flag : Flag := ⟨10, 35, 4349⟩
private def endpoint_10_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_35_base : receiptBase endpoint_10_35_flag endpoint_10_35_sources = some 202774825388119231 := by decide +kernel
private theorem endpoint_10_35_w0 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 2 202774825388119231 = some 202774825388119231 := by decide +kernel
private theorem endpoint_10_35_w2 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 2 2 202774825388119231 = some 202774825388119231 := by decide +kernel
private theorem endpoint_10_35_p4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 4 202774825388119231 = some 202774825388119231 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 2 2 202774825388119231 202774825388119231 202774825388119231 endpoint_10_35_w0 endpoint_10_35_w2
private theorem endpoint_10_35_w4 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 4 2 202774825388119231 = some 202774825388119231 := by decide +kernel
private theorem endpoint_10_35_p6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 6 202774825388119231 = some 202774825388119231 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 4 2 202774825388119231 202774825388119231 202774825388119231 endpoint_10_35_p4 endpoint_10_35_w4
private theorem endpoint_10_35_w6 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 6 2 202774825388119231 = some 202774825388119231 := by decide +kernel
private theorem endpoint_10_35_p8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 8 202774825388119231 = some 202774825388119231 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 6 2 202774825388119231 202774825388119231 202774825388119231 endpoint_10_35_p6 endpoint_10_35_w6
private theorem endpoint_10_35_w8 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 8 1 202774825388119231 = some 202774825388119231 := by decide +kernel
private theorem endpoint_10_35_p9 : receiptWindow endpoint_10_35_flag endpoint_10_35_sources 0 9 202774825388119231 = some 202774825388119231 :=
  join_receipt_window endpoint_10_35_flag endpoint_10_35_sources 0 8 1 202774825388119231 202774825388119231 202774825388119231 endpoint_10_35_p8 endpoint_10_35_w8
def endpoint_10_35 : CertifiedEndpoint :=
  ⟨⟨10, 35, 4349⟩, 202774825388119231, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_35_flag endpoint_10_35_sources 9 202774825388119231 202774825388119231 rfl endpoint_10_35_base endpoint_10_35_p9) (by decide)⟩
private def endpoint_10_36_flag : Flag := ⟨10, 36, 4321⟩
private def endpoint_10_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_36_base : receiptBase endpoint_10_36_flag endpoint_10_36_sources = some 206245448640690929 := by decide +kernel
private theorem endpoint_10_36_w0 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 2 206245448640690929 = some 206245448640690929 := by decide +kernel
private theorem endpoint_10_36_w2 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 2 2 206245448640690929 = some 206245448640690929 := by decide +kernel
private theorem endpoint_10_36_p4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 4 206245448640690929 = some 206245448640690929 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 2 2 206245448640690929 206245448640690929 206245448640690929 endpoint_10_36_w0 endpoint_10_36_w2
private theorem endpoint_10_36_w4 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 4 2 206245448640690929 = some 206245448640690929 := by decide +kernel
private theorem endpoint_10_36_p6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 6 206245448640690929 = some 206245448640690929 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 4 2 206245448640690929 206245448640690929 206245448640690929 endpoint_10_36_p4 endpoint_10_36_w4
private theorem endpoint_10_36_w6 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 6 2 206245448640690929 = some 206245448640690929 := by decide +kernel
private theorem endpoint_10_36_p8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 8 206245448640690929 = some 206245448640690929 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 6 2 206245448640690929 206245448640690929 206245448640690929 endpoint_10_36_p6 endpoint_10_36_w6
private theorem endpoint_10_36_w8 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 8 1 206245448640690929 = some 206245448640690929 := by decide +kernel
private theorem endpoint_10_36_p9 : receiptWindow endpoint_10_36_flag endpoint_10_36_sources 0 9 206245448640690929 = some 206245448640690929 :=
  join_receipt_window endpoint_10_36_flag endpoint_10_36_sources 0 8 1 206245448640690929 206245448640690929 206245448640690929 endpoint_10_36_p8 endpoint_10_36_w8
def endpoint_10_36 : CertifiedEndpoint :=
  ⟨⟨10, 36, 4321⟩, 206245448640690929, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_36_flag endpoint_10_36_sources 9 206245448640690929 206245448640690929 rfl endpoint_10_36_base endpoint_10_36_p9) (by decide)⟩
private def endpoint_10_37_flag : Flag := ⟨10, 37, 4293⟩
private def endpoint_10_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_37_base : receiptBase endpoint_10_37_flag endpoint_10_37_sources = some 209654295187687019 := by decide +kernel
private theorem endpoint_10_37_w0 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 2 209654295187687019 = some 209654295187687019 := by decide +kernel
private theorem endpoint_10_37_w2 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 2 2 209654295187687019 = some 209654295187687019 := by decide +kernel
private theorem endpoint_10_37_p4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 4 209654295187687019 = some 209654295187687019 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 2 2 209654295187687019 209654295187687019 209654295187687019 endpoint_10_37_w0 endpoint_10_37_w2
private theorem endpoint_10_37_w4 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 4 2 209654295187687019 = some 209654295187687019 := by decide +kernel
private theorem endpoint_10_37_p6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 6 209654295187687019 = some 209654295187687019 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 4 2 209654295187687019 209654295187687019 209654295187687019 endpoint_10_37_p4 endpoint_10_37_w4
private theorem endpoint_10_37_w6 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 6 2 209654295187687019 = some 209654295187687019 := by decide +kernel
private theorem endpoint_10_37_p8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 8 209654295187687019 = some 209654295187687019 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 6 2 209654295187687019 209654295187687019 209654295187687019 endpoint_10_37_p6 endpoint_10_37_w6
private theorem endpoint_10_37_w8 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 8 1 209654295187687019 = some 209654295187687019 := by decide +kernel
private theorem endpoint_10_37_p9 : receiptWindow endpoint_10_37_flag endpoint_10_37_sources 0 9 209654295187687019 = some 209654295187687019 :=
  join_receipt_window endpoint_10_37_flag endpoint_10_37_sources 0 8 1 209654295187687019 209654295187687019 209654295187687019 endpoint_10_37_p8 endpoint_10_37_w8
def endpoint_10_37 : CertifiedEndpoint :=
  ⟨⟨10, 37, 4293⟩, 209654295187687019, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_37_flag endpoint_10_37_sources 9 209654295187687019 209654295187687019 rfl endpoint_10_37_base endpoint_10_37_p9) (by decide)⟩
private def endpoint_10_38_flag : Flag := ⟨10, 38, 4264⟩
private def endpoint_10_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_38_base : receiptBase endpoint_10_38_flag endpoint_10_38_sources = some 212952097796763023 := by decide +kernel
private theorem endpoint_10_38_w0 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 2 212952097796763023 = some 212952097796763023 := by decide +kernel
private theorem endpoint_10_38_w2 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 2 2 212952097796763023 = some 212952097796763023 := by decide +kernel
private theorem endpoint_10_38_p4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 4 212952097796763023 = some 212952097796763023 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 2 2 212952097796763023 212952097796763023 212952097796763023 endpoint_10_38_w0 endpoint_10_38_w2
private theorem endpoint_10_38_w4 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 4 2 212952097796763023 = some 212952097796763023 := by decide +kernel
private theorem endpoint_10_38_p6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 6 212952097796763023 = some 212952097796763023 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 4 2 212952097796763023 212952097796763023 212952097796763023 endpoint_10_38_p4 endpoint_10_38_w4
private theorem endpoint_10_38_w6 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 6 2 212952097796763023 = some 212952097796763023 := by decide +kernel
private theorem endpoint_10_38_p8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 8 212952097796763023 = some 212952097796763023 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 6 2 212952097796763023 212952097796763023 212952097796763023 endpoint_10_38_p6 endpoint_10_38_w6
private theorem endpoint_10_38_w8 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 8 1 212952097796763023 = some 212952097796763023 := by decide +kernel
private theorem endpoint_10_38_p9 : receiptWindow endpoint_10_38_flag endpoint_10_38_sources 0 9 212952097796763023 = some 212952097796763023 :=
  join_receipt_window endpoint_10_38_flag endpoint_10_38_sources 0 8 1 212952097796763023 212952097796763023 212952097796763023 endpoint_10_38_p8 endpoint_10_38_w8
def endpoint_10_38 : CertifiedEndpoint :=
  ⟨⟨10, 38, 4264⟩, 212952097796763023, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_38_flag endpoint_10_38_sources 9 212952097796763023 212952097796763023 rfl endpoint_10_38_base endpoint_10_38_p9) (by decide)⟩
private def endpoint_10_39_flag : Flag := ⟨10, 39, 4235⟩
private def endpoint_10_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_39_base : receiptBase endpoint_10_39_flag endpoint_10_39_sources = some 216185956254439888 := by decide +kernel
private theorem endpoint_10_39_w0 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 2 216185956254439888 = some 216185956254439888 := by decide +kernel
private theorem endpoint_10_39_w2 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 2 2 216185956254439888 = some 216185956254439888 := by decide +kernel
private theorem endpoint_10_39_p4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 4 216185956254439888 = some 216185956254439888 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 2 2 216185956254439888 216185956254439888 216185956254439888 endpoint_10_39_w0 endpoint_10_39_w2
private theorem endpoint_10_39_w4 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 4 2 216185956254439888 = some 216185956254439888 := by decide +kernel
private theorem endpoint_10_39_p6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 6 216185956254439888 = some 216185956254439888 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 4 2 216185956254439888 216185956254439888 216185956254439888 endpoint_10_39_p4 endpoint_10_39_w4
private theorem endpoint_10_39_w6 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 6 2 216185956254439888 = some 216185956254439888 := by decide +kernel
private theorem endpoint_10_39_p8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 8 216185956254439888 = some 216185956254439888 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 6 2 216185956254439888 216185956254439888 216185956254439888 endpoint_10_39_p6 endpoint_10_39_w6
private theorem endpoint_10_39_w8 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 8 1 216185956254439888 = some 216185956254439888 := by decide +kernel
private theorem endpoint_10_39_p9 : receiptWindow endpoint_10_39_flag endpoint_10_39_sources 0 9 216185956254439888 = some 216185956254439888 :=
  join_receipt_window endpoint_10_39_flag endpoint_10_39_sources 0 8 1 216185956254439888 216185956254439888 216185956254439888 endpoint_10_39_p8 endpoint_10_39_w8
def endpoint_10_39 : CertifiedEndpoint :=
  ⟨⟨10, 39, 4235⟩, 216185956254439888, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_39_flag endpoint_10_39_sources 9 216185956254439888 216185956254439888 rfl endpoint_10_39_base endpoint_10_39_p9) (by decide)⟩
private def endpoint_10_40_flag : Flag := ⟨10, 40, 4205⟩
private def endpoint_10_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_40_base : receiptBase endpoint_10_40_flag endpoint_10_40_sources = some 219304435882549608 := by decide +kernel
private theorem endpoint_10_40_w0 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 2 219304435882549608 = some 219304435882549608 := by decide +kernel
private theorem endpoint_10_40_w2 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 2 2 219304435882549608 = some 219304435882549608 := by decide +kernel
private theorem endpoint_10_40_p4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 4 219304435882549608 = some 219304435882549608 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 2 2 219304435882549608 219304435882549608 219304435882549608 endpoint_10_40_w0 endpoint_10_40_w2
private theorem endpoint_10_40_w4 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 4 2 219304435882549608 = some 219304435882549608 := by decide +kernel
private theorem endpoint_10_40_p6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 6 219304435882549608 = some 219304435882549608 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 4 2 219304435882549608 219304435882549608 219304435882549608 endpoint_10_40_p4 endpoint_10_40_w4
private theorem endpoint_10_40_w6 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 6 2 219304435882549608 = some 219304435882549608 := by decide +kernel
private theorem endpoint_10_40_p8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 8 219304435882549608 = some 219304435882549608 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 6 2 219304435882549608 219304435882549608 219304435882549608 endpoint_10_40_p6 endpoint_10_40_w6
private theorem endpoint_10_40_w8 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 8 1 219304435882549608 = some 219304435882549608 := by decide +kernel
private theorem endpoint_10_40_p9 : receiptWindow endpoint_10_40_flag endpoint_10_40_sources 0 9 219304435882549608 = some 219304435882549608 :=
  join_receipt_window endpoint_10_40_flag endpoint_10_40_sources 0 8 1 219304435882549608 219304435882549608 219304435882549608 endpoint_10_40_p8 endpoint_10_40_w8
def endpoint_10_40 : CertifiedEndpoint :=
  ⟨⟨10, 40, 4205⟩, 219304435882549608, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_40_flag endpoint_10_40_sources 9 219304435882549608 219304435882549608 rfl endpoint_10_40_base endpoint_10_40_p9) (by decide)⟩
private def endpoint_10_41_flag : Flag := ⟨10, 41, 4175⟩
private def endpoint_10_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_41_base : receiptBase endpoint_10_41_flag endpoint_10_41_sources = some 222356803913436661 := by decide +kernel
private theorem endpoint_10_41_w0 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 2 222356803913436661 = some 222356803913436661 := by decide +kernel
private theorem endpoint_10_41_w2 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 2 2 222356803913436661 = some 222356803913436661 := by decide +kernel
private theorem endpoint_10_41_p4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 4 222356803913436661 = some 222356803913436661 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 2 2 222356803913436661 222356803913436661 222356803913436661 endpoint_10_41_w0 endpoint_10_41_w2
private theorem endpoint_10_41_w4 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 4 2 222356803913436661 = some 222356803913436661 := by decide +kernel
private theorem endpoint_10_41_p6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 6 222356803913436661 = some 222356803913436661 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 4 2 222356803913436661 222356803913436661 222356803913436661 endpoint_10_41_p4 endpoint_10_41_w4
private theorem endpoint_10_41_w6 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 6 2 222356803913436661 = some 222356803913436661 := by decide +kernel
private theorem endpoint_10_41_p8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 8 222356803913436661 = some 222356803913436661 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 6 2 222356803913436661 222356803913436661 222356803913436661 endpoint_10_41_p6 endpoint_10_41_w6
private theorem endpoint_10_41_w8 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 8 1 222356803913436661 = some 222356803913436661 := by decide +kernel
private theorem endpoint_10_41_p9 : receiptWindow endpoint_10_41_flag endpoint_10_41_sources 0 9 222356803913436661 = some 222356803913436661 :=
  join_receipt_window endpoint_10_41_flag endpoint_10_41_sources 0 8 1 222356803913436661 222356803913436661 222356803913436661 endpoint_10_41_p8 endpoint_10_41_w8
def endpoint_10_41 : CertifiedEndpoint :=
  ⟨⟨10, 41, 4175⟩, 222356803913436661, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_41_flag endpoint_10_41_sources 9 222356803913436661 222356803913436661 rfl endpoint_10_41_base endpoint_10_41_p9) (by decide)⟩
private def endpoint_10_42_flag : Flag := ⟨10, 42, 4144⟩
private def endpoint_10_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_10_42_base : receiptBase endpoint_10_42_flag endpoint_10_42_sources = some 225289458223109508 := by decide +kernel
private theorem endpoint_10_42_w0 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 2 225289458223109508 = some 225289458223109508 := by decide +kernel
private theorem endpoint_10_42_w2 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 2 2 225289458223109508 = some 225289458223109508 := by decide +kernel
private theorem endpoint_10_42_p4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 4 225289458223109508 = some 225289458223109508 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 2 2 225289458223109508 225289458223109508 225289458223109508 endpoint_10_42_w0 endpoint_10_42_w2
private theorem endpoint_10_42_w4 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 4 2 225289458223109508 = some 225289458223109508 := by decide +kernel
private theorem endpoint_10_42_p6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 6 225289458223109508 = some 225289458223109508 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 4 2 225289458223109508 225289458223109508 225289458223109508 endpoint_10_42_p4 endpoint_10_42_w4
private theorem endpoint_10_42_w6 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 6 2 225289458223109508 = some 225289458223109508 := by decide +kernel
private theorem endpoint_10_42_p8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 8 225289458223109508 = some 225289458223109508 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 6 2 225289458223109508 225289458223109508 225289458223109508 endpoint_10_42_p6 endpoint_10_42_w6
private theorem endpoint_10_42_w8 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 8 1 225289458223109508 = some 225289458223109508 := by decide +kernel
private theorem endpoint_10_42_p9 : receiptWindow endpoint_10_42_flag endpoint_10_42_sources 0 9 225289458223109508 = some 225289458223109508 :=
  join_receipt_window endpoint_10_42_flag endpoint_10_42_sources 0 8 1 225289458223109508 225289458223109508 225289458223109508 endpoint_10_42_p8 endpoint_10_42_w8
def endpoint_10_42 : CertifiedEndpoint :=
  ⟨⟨10, 42, 4144⟩, 225289458223109508, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_10_42_flag endpoint_10_42_sources 9 225289458223109508 225289458223109508 rfl endpoint_10_42_base endpoint_10_42_p9) (by decide)⟩
private def endpoint_10_43_flag : Flag := ⟨10, 43, 4113⟩
private def endpoint_10_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_43_base : receiptBase endpoint_10_43_flag endpoint_10_43_sources = some 228747383090884766 := by decide +kernel
private theorem endpoint_10_43_w0 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 2 228747383090884766 = some 228747383090884766 := by decide +kernel
private theorem endpoint_10_43_w2 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 2 2 228747383090884766 = some 228747383090884766 := by decide +kernel
private theorem endpoint_10_43_p4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 4 228747383090884766 = some 228747383090884766 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 2 2 228747383090884766 228747383090884766 228747383090884766 endpoint_10_43_w0 endpoint_10_43_w2
private theorem endpoint_10_43_w4 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 4 2 228747383090884766 = some 228747383090884766 := by decide +kernel
private theorem endpoint_10_43_p6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 6 228747383090884766 = some 228747383090884766 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 4 2 228747383090884766 228747383090884766 228747383090884766 endpoint_10_43_p4 endpoint_10_43_w4
private theorem endpoint_10_43_w6 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 6 2 228747383090884766 = some 228747383090884766 := by decide +kernel
private theorem endpoint_10_43_p8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 8 228747383090884766 = some 228747383090884766 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 6 2 228747383090884766 228747383090884766 228747383090884766 endpoint_10_43_p6 endpoint_10_43_w6
private theorem endpoint_10_43_w8 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 8 1 228747383090884766 = some 228747383090884766 := by decide +kernel
private theorem endpoint_10_43_p9 : receiptWindow endpoint_10_43_flag endpoint_10_43_sources 0 9 228747383090884766 = some 228747383090884766 :=
  join_receipt_window endpoint_10_43_flag endpoint_10_43_sources 0 8 1 228747383090884766 228747383090884766 228747383090884766 endpoint_10_43_p8 endpoint_10_43_w8
def endpoint_10_43 : CertifiedEndpoint :=
  ⟨⟨10, 43, 4113⟩, 228747383090884766, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_43_flag endpoint_10_43_sources 9 228747383090884766 228747383090884766 rfl endpoint_10_43_base endpoint_10_43_p9) (by decide)⟩
private def endpoint_10_44_flag : Flag := ⟨10, 44, 4081⟩
private def endpoint_10_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_44_base : receiptBase endpoint_10_44_flag endpoint_10_44_sources = some 231454933891565424 := by decide +kernel
private theorem endpoint_10_44_w0 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 2 231454933891565424 = some 231454933891565424 := by decide +kernel
private theorem endpoint_10_44_w2 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 2 2 231454933891565424 = some 231454933891565424 := by decide +kernel
private theorem endpoint_10_44_p4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 4 231454933891565424 = some 231454933891565424 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 2 2 231454933891565424 231454933891565424 231454933891565424 endpoint_10_44_w0 endpoint_10_44_w2
private theorem endpoint_10_44_w4 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 4 2 231454933891565424 = some 231454933891565424 := by decide +kernel
private theorem endpoint_10_44_p6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 6 231454933891565424 = some 231454933891565424 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 4 2 231454933891565424 231454933891565424 231454933891565424 endpoint_10_44_p4 endpoint_10_44_w4
private theorem endpoint_10_44_w6 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 6 2 231454933891565424 = some 231454933891565424 := by decide +kernel
private theorem endpoint_10_44_p8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 8 231454933891565424 = some 231454933891565424 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 6 2 231454933891565424 231454933891565424 231454933891565424 endpoint_10_44_p6 endpoint_10_44_w6
private theorem endpoint_10_44_w8 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 8 1 231454933891565424 = some 231454933891565424 := by decide +kernel
private theorem endpoint_10_44_p9 : receiptWindow endpoint_10_44_flag endpoint_10_44_sources 0 9 231454933891565424 = some 231454933891565424 :=
  join_receipt_window endpoint_10_44_flag endpoint_10_44_sources 0 8 1 231454933891565424 231454933891565424 231454933891565424 endpoint_10_44_p8 endpoint_10_44_w8
def endpoint_10_44 : CertifiedEndpoint :=
  ⟨⟨10, 44, 4081⟩, 231454933891565424, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_44_flag endpoint_10_44_sources 9 231454933891565424 231454933891565424 rfl endpoint_10_44_base endpoint_10_44_p9) (by decide)⟩
private def endpoint_10_45_flag : Flag := ⟨10, 45, 4049⟩
private def endpoint_10_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_45_base : receiptBase endpoint_10_45_flag endpoint_10_45_sources = some 234092335127939583 := by decide +kernel
private theorem endpoint_10_45_w0 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 2 234092335127939583 = some 234092335127939583 := by decide +kernel
private theorem endpoint_10_45_w2 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 2 2 234092335127939583 = some 234092335127939583 := by decide +kernel
private theorem endpoint_10_45_p4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 4 234092335127939583 = some 234092335127939583 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 2 2 234092335127939583 234092335127939583 234092335127939583 endpoint_10_45_w0 endpoint_10_45_w2
private theorem endpoint_10_45_w4 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 4 2 234092335127939583 = some 234092335127939583 := by decide +kernel
private theorem endpoint_10_45_p6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 6 234092335127939583 = some 234092335127939583 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 4 2 234092335127939583 234092335127939583 234092335127939583 endpoint_10_45_p4 endpoint_10_45_w4
private theorem endpoint_10_45_w6 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 6 2 234092335127939583 = some 234092335127939583 := by decide +kernel
private theorem endpoint_10_45_p8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 8 234092335127939583 = some 234092335127939583 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 6 2 234092335127939583 234092335127939583 234092335127939583 endpoint_10_45_p6 endpoint_10_45_w6
private theorem endpoint_10_45_w8 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 8 1 234092335127939583 = some 234092335127939583 := by decide +kernel
private theorem endpoint_10_45_p9 : receiptWindow endpoint_10_45_flag endpoint_10_45_sources 0 9 234092335127939583 = some 234092335127939583 :=
  join_receipt_window endpoint_10_45_flag endpoint_10_45_sources 0 8 1 234092335127939583 234092335127939583 234092335127939583 endpoint_10_45_p8 endpoint_10_45_w8
def endpoint_10_45 : CertifiedEndpoint :=
  ⟨⟨10, 45, 4049⟩, 234092335127939583, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_45_flag endpoint_10_45_sources 9 234092335127939583 234092335127939583 rfl endpoint_10_45_base endpoint_10_45_p9) (by decide)⟩
private def endpoint_10_46_flag : Flag := ⟨10, 46, 4015⟩
private def endpoint_10_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_46_base : receiptBase endpoint_10_46_flag endpoint_10_46_sources = some 236543294529785779 := by decide +kernel
private theorem endpoint_10_46_w0 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 2 236543294529785779 = some 236543294529785779 := by decide +kernel
private theorem endpoint_10_46_w2 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 2 2 236543294529785779 = some 236543294529785779 := by decide +kernel
private theorem endpoint_10_46_p4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 4 236543294529785779 = some 236543294529785779 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 2 2 236543294529785779 236543294529785779 236543294529785779 endpoint_10_46_w0 endpoint_10_46_w2
private theorem endpoint_10_46_w4 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 4 2 236543294529785779 = some 236543294529785779 := by decide +kernel
private theorem endpoint_10_46_p6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 6 236543294529785779 = some 236543294529785779 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 4 2 236543294529785779 236543294529785779 236543294529785779 endpoint_10_46_p4 endpoint_10_46_w4
private theorem endpoint_10_46_w6 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 6 2 236543294529785779 = some 236543294529785779 := by decide +kernel
private theorem endpoint_10_46_p8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 8 236543294529785779 = some 236543294529785779 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 6 2 236543294529785779 236543294529785779 236543294529785779 endpoint_10_46_p6 endpoint_10_46_w6
private theorem endpoint_10_46_w8 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 8 1 236543294529785779 = some 236543294529785779 := by decide +kernel
private theorem endpoint_10_46_p9 : receiptWindow endpoint_10_46_flag endpoint_10_46_sources 0 9 236543294529785779 = some 236543294529785779 :=
  join_receipt_window endpoint_10_46_flag endpoint_10_46_sources 0 8 1 236543294529785779 236543294529785779 236543294529785779 endpoint_10_46_p8 endpoint_10_46_w8
def endpoint_10_46 : CertifiedEndpoint :=
  ⟨⟨10, 46, 4015⟩, 236543294529785779, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_46_flag endpoint_10_46_sources 9 236543294529785779 236543294529785779 rfl endpoint_10_46_base endpoint_10_46_p9) (by decide)⟩
private def endpoint_10_47_flag : Flag := ⟨10, 47, 3982⟩
private def endpoint_10_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_47_base : receiptBase endpoint_10_47_flag endpoint_10_47_sources = some 238979012830237447 := by decide +kernel
private theorem endpoint_10_47_w0 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 2 238979012830237447 = some 238979012830237447 := by decide +kernel
private theorem endpoint_10_47_w2 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 2 2 238979012830237447 = some 238979012830237447 := by decide +kernel
private theorem endpoint_10_47_p4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 4 238979012830237447 = some 238979012830237447 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 2 2 238979012830237447 238979012830237447 238979012830237447 endpoint_10_47_w0 endpoint_10_47_w2
private theorem endpoint_10_47_w4 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 4 2 238979012830237447 = some 238979012830237447 := by decide +kernel
private theorem endpoint_10_47_p6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 6 238979012830237447 = some 238979012830237447 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 4 2 238979012830237447 238979012830237447 238979012830237447 endpoint_10_47_p4 endpoint_10_47_w4
private theorem endpoint_10_47_w6 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 6 2 238979012830237447 = some 238979012830237447 := by decide +kernel
private theorem endpoint_10_47_p8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 8 238979012830237447 = some 238979012830237447 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 6 2 238979012830237447 238979012830237447 238979012830237447 endpoint_10_47_p6 endpoint_10_47_w6
private theorem endpoint_10_47_w8 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 8 1 238979012830237447 = some 238979012830237447 := by decide +kernel
private theorem endpoint_10_47_p9 : receiptWindow endpoint_10_47_flag endpoint_10_47_sources 0 9 238979012830237447 = some 238979012830237447 :=
  join_receipt_window endpoint_10_47_flag endpoint_10_47_sources 0 8 1 238979012830237447 238979012830237447 238979012830237447 endpoint_10_47_p8 endpoint_10_47_w8
def endpoint_10_47 : CertifiedEndpoint :=
  ⟨⟨10, 47, 3982⟩, 238979012830237447, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_47_flag endpoint_10_47_sources 9 238979012830237447 238979012830237447 rfl endpoint_10_47_base endpoint_10_47_p9) (by decide)⟩
private def endpoint_10_48_flag : Flag := ⟨10, 48, 3947⟩
private def endpoint_10_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_48_base : receiptBase endpoint_10_48_flag endpoint_10_48_sources = some 241221813951763629 := by decide +kernel
private theorem endpoint_10_48_w0 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 2 241221813951763629 = some 241221813951763629 := by decide +kernel
private theorem endpoint_10_48_w2 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 2 2 241221813951763629 = some 241221813951763629 := by decide +kernel
private theorem endpoint_10_48_p4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 4 241221813951763629 = some 241221813951763629 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 2 2 241221813951763629 241221813951763629 241221813951763629 endpoint_10_48_w0 endpoint_10_48_w2
private theorem endpoint_10_48_w4 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 4 2 241221813951763629 = some 241221813951763629 := by decide +kernel
private theorem endpoint_10_48_p6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 6 241221813951763629 = some 241221813951763629 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 4 2 241221813951763629 241221813951763629 241221813951763629 endpoint_10_48_p4 endpoint_10_48_w4
private theorem endpoint_10_48_w6 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 6 2 241221813951763629 = some 241221813951763629 := by decide +kernel
private theorem endpoint_10_48_p8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 8 241221813951763629 = some 241221813951763629 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 6 2 241221813951763629 241221813951763629 241221813951763629 endpoint_10_48_p6 endpoint_10_48_w6
private theorem endpoint_10_48_w8 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 8 1 241221813951763629 = some 241221813951763629 := by decide +kernel
private theorem endpoint_10_48_p9 : receiptWindow endpoint_10_48_flag endpoint_10_48_sources 0 9 241221813951763629 = some 241221813951763629 :=
  join_receipt_window endpoint_10_48_flag endpoint_10_48_sources 0 8 1 241221813951763629 241221813951763629 241221813951763629 endpoint_10_48_p8 endpoint_10_48_w8
def endpoint_10_48 : CertifiedEndpoint :=
  ⟨⟨10, 48, 3947⟩, 241221813951763629, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_48_flag endpoint_10_48_sources 9 241221813951763629 241221813951763629 rfl endpoint_10_48_base endpoint_10_48_p9) (by decide)⟩
private def endpoint_10_49_flag : Flag := ⟨10, 49, 3912⟩
private def endpoint_10_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_49_base : receiptBase endpoint_10_49_flag endpoint_10_49_sources = some 243387990164585789 := by decide +kernel
private theorem endpoint_10_49_w0 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 2 243387990164585789 = some 243387990164585789 := by decide +kernel
private theorem endpoint_10_49_w2 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 2 2 243387990164585789 = some 243387990164585789 := by decide +kernel
private theorem endpoint_10_49_p4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 4 243387990164585789 = some 243387990164585789 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 2 2 243387990164585789 243387990164585789 243387990164585789 endpoint_10_49_w0 endpoint_10_49_w2
private theorem endpoint_10_49_w4 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 4 2 243387990164585789 = some 243387990164585789 := by decide +kernel
private theorem endpoint_10_49_p6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 6 243387990164585789 = some 243387990164585789 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 4 2 243387990164585789 243387990164585789 243387990164585789 endpoint_10_49_p4 endpoint_10_49_w4
private theorem endpoint_10_49_w6 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 6 2 243387990164585789 = some 243387990164585789 := by decide +kernel
private theorem endpoint_10_49_p8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 8 243387990164585789 = some 243387990164585789 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 6 2 243387990164585789 243387990164585789 243387990164585789 endpoint_10_49_p6 endpoint_10_49_w6
private theorem endpoint_10_49_w8 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 8 1 243387990164585789 = some 243387990164585789 := by decide +kernel
private theorem endpoint_10_49_p9 : receiptWindow endpoint_10_49_flag endpoint_10_49_sources 0 9 243387990164585789 = some 243387990164585789 :=
  join_receipt_window endpoint_10_49_flag endpoint_10_49_sources 0 8 1 243387990164585789 243387990164585789 243387990164585789 endpoint_10_49_p8 endpoint_10_49_w8
def endpoint_10_49 : CertifiedEndpoint :=
  ⟨⟨10, 49, 3912⟩, 243387990164585789, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_49_flag endpoint_10_49_sources 9 243387990164585789 243387990164585789 rfl endpoint_10_49_base endpoint_10_49_p9) (by decide)⟩
private def endpoint_10_50_flag : Flag := ⟨10, 50, 3876⟩
private def endpoint_10_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_50_base : receiptBase endpoint_10_50_flag endpoint_10_50_sources = some 245415078437328180 := by decide +kernel
private theorem endpoint_10_50_w0 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 2 245415078437328180 = some 245415078437328180 := by decide +kernel
private theorem endpoint_10_50_w2 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 2 2 245415078437328180 = some 245415078437328180 := by decide +kernel
private theorem endpoint_10_50_p4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 4 245415078437328180 = some 245415078437328180 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 2 2 245415078437328180 245415078437328180 245415078437328180 endpoint_10_50_w0 endpoint_10_50_w2
private theorem endpoint_10_50_w4 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 4 2 245415078437328180 = some 245415078437328180 := by decide +kernel
private theorem endpoint_10_50_p6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 6 245415078437328180 = some 245415078437328180 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 4 2 245415078437328180 245415078437328180 245415078437328180 endpoint_10_50_p4 endpoint_10_50_w4
private theorem endpoint_10_50_w6 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 6 2 245415078437328180 = some 245415078437328180 := by decide +kernel
private theorem endpoint_10_50_p8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 8 245415078437328180 = some 245415078437328180 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 6 2 245415078437328180 245415078437328180 245415078437328180 endpoint_10_50_p6 endpoint_10_50_w6
private theorem endpoint_10_50_w8 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 8 1 245415078437328180 = some 245415078437328180 := by decide +kernel
private theorem endpoint_10_50_p9 : receiptWindow endpoint_10_50_flag endpoint_10_50_sources 0 9 245415078437328180 = some 245415078437328180 :=
  join_receipt_window endpoint_10_50_flag endpoint_10_50_sources 0 8 1 245415078437328180 245415078437328180 245415078437328180 endpoint_10_50_p8 endpoint_10_50_w8
def endpoint_10_50 : CertifiedEndpoint :=
  ⟨⟨10, 50, 3876⟩, 245415078437328180, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_50_flag endpoint_10_50_sources 9 245415078437328180 245415078437328180 rfl endpoint_10_50_base endpoint_10_50_p9) (by decide)⟩
private def endpoint_10_51_flag : Flag := ⟨10, 51, 3839⟩
private def endpoint_10_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_51_base : receiptBase endpoint_10_51_flag endpoint_10_51_sources = some 247299841097792040 := by decide +kernel
private theorem endpoint_10_51_w0 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 2 247299841097792040 = some 247299841097792040 := by decide +kernel
private theorem endpoint_10_51_w2 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 2 2 247299841097792040 = some 247299841097792040 := by decide +kernel
private theorem endpoint_10_51_p4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 4 247299841097792040 = some 247299841097792040 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 2 2 247299841097792040 247299841097792040 247299841097792040 endpoint_10_51_w0 endpoint_10_51_w2
private theorem endpoint_10_51_w4 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 4 2 247299841097792040 = some 247299841097792040 := by decide +kernel
private theorem endpoint_10_51_p6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 6 247299841097792040 = some 247299841097792040 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 4 2 247299841097792040 247299841097792040 247299841097792040 endpoint_10_51_p4 endpoint_10_51_w4
private theorem endpoint_10_51_w6 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 6 2 247299841097792040 = some 247299841097792040 := by decide +kernel
private theorem endpoint_10_51_p8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 8 247299841097792040 = some 247299841097792040 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 6 2 247299841097792040 247299841097792040 247299841097792040 endpoint_10_51_p6 endpoint_10_51_w6
private theorem endpoint_10_51_w8 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 8 1 247299841097792040 = some 247299841097792040 := by decide +kernel
private theorem endpoint_10_51_p9 : receiptWindow endpoint_10_51_flag endpoint_10_51_sources 0 9 247299841097792040 = some 247299841097792040 :=
  join_receipt_window endpoint_10_51_flag endpoint_10_51_sources 0 8 1 247299841097792040 247299841097792040 247299841097792040 endpoint_10_51_p8 endpoint_10_51_w8
def endpoint_10_51 : CertifiedEndpoint :=
  ⟨⟨10, 51, 3839⟩, 247299841097792040, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_51_flag endpoint_10_51_sources 9 247299841097792040 247299841097792040 rfl endpoint_10_51_base endpoint_10_51_p9) (by decide)⟩
private def endpoint_10_52_flag : Flag := ⟨10, 52, 3802⟩
private def endpoint_10_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_10_52_base : receiptBase endpoint_10_52_flag endpoint_10_52_sources = some 249103661953286863 := by decide +kernel
private theorem endpoint_10_52_w0 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 2 249103661953286863 = some 249103661953286863 := by decide +kernel
private theorem endpoint_10_52_w2 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 2 2 249103661953286863 = some 249103661953286863 := by decide +kernel
private theorem endpoint_10_52_p4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 4 249103661953286863 = some 249103661953286863 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 2 2 249103661953286863 249103661953286863 249103661953286863 endpoint_10_52_w0 endpoint_10_52_w2
private theorem endpoint_10_52_w4 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 4 2 249103661953286863 = some 249103661953286863 := by decide +kernel
private theorem endpoint_10_52_p6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 6 249103661953286863 = some 249103661953286863 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 4 2 249103661953286863 249103661953286863 249103661953286863 endpoint_10_52_p4 endpoint_10_52_w4
private theorem endpoint_10_52_w6 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 6 2 249103661953286863 = some 249103661953286863 := by decide +kernel
private theorem endpoint_10_52_p8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 8 249103661953286863 = some 249103661953286863 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 6 2 249103661953286863 249103661953286863 249103661953286863 endpoint_10_52_p6 endpoint_10_52_w6
private theorem endpoint_10_52_w8 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 8 1 249103661953286863 = some 249103661953286863 := by decide +kernel
private theorem endpoint_10_52_p9 : receiptWindow endpoint_10_52_flag endpoint_10_52_sources 0 9 249103661953286863 = some 249103661953286863 :=
  join_receipt_window endpoint_10_52_flag endpoint_10_52_sources 0 8 1 249103661953286863 249103661953286863 249103661953286863 endpoint_10_52_p8 endpoint_10_52_w8
def endpoint_10_52 : CertifiedEndpoint :=
  ⟨⟨10, 52, 3802⟩, 249103661953286863, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_10_52_flag endpoint_10_52_sources 9 249103661953286863 249103661953286863 rfl endpoint_10_52_base endpoint_10_52_p9) (by decide)⟩
private def endpoint_10_53_flag : Flag := ⟨10, 53, 3763⟩
private def endpoint_10_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_53_base : receiptBase endpoint_10_53_flag endpoint_10_53_sources = some 251413045566678323 := by decide +kernel
private theorem endpoint_10_53_w0 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 2 251413045566678323 = some 251413045566678323 := by decide +kernel
private theorem endpoint_10_53_w2 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 2 2 251413045566678323 = some 251413045566678323 := by decide +kernel
private theorem endpoint_10_53_p4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 4 251413045566678323 = some 251413045566678323 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 2 2 251413045566678323 251413045566678323 251413045566678323 endpoint_10_53_w0 endpoint_10_53_w2
private theorem endpoint_10_53_w4 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 4 2 251413045566678323 = some 251413045566678323 := by decide +kernel
private theorem endpoint_10_53_p6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 6 251413045566678323 = some 251413045566678323 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 4 2 251413045566678323 251413045566678323 251413045566678323 endpoint_10_53_p4 endpoint_10_53_w4
private theorem endpoint_10_53_w6 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 6 2 251413045566678323 = some 251413045566678323 := by decide +kernel
private theorem endpoint_10_53_p8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 8 251413045566678323 = some 251413045566678323 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 6 2 251413045566678323 251413045566678323 251413045566678323 endpoint_10_53_p6 endpoint_10_53_w6
private theorem endpoint_10_53_w8 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 8 1 251413045566678323 = some 251413045566678323 := by decide +kernel
private theorem endpoint_10_53_p9 : receiptWindow endpoint_10_53_flag endpoint_10_53_sources 0 9 251413045566678323 = some 251413045566678323 :=
  join_receipt_window endpoint_10_53_flag endpoint_10_53_sources 0 8 1 251413045566678323 251413045566678323 251413045566678323 endpoint_10_53_p8 endpoint_10_53_w8
def endpoint_10_53 : CertifiedEndpoint :=
  ⟨⟨10, 53, 3763⟩, 251413045566678323, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_53_flag endpoint_10_53_sources 9 251413045566678323 251413045566678323 rfl endpoint_10_53_base endpoint_10_53_p9) (by decide)⟩
private def endpoint_10_54_flag : Flag := ⟨10, 54, 3723⟩
private def endpoint_10_54_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_54_base : receiptBase endpoint_10_54_flag endpoint_10_54_sources = some 252861061515396463 := by decide +kernel
private theorem endpoint_10_54_w0 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 2 252861061515396463 = some 252861061515396463 := by decide +kernel
private theorem endpoint_10_54_w2 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 2 2 252861061515396463 = some 252861061515396463 := by decide +kernel
private theorem endpoint_10_54_p4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 4 252861061515396463 = some 252861061515396463 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 2 2 252861061515396463 252861061515396463 252861061515396463 endpoint_10_54_w0 endpoint_10_54_w2
private theorem endpoint_10_54_w4 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 4 2 252861061515396463 = some 252861061515396463 := by decide +kernel
private theorem endpoint_10_54_p6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 6 252861061515396463 = some 252861061515396463 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 4 2 252861061515396463 252861061515396463 252861061515396463 endpoint_10_54_p4 endpoint_10_54_w4
private theorem endpoint_10_54_w6 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 6 2 252861061515396463 = some 252861061515396463 := by decide +kernel
private theorem endpoint_10_54_p8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 8 252861061515396463 = some 252861061515396463 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 6 2 252861061515396463 252861061515396463 252861061515396463 endpoint_10_54_p6 endpoint_10_54_w6
private theorem endpoint_10_54_w8 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 8 1 252861061515396463 = some 252861061515396463 := by decide +kernel
private theorem endpoint_10_54_p9 : receiptWindow endpoint_10_54_flag endpoint_10_54_sources 0 9 252861061515396463 = some 252861061515396463 :=
  join_receipt_window endpoint_10_54_flag endpoint_10_54_sources 0 8 1 252861061515396463 252861061515396463 252861061515396463 endpoint_10_54_p8 endpoint_10_54_w8
def endpoint_10_54 : CertifiedEndpoint :=
  ⟨⟨10, 54, 3723⟩, 252861061515396463, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_54_flag endpoint_10_54_sources 9 252861061515396463 252861061515396463 rfl endpoint_10_54_base endpoint_10_54_p9) (by decide)⟩
private def endpoint_10_55_flag : Flag := ⟨10, 55, 3682⟩
private def endpoint_10_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_10_55_base : receiptBase endpoint_10_55_flag endpoint_10_55_sources = some 254153229617506149 := by decide +kernel
private theorem endpoint_10_55_w0 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 2 254153229617506149 = some 254153229617506149 := by decide +kernel
private theorem endpoint_10_55_w2 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 2 2 254153229617506149 = some 254153229617506149 := by decide +kernel
private theorem endpoint_10_55_p4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 4 254153229617506149 = some 254153229617506149 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 2 2 254153229617506149 254153229617506149 254153229617506149 endpoint_10_55_w0 endpoint_10_55_w2
private theorem endpoint_10_55_w4 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 4 2 254153229617506149 = some 254153229617506149 := by decide +kernel
private theorem endpoint_10_55_p6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 6 254153229617506149 = some 254153229617506149 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 4 2 254153229617506149 254153229617506149 254153229617506149 endpoint_10_55_p4 endpoint_10_55_w4
private theorem endpoint_10_55_w6 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 6 2 254153229617506149 = some 254153229617506149 := by decide +kernel
private theorem endpoint_10_55_p8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 8 254153229617506149 = some 254153229617506149 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 6 2 254153229617506149 254153229617506149 254153229617506149 endpoint_10_55_p6 endpoint_10_55_w6
private theorem endpoint_10_55_w8 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 8 1 254153229617506149 = some 254153229617506149 := by decide +kernel
private theorem endpoint_10_55_p9 : receiptWindow endpoint_10_55_flag endpoint_10_55_sources 0 9 254153229617506149 = some 254153229617506149 :=
  join_receipt_window endpoint_10_55_flag endpoint_10_55_sources 0 8 1 254153229617506149 254153229617506149 254153229617506149 endpoint_10_55_p8 endpoint_10_55_w8
def endpoint_10_55 : CertifiedEndpoint :=
  ⟨⟨10, 55, 3682⟩, 254153229617506149, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_10_55_flag endpoint_10_55_sources 9 254153229617506149 254153229617506149 rfl endpoint_10_55_base endpoint_10_55_p9) (by decide)⟩
private def endpoint_10_56_flag : Flag := ⟨10, 56, 3640⟩
private def endpoint_10_56_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_10_56_base : receiptBase endpoint_10_56_flag endpoint_10_56_sources = some 255512094530140157 := by decide +kernel
private theorem endpoint_10_56_w0 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 2 255512094530140157 = some 255512094530140157 := by decide +kernel
private theorem endpoint_10_56_w2 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 2 2 255512094530140157 = some 255512094530140157 := by decide +kernel
private theorem endpoint_10_56_p4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 4 255512094530140157 = some 255512094530140157 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 2 2 255512094530140157 255512094530140157 255512094530140157 endpoint_10_56_w0 endpoint_10_56_w2
private theorem endpoint_10_56_w4 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 4 2 255512094530140157 = some 255512094530140157 := by decide +kernel
private theorem endpoint_10_56_p6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 6 255512094530140157 = some 255512094530140157 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 4 2 255512094530140157 255512094530140157 255512094530140157 endpoint_10_56_p4 endpoint_10_56_w4
private theorem endpoint_10_56_w6 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 6 2 255512094530140157 = some 255512094530140157 := by decide +kernel
private theorem endpoint_10_56_p8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 8 255512094530140157 = some 255512094530140157 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 6 2 255512094530140157 255512094530140157 255512094530140157 endpoint_10_56_p6 endpoint_10_56_w6
private theorem endpoint_10_56_w8 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 8 1 255512094530140157 = some 255512094530140157 := by decide +kernel
private theorem endpoint_10_56_p9 : receiptWindow endpoint_10_56_flag endpoint_10_56_sources 0 9 255512094530140157 = some 255512094530140157 :=
  join_receipt_window endpoint_10_56_flag endpoint_10_56_sources 0 8 1 255512094530140157 255512094530140157 255512094530140157 endpoint_10_56_p8 endpoint_10_56_w8
def endpoint_10_56 : CertifiedEndpoint :=
  ⟨⟨10, 56, 3640⟩, 255512094530140157, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_10_56_flag endpoint_10_56_sources 9 255512094530140157 255512094530140157 rfl endpoint_10_56_base endpoint_10_56_p9) (by decide)⟩
private def endpoint_10_57_flag : Flag := ⟨10, 57, 3597⟩
private def endpoint_10_57_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_57_base : receiptBase endpoint_10_57_flag endpoint_10_57_sources = some 258948009436011646 := by decide +kernel
private theorem endpoint_10_57_w0 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 2 258948009436011646 = some 258948009436011646 := by decide +kernel
private theorem endpoint_10_57_w2 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 2 2 258948009436011646 = some 258948009436011646 := by decide +kernel
private theorem endpoint_10_57_p4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 4 258948009436011646 = some 258948009436011646 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 2 2 258948009436011646 258948009436011646 258948009436011646 endpoint_10_57_w0 endpoint_10_57_w2
private theorem endpoint_10_57_w4 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 4 2 258948009436011646 = some 258948009436011646 := by decide +kernel
private theorem endpoint_10_57_p6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 6 258948009436011646 = some 258948009436011646 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 4 2 258948009436011646 258948009436011646 258948009436011646 endpoint_10_57_p4 endpoint_10_57_w4
private theorem endpoint_10_57_w6 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 6 2 258948009436011646 = some 258948009436011646 := by decide +kernel
private theorem endpoint_10_57_p8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 8 258948009436011646 = some 258948009436011646 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 6 2 258948009436011646 258948009436011646 258948009436011646 endpoint_10_57_p6 endpoint_10_57_w6
private theorem endpoint_10_57_w8 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 8 1 258948009436011646 = some 258948009436011646 := by decide +kernel
private theorem endpoint_10_57_p9 : receiptWindow endpoint_10_57_flag endpoint_10_57_sources 0 9 258948009436011646 = some 258948009436011646 :=
  join_receipt_window endpoint_10_57_flag endpoint_10_57_sources 0 8 1 258948009436011646 258948009436011646 258948009436011646 endpoint_10_57_p8 endpoint_10_57_w8
def endpoint_10_57 : CertifiedEndpoint :=
  ⟨⟨10, 57, 3597⟩, 258948009436011646, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_57_flag endpoint_10_57_sources 9 258948009436011646 258948009436011646 rfl endpoint_10_57_base endpoint_10_57_p9) (by decide)⟩
private def endpoint_10_58_flag : Flag := ⟨10, 58, 3552⟩
private def endpoint_10_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_58_base : receiptBase endpoint_10_58_flag endpoint_10_58_sources = some 259641558181386358 := by decide +kernel
private theorem endpoint_10_58_w0 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 2 259641558181386358 = some 259641558181386358 := by decide +kernel
private theorem endpoint_10_58_w2 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 2 2 259641558181386358 = some 259641558181386358 := by decide +kernel
private theorem endpoint_10_58_p4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 4 259641558181386358 = some 259641558181386358 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 2 2 259641558181386358 259641558181386358 259641558181386358 endpoint_10_58_w0 endpoint_10_58_w2
private theorem endpoint_10_58_w4 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 4 2 259641558181386358 = some 259641558181386358 := by decide +kernel
private theorem endpoint_10_58_p6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 6 259641558181386358 = some 259641558181386358 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 4 2 259641558181386358 259641558181386358 259641558181386358 endpoint_10_58_p4 endpoint_10_58_w4
private theorem endpoint_10_58_w6 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 6 2 259641558181386358 = some 259641558181386358 := by decide +kernel
private theorem endpoint_10_58_p8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 8 259641558181386358 = some 259641558181386358 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 6 2 259641558181386358 259641558181386358 259641558181386358 endpoint_10_58_p6 endpoint_10_58_w6
private theorem endpoint_10_58_w8 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 8 1 259641558181386358 = some 259641558181386358 := by decide +kernel
private theorem endpoint_10_58_p9 : receiptWindow endpoint_10_58_flag endpoint_10_58_sources 0 9 259641558181386358 = some 259641558181386358 :=
  join_receipt_window endpoint_10_58_flag endpoint_10_58_sources 0 8 1 259641558181386358 259641558181386358 259641558181386358 endpoint_10_58_p8 endpoint_10_58_w8
def endpoint_10_58 : CertifiedEndpoint :=
  ⟨⟨10, 58, 3552⟩, 259641558181386358, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_58_flag endpoint_10_58_sources 9 259641558181386358 259641558181386358 rfl endpoint_10_58_base endpoint_10_58_p9) (by decide)⟩
private def endpoint_10_59_flag : Flag := ⟨10, 59, 3505⟩
private def endpoint_10_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_59_base : receiptBase endpoint_10_59_flag endpoint_10_59_sources = some 260089373248026334 := by decide +kernel
private theorem endpoint_10_59_w0 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 2 260089373248026334 = some 260089373248026334 := by decide +kernel
private theorem endpoint_10_59_w2 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 2 2 260089373248026334 = some 260089373248026334 := by decide +kernel
private theorem endpoint_10_59_p4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 4 260089373248026334 = some 260089373248026334 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 2 2 260089373248026334 260089373248026334 260089373248026334 endpoint_10_59_w0 endpoint_10_59_w2
private theorem endpoint_10_59_w4 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 4 2 260089373248026334 = some 260089373248026334 := by decide +kernel
private theorem endpoint_10_59_p6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 6 260089373248026334 = some 260089373248026334 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 4 2 260089373248026334 260089373248026334 260089373248026334 endpoint_10_59_p4 endpoint_10_59_w4
private theorem endpoint_10_59_w6 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 6 2 260089373248026334 = some 260089373248026334 := by decide +kernel
private theorem endpoint_10_59_p8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 8 260089373248026334 = some 260089373248026334 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 6 2 260089373248026334 260089373248026334 260089373248026334 endpoint_10_59_p6 endpoint_10_59_w6
private theorem endpoint_10_59_w8 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 8 1 260089373248026334 = some 260089373248026334 := by decide +kernel
private theorem endpoint_10_59_p9 : receiptWindow endpoint_10_59_flag endpoint_10_59_sources 0 9 260089373248026334 = some 260089373248026334 :=
  join_receipt_window endpoint_10_59_flag endpoint_10_59_sources 0 8 1 260089373248026334 260089373248026334 260089373248026334 endpoint_10_59_p8 endpoint_10_59_w8
def endpoint_10_59 : CertifiedEndpoint :=
  ⟨⟨10, 59, 3505⟩, 260089373248026334, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_59_flag endpoint_10_59_sources 9 260089373248026334 260089373248026334 rfl endpoint_10_59_base endpoint_10_59_p9) (by decide)⟩
private def endpoint_10_60_flag : Flag := ⟨10, 60, 3457⟩
private def endpoint_10_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_60_base : receiptBase endpoint_10_60_flag endpoint_10_60_sources = some 260359366391621660 := by decide +kernel
private theorem endpoint_10_60_w0 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 2 260359366391621660 = some 260359366391621660 := by decide +kernel
private theorem endpoint_10_60_w2 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 2 2 260359366391621660 = some 260359366391621660 := by decide +kernel
private theorem endpoint_10_60_p4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 4 260359366391621660 = some 260359366391621660 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 2 2 260359366391621660 260359366391621660 260359366391621660 endpoint_10_60_w0 endpoint_10_60_w2
private theorem endpoint_10_60_w4 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 4 2 260359366391621660 = some 260359366391621660 := by decide +kernel
private theorem endpoint_10_60_p6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 6 260359366391621660 = some 260359366391621660 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 4 2 260359366391621660 260359366391621660 260359366391621660 endpoint_10_60_p4 endpoint_10_60_w4
private theorem endpoint_10_60_w6 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 6 2 260359366391621660 = some 260359366391621660 := by decide +kernel
private theorem endpoint_10_60_p8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 8 260359366391621660 = some 260359366391621660 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 6 2 260359366391621660 260359366391621660 260359366391621660 endpoint_10_60_p6 endpoint_10_60_w6
private theorem endpoint_10_60_w8 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 8 1 260359366391621660 = some 260359366391621660 := by decide +kernel
private theorem endpoint_10_60_p9 : receiptWindow endpoint_10_60_flag endpoint_10_60_sources 0 9 260359366391621660 = some 260359366391621660 :=
  join_receipt_window endpoint_10_60_flag endpoint_10_60_sources 0 8 1 260359366391621660 260359366391621660 260359366391621660 endpoint_10_60_p8 endpoint_10_60_w8
def endpoint_10_60 : CertifiedEndpoint :=
  ⟨⟨10, 60, 3457⟩, 260359366391621660, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_60_flag endpoint_10_60_sources 9 260359366391621660 260359366391621660 rfl endpoint_10_60_base endpoint_10_60_p9) (by decide)⟩
private def endpoint_10_61_flag : Flag := ⟨10, 61, 3407⟩
private def endpoint_10_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_10_61_base : receiptBase endpoint_10_61_flag endpoint_10_61_sources = some 260372743661694668 := by decide +kernel
private theorem endpoint_10_61_w0 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 2 260372743661694668 = some 260372743661694668 := by decide +kernel
private theorem endpoint_10_61_w2 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 2 2 260372743661694668 = some 260372743661694668 := by decide +kernel
private theorem endpoint_10_61_p4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 4 260372743661694668 = some 260372743661694668 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 2 2 260372743661694668 260372743661694668 260372743661694668 endpoint_10_61_w0 endpoint_10_61_w2
private theorem endpoint_10_61_w4 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 4 2 260372743661694668 = some 260372743661694668 := by decide +kernel
private theorem endpoint_10_61_p6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 6 260372743661694668 = some 260372743661694668 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 4 2 260372743661694668 260372743661694668 260372743661694668 endpoint_10_61_p4 endpoint_10_61_w4
private theorem endpoint_10_61_w6 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 6 2 260372743661694668 = some 260372743661694668 := by decide +kernel
private theorem endpoint_10_61_p8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 8 260372743661694668 = some 260372743661694668 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 6 2 260372743661694668 260372743661694668 260372743661694668 endpoint_10_61_p6 endpoint_10_61_w6
private theorem endpoint_10_61_w8 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 8 1 260372743661694668 = some 260372743661694668 := by decide +kernel
private theorem endpoint_10_61_p9 : receiptWindow endpoint_10_61_flag endpoint_10_61_sources 0 9 260372743661694668 = some 260372743661694668 :=
  join_receipt_window endpoint_10_61_flag endpoint_10_61_sources 0 8 1 260372743661694668 260372743661694668 260372743661694668 endpoint_10_61_p8 endpoint_10_61_w8
def endpoint_10_61 : CertifiedEndpoint :=
  ⟨⟨10, 61, 3407⟩, 260372743661694668, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_10_61_flag endpoint_10_61_sources 9 260372743661694668 260372743661694668 rfl endpoint_10_61_base endpoint_10_61_p9) (by decide)⟩
private def endpoint_10_62_flag : Flag := ⟨10, 62, 3354⟩
private def endpoint_10_62_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_62_base : receiptBase endpoint_10_62_flag endpoint_10_62_sources = some 261394502523459557 := by decide +kernel
private theorem endpoint_10_62_w0 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 2 261394502523459557 = some 261394502523459557 := by decide +kernel
private theorem endpoint_10_62_w2 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 2 2 261394502523459557 = some 261394502523459557 := by decide +kernel
private theorem endpoint_10_62_p4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 4 261394502523459557 = some 261394502523459557 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 2 2 261394502523459557 261394502523459557 261394502523459557 endpoint_10_62_w0 endpoint_10_62_w2
private theorem endpoint_10_62_w4 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 4 2 261394502523459557 = some 261394502523459557 := by decide +kernel
private theorem endpoint_10_62_p6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 6 261394502523459557 = some 261394502523459557 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 4 2 261394502523459557 261394502523459557 261394502523459557 endpoint_10_62_p4 endpoint_10_62_w4
private theorem endpoint_10_62_w6 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 6 2 261394502523459557 = some 261394502523459557 := by decide +kernel
private theorem endpoint_10_62_p8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 8 261394502523459557 = some 261394502523459557 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 6 2 261394502523459557 261394502523459557 261394502523459557 endpoint_10_62_p6 endpoint_10_62_w6
private theorem endpoint_10_62_w8 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 8 1 261394502523459557 = some 261394502523459557 := by decide +kernel
private theorem endpoint_10_62_p9 : receiptWindow endpoint_10_62_flag endpoint_10_62_sources 0 9 261394502523459557 = some 261394502523459557 :=
  join_receipt_window endpoint_10_62_flag endpoint_10_62_sources 0 8 1 261394502523459557 261394502523459557 261394502523459557 endpoint_10_62_p8 endpoint_10_62_w8
def endpoint_10_62 : CertifiedEndpoint :=
  ⟨⟨10, 62, 3354⟩, 261394502523459557, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_62_flag endpoint_10_62_sources 9 261394502523459557 261394502523459557 rfl endpoint_10_62_base endpoint_10_62_p9) (by decide)⟩
private def endpoint_10_63_flag : Flag := ⟨10, 63, 3299⟩
private def endpoint_10_63_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_10_63_base : receiptBase endpoint_10_63_flag endpoint_10_63_sources = some 260796054019236717 := by decide +kernel
private theorem endpoint_10_63_w0 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 2 260796054019236717 = some 260796054019236717 := by decide +kernel
private theorem endpoint_10_63_w2 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 2 2 260796054019236717 = some 260796054019236717 := by decide +kernel
private theorem endpoint_10_63_p4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 4 260796054019236717 = some 260796054019236717 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 2 2 260796054019236717 260796054019236717 260796054019236717 endpoint_10_63_w0 endpoint_10_63_w2
private theorem endpoint_10_63_w4 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 4 2 260796054019236717 = some 260796054019236717 := by decide +kernel
private theorem endpoint_10_63_p6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 6 260796054019236717 = some 260796054019236717 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 4 2 260796054019236717 260796054019236717 260796054019236717 endpoint_10_63_p4 endpoint_10_63_w4
private theorem endpoint_10_63_w6 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 6 2 260796054019236717 = some 260796054019236717 := by decide +kernel
private theorem endpoint_10_63_p8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 8 260796054019236717 = some 260796054019236717 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 6 2 260796054019236717 260796054019236717 260796054019236717 endpoint_10_63_p6 endpoint_10_63_w6
private theorem endpoint_10_63_w8 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 8 1 260796054019236717 = some 260796054019236717 := by decide +kernel
private theorem endpoint_10_63_p9 : receiptWindow endpoint_10_63_flag endpoint_10_63_sources 0 9 260796054019236717 = some 260796054019236717 :=
  join_receipt_window endpoint_10_63_flag endpoint_10_63_sources 0 8 1 260796054019236717 260796054019236717 260796054019236717 endpoint_10_63_p8 endpoint_10_63_w8
def endpoint_10_63 : CertifiedEndpoint :=
  ⟨⟨10, 63, 3299⟩, 260796054019236717, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_10_63_flag endpoint_10_63_sources 9 260796054019236717 260796054019236717 rfl endpoint_10_63_base endpoint_10_63_p9) (by decide)⟩
private def endpoint_10_64_flag : Flag := ⟨10, 64, 3241⟩
private def endpoint_10_64_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_64_base : receiptBase endpoint_10_64_flag endpoint_10_64_sources = some 261238408526229992 := by decide +kernel
private theorem endpoint_10_64_w0 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 2 261238408526229992 = some 261238408526229992 := by decide +kernel
private theorem endpoint_10_64_w2 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 2 2 261238408526229992 = some 261238408526229992 := by decide +kernel
private theorem endpoint_10_64_p4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 4 261238408526229992 = some 261238408526229992 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 2 2 261238408526229992 261238408526229992 261238408526229992 endpoint_10_64_w0 endpoint_10_64_w2
private theorem endpoint_10_64_w4 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 4 2 261238408526229992 = some 261238408526229992 := by decide +kernel
private theorem endpoint_10_64_p6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 6 261238408526229992 = some 261238408526229992 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 4 2 261238408526229992 261238408526229992 261238408526229992 endpoint_10_64_p4 endpoint_10_64_w4
private theorem endpoint_10_64_w6 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 6 2 261238408526229992 = some 261238408526229992 := by decide +kernel
private theorem endpoint_10_64_p8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 8 261238408526229992 = some 261238408526229992 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 6 2 261238408526229992 261238408526229992 261238408526229992 endpoint_10_64_p6 endpoint_10_64_w6
private theorem endpoint_10_64_w8 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 8 1 261238408526229992 = some 261238408526229992 := by decide +kernel
private theorem endpoint_10_64_p9 : receiptWindow endpoint_10_64_flag endpoint_10_64_sources 0 9 261238408526229992 = some 261238408526229992 :=
  join_receipt_window endpoint_10_64_flag endpoint_10_64_sources 0 8 1 261238408526229992 261238408526229992 261238408526229992 endpoint_10_64_p8 endpoint_10_64_w8
def endpoint_10_64 : CertifiedEndpoint :=
  ⟨⟨10, 64, 3241⟩, 261238408526229992, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_64_flag endpoint_10_64_sources 9 261238408526229992 261238408526229992 rfl endpoint_10_64_base endpoint_10_64_p9) (by decide)⟩
private def endpoint_10_65_flag : Flag := ⟨10, 65, 3180⟩
private def endpoint_10_65_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_10_65_base : receiptBase endpoint_10_65_flag endpoint_10_65_sources = some 259906689193482066 := by decide +kernel
private theorem endpoint_10_65_w0 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 2 259906689193482066 = some 259906689193482066 := by decide +kernel
private theorem endpoint_10_65_w2 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 2 2 259906689193482066 = some 259906689193482066 := by decide +kernel
private theorem endpoint_10_65_p4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 4 259906689193482066 = some 259906689193482066 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 2 2 259906689193482066 259906689193482066 259906689193482066 endpoint_10_65_w0 endpoint_10_65_w2
private theorem endpoint_10_65_w4 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 4 2 259906689193482066 = some 259906689193482066 := by decide +kernel
private theorem endpoint_10_65_p6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 6 259906689193482066 = some 259906689193482066 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 4 2 259906689193482066 259906689193482066 259906689193482066 endpoint_10_65_p4 endpoint_10_65_w4
private theorem endpoint_10_65_w6 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 6 2 259906689193482066 = some 259906689193482066 := by decide +kernel
private theorem endpoint_10_65_p8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 8 259906689193482066 = some 259906689193482066 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 6 2 259906689193482066 259906689193482066 259906689193482066 endpoint_10_65_p6 endpoint_10_65_w6
private theorem endpoint_10_65_w8 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 8 1 259906689193482066 = some 259906689193482066 := by decide +kernel
private theorem endpoint_10_65_p9 : receiptWindow endpoint_10_65_flag endpoint_10_65_sources 0 9 259906689193482066 = some 259906689193482066 :=
  join_receipt_window endpoint_10_65_flag endpoint_10_65_sources 0 8 1 259906689193482066 259906689193482066 259906689193482066 endpoint_10_65_p8 endpoint_10_65_w8
def endpoint_10_65 : CertifiedEndpoint :=
  ⟨⟨10, 65, 3180⟩, 259906689193482066, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_10_65_flag endpoint_10_65_sources 9 259906689193482066 259906689193482066 rfl endpoint_10_65_base endpoint_10_65_p9) (by decide)⟩
private def endpoint_10_66_flag : Flag := ⟨10, 66, 3116⟩
private def endpoint_10_66_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_10_66_base : receiptBase endpoint_10_66_flag endpoint_10_66_sources = some 259634745372974460 := by decide +kernel
private theorem endpoint_10_66_w0 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 2 259634745372974460 = some 259634745372974460 := by decide +kernel
private theorem endpoint_10_66_w2 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 2 2 259634745372974460 = some 259634745372974460 := by decide +kernel
private theorem endpoint_10_66_p4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 4 259634745372974460 = some 259634745372974460 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 2 2 259634745372974460 259634745372974460 259634745372974460 endpoint_10_66_w0 endpoint_10_66_w2
private theorem endpoint_10_66_w4 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 4 2 259634745372974460 = some 259634745372974460 := by decide +kernel
private theorem endpoint_10_66_p6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 6 259634745372974460 = some 259634745372974460 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 4 2 259634745372974460 259634745372974460 259634745372974460 endpoint_10_66_p4 endpoint_10_66_w4
private theorem endpoint_10_66_w6 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 6 2 259634745372974460 = some 259634745372974460 := by decide +kernel
private theorem endpoint_10_66_p8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 8 259634745372974460 = some 259634745372974460 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 6 2 259634745372974460 259634745372974460 259634745372974460 endpoint_10_66_p6 endpoint_10_66_w6
private theorem endpoint_10_66_w8 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 8 1 259634745372974460 = some 259634745372974460 := by decide +kernel
private theorem endpoint_10_66_p9 : receiptWindow endpoint_10_66_flag endpoint_10_66_sources 0 9 259634745372974460 = some 259634745372974460 :=
  join_receipt_window endpoint_10_66_flag endpoint_10_66_sources 0 8 1 259634745372974460 259634745372974460 259634745372974460 endpoint_10_66_p8 endpoint_10_66_w8
def endpoint_10_66 : CertifiedEndpoint :=
  ⟨⟨10, 66, 3116⟩, 259634745372974460, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_10_66_flag endpoint_10_66_sources 9 259634745372974460 259634745372974460 rfl endpoint_10_66_base endpoint_10_66_p9) (by decide)⟩
private def endpoint_10_67_flag : Flag := ⟨10, 67, 3049⟩
private def endpoint_10_67_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_10_67_base : receiptBase endpoint_10_67_flag endpoint_10_67_sources = some 258991844278238882 := by decide +kernel
private theorem endpoint_10_67_w0 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 2 258991844278238882 = some 258991844278238882 := by decide +kernel
private theorem endpoint_10_67_w2 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 2 2 258991844278238882 = some 258991844278238882 := by decide +kernel
private theorem endpoint_10_67_p4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 4 258991844278238882 = some 258991844278238882 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 2 2 258991844278238882 258991844278238882 258991844278238882 endpoint_10_67_w0 endpoint_10_67_w2
private theorem endpoint_10_67_w4 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 4 2 258991844278238882 = some 258991844278238882 := by decide +kernel
private theorem endpoint_10_67_p6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 6 258991844278238882 = some 258991844278238882 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 4 2 258991844278238882 258991844278238882 258991844278238882 endpoint_10_67_p4 endpoint_10_67_w4
private theorem endpoint_10_67_w6 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 6 2 258991844278238882 = some 258991844278238882 := by decide +kernel
private theorem endpoint_10_67_p8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 8 258991844278238882 = some 258991844278238882 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 6 2 258991844278238882 258991844278238882 258991844278238882 endpoint_10_67_p6 endpoint_10_67_w6
private theorem endpoint_10_67_w8 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 8 1 258991844278238882 = some 258991844278238882 := by decide +kernel
private theorem endpoint_10_67_p9 : receiptWindow endpoint_10_67_flag endpoint_10_67_sources 0 9 258991844278238882 = some 258991844278238882 :=
  join_receipt_window endpoint_10_67_flag endpoint_10_67_sources 0 8 1 258991844278238882 258991844278238882 258991844278238882 endpoint_10_67_p8 endpoint_10_67_w8
def endpoint_10_67 : CertifiedEndpoint :=
  ⟨⟨10, 67, 3049⟩, 258991844278238882, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_10_67_flag endpoint_10_67_sources 9 258991844278238882 258991844278238882 rfl endpoint_10_67_base endpoint_10_67_p9) (by decide)⟩
private def endpoint_10_68_flag : Flag := ⟨10, 68, 2979⟩
private def endpoint_10_68_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_68_base : receiptBase endpoint_10_68_flag endpoint_10_68_sources = some 257806503029930195 := by decide +kernel
private theorem endpoint_10_68_w0 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 2 257806503029930195 = some 257806503029930195 := by decide +kernel
private theorem endpoint_10_68_w2 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 2 2 257806503029930195 = some 257806503029930195 := by decide +kernel
private theorem endpoint_10_68_p4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 4 257806503029930195 = some 257806503029930195 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 2 2 257806503029930195 257806503029930195 257806503029930195 endpoint_10_68_w0 endpoint_10_68_w2
private theorem endpoint_10_68_w4 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 4 2 257806503029930195 = some 257806503029930195 := by decide +kernel
private theorem endpoint_10_68_p6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 6 257806503029930195 = some 257806503029930195 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 4 2 257806503029930195 257806503029930195 257806503029930195 endpoint_10_68_p4 endpoint_10_68_w4
private theorem endpoint_10_68_w6 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 6 2 257806503029930195 = some 257806503029930195 := by decide +kernel
private theorem endpoint_10_68_p8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 8 257806503029930195 = some 257806503029930195 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 6 2 257806503029930195 257806503029930195 257806503029930195 endpoint_10_68_p6 endpoint_10_68_w6
private theorem endpoint_10_68_w8 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 8 1 257806503029930195 = some 257806503029930195 := by decide +kernel
private theorem endpoint_10_68_p9 : receiptWindow endpoint_10_68_flag endpoint_10_68_sources 0 9 257806503029930195 = some 257806503029930195 :=
  join_receipt_window endpoint_10_68_flag endpoint_10_68_sources 0 8 1 257806503029930195 257806503029930195 257806503029930195 endpoint_10_68_p8 endpoint_10_68_w8
def endpoint_10_68 : CertifiedEndpoint :=
  ⟨⟨10, 68, 2979⟩, 257806503029930195, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_68_flag endpoint_10_68_sources 9 257806503029930195 257806503029930195 rfl endpoint_10_68_base endpoint_10_68_p9) (by decide)⟩
private def endpoint_10_69_flag : Flag := ⟨10, 69, 2907⟩
private def endpoint_10_69_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_69_base : receiptBase endpoint_10_69_flag endpoint_10_69_sources = some 254930934629561337 := by decide +kernel
private theorem endpoint_10_69_w0 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 2 254930934629561337 = some 254930934629561337 := by decide +kernel
private theorem endpoint_10_69_w2 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 2 2 254930934629561337 = some 254930934629561337 := by decide +kernel
private theorem endpoint_10_69_p4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 4 254930934629561337 = some 254930934629561337 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 2 2 254930934629561337 254930934629561337 254930934629561337 endpoint_10_69_w0 endpoint_10_69_w2
private theorem endpoint_10_69_w4 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 4 2 254930934629561337 = some 254930934629561337 := by decide +kernel
private theorem endpoint_10_69_p6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 6 254930934629561337 = some 254930934629561337 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 4 2 254930934629561337 254930934629561337 254930934629561337 endpoint_10_69_p4 endpoint_10_69_w4
private theorem endpoint_10_69_w6 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 6 2 254930934629561337 = some 254930934629561337 := by decide +kernel
private theorem endpoint_10_69_p8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 8 254930934629561337 = some 254930934629561337 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 6 2 254930934629561337 254930934629561337 254930934629561337 endpoint_10_69_p6 endpoint_10_69_w6
private theorem endpoint_10_69_w8 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 8 1 254930934629561337 = some 254930934629561337 := by decide +kernel
private theorem endpoint_10_69_p9 : receiptWindow endpoint_10_69_flag endpoint_10_69_sources 0 9 254930934629561337 = some 254930934629561337 :=
  join_receipt_window endpoint_10_69_flag endpoint_10_69_sources 0 8 1 254930934629561337 254930934629561337 254930934629561337 endpoint_10_69_p8 endpoint_10_69_w8
def endpoint_10_69 : CertifiedEndpoint :=
  ⟨⟨10, 69, 2907⟩, 254930934629561337, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_69_flag endpoint_10_69_sources 9 254930934629561337 254930934629561337 rfl endpoint_10_69_base endpoint_10_69_p9) (by decide)⟩
private def endpoint_10_70_flag : Flag := ⟨10, 70, 2831⟩
private def endpoint_10_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_70_base : receiptBase endpoint_10_70_flag endpoint_10_70_sources = some 251539021606441493 := by decide +kernel
private theorem endpoint_10_70_w0 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 2 251539021606441493 = some 251539021606441493 := by decide +kernel
private theorem endpoint_10_70_w2 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 2 2 251539021606441493 = some 251539021606441493 := by decide +kernel
private theorem endpoint_10_70_p4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 4 251539021606441493 = some 251539021606441493 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 2 2 251539021606441493 251539021606441493 251539021606441493 endpoint_10_70_w0 endpoint_10_70_w2
private theorem endpoint_10_70_w4 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 4 2 251539021606441493 = some 251539021606441493 := by decide +kernel
private theorem endpoint_10_70_p6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 6 251539021606441493 = some 251539021606441493 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 4 2 251539021606441493 251539021606441493 251539021606441493 endpoint_10_70_p4 endpoint_10_70_w4
private theorem endpoint_10_70_w6 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 6 2 251539021606441493 = some 251539021606441493 := by decide +kernel
private theorem endpoint_10_70_p8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 8 251539021606441493 = some 251539021606441493 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 6 2 251539021606441493 251539021606441493 251539021606441493 endpoint_10_70_p6 endpoint_10_70_w6
private theorem endpoint_10_70_w8 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 8 1 251539021606441493 = some 251539021606441493 := by decide +kernel
private theorem endpoint_10_70_p9 : receiptWindow endpoint_10_70_flag endpoint_10_70_sources 0 9 251539021606441493 = some 251539021606441493 :=
  join_receipt_window endpoint_10_70_flag endpoint_10_70_sources 0 8 1 251539021606441493 251539021606441493 251539021606441493 endpoint_10_70_p8 endpoint_10_70_w8
def endpoint_10_70 : CertifiedEndpoint :=
  ⟨⟨10, 70, 2831⟩, 251539021606441493, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_70_flag endpoint_10_70_sources 9 251539021606441493 251539021606441493 rfl endpoint_10_70_base endpoint_10_70_p9) (by decide)⟩
private def endpoint_10_71_flag : Flag := ⟨10, 71, 2752⟩
private def endpoint_10_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_10_71_base : receiptBase endpoint_10_71_flag endpoint_10_71_sources = some 247706305467196732 := by decide +kernel
private theorem endpoint_10_71_w0 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 2 247706305467196732 = some 247706305467196732 := by decide +kernel
private theorem endpoint_10_71_w2 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 2 2 247706305467196732 = some 247706305467196732 := by decide +kernel
private theorem endpoint_10_71_p4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 4 247706305467196732 = some 247706305467196732 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 2 2 247706305467196732 247706305467196732 247706305467196732 endpoint_10_71_w0 endpoint_10_71_w2
private theorem endpoint_10_71_w4 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 4 2 247706305467196732 = some 247706305467196732 := by decide +kernel
private theorem endpoint_10_71_p6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 6 247706305467196732 = some 247706305467196732 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 4 2 247706305467196732 247706305467196732 247706305467196732 endpoint_10_71_p4 endpoint_10_71_w4
private theorem endpoint_10_71_w6 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 6 2 247706305467196732 = some 247706305467196732 := by decide +kernel
private theorem endpoint_10_71_p8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 8 247706305467196732 = some 247706305467196732 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 6 2 247706305467196732 247706305467196732 247706305467196732 endpoint_10_71_p6 endpoint_10_71_w6
private theorem endpoint_10_71_w8 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 8 1 247706305467196732 = some 247706305467196732 := by decide +kernel
private theorem endpoint_10_71_p9 : receiptWindow endpoint_10_71_flag endpoint_10_71_sources 0 9 247706305467196732 = some 247706305467196732 :=
  join_receipt_window endpoint_10_71_flag endpoint_10_71_sources 0 8 1 247706305467196732 247706305467196732 247706305467196732 endpoint_10_71_p8 endpoint_10_71_w8
def endpoint_10_71 : CertifiedEndpoint :=
  ⟨⟨10, 71, 2752⟩, 247706305467196732, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_10_71_flag endpoint_10_71_sources 9 247706305467196732 247706305467196732 rfl endpoint_10_71_base endpoint_10_71_p9) (by decide)⟩
private def endpoint_10_72_flag : Flag := ⟨10, 72, 2670⟩
private def endpoint_10_72_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_72_base : receiptBase endpoint_10_72_flag endpoint_10_72_sources = some 248512081076730401 := by decide +kernel
private theorem endpoint_10_72_w0 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 2 248512081076730401 = some 248512081076730401 := by decide +kernel
private theorem endpoint_10_72_w2 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 2 2 248512081076730401 = some 248512081076730401 := by decide +kernel
private theorem endpoint_10_72_p4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 4 248512081076730401 = some 248512081076730401 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 2 2 248512081076730401 248512081076730401 248512081076730401 endpoint_10_72_w0 endpoint_10_72_w2
private theorem endpoint_10_72_w4 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 4 2 248512081076730401 = some 248512081076730401 := by decide +kernel
private theorem endpoint_10_72_p6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 6 248512081076730401 = some 248512081076730401 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 4 2 248512081076730401 248512081076730401 248512081076730401 endpoint_10_72_p4 endpoint_10_72_w4
private theorem endpoint_10_72_w6 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 6 2 248512081076730401 = some 248512081076730401 := by decide +kernel
private theorem endpoint_10_72_p8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 8 248512081076730401 = some 248512081076730401 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 6 2 248512081076730401 248512081076730401 248512081076730401 endpoint_10_72_p6 endpoint_10_72_w6
private theorem endpoint_10_72_w8 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 8 1 248512081076730401 = some 248512081076730401 := by decide +kernel
private theorem endpoint_10_72_p9 : receiptWindow endpoint_10_72_flag endpoint_10_72_sources 0 9 248512081076730401 = some 248512081076730401 :=
  join_receipt_window endpoint_10_72_flag endpoint_10_72_sources 0 8 1 248512081076730401 248512081076730401 248512081076730401 endpoint_10_72_p8 endpoint_10_72_w8
def endpoint_10_72 : CertifiedEndpoint :=
  ⟨⟨10, 72, 2670⟩, 248512081076730401, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_72_flag endpoint_10_72_sources 9 248512081076730401 248512081076730401 rfl endpoint_10_72_base endpoint_10_72_p9) (by decide)⟩
private def endpoint_10_73_flag : Flag := ⟨10, 73, 2585⟩
private def endpoint_10_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_73_base : receiptBase endpoint_10_73_flag endpoint_10_73_sources = some 243720209763521028 := by decide +kernel
private theorem endpoint_10_73_w0 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 2 243720209763521028 = some 243720209763521028 := by decide +kernel
private theorem endpoint_10_73_w2 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 2 2 243720209763521028 = some 243720209763521028 := by decide +kernel
private theorem endpoint_10_73_p4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 4 243720209763521028 = some 243720209763521028 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 2 2 243720209763521028 243720209763521028 243720209763521028 endpoint_10_73_w0 endpoint_10_73_w2
private theorem endpoint_10_73_w4 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 4 2 243720209763521028 = some 243720209763521028 := by decide +kernel
private theorem endpoint_10_73_p6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 6 243720209763521028 = some 243720209763521028 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 4 2 243720209763521028 243720209763521028 243720209763521028 endpoint_10_73_p4 endpoint_10_73_w4
private theorem endpoint_10_73_w6 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 6 2 243720209763521028 = some 243720209763521028 := by decide +kernel
private theorem endpoint_10_73_p8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 8 243720209763521028 = some 243720209763521028 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 6 2 243720209763521028 243720209763521028 243720209763521028 endpoint_10_73_p6 endpoint_10_73_w6
private theorem endpoint_10_73_w8 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 8 1 243720209763521028 = some 243720209763521028 := by decide +kernel
private theorem endpoint_10_73_p9 : receiptWindow endpoint_10_73_flag endpoint_10_73_sources 0 9 243720209763521028 = some 243720209763521028 :=
  join_receipt_window endpoint_10_73_flag endpoint_10_73_sources 0 8 1 243720209763521028 243720209763521028 243720209763521028 endpoint_10_73_p8 endpoint_10_73_w8
def endpoint_10_73 : CertifiedEndpoint :=
  ⟨⟨10, 73, 2585⟩, 243720209763521028, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_73_flag endpoint_10_73_sources 9 243720209763521028 243720209763521028 rfl endpoint_10_73_base endpoint_10_73_p9) (by decide)⟩
private def endpoint_10_74_flag : Flag := ⟨10, 74, 2498⟩
private def endpoint_10_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_10_74_base : receiptBase endpoint_10_74_flag endpoint_10_74_sources = some 238547003249194828 := by decide +kernel
private theorem endpoint_10_74_w0 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 2 238547003249194828 = some 238547003249194828 := by decide +kernel
private theorem endpoint_10_74_w2 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 2 2 238547003249194828 = some 238547003249194828 := by decide +kernel
private theorem endpoint_10_74_p4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 4 238547003249194828 = some 238547003249194828 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 2 2 238547003249194828 238547003249194828 238547003249194828 endpoint_10_74_w0 endpoint_10_74_w2
private theorem endpoint_10_74_w4 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 4 2 238547003249194828 = some 238547003249194828 := by decide +kernel
private theorem endpoint_10_74_p6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 6 238547003249194828 = some 238547003249194828 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 4 2 238547003249194828 238547003249194828 238547003249194828 endpoint_10_74_p4 endpoint_10_74_w4
private theorem endpoint_10_74_w6 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 6 2 238547003249194828 = some 238547003249194828 := by decide +kernel
private theorem endpoint_10_74_p8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 8 238547003249194828 = some 238547003249194828 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 6 2 238547003249194828 238547003249194828 238547003249194828 endpoint_10_74_p6 endpoint_10_74_w6
private theorem endpoint_10_74_w8 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 8 1 238547003249194828 = some 238547003249194828 := by decide +kernel
private theorem endpoint_10_74_p9 : receiptWindow endpoint_10_74_flag endpoint_10_74_sources 0 9 238547003249194828 = some 238547003249194828 :=
  join_receipt_window endpoint_10_74_flag endpoint_10_74_sources 0 8 1 238547003249194828 238547003249194828 238547003249194828 endpoint_10_74_p8 endpoint_10_74_w8
def endpoint_10_74 : CertifiedEndpoint :=
  ⟨⟨10, 74, 2498⟩, 238547003249194828, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_10_74_flag endpoint_10_74_sources 9 238547003249194828 238547003249194828 rfl endpoint_10_74_base endpoint_10_74_p9) (by decide)⟩
private def endpoint_10_75_flag : Flag := ⟨10, 75, 2407⟩
private def endpoint_10_75_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_75_base : receiptBase endpoint_10_75_flag endpoint_10_75_sources = some 234758461484758358 := by decide +kernel
private theorem endpoint_10_75_w0 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 2 234758461484758358 = some 234758461484758358 := by decide +kernel
private theorem endpoint_10_75_w2 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 2 2 234758461484758358 = some 234758461484758358 := by decide +kernel
private theorem endpoint_10_75_p4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 4 234758461484758358 = some 234758461484758358 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 2 2 234758461484758358 234758461484758358 234758461484758358 endpoint_10_75_w0 endpoint_10_75_w2
private theorem endpoint_10_75_w4 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 4 2 234758461484758358 = some 234758461484758358 := by decide +kernel
private theorem endpoint_10_75_p6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 6 234758461484758358 = some 234758461484758358 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 4 2 234758461484758358 234758461484758358 234758461484758358 endpoint_10_75_p4 endpoint_10_75_w4
private theorem endpoint_10_75_w6 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 6 2 234758461484758358 = some 234758461484758358 := by decide +kernel
private theorem endpoint_10_75_p8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 8 234758461484758358 = some 234758461484758358 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 6 2 234758461484758358 234758461484758358 234758461484758358 endpoint_10_75_p6 endpoint_10_75_w6
private theorem endpoint_10_75_w8 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 8 1 234758461484758358 = some 234758461484758358 := by decide +kernel
private theorem endpoint_10_75_p9 : receiptWindow endpoint_10_75_flag endpoint_10_75_sources 0 9 234758461484758358 = some 234758461484758358 :=
  join_receipt_window endpoint_10_75_flag endpoint_10_75_sources 0 8 1 234758461484758358 234758461484758358 234758461484758358 endpoint_10_75_p8 endpoint_10_75_w8
def endpoint_10_75 : CertifiedEndpoint :=
  ⟨⟨10, 75, 2407⟩, 234758461484758358, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_75_flag endpoint_10_75_sources 9 234758461484758358 234758461484758358 rfl endpoint_10_75_base endpoint_10_75_p9) (by decide)⟩
private def endpoint_10_76_flag : Flag := ⟨10, 76, 2313⟩
private def endpoint_10_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_10_76_base : receiptBase endpoint_10_76_flag endpoint_10_76_sources = some 228369119643523402 := by decide +kernel
private theorem endpoint_10_76_w0 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 2 228369119643523402 = some 228369119643523402 := by decide +kernel
private theorem endpoint_10_76_w2 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 2 2 228369119643523402 = some 228369119643523402 := by decide +kernel
private theorem endpoint_10_76_p4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 4 228369119643523402 = some 228369119643523402 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 2 2 228369119643523402 228369119643523402 228369119643523402 endpoint_10_76_w0 endpoint_10_76_w2
private theorem endpoint_10_76_w4 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 4 2 228369119643523402 = some 228369119643523402 := by decide +kernel
private theorem endpoint_10_76_p6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 6 228369119643523402 = some 228369119643523402 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 4 2 228369119643523402 228369119643523402 228369119643523402 endpoint_10_76_p4 endpoint_10_76_w4
private theorem endpoint_10_76_w6 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 6 2 228369119643523402 = some 228369119643523402 := by decide +kernel
private theorem endpoint_10_76_p8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 8 228369119643523402 = some 228369119643523402 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 6 2 228369119643523402 228369119643523402 228369119643523402 endpoint_10_76_p6 endpoint_10_76_w6
private theorem endpoint_10_76_w8 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 8 1 228369119643523402 = some 228369119643523402 := by decide +kernel
private theorem endpoint_10_76_p9 : receiptWindow endpoint_10_76_flag endpoint_10_76_sources 0 9 228369119643523402 = some 228369119643523402 :=
  join_receipt_window endpoint_10_76_flag endpoint_10_76_sources 0 8 1 228369119643523402 228369119643523402 228369119643523402 endpoint_10_76_p8 endpoint_10_76_w8
def endpoint_10_76 : CertifiedEndpoint :=
  ⟨⟨10, 76, 2313⟩, 228369119643523402, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_10_76_flag endpoint_10_76_sources 9 228369119643523402 228369119643523402 rfl endpoint_10_76_base endpoint_10_76_p9) (by decide)⟩
private def endpoint_10_77_flag : Flag := ⟨10, 77, 2216⟩
private def endpoint_10_77_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_10_77_base : receiptBase endpoint_10_77_flag endpoint_10_77_sources = some 223479990059867777 := by decide +kernel
private theorem endpoint_10_77_w0 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 2 223479990059867777 = some 223479990059867777 := by decide +kernel
private theorem endpoint_10_77_w2 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 2 2 223479990059867777 = some 223479990059867777 := by decide +kernel
private theorem endpoint_10_77_p4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 4 223479990059867777 = some 223479990059867777 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 2 2 223479990059867777 223479990059867777 223479990059867777 endpoint_10_77_w0 endpoint_10_77_w2
private theorem endpoint_10_77_w4 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 4 2 223479990059867777 = some 223479990059867777 := by decide +kernel
private theorem endpoint_10_77_p6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 6 223479990059867777 = some 223479990059867777 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 4 2 223479990059867777 223479990059867777 223479990059867777 endpoint_10_77_p4 endpoint_10_77_w4
private theorem endpoint_10_77_w6 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 6 2 223479990059867777 = some 223479990059867777 := by decide +kernel
private theorem endpoint_10_77_p8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 8 223479990059867777 = some 223479990059867777 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 6 2 223479990059867777 223479990059867777 223479990059867777 endpoint_10_77_p6 endpoint_10_77_w6
private theorem endpoint_10_77_w8 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 8 1 223479990059867777 = some 223479990059867777 := by decide +kernel
private theorem endpoint_10_77_p9 : receiptWindow endpoint_10_77_flag endpoint_10_77_sources 0 9 223479990059867777 = some 223479990059867777 :=
  join_receipt_window endpoint_10_77_flag endpoint_10_77_sources 0 8 1 223479990059867777 223479990059867777 223479990059867777 endpoint_10_77_p8 endpoint_10_77_w8
def endpoint_10_77 : CertifiedEndpoint :=
  ⟨⟨10, 77, 2216⟩, 223479990059867777, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_10_77_flag endpoint_10_77_sources 9 223479990059867777 223479990059867777 rfl endpoint_10_77_base endpoint_10_77_p9) (by decide)⟩
private def endpoint_10_78_flag : Flag := ⟨10, 78, 2116⟩
private def endpoint_10_78_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_78_base : receiptBase endpoint_10_78_flag endpoint_10_78_sources = some 218039801980173750 := by decide +kernel
private theorem endpoint_10_78_w0 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 2 218039801980173750 = some 218039801980173750 := by decide +kernel
private theorem endpoint_10_78_w2 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 2 2 218039801980173750 = some 218039801980173750 := by decide +kernel
private theorem endpoint_10_78_p4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 4 218039801980173750 = some 218039801980173750 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 2 2 218039801980173750 218039801980173750 218039801980173750 endpoint_10_78_w0 endpoint_10_78_w2
private theorem endpoint_10_78_w4 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 4 2 218039801980173750 = some 218039801980173750 := by decide +kernel
private theorem endpoint_10_78_p6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 6 218039801980173750 = some 218039801980173750 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 4 2 218039801980173750 218039801980173750 218039801980173750 endpoint_10_78_p4 endpoint_10_78_w4
private theorem endpoint_10_78_w6 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 6 2 218039801980173750 = some 218039801980173750 := by decide +kernel
private theorem endpoint_10_78_p8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 8 218039801980173750 = some 218039801980173750 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 6 2 218039801980173750 218039801980173750 218039801980173750 endpoint_10_78_p6 endpoint_10_78_w6
private theorem endpoint_10_78_w8 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 8 1 218039801980173750 = some 218039801980173750 := by decide +kernel
private theorem endpoint_10_78_p9 : receiptWindow endpoint_10_78_flag endpoint_10_78_sources 0 9 218039801980173750 = some 218039801980173750 :=
  join_receipt_window endpoint_10_78_flag endpoint_10_78_sources 0 8 1 218039801980173750 218039801980173750 218039801980173750 endpoint_10_78_p8 endpoint_10_78_w8
def endpoint_10_78 : CertifiedEndpoint :=
  ⟨⟨10, 78, 2116⟩, 218039801980173750, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_78_flag endpoint_10_78_sources 9 218039801980173750 218039801980173750 rfl endpoint_10_78_base endpoint_10_78_p9) (by decide)⟩
private def endpoint_10_79_flag : Flag := ⟨10, 79, 2012⟩
private def endpoint_10_79_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_79_base : receiptBase endpoint_10_79_flag endpoint_10_79_sources = some 209779115001117686 := by decide +kernel
private theorem endpoint_10_79_w0 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 2 209779115001117686 = some 209779115001117686 := by decide +kernel
private theorem endpoint_10_79_w2 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 2 2 209779115001117686 = some 209779115001117686 := by decide +kernel
private theorem endpoint_10_79_p4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 4 209779115001117686 = some 209779115001117686 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 2 2 209779115001117686 209779115001117686 209779115001117686 endpoint_10_79_w0 endpoint_10_79_w2
private theorem endpoint_10_79_w4 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 4 2 209779115001117686 = some 209779115001117686 := by decide +kernel
private theorem endpoint_10_79_p6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 6 209779115001117686 = some 209779115001117686 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 4 2 209779115001117686 209779115001117686 209779115001117686 endpoint_10_79_p4 endpoint_10_79_w4
private theorem endpoint_10_79_w6 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 6 2 209779115001117686 = some 209779115001117686 := by decide +kernel
private theorem endpoint_10_79_p8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 8 209779115001117686 = some 209779115001117686 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 6 2 209779115001117686 209779115001117686 209779115001117686 endpoint_10_79_p6 endpoint_10_79_w6
private theorem endpoint_10_79_w8 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 8 1 209779115001117686 = some 209779115001117686 := by decide +kernel
private theorem endpoint_10_79_p9 : receiptWindow endpoint_10_79_flag endpoint_10_79_sources 0 9 209779115001117686 = some 209779115001117686 :=
  join_receipt_window endpoint_10_79_flag endpoint_10_79_sources 0 8 1 209779115001117686 209779115001117686 209779115001117686 endpoint_10_79_p8 endpoint_10_79_w8
def endpoint_10_79 : CertifiedEndpoint :=
  ⟨⟨10, 79, 2012⟩, 209779115001117686, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_79_flag endpoint_10_79_sources 9 209779115001117686 209779115001117686 rfl endpoint_10_79_base endpoint_10_79_p9) (by decide)⟩
private def endpoint_10_80_flag : Flag := ⟨10, 80, 1906⟩
private def endpoint_10_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_10_80_base : receiptBase endpoint_10_80_flag endpoint_10_80_sources = some 201062192015262589 := by decide +kernel
private theorem endpoint_10_80_w0 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 2 201062192015262589 = some 201062192015262589 := by decide +kernel
private theorem endpoint_10_80_w2 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 2 2 201062192015262589 = some 201062192015262589 := by decide +kernel
private theorem endpoint_10_80_p4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 4 201062192015262589 = some 201062192015262589 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 2 2 201062192015262589 201062192015262589 201062192015262589 endpoint_10_80_w0 endpoint_10_80_w2
private theorem endpoint_10_80_w4 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 4 2 201062192015262589 = some 201062192015262589 := by decide +kernel
private theorem endpoint_10_80_p6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 6 201062192015262589 = some 201062192015262589 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 4 2 201062192015262589 201062192015262589 201062192015262589 endpoint_10_80_p4 endpoint_10_80_w4
private theorem endpoint_10_80_w6 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 6 2 201062192015262589 = some 201062192015262589 := by decide +kernel
private theorem endpoint_10_80_p8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 8 201062192015262589 = some 201062192015262589 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 6 2 201062192015262589 201062192015262589 201062192015262589 endpoint_10_80_p6 endpoint_10_80_w6
private theorem endpoint_10_80_w8 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 8 1 201062192015262589 = some 201062192015262589 := by decide +kernel
private theorem endpoint_10_80_p9 : receiptWindow endpoint_10_80_flag endpoint_10_80_sources 0 9 201062192015262589 = some 201062192015262589 :=
  join_receipt_window endpoint_10_80_flag endpoint_10_80_sources 0 8 1 201062192015262589 201062192015262589 201062192015262589 endpoint_10_80_p8 endpoint_10_80_w8
def endpoint_10_80 : CertifiedEndpoint :=
  ⟨⟨10, 80, 1906⟩, 201062192015262589, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_10_80_flag endpoint_10_80_sources 9 201062192015262589 201062192015262589 rfl endpoint_10_80_base endpoint_10_80_p9) (by decide)⟩
private def endpoint_10_81_flag : Flag := ⟨10, 81, 1797⟩
private def endpoint_10_81_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_81_base : receiptBase endpoint_10_81_flag endpoint_10_81_sources = some 195601592565246801 := by decide +kernel
private theorem endpoint_10_81_w0 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 2 195601592565246801 = some 195601592565246801 := by decide +kernel
private theorem endpoint_10_81_w2 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 2 2 195601592565246801 = some 195601592565246801 := by decide +kernel
private theorem endpoint_10_81_p4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 4 195601592565246801 = some 195601592565246801 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 2 2 195601592565246801 195601592565246801 195601592565246801 endpoint_10_81_w0 endpoint_10_81_w2
private theorem endpoint_10_81_w4 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 4 2 195601592565246801 = some 195601592565246801 := by decide +kernel
private theorem endpoint_10_81_p6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 6 195601592565246801 = some 195601592565246801 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 4 2 195601592565246801 195601592565246801 195601592565246801 endpoint_10_81_p4 endpoint_10_81_w4
private theorem endpoint_10_81_w6 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 6 2 195601592565246801 = some 195601592565246801 := by decide +kernel
private theorem endpoint_10_81_p8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 8 195601592565246801 = some 195601592565246801 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 6 2 195601592565246801 195601592565246801 195601592565246801 endpoint_10_81_p6 endpoint_10_81_w6
private theorem endpoint_10_81_w8 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 8 1 195601592565246801 = some 195601592565246801 := by decide +kernel
private theorem endpoint_10_81_p9 : receiptWindow endpoint_10_81_flag endpoint_10_81_sources 0 9 195601592565246801 = some 195601592565246801 :=
  join_receipt_window endpoint_10_81_flag endpoint_10_81_sources 0 8 1 195601592565246801 195601592565246801 195601592565246801 endpoint_10_81_p8 endpoint_10_81_w8
def endpoint_10_81 : CertifiedEndpoint :=
  ⟨⟨10, 81, 1797⟩, 195601592565246801, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_81_flag endpoint_10_81_sources 9 195601592565246801 195601592565246801 rfl endpoint_10_81_base endpoint_10_81_p9) (by decide)⟩
private def endpoint_10_82_flag : Flag := ⟨10, 82, 1684⟩
private def endpoint_10_82_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_82_base : receiptBase endpoint_10_82_flag endpoint_10_82_sources = some 185372566562825502 := by decide +kernel
private theorem endpoint_10_82_w0 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 2 185372566562825502 = some 185372566562825502 := by decide +kernel
private theorem endpoint_10_82_w2 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 2 2 185372566562825502 = some 185372566562825502 := by decide +kernel
private theorem endpoint_10_82_p4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 4 185372566562825502 = some 185372566562825502 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 2 2 185372566562825502 185372566562825502 185372566562825502 endpoint_10_82_w0 endpoint_10_82_w2
private theorem endpoint_10_82_w4 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 4 2 185372566562825502 = some 185372566562825502 := by decide +kernel
private theorem endpoint_10_82_p6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 6 185372566562825502 = some 185372566562825502 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 4 2 185372566562825502 185372566562825502 185372566562825502 endpoint_10_82_p4 endpoint_10_82_w4
private theorem endpoint_10_82_w6 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 6 2 185372566562825502 = some 185372566562825502 := by decide +kernel
private theorem endpoint_10_82_p8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 8 185372566562825502 = some 185372566562825502 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 6 2 185372566562825502 185372566562825502 185372566562825502 endpoint_10_82_p6 endpoint_10_82_w6
private theorem endpoint_10_82_w8 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 8 1 185372566562825502 = some 185372566562825502 := by decide +kernel
private theorem endpoint_10_82_p9 : receiptWindow endpoint_10_82_flag endpoint_10_82_sources 0 9 185372566562825502 = some 185372566562825502 :=
  join_receipt_window endpoint_10_82_flag endpoint_10_82_sources 0 8 1 185372566562825502 185372566562825502 185372566562825502 endpoint_10_82_p8 endpoint_10_82_w8
def endpoint_10_82 : CertifiedEndpoint :=
  ⟨⟨10, 82, 1684⟩, 185372566562825502, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_82_flag endpoint_10_82_sources 9 185372566562825502 185372566562825502 rfl endpoint_10_82_base endpoint_10_82_p9) (by decide)⟩
private def endpoint_10_83_flag : Flag := ⟨10, 83, 1568⟩
private def endpoint_10_83_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_83_base : receiptBase endpoint_10_83_flag endpoint_10_83_sources = some 174535647363583454 := by decide +kernel
private theorem endpoint_10_83_w0 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 2 174535647363583454 = some 174535647363583454 := by decide +kernel
private theorem endpoint_10_83_w2 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 2 2 174535647363583454 = some 174535647363583454 := by decide +kernel
private theorem endpoint_10_83_p4 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 4 174535647363583454 = some 174535647363583454 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 2 2 174535647363583454 174535647363583454 174535647363583454 endpoint_10_83_w0 endpoint_10_83_w2
private theorem endpoint_10_83_w4 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 4 2 174535647363583454 = some 174535647363583454 := by decide +kernel
private theorem endpoint_10_83_p6 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 6 174535647363583454 = some 174535647363583454 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 4 2 174535647363583454 174535647363583454 174535647363583454 endpoint_10_83_p4 endpoint_10_83_w4
private theorem endpoint_10_83_w6 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 6 2 174535647363583454 = some 174535647363583454 := by decide +kernel
private theorem endpoint_10_83_p8 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 8 174535647363583454 = some 174535647363583454 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 6 2 174535647363583454 174535647363583454 174535647363583454 endpoint_10_83_p6 endpoint_10_83_w6
private theorem endpoint_10_83_w8 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 8 1 174535647363583454 = some 174535647363583454 := by decide +kernel
private theorem endpoint_10_83_p9 : receiptWindow endpoint_10_83_flag endpoint_10_83_sources 0 9 174535647363583454 = some 174535647363583454 :=
  join_receipt_window endpoint_10_83_flag endpoint_10_83_sources 0 8 1 174535647363583454 174535647363583454 174535647363583454 endpoint_10_83_p8 endpoint_10_83_w8
def endpoint_10_83 : CertifiedEndpoint :=
  ⟨⟨10, 83, 1568⟩, 174535647363583454, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_83_flag endpoint_10_83_sources 9 174535647363583454 174535647363583454 rfl endpoint_10_83_base endpoint_10_83_p9) (by decide)⟩
private def endpoint_10_84_flag : Flag := ⟨10, 84, 1450⟩
private def endpoint_10_84_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_10_84_base : receiptBase endpoint_10_84_flag endpoint_10_84_sources = some 163191880439318353 := by decide +kernel
private theorem endpoint_10_84_w0 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 2 163191880439318353 = some 163191880439318353 := by decide +kernel
private theorem endpoint_10_84_w2 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 2 2 163191880439318353 = some 163191880439318353 := by decide +kernel
private theorem endpoint_10_84_p4 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 4 163191880439318353 = some 163191880439318353 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 2 2 163191880439318353 163191880439318353 163191880439318353 endpoint_10_84_w0 endpoint_10_84_w2
private theorem endpoint_10_84_w4 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 4 2 163191880439318353 = some 163191880439318353 := by decide +kernel
private theorem endpoint_10_84_p6 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 6 163191880439318353 = some 163191880439318353 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 4 2 163191880439318353 163191880439318353 163191880439318353 endpoint_10_84_p4 endpoint_10_84_w4
private theorem endpoint_10_84_w6 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 6 2 163191880439318353 = some 163191880439318353 := by decide +kernel
private theorem endpoint_10_84_p8 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 8 163191880439318353 = some 163191880439318353 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 6 2 163191880439318353 163191880439318353 163191880439318353 endpoint_10_84_p6 endpoint_10_84_w6
private theorem endpoint_10_84_w8 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 8 1 163191880439318353 = some 163191880439318353 := by decide +kernel
private theorem endpoint_10_84_p9 : receiptWindow endpoint_10_84_flag endpoint_10_84_sources 0 9 163191880439318353 = some 163191880439318353 :=
  join_receipt_window endpoint_10_84_flag endpoint_10_84_sources 0 8 1 163191880439318353 163191880439318353 163191880439318353 endpoint_10_84_p8 endpoint_10_84_w8
def endpoint_10_84 : CertifiedEndpoint :=
  ⟨⟨10, 84, 1450⟩, 163191880439318353, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_10_84_flag endpoint_10_84_sources 9 163191880439318353 163191880439318353 rfl endpoint_10_84_base endpoint_10_84_p9) (by decide)⟩
def endpoint_10_85 : CertifiedEndpoint :=
  ⟨⟨10, 85, 1328⟩, 250560027525614873, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_86 : CertifiedEndpoint :=
  ⟨⟨10, 86, 1203⟩, 228890123981804073, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_87 : CertifiedEndpoint :=
  ⟨⟨10, 87, 1075⟩, 206002858593767400, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_88 : CertifiedEndpoint :=
  ⟨⟨10, 88, 944⟩, 181876120314247544, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_89 : CertifiedEndpoint :=
  ⟨⟨10, 89, 809⟩, 156282648095246754, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_90 : CertifiedEndpoint :=
  ⟨⟨10, 90, 672⟩, 129608174107960012, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_91 : CertifiedEndpoint :=
  ⟨⟨10, 91, 531⟩, 101417830520620536, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_92 : CertifiedEndpoint :=
  ⟨⟨10, 92, 387⟩, 71894656286711457, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_10_93 : CertifiedEndpoint :=
  ⟨⟨10, 93, 240⟩, 41016540358975465, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_11 : CertifiedEndpoint :=
  ⟨⟨11, 11, 4830⟩, 83126380312413219, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_12 : CertifiedEndpoint :=
  ⟨⟨11, 12, 4808⟩, 86989637809877674, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_13 : CertifiedEndpoint :=
  ⟨⟨11, 13, 4786⟩, 90813964734695933, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_14 : CertifiedEndpoint :=
  ⟨⟨11, 14, 4764⟩, 103290916220249208, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_15 : CertifiedEndpoint :=
  ⟨⟨11, 15, 4741⟩, 115621276767807766, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_16 : CertifiedEndpoint :=
  ⟨⟨11, 16, 4719⟩, 127851209903797419, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_17 : CertifiedEndpoint :=
  ⟨⟨11, 17, 4696⟩, 139929123127076671, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_18 : CertifiedEndpoint :=
  ⟨⟨11, 18, 4673⟩, 151879455444537349, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_19 : CertifiedEndpoint :=
  ⟨⟨11, 19, 4649⟩, 163666909899856258, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_20 : CertifiedEndpoint :=
  ⟨⟨11, 20, 4626⟩, 175359365918321946, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_21 : CertifiedEndpoint :=
  ⟨⟨11, 21, 4602⟩, 186883515099930181, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_22 : CertifiedEndpoint :=
  ⟨⟨11, 22, 4578⟩, 198274654401004158, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_23 : CertifiedEndpoint :=
  ⟨⟨11, 23, 4554⟩, 209532783821543877, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_24 : CertifiedEndpoint :=
  ⟨⟨11, 24, 4529⟩, 220609033968436933, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_25 : CertifiedEndpoint :=
  ⟨⟨11, 25, 4504⟩, 231546845260080047, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_26 : CertifiedEndpoint :=
  ⟨⟨11, 26, 4479⟩, 242346217696473219, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_27 : CertifiedEndpoint :=
  ⟨⟨11, 27, 4454⟩, 253007151277616449, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_11_28 : CertifiedEndpoint :=
  ⟨⟨11, 28, 4428⟩, 263469918660965964, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_11_29_flag : Flag := ⟨11, 29, 4402⟩
private def endpoint_11_29_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_29_base : receiptBase endpoint_11_29_flag endpoint_11_29_sources = some 187277215921694338 := by decide +kernel
private theorem endpoint_11_29_w0 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 2 187277215921694338 = some 187277215921694338 := by decide +kernel
private theorem endpoint_11_29_w2 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 2 2 187277215921694338 = some 187277215921694338 := by decide +kernel
private theorem endpoint_11_29_p4 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 4 187277215921694338 = some 187277215921694338 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 2 2 187277215921694338 187277215921694338 187277215921694338 endpoint_11_29_w0 endpoint_11_29_w2
private theorem endpoint_11_29_w4 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 4 2 187277215921694338 = some 187277215921694338 := by decide +kernel
private theorem endpoint_11_29_p6 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 6 187277215921694338 = some 187277215921694338 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 4 2 187277215921694338 187277215921694338 187277215921694338 endpoint_11_29_p4 endpoint_11_29_w4
private theorem endpoint_11_29_w6 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 6 2 187277215921694338 = some 187277215921694338 := by decide +kernel
private theorem endpoint_11_29_p8 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 8 187277215921694338 = some 187277215921694338 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 6 2 187277215921694338 187277215921694338 187277215921694338 endpoint_11_29_p6 endpoint_11_29_w6
private theorem endpoint_11_29_w8 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 8 2 187277215921694338 = some 187277215921694338 := by decide +kernel
private theorem endpoint_11_29_p10 : receiptWindow endpoint_11_29_flag endpoint_11_29_sources 0 10 187277215921694338 = some 187277215921694338 :=
  join_receipt_window endpoint_11_29_flag endpoint_11_29_sources 0 8 2 187277215921694338 187277215921694338 187277215921694338 endpoint_11_29_p8 endpoint_11_29_w8
def endpoint_11_29 : CertifiedEndpoint :=
  ⟨⟨11, 29, 4402⟩, 187277215921694338, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_29_flag endpoint_11_29_sources 10 187277215921694338 187277215921694338 rfl endpoint_11_29_base endpoint_11_29_p10) (by decide)⟩
private def endpoint_11_30_flag : Flag := ⟨11, 30, 4375⟩
private def endpoint_11_30_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_30_base : receiptBase endpoint_11_30_flag endpoint_11_30_sources = some 191277591830594640 := by decide +kernel
private theorem endpoint_11_30_w0 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 2 191277591830594640 = some 191277591830594640 := by decide +kernel
private theorem endpoint_11_30_w2 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 2 2 191277591830594640 = some 191277591830594640 := by decide +kernel
private theorem endpoint_11_30_p4 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 4 191277591830594640 = some 191277591830594640 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 2 2 191277591830594640 191277591830594640 191277591830594640 endpoint_11_30_w0 endpoint_11_30_w2
private theorem endpoint_11_30_w4 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 4 2 191277591830594640 = some 191277591830594640 := by decide +kernel
private theorem endpoint_11_30_p6 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 6 191277591830594640 = some 191277591830594640 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 4 2 191277591830594640 191277591830594640 191277591830594640 endpoint_11_30_p4 endpoint_11_30_w4
private theorem endpoint_11_30_w6 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 6 2 191277591830594640 = some 191277591830594640 := by decide +kernel
private theorem endpoint_11_30_p8 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 8 191277591830594640 = some 191277591830594640 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 6 2 191277591830594640 191277591830594640 191277591830594640 endpoint_11_30_p6 endpoint_11_30_w6
private theorem endpoint_11_30_w8 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 8 2 191277591830594640 = some 191277591830594640 := by decide +kernel
private theorem endpoint_11_30_p10 : receiptWindow endpoint_11_30_flag endpoint_11_30_sources 0 10 191277591830594640 = some 191277591830594640 :=
  join_receipt_window endpoint_11_30_flag endpoint_11_30_sources 0 8 2 191277591830594640 191277591830594640 191277591830594640 endpoint_11_30_p8 endpoint_11_30_w8
def endpoint_11_30 : CertifiedEndpoint :=
  ⟨⟨11, 30, 4375⟩, 191277591830594640, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_30_flag endpoint_11_30_sources 10 191277591830594640 191277591830594640 rfl endpoint_11_30_base endpoint_11_30_p10) (by decide)⟩
private def endpoint_11_31_flag : Flag := ⟨11, 31, 4349⟩
private def endpoint_11_31_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_31_base : receiptBase endpoint_11_31_flag endpoint_11_31_sources = some 195258894542899620 := by decide +kernel
private theorem endpoint_11_31_w0 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 2 195258894542899620 = some 195258894542899620 := by decide +kernel
private theorem endpoint_11_31_w2 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 2 2 195258894542899620 = some 195258894542899620 := by decide +kernel
private theorem endpoint_11_31_p4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 4 195258894542899620 = some 195258894542899620 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 2 2 195258894542899620 195258894542899620 195258894542899620 endpoint_11_31_w0 endpoint_11_31_w2
private theorem endpoint_11_31_w4 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 4 2 195258894542899620 = some 195258894542899620 := by decide +kernel
private theorem endpoint_11_31_p6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 6 195258894542899620 = some 195258894542899620 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 4 2 195258894542899620 195258894542899620 195258894542899620 endpoint_11_31_p4 endpoint_11_31_w4
private theorem endpoint_11_31_w6 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 6 2 195258894542899620 = some 195258894542899620 := by decide +kernel
private theorem endpoint_11_31_p8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 8 195258894542899620 = some 195258894542899620 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 6 2 195258894542899620 195258894542899620 195258894542899620 endpoint_11_31_p6 endpoint_11_31_w6
private theorem endpoint_11_31_w8 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 8 2 195258894542899620 = some 195258894542899620 := by decide +kernel
private theorem endpoint_11_31_p10 : receiptWindow endpoint_11_31_flag endpoint_11_31_sources 0 10 195258894542899620 = some 195258894542899620 :=
  join_receipt_window endpoint_11_31_flag endpoint_11_31_sources 0 8 2 195258894542899620 195258894542899620 195258894542899620 endpoint_11_31_p8 endpoint_11_31_w8
def endpoint_11_31 : CertifiedEndpoint :=
  ⟨⟨11, 31, 4349⟩, 195258894542899620, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_31_flag endpoint_11_31_sources 10 195258894542899620 195258894542899620 rfl endpoint_11_31_base endpoint_11_31_p10) (by decide)⟩
private def endpoint_11_32_flag : Flag := ⟨11, 32, 4322⟩
private def endpoint_11_32_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_32_base : receiptBase endpoint_11_32_flag endpoint_11_32_sources = some 199133645117948520 := by decide +kernel
private theorem endpoint_11_32_w0 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 2 199133645117948520 = some 199133645117948520 := by decide +kernel
private theorem endpoint_11_32_w2 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 2 2 199133645117948520 = some 199133645117948520 := by decide +kernel
private theorem endpoint_11_32_p4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 4 199133645117948520 = some 199133645117948520 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 2 2 199133645117948520 199133645117948520 199133645117948520 endpoint_11_32_w0 endpoint_11_32_w2
private theorem endpoint_11_32_w4 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 4 2 199133645117948520 = some 199133645117948520 := by decide +kernel
private theorem endpoint_11_32_p6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 6 199133645117948520 = some 199133645117948520 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 4 2 199133645117948520 199133645117948520 199133645117948520 endpoint_11_32_p4 endpoint_11_32_w4
private theorem endpoint_11_32_w6 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 6 2 199133645117948520 = some 199133645117948520 := by decide +kernel
private theorem endpoint_11_32_p8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 8 199133645117948520 = some 199133645117948520 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 6 2 199133645117948520 199133645117948520 199133645117948520 endpoint_11_32_p6 endpoint_11_32_w6
private theorem endpoint_11_32_w8 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 8 2 199133645117948520 = some 199133645117948520 := by decide +kernel
private theorem endpoint_11_32_p10 : receiptWindow endpoint_11_32_flag endpoint_11_32_sources 0 10 199133645117948520 = some 199133645117948520 :=
  join_receipt_window endpoint_11_32_flag endpoint_11_32_sources 0 8 2 199133645117948520 199133645117948520 199133645117948520 endpoint_11_32_p8 endpoint_11_32_w8
def endpoint_11_32 : CertifiedEndpoint :=
  ⟨⟨11, 32, 4322⟩, 199133645117948520, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_32_flag endpoint_11_32_sources 10 199133645117948520 199133645117948520 rfl endpoint_11_32_base endpoint_11_32_p10) (by decide)⟩
private def endpoint_11_33_flag : Flag := ⟨11, 33, 4294⟩
private def endpoint_11_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_33_base : receiptBase endpoint_11_33_flag endpoint_11_33_sources = some 202898386225430112 := by decide +kernel
private theorem endpoint_11_33_w0 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 2 202898386225430112 = some 202898386225430112 := by decide +kernel
private theorem endpoint_11_33_w2 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 2 2 202898386225430112 = some 202898386225430112 := by decide +kernel
private theorem endpoint_11_33_p4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 4 202898386225430112 = some 202898386225430112 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 2 2 202898386225430112 202898386225430112 202898386225430112 endpoint_11_33_w0 endpoint_11_33_w2
private theorem endpoint_11_33_w4 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 4 2 202898386225430112 = some 202898386225430112 := by decide +kernel
private theorem endpoint_11_33_p6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 6 202898386225430112 = some 202898386225430112 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 4 2 202898386225430112 202898386225430112 202898386225430112 endpoint_11_33_p4 endpoint_11_33_w4
private theorem endpoint_11_33_w6 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 6 2 202898386225430112 = some 202898386225430112 := by decide +kernel
private theorem endpoint_11_33_p8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 8 202898386225430112 = some 202898386225430112 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 6 2 202898386225430112 202898386225430112 202898386225430112 endpoint_11_33_p6 endpoint_11_33_w6
private theorem endpoint_11_33_w8 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 8 2 202898386225430112 = some 202898386225430112 := by decide +kernel
private theorem endpoint_11_33_p10 : receiptWindow endpoint_11_33_flag endpoint_11_33_sources 0 10 202898386225430112 = some 202898386225430112 :=
  join_receipt_window endpoint_11_33_flag endpoint_11_33_sources 0 8 2 202898386225430112 202898386225430112 202898386225430112 endpoint_11_33_p8 endpoint_11_33_w8
def endpoint_11_33 : CertifiedEndpoint :=
  ⟨⟨11, 33, 4294⟩, 202898386225430112, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_33_flag endpoint_11_33_sources 10 202898386225430112 202898386225430112 rfl endpoint_11_33_base endpoint_11_33_p10) (by decide)⟩
private def endpoint_11_34_flag : Flag := ⟨11, 34, 4266⟩
private def endpoint_11_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_34_base : receiptBase endpoint_11_34_flag endpoint_11_34_sources = some 206597433557393311 := by decide +kernel
private theorem endpoint_11_34_w0 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 2 206597433557393311 = some 206597433557393311 := by decide +kernel
private theorem endpoint_11_34_w2 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 2 2 206597433557393311 = some 206597433557393311 := by decide +kernel
private theorem endpoint_11_34_p4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 4 206597433557393311 = some 206597433557393311 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 2 2 206597433557393311 206597433557393311 206597433557393311 endpoint_11_34_w0 endpoint_11_34_w2
private theorem endpoint_11_34_w4 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 4 2 206597433557393311 = some 206597433557393311 := by decide +kernel
private theorem endpoint_11_34_p6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 6 206597433557393311 = some 206597433557393311 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 4 2 206597433557393311 206597433557393311 206597433557393311 endpoint_11_34_p4 endpoint_11_34_w4
private theorem endpoint_11_34_w6 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 6 2 206597433557393311 = some 206597433557393311 := by decide +kernel
private theorem endpoint_11_34_p8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 8 206597433557393311 = some 206597433557393311 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 6 2 206597433557393311 206597433557393311 206597433557393311 endpoint_11_34_p6 endpoint_11_34_w6
private theorem endpoint_11_34_w8 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 8 2 206597433557393311 = some 206597433557393311 := by decide +kernel
private theorem endpoint_11_34_p10 : receiptWindow endpoint_11_34_flag endpoint_11_34_sources 0 10 206597433557393311 = some 206597433557393311 :=
  join_receipt_window endpoint_11_34_flag endpoint_11_34_sources 0 8 2 206597433557393311 206597433557393311 206597433557393311 endpoint_11_34_p8 endpoint_11_34_w8
def endpoint_11_34 : CertifiedEndpoint :=
  ⟨⟨11, 34, 4266⟩, 206597433557393311, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_34_flag endpoint_11_34_sources 10 206597433557393311 206597433557393311 rfl endpoint_11_34_base endpoint_11_34_p10) (by decide)⟩
private def endpoint_11_35_flag : Flag := ⟨11, 35, 4238⟩
private def endpoint_11_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_35_base : receiptBase endpoint_11_35_flag endpoint_11_35_sources = some 210230787113838118 := by decide +kernel
private theorem endpoint_11_35_w0 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 2 210230787113838118 = some 210230787113838118 := by decide +kernel
private theorem endpoint_11_35_w2 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 2 2 210230787113838118 = some 210230787113838118 := by decide +kernel
private theorem endpoint_11_35_p4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 4 210230787113838118 = some 210230787113838118 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 2 2 210230787113838118 210230787113838118 210230787113838118 endpoint_11_35_w0 endpoint_11_35_w2
private theorem endpoint_11_35_w4 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 4 2 210230787113838118 = some 210230787113838118 := by decide +kernel
private theorem endpoint_11_35_p6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 6 210230787113838118 = some 210230787113838118 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 4 2 210230787113838118 210230787113838118 210230787113838118 endpoint_11_35_p4 endpoint_11_35_w4
private theorem endpoint_11_35_w6 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 6 2 210230787113838118 = some 210230787113838118 := by decide +kernel
private theorem endpoint_11_35_p8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 8 210230787113838118 = some 210230787113838118 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 6 2 210230787113838118 210230787113838118 210230787113838118 endpoint_11_35_p6 endpoint_11_35_w6
private theorem endpoint_11_35_w8 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 8 2 210230787113838118 = some 210230787113838118 := by decide +kernel
private theorem endpoint_11_35_p10 : receiptWindow endpoint_11_35_flag endpoint_11_35_sources 0 10 210230787113838118 = some 210230787113838118 :=
  join_receipt_window endpoint_11_35_flag endpoint_11_35_sources 0 8 2 210230787113838118 210230787113838118 210230787113838118 endpoint_11_35_p8 endpoint_11_35_w8
def endpoint_11_35 : CertifiedEndpoint :=
  ⟨⟨11, 35, 4238⟩, 210230787113838118, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_35_flag endpoint_11_35_sources 10 210230787113838118 210230787113838118 rfl endpoint_11_35_base endpoint_11_35_p10) (by decide)⟩
private def endpoint_11_36_flag : Flag := ⟨11, 36, 4209⟩
private def endpoint_11_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_36_base : receiptBase endpoint_11_36_flag endpoint_11_36_sources = some 213748368985530232 := by decide +kernel
private theorem endpoint_11_36_w0 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 2 213748368985530232 = some 213748368985530232 := by decide +kernel
private theorem endpoint_11_36_w2 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 2 2 213748368985530232 = some 213748368985530232 := by decide +kernel
private theorem endpoint_11_36_p4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 4 213748368985530232 = some 213748368985530232 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 2 2 213748368985530232 213748368985530232 213748368985530232 endpoint_11_36_w0 endpoint_11_36_w2
private theorem endpoint_11_36_w4 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 4 2 213748368985530232 = some 213748368985530232 := by decide +kernel
private theorem endpoint_11_36_p6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 6 213748368985530232 = some 213748368985530232 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 4 2 213748368985530232 213748368985530232 213748368985530232 endpoint_11_36_p4 endpoint_11_36_w4
private theorem endpoint_11_36_w6 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 6 2 213748368985530232 = some 213748368985530232 := by decide +kernel
private theorem endpoint_11_36_p8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 8 213748368985530232 = some 213748368985530232 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 6 2 213748368985530232 213748368985530232 213748368985530232 endpoint_11_36_p6 endpoint_11_36_w6
private theorem endpoint_11_36_w8 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 8 2 213748368985530232 = some 213748368985530232 := by decide +kernel
private theorem endpoint_11_36_p10 : receiptWindow endpoint_11_36_flag endpoint_11_36_sources 0 10 213748368985530232 = some 213748368985530232 :=
  join_receipt_window endpoint_11_36_flag endpoint_11_36_sources 0 8 2 213748368985530232 213748368985530232 213748368985530232 endpoint_11_36_p8 endpoint_11_36_w8
def endpoint_11_36 : CertifiedEndpoint :=
  ⟨⟨11, 36, 4209⟩, 213748368985530232, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_36_flag endpoint_11_36_sources 10 213748368985530232 213748368985530232 rfl endpoint_11_36_base endpoint_11_36_p10) (by decide)⟩
private def endpoint_11_37_flag : Flag := ⟨11, 37, 4180⟩
private def endpoint_11_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_37_base : receiptBase endpoint_11_37_flag endpoint_11_37_sources = some 217197952194829800 := by decide +kernel
private theorem endpoint_11_37_w0 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 2 217197952194829800 = some 217197952194829800 := by decide +kernel
private theorem endpoint_11_37_w2 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 2 2 217197952194829800 = some 217197952194829800 := by decide +kernel
private theorem endpoint_11_37_p4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 4 217197952194829800 = some 217197952194829800 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 2 2 217197952194829800 217197952194829800 217197952194829800 endpoint_11_37_w0 endpoint_11_37_w2
private theorem endpoint_11_37_w4 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 4 2 217197952194829800 = some 217197952194829800 := by decide +kernel
private theorem endpoint_11_37_p6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 6 217197952194829800 = some 217197952194829800 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 4 2 217197952194829800 217197952194829800 217197952194829800 endpoint_11_37_p4 endpoint_11_37_w4
private theorem endpoint_11_37_w6 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 6 2 217197952194829800 = some 217197952194829800 := by decide +kernel
private theorem endpoint_11_37_p8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 8 217197952194829800 = some 217197952194829800 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 6 2 217197952194829800 217197952194829800 217197952194829800 endpoint_11_37_p6 endpoint_11_37_w6
private theorem endpoint_11_37_w8 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 8 2 217197952194829800 = some 217197952194829800 := by decide +kernel
private theorem endpoint_11_37_p10 : receiptWindow endpoint_11_37_flag endpoint_11_37_sources 0 10 217197952194829800 = some 217197952194829800 :=
  join_receipt_window endpoint_11_37_flag endpoint_11_37_sources 0 8 2 217197952194829800 217197952194829800 217197952194829800 endpoint_11_37_p8 endpoint_11_37_w8
def endpoint_11_37 : CertifiedEndpoint :=
  ⟨⟨11, 37, 4180⟩, 217197952194829800, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_37_flag endpoint_11_37_sources 10 217197952194829800 217197952194829800 rfl endpoint_11_37_base endpoint_11_37_p10) (by decide)⟩
private def endpoint_11_38_flag : Flag := ⟨11, 38, 4151⟩
private def endpoint_11_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_38_base : receiptBase endpoint_11_38_flag endpoint_11_38_sources = some 220579536741736822 := by decide +kernel
private theorem endpoint_11_38_w0 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 2 220579536741736822 = some 220579536741736822 := by decide +kernel
private theorem endpoint_11_38_w2 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 2 2 220579536741736822 = some 220579536741736822 := by decide +kernel
private theorem endpoint_11_38_p4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 4 220579536741736822 = some 220579536741736822 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 2 2 220579536741736822 220579536741736822 220579536741736822 endpoint_11_38_w0 endpoint_11_38_w2
private theorem endpoint_11_38_w4 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 4 2 220579536741736822 = some 220579536741736822 := by decide +kernel
private theorem endpoint_11_38_p6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 6 220579536741736822 = some 220579536741736822 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 4 2 220579536741736822 220579536741736822 220579536741736822 endpoint_11_38_p4 endpoint_11_38_w4
private theorem endpoint_11_38_w6 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 6 2 220579536741736822 = some 220579536741736822 := by decide +kernel
private theorem endpoint_11_38_p8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 8 220579536741736822 = some 220579536741736822 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 6 2 220579536741736822 220579536741736822 220579536741736822 endpoint_11_38_p6 endpoint_11_38_w6
private theorem endpoint_11_38_w8 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 8 2 220579536741736822 = some 220579536741736822 := by decide +kernel
private theorem endpoint_11_38_p10 : receiptWindow endpoint_11_38_flag endpoint_11_38_sources 0 10 220579536741736822 = some 220579536741736822 :=
  join_receipt_window endpoint_11_38_flag endpoint_11_38_sources 0 8 2 220579536741736822 220579536741736822 220579536741736822 endpoint_11_38_p8 endpoint_11_38_w8
def endpoint_11_38 : CertifiedEndpoint :=
  ⟨⟨11, 38, 4151⟩, 220579536741736822, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_38_flag endpoint_11_38_sources 10 220579536741736822 220579536741736822 rfl endpoint_11_38_base endpoint_11_38_p10) (by decide)⟩
private def endpoint_11_39_flag : Flag := ⟨11, 39, 4121⟩
private def endpoint_11_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_39_base : receiptBase endpoint_11_39_flag endpoint_11_39_sources = some 223839587386705768 := by decide +kernel
private theorem endpoint_11_39_w0 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 2 223839587386705768 = some 223839587386705768 := by decide +kernel
private theorem endpoint_11_39_w2 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 2 2 223839587386705768 = some 223839587386705768 := by decide +kernel
private theorem endpoint_11_39_p4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 4 223839587386705768 = some 223839587386705768 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 2 2 223839587386705768 223839587386705768 223839587386705768 endpoint_11_39_w0 endpoint_11_39_w2
private theorem endpoint_11_39_w4 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 4 2 223839587386705768 = some 223839587386705768 := by decide +kernel
private theorem endpoint_11_39_p6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 6 223839587386705768 = some 223839587386705768 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 4 2 223839587386705768 223839587386705768 223839587386705768 endpoint_11_39_p4 endpoint_11_39_w4
private theorem endpoint_11_39_w6 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 6 2 223839587386705768 = some 223839587386705768 := by decide +kernel
private theorem endpoint_11_39_p8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 8 223839587386705768 = some 223839587386705768 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 6 2 223839587386705768 223839587386705768 223839587386705768 endpoint_11_39_p6 endpoint_11_39_w6
private theorem endpoint_11_39_w8 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 8 2 223839587386705768 = some 223839587386705768 := by decide +kernel
private theorem endpoint_11_39_p10 : receiptWindow endpoint_11_39_flag endpoint_11_39_sources 0 10 223839587386705768 = some 223839587386705768 :=
  join_receipt_window endpoint_11_39_flag endpoint_11_39_sources 0 8 2 223839587386705768 223839587386705768 223839587386705768 endpoint_11_39_p8 endpoint_11_39_w8
def endpoint_11_39 : CertifiedEndpoint :=
  ⟨⟨11, 39, 4121⟩, 223839587386705768, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_39_flag endpoint_11_39_sources 10 223839587386705768 223839587386705768 rfl endpoint_11_39_base endpoint_11_39_p10) (by decide)⟩
private def endpoint_11_40_flag : Flag := ⟨11, 40, 4090⟩
private def endpoint_11_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_40_base : receiptBase endpoint_11_40_flag endpoint_11_40_sources = some 226974646799425406 := by decide +kernel
private theorem endpoint_11_40_w0 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 2 226974646799425406 = some 226974646799425406 := by decide +kernel
private theorem endpoint_11_40_w2 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 2 2 226974646799425406 = some 226974646799425406 := by decide +kernel
private theorem endpoint_11_40_p4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 4 226974646799425406 = some 226974646799425406 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 2 2 226974646799425406 226974646799425406 226974646799425406 endpoint_11_40_w0 endpoint_11_40_w2
private theorem endpoint_11_40_w4 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 4 2 226974646799425406 = some 226974646799425406 := by decide +kernel
private theorem endpoint_11_40_p6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 6 226974646799425406 = some 226974646799425406 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 4 2 226974646799425406 226974646799425406 226974646799425406 endpoint_11_40_p4 endpoint_11_40_w4
private theorem endpoint_11_40_w6 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 6 2 226974646799425406 = some 226974646799425406 := by decide +kernel
private theorem endpoint_11_40_p8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 8 226974646799425406 = some 226974646799425406 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 6 2 226974646799425406 226974646799425406 226974646799425406 endpoint_11_40_p6 endpoint_11_40_w6
private theorem endpoint_11_40_w8 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 8 2 226974646799425406 = some 226974646799425406 := by decide +kernel
private theorem endpoint_11_40_p10 : receiptWindow endpoint_11_40_flag endpoint_11_40_sources 0 10 226974646799425406 = some 226974646799425406 :=
  join_receipt_window endpoint_11_40_flag endpoint_11_40_sources 0 8 2 226974646799425406 226974646799425406 226974646799425406 endpoint_11_40_p8 endpoint_11_40_w8
def endpoint_11_40 : CertifiedEndpoint :=
  ⟨⟨11, 40, 4090⟩, 226974646799425406, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_40_flag endpoint_11_40_sources 10 226974646799425406 226974646799425406 rfl endpoint_11_40_base endpoint_11_40_p10) (by decide)⟩
private def endpoint_11_41_flag : Flag := ⟨11, 41, 4059⟩
private def endpoint_11_41_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_41_base : receiptBase endpoint_11_41_flag endpoint_11_41_sources = some 230037097776004191 := by decide +kernel
private theorem endpoint_11_41_w0 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 2 230037097776004191 = some 230037097776004191 := by decide +kernel
private theorem endpoint_11_41_w2 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 2 2 230037097776004191 = some 230037097776004191 := by decide +kernel
private theorem endpoint_11_41_p4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 4 230037097776004191 = some 230037097776004191 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 2 2 230037097776004191 230037097776004191 230037097776004191 endpoint_11_41_w0 endpoint_11_41_w2
private theorem endpoint_11_41_w4 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 4 2 230037097776004191 = some 230037097776004191 := by decide +kernel
private theorem endpoint_11_41_p6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 6 230037097776004191 = some 230037097776004191 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 4 2 230037097776004191 230037097776004191 230037097776004191 endpoint_11_41_p4 endpoint_11_41_w4
private theorem endpoint_11_41_w6 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 6 2 230037097776004191 = some 230037097776004191 := by decide +kernel
private theorem endpoint_11_41_p8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 8 230037097776004191 = some 230037097776004191 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 6 2 230037097776004191 230037097776004191 230037097776004191 endpoint_11_41_p6 endpoint_11_41_w6
private theorem endpoint_11_41_w8 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 8 2 230037097776004191 = some 230037097776004191 := by decide +kernel
private theorem endpoint_11_41_p10 : receiptWindow endpoint_11_41_flag endpoint_11_41_sources 0 10 230037097776004191 = some 230037097776004191 :=
  join_receipt_window endpoint_11_41_flag endpoint_11_41_sources 0 8 2 230037097776004191 230037097776004191 230037097776004191 endpoint_11_41_p8 endpoint_11_41_w8
def endpoint_11_41 : CertifiedEndpoint :=
  ⟨⟨11, 41, 4059⟩, 230037097776004191, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_41_flag endpoint_11_41_sources 10 230037097776004191 230037097776004191 rfl endpoint_11_41_base endpoint_11_41_p10) (by decide)⟩
private def endpoint_11_42_flag : Flag := ⟨11, 42, 4028⟩
private def endpoint_11_42_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_42_base : receiptBase endpoint_11_42_flag endpoint_11_42_sources = some 233026940316442123 := by decide +kernel
private theorem endpoint_11_42_w0 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 2 233026940316442123 = some 233026940316442123 := by decide +kernel
private theorem endpoint_11_42_w2 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 2 2 233026940316442123 = some 233026940316442123 := by decide +kernel
private theorem endpoint_11_42_p4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 4 233026940316442123 = some 233026940316442123 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 2 2 233026940316442123 233026940316442123 233026940316442123 endpoint_11_42_w0 endpoint_11_42_w2
private theorem endpoint_11_42_w4 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 4 2 233026940316442123 = some 233026940316442123 := by decide +kernel
private theorem endpoint_11_42_p6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 6 233026940316442123 = some 233026940316442123 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 4 2 233026940316442123 233026940316442123 233026940316442123 endpoint_11_42_p4 endpoint_11_42_w4
private theorem endpoint_11_42_w6 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 6 2 233026940316442123 = some 233026940316442123 := by decide +kernel
private theorem endpoint_11_42_p8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 8 233026940316442123 = some 233026940316442123 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 6 2 233026940316442123 233026940316442123 233026940316442123 endpoint_11_42_p6 endpoint_11_42_w6
private theorem endpoint_11_42_w8 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 8 2 233026940316442123 = some 233026940316442123 := by decide +kernel
private theorem endpoint_11_42_p10 : receiptWindow endpoint_11_42_flag endpoint_11_42_sources 0 10 233026940316442123 = some 233026940316442123 :=
  join_receipt_window endpoint_11_42_flag endpoint_11_42_sources 0 8 2 233026940316442123 233026940316442123 233026940316442123 endpoint_11_42_p8 endpoint_11_42_w8
def endpoint_11_42 : CertifiedEndpoint :=
  ⟨⟨11, 42, 4028⟩, 233026940316442123, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_42_flag endpoint_11_42_sources 10 233026940316442123 233026940316442123 rfl endpoint_11_42_base endpoint_11_42_p10) (by decide)⟩
private def endpoint_11_43_flag : Flag := ⟨11, 43, 3996⟩
private def endpoint_11_43_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_43_base : receiptBase endpoint_11_43_flag endpoint_11_43_sources = some 235886029407445364 := by decide +kernel
private theorem endpoint_11_43_w0 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 2 235886029407445364 = some 235886029407445364 := by decide +kernel
private theorem endpoint_11_43_w2 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 2 2 235886029407445364 = some 235886029407445364 := by decide +kernel
private theorem endpoint_11_43_p4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 4 235886029407445364 = some 235886029407445364 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 2 2 235886029407445364 235886029407445364 235886029407445364 endpoint_11_43_w0 endpoint_11_43_w2
private theorem endpoint_11_43_w4 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 4 2 235886029407445364 = some 235886029407445364 := by decide +kernel
private theorem endpoint_11_43_p6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 6 235886029407445364 = some 235886029407445364 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 4 2 235886029407445364 235886029407445364 235886029407445364 endpoint_11_43_p4 endpoint_11_43_w4
private theorem endpoint_11_43_w6 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 6 2 235886029407445364 = some 235886029407445364 := by decide +kernel
private theorem endpoint_11_43_p8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 8 235886029407445364 = some 235886029407445364 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 6 2 235886029407445364 235886029407445364 235886029407445364 endpoint_11_43_p6 endpoint_11_43_w6
private theorem endpoint_11_43_w8 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 8 2 235886029407445364 = some 235886029407445364 := by decide +kernel
private theorem endpoint_11_43_p10 : receiptWindow endpoint_11_43_flag endpoint_11_43_sources 0 10 235886029407445364 = some 235886029407445364 :=
  join_receipt_window endpoint_11_43_flag endpoint_11_43_sources 0 8 2 235886029407445364 235886029407445364 235886029407445364 endpoint_11_43_p8 endpoint_11_43_w8
def endpoint_11_43 : CertifiedEndpoint :=
  ⟨⟨11, 43, 3996⟩, 235886029407445364, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_43_flag endpoint_11_43_sources 10 235886029407445364 235886029407445364 rfl endpoint_11_43_base endpoint_11_43_p10) (by decide)⟩
private def endpoint_11_44_flag : Flag := ⟨11, 44, 3963⟩
private def endpoint_11_44_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_11_44_base : receiptBase endpoint_11_44_flag endpoint_11_44_sources = some 238610907718702684 := by decide +kernel
private theorem endpoint_11_44_w0 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 2 238610907718702684 = some 238610907718702684 := by decide +kernel
private theorem endpoint_11_44_w2 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 2 2 238610907718702684 = some 238610907718702684 := by decide +kernel
private theorem endpoint_11_44_p4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 4 238610907718702684 = some 238610907718702684 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 2 2 238610907718702684 238610907718702684 238610907718702684 endpoint_11_44_w0 endpoint_11_44_w2
private theorem endpoint_11_44_w4 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 4 2 238610907718702684 = some 238610907718702684 := by decide +kernel
private theorem endpoint_11_44_p6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 6 238610907718702684 = some 238610907718702684 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 4 2 238610907718702684 238610907718702684 238610907718702684 endpoint_11_44_p4 endpoint_11_44_w4
private theorem endpoint_11_44_w6 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 6 2 238610907718702684 = some 238610907718702684 := by decide +kernel
private theorem endpoint_11_44_p8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 8 238610907718702684 = some 238610907718702684 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 6 2 238610907718702684 238610907718702684 238610907718702684 endpoint_11_44_p6 endpoint_11_44_w6
private theorem endpoint_11_44_w8 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 8 2 238610907718702684 = some 238610907718702684 := by decide +kernel
private theorem endpoint_11_44_p10 : receiptWindow endpoint_11_44_flag endpoint_11_44_sources 0 10 238610907718702684 = some 238610907718702684 :=
  join_receipt_window endpoint_11_44_flag endpoint_11_44_sources 0 8 2 238610907718702684 238610907718702684 238610907718702684 endpoint_11_44_p8 endpoint_11_44_w8
def endpoint_11_44 : CertifiedEndpoint :=
  ⟨⟨11, 44, 3963⟩, 238610907718702684, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_11_44_flag endpoint_11_44_sources 10 238610907718702684 238610907718702684 rfl endpoint_11_44_base endpoint_11_44_p10) (by decide)⟩
private def endpoint_11_45_flag : Flag := ⟨11, 45, 3930⟩
private def endpoint_11_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_45_base : receiptBase endpoint_11_45_flag endpoint_11_45_sources = some 241892268213642529 := by decide +kernel
private theorem endpoint_11_45_w0 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 2 241892268213642529 = some 241892268213642529 := by decide +kernel
private theorem endpoint_11_45_w2 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 2 2 241892268213642529 = some 241892268213642529 := by decide +kernel
private theorem endpoint_11_45_p4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 4 241892268213642529 = some 241892268213642529 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 2 2 241892268213642529 241892268213642529 241892268213642529 endpoint_11_45_w0 endpoint_11_45_w2
private theorem endpoint_11_45_w4 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 4 2 241892268213642529 = some 241892268213642529 := by decide +kernel
private theorem endpoint_11_45_p6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 6 241892268213642529 = some 241892268213642529 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 4 2 241892268213642529 241892268213642529 241892268213642529 endpoint_11_45_p4 endpoint_11_45_w4
private theorem endpoint_11_45_w6 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 6 2 241892268213642529 = some 241892268213642529 := by decide +kernel
private theorem endpoint_11_45_p8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 8 241892268213642529 = some 241892268213642529 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 6 2 241892268213642529 241892268213642529 241892268213642529 endpoint_11_45_p6 endpoint_11_45_w6
private theorem endpoint_11_45_w8 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 8 2 241892268213642529 = some 241892268213642529 := by decide +kernel
private theorem endpoint_11_45_p10 : receiptWindow endpoint_11_45_flag endpoint_11_45_sources 0 10 241892268213642529 = some 241892268213642529 :=
  join_receipt_window endpoint_11_45_flag endpoint_11_45_sources 0 8 2 241892268213642529 241892268213642529 241892268213642529 endpoint_11_45_p8 endpoint_11_45_w8
def endpoint_11_45 : CertifiedEndpoint :=
  ⟨⟨11, 45, 3930⟩, 241892268213642529, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_45_flag endpoint_11_45_sources 10 241892268213642529 241892268213642529 rfl endpoint_11_45_base endpoint_11_45_p10) (by decide)⟩
private def endpoint_11_46_flag : Flag := ⟨11, 46, 3896⟩
private def endpoint_11_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_46_base : receiptBase endpoint_11_46_flag endpoint_11_46_sources = some 244366762783513820 := by decide +kernel
private theorem endpoint_11_46_w0 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 2 244366762783513820 = some 244366762783513820 := by decide +kernel
private theorem endpoint_11_46_w2 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 2 2 244366762783513820 = some 244366762783513820 := by decide +kernel
private theorem endpoint_11_46_p4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 4 244366762783513820 = some 244366762783513820 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 2 2 244366762783513820 244366762783513820 244366762783513820 endpoint_11_46_w0 endpoint_11_46_w2
private theorem endpoint_11_46_w4 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 4 2 244366762783513820 = some 244366762783513820 := by decide +kernel
private theorem endpoint_11_46_p6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 6 244366762783513820 = some 244366762783513820 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 4 2 244366762783513820 244366762783513820 244366762783513820 endpoint_11_46_p4 endpoint_11_46_w4
private theorem endpoint_11_46_w6 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 6 2 244366762783513820 = some 244366762783513820 := by decide +kernel
private theorem endpoint_11_46_p8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 8 244366762783513820 = some 244366762783513820 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 6 2 244366762783513820 244366762783513820 244366762783513820 endpoint_11_46_p6 endpoint_11_46_w6
private theorem endpoint_11_46_w8 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 8 2 244366762783513820 = some 244366762783513820 := by decide +kernel
private theorem endpoint_11_46_p10 : receiptWindow endpoint_11_46_flag endpoint_11_46_sources 0 10 244366762783513820 = some 244366762783513820 :=
  join_receipt_window endpoint_11_46_flag endpoint_11_46_sources 0 8 2 244366762783513820 244366762783513820 244366762783513820 endpoint_11_46_p8 endpoint_11_46_w8
def endpoint_11_46 : CertifiedEndpoint :=
  ⟨⟨11, 46, 3896⟩, 244366762783513820, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_46_flag endpoint_11_46_sources 10 244366762783513820 244366762783513820 rfl endpoint_11_46_base endpoint_11_46_p10) (by decide)⟩
private def endpoint_11_47_flag : Flag := ⟨11, 47, 3861⟩
private def endpoint_11_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_47_base : receiptBase endpoint_11_47_flag endpoint_11_47_sources = some 246699047016574593 := by decide +kernel
private theorem endpoint_11_47_w0 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 2 246699047016574593 = some 246699047016574593 := by decide +kernel
private theorem endpoint_11_47_w2 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 2 2 246699047016574593 = some 246699047016574593 := by decide +kernel
private theorem endpoint_11_47_p4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 4 246699047016574593 = some 246699047016574593 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 2 2 246699047016574593 246699047016574593 246699047016574593 endpoint_11_47_w0 endpoint_11_47_w2
private theorem endpoint_11_47_w4 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 4 2 246699047016574593 = some 246699047016574593 := by decide +kernel
private theorem endpoint_11_47_p6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 6 246699047016574593 = some 246699047016574593 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 4 2 246699047016574593 246699047016574593 246699047016574593 endpoint_11_47_p4 endpoint_11_47_w4
private theorem endpoint_11_47_w6 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 6 2 246699047016574593 = some 246699047016574593 := by decide +kernel
private theorem endpoint_11_47_p8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 8 246699047016574593 = some 246699047016574593 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 6 2 246699047016574593 246699047016574593 246699047016574593 endpoint_11_47_p6 endpoint_11_47_w6
private theorem endpoint_11_47_w8 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 8 2 246699047016574593 = some 246699047016574593 := by decide +kernel
private theorem endpoint_11_47_p10 : receiptWindow endpoint_11_47_flag endpoint_11_47_sources 0 10 246699047016574593 = some 246699047016574593 :=
  join_receipt_window endpoint_11_47_flag endpoint_11_47_sources 0 8 2 246699047016574593 246699047016574593 246699047016574593 endpoint_11_47_p8 endpoint_11_47_w8
def endpoint_11_47 : CertifiedEndpoint :=
  ⟨⟨11, 47, 3861⟩, 246699047016574593, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_47_flag endpoint_11_47_sources 10 246699047016574593 246699047016574593 rfl endpoint_11_47_base endpoint_11_47_p10) (by decide)⟩
private def endpoint_11_48_flag : Flag := ⟨11, 48, 3825⟩
private def endpoint_11_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_48_base : receiptBase endpoint_11_48_flag endpoint_11_48_sources = some 248885677079050149 := by decide +kernel
private theorem endpoint_11_48_w0 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 2 248885677079050149 = some 248885677079050149 := by decide +kernel
private theorem endpoint_11_48_w2 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 2 2 248885677079050149 = some 248885677079050149 := by decide +kernel
private theorem endpoint_11_48_p4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 4 248885677079050149 = some 248885677079050149 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 2 2 248885677079050149 248885677079050149 248885677079050149 endpoint_11_48_w0 endpoint_11_48_w2
private theorem endpoint_11_48_w4 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 4 2 248885677079050149 = some 248885677079050149 := by decide +kernel
private theorem endpoint_11_48_p6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 6 248885677079050149 = some 248885677079050149 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 4 2 248885677079050149 248885677079050149 248885677079050149 endpoint_11_48_p4 endpoint_11_48_w4
private theorem endpoint_11_48_w6 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 6 2 248885677079050149 = some 248885677079050149 := by decide +kernel
private theorem endpoint_11_48_p8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 8 248885677079050149 = some 248885677079050149 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 6 2 248885677079050149 248885677079050149 248885677079050149 endpoint_11_48_p6 endpoint_11_48_w6
private theorem endpoint_11_48_w8 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 8 2 248885677079050149 = some 248885677079050149 := by decide +kernel
private theorem endpoint_11_48_p10 : receiptWindow endpoint_11_48_flag endpoint_11_48_sources 0 10 248885677079050149 = some 248885677079050149 :=
  join_receipt_window endpoint_11_48_flag endpoint_11_48_sources 0 8 2 248885677079050149 248885677079050149 248885677079050149 endpoint_11_48_p8 endpoint_11_48_w8
def endpoint_11_48 : CertifiedEndpoint :=
  ⟨⟨11, 48, 3825⟩, 248885677079050149, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_48_flag endpoint_11_48_sources 10 248885677079050149 248885677079050149 rfl endpoint_11_48_base endpoint_11_48_p10) (by decide)⟩
private def endpoint_11_49_flag : Flag := ⟨11, 49, 3789⟩
private def endpoint_11_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_49_base : receiptBase endpoint_11_49_flag endpoint_11_49_sources = some 250988507186341400 := by decide +kernel
private theorem endpoint_11_49_w0 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 2 250988507186341400 = some 250988507186341400 := by decide +kernel
private theorem endpoint_11_49_w2 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 2 2 250988507186341400 = some 250988507186341400 := by decide +kernel
private theorem endpoint_11_49_p4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 4 250988507186341400 = some 250988507186341400 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 2 2 250988507186341400 250988507186341400 250988507186341400 endpoint_11_49_w0 endpoint_11_49_w2
private theorem endpoint_11_49_w4 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 4 2 250988507186341400 = some 250988507186341400 := by decide +kernel
private theorem endpoint_11_49_p6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 6 250988507186341400 = some 250988507186341400 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 4 2 250988507186341400 250988507186341400 250988507186341400 endpoint_11_49_p4 endpoint_11_49_w4
private theorem endpoint_11_49_w6 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 6 2 250988507186341400 = some 250988507186341400 := by decide +kernel
private theorem endpoint_11_49_p8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 8 250988507186341400 = some 250988507186341400 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 6 2 250988507186341400 250988507186341400 250988507186341400 endpoint_11_49_p6 endpoint_11_49_w6
private theorem endpoint_11_49_w8 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 8 2 250988507186341400 = some 250988507186341400 := by decide +kernel
private theorem endpoint_11_49_p10 : receiptWindow endpoint_11_49_flag endpoint_11_49_sources 0 10 250988507186341400 = some 250988507186341400 :=
  join_receipt_window endpoint_11_49_flag endpoint_11_49_sources 0 8 2 250988507186341400 250988507186341400 250988507186341400 endpoint_11_49_p8 endpoint_11_49_w8
def endpoint_11_49 : CertifiedEndpoint :=
  ⟨⟨11, 49, 3789⟩, 250988507186341400, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_49_flag endpoint_11_49_sources 10 250988507186341400 250988507186341400 rfl endpoint_11_49_base endpoint_11_49_p10) (by decide)⟩
private def endpoint_11_50_flag : Flag := ⟨11, 50, 3752⟩
private def endpoint_11_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_50_base : receiptBase endpoint_11_50_flag endpoint_11_50_sources = some 252941091344681171 := by decide +kernel
private theorem endpoint_11_50_w0 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 2 252941091344681171 = some 252941091344681171 := by decide +kernel
private theorem endpoint_11_50_w2 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 2 2 252941091344681171 = some 252941091344681171 := by decide +kernel
private theorem endpoint_11_50_p4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 4 252941091344681171 = some 252941091344681171 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 2 2 252941091344681171 252941091344681171 252941091344681171 endpoint_11_50_w0 endpoint_11_50_w2
private theorem endpoint_11_50_w4 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 4 2 252941091344681171 = some 252941091344681171 := by decide +kernel
private theorem endpoint_11_50_p6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 6 252941091344681171 = some 252941091344681171 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 4 2 252941091344681171 252941091344681171 252941091344681171 endpoint_11_50_p4 endpoint_11_50_w4
private theorem endpoint_11_50_w6 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 6 2 252941091344681171 = some 252941091344681171 := by decide +kernel
private theorem endpoint_11_50_p8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 8 252941091344681171 = some 252941091344681171 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 6 2 252941091344681171 252941091344681171 252941091344681171 endpoint_11_50_p6 endpoint_11_50_w6
private theorem endpoint_11_50_w8 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 8 2 252941091344681171 = some 252941091344681171 := by decide +kernel
private theorem endpoint_11_50_p10 : receiptWindow endpoint_11_50_flag endpoint_11_50_sources 0 10 252941091344681171 = some 252941091344681171 :=
  join_receipt_window endpoint_11_50_flag endpoint_11_50_sources 0 8 2 252941091344681171 252941091344681171 252941091344681171 endpoint_11_50_p8 endpoint_11_50_w8
def endpoint_11_50 : CertifiedEndpoint :=
  ⟨⟨11, 50, 3752⟩, 252941091344681171, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_50_flag endpoint_11_50_sources 10 252941091344681171 252941091344681171 rfl endpoint_11_50_base endpoint_11_50_p10) (by decide)⟩
private def endpoint_11_51_flag : Flag := ⟨11, 51, 3714⟩
private def endpoint_11_51_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_51_base : receiptBase endpoint_11_51_flag endpoint_11_51_sources = some 255399340056835447 := by decide +kernel
private theorem endpoint_11_51_w0 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 2 255399340056835447 = some 255399340056835447 := by decide +kernel
private theorem endpoint_11_51_w2 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 2 2 255399340056835447 = some 255399340056835447 := by decide +kernel
private theorem endpoint_11_51_p4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 4 255399340056835447 = some 255399340056835447 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 2 2 255399340056835447 255399340056835447 255399340056835447 endpoint_11_51_w0 endpoint_11_51_w2
private theorem endpoint_11_51_w4 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 4 2 255399340056835447 = some 255399340056835447 := by decide +kernel
private theorem endpoint_11_51_p6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 6 255399340056835447 = some 255399340056835447 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 4 2 255399340056835447 255399340056835447 255399340056835447 endpoint_11_51_p4 endpoint_11_51_w4
private theorem endpoint_11_51_w6 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 6 2 255399340056835447 = some 255399340056835447 := by decide +kernel
private theorem endpoint_11_51_p8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 8 255399340056835447 = some 255399340056835447 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 6 2 255399340056835447 255399340056835447 255399340056835447 endpoint_11_51_p6 endpoint_11_51_w6
private theorem endpoint_11_51_w8 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 8 2 255399340056835447 = some 255399340056835447 := by decide +kernel
private theorem endpoint_11_51_p10 : receiptWindow endpoint_11_51_flag endpoint_11_51_sources 0 10 255399340056835447 = some 255399340056835447 :=
  join_receipt_window endpoint_11_51_flag endpoint_11_51_sources 0 8 2 255399340056835447 255399340056835447 255399340056835447 endpoint_11_51_p8 endpoint_11_51_w8
def endpoint_11_51 : CertifiedEndpoint :=
  ⟨⟨11, 51, 3714⟩, 255399340056835447, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_51_flag endpoint_11_51_sources 10 255399340056835447 255399340056835447 rfl endpoint_11_51_base endpoint_11_51_p10) (by decide)⟩
private def endpoint_11_52_flag : Flag := ⟨11, 52, 3675⟩
private def endpoint_11_52_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_52_base : receiptBase endpoint_11_52_flag endpoint_11_52_sources = some 257050204206989347 := by decide +kernel
private theorem endpoint_11_52_w0 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 2 257050204206989347 = some 257050204206989347 := by decide +kernel
private theorem endpoint_11_52_w2 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 2 2 257050204206989347 = some 257050204206989347 := by decide +kernel
private theorem endpoint_11_52_p4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 4 257050204206989347 = some 257050204206989347 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 2 2 257050204206989347 257050204206989347 257050204206989347 endpoint_11_52_w0 endpoint_11_52_w2
private theorem endpoint_11_52_w4 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 4 2 257050204206989347 = some 257050204206989347 := by decide +kernel
private theorem endpoint_11_52_p6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 6 257050204206989347 = some 257050204206989347 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 4 2 257050204206989347 257050204206989347 257050204206989347 endpoint_11_52_p4 endpoint_11_52_w4
private theorem endpoint_11_52_w6 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 6 2 257050204206989347 = some 257050204206989347 := by decide +kernel
private theorem endpoint_11_52_p8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 8 257050204206989347 = some 257050204206989347 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 6 2 257050204206989347 257050204206989347 257050204206989347 endpoint_11_52_p6 endpoint_11_52_w6
private theorem endpoint_11_52_w8 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 8 2 257050204206989347 = some 257050204206989347 := by decide +kernel
private theorem endpoint_11_52_p10 : receiptWindow endpoint_11_52_flag endpoint_11_52_sources 0 10 257050204206989347 = some 257050204206989347 :=
  join_receipt_window endpoint_11_52_flag endpoint_11_52_sources 0 8 2 257050204206989347 257050204206989347 257050204206989347 endpoint_11_52_p8 endpoint_11_52_w8
def endpoint_11_52 : CertifiedEndpoint :=
  ⟨⟨11, 52, 3675⟩, 257050204206989347, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_52_flag endpoint_11_52_sources 10 257050204206989347 257050204206989347 rfl endpoint_11_52_base endpoint_11_52_p10) (by decide)⟩
private def endpoint_11_53_flag : Flag := ⟨11, 53, 3635⟩
private def endpoint_11_53_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_11_53_base : receiptBase endpoint_11_53_flag endpoint_11_53_sources = some 258539941863155411 := by decide +kernel
private theorem endpoint_11_53_w0 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 2 258539941863155411 = some 258539941863155411 := by decide +kernel
private theorem endpoint_11_53_w2 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 2 2 258539941863155411 = some 258539941863155411 := by decide +kernel
private theorem endpoint_11_53_p4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 4 258539941863155411 = some 258539941863155411 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 2 2 258539941863155411 258539941863155411 258539941863155411 endpoint_11_53_w0 endpoint_11_53_w2
private theorem endpoint_11_53_w4 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 4 2 258539941863155411 = some 258539941863155411 := by decide +kernel
private theorem endpoint_11_53_p6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 6 258539941863155411 = some 258539941863155411 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 4 2 258539941863155411 258539941863155411 258539941863155411 endpoint_11_53_p4 endpoint_11_53_w4
private theorem endpoint_11_53_w6 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 6 2 258539941863155411 = some 258539941863155411 := by decide +kernel
private theorem endpoint_11_53_p8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 8 258539941863155411 = some 258539941863155411 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 6 2 258539941863155411 258539941863155411 258539941863155411 endpoint_11_53_p6 endpoint_11_53_w6
private theorem endpoint_11_53_w8 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 8 2 258539941863155411 = some 258539941863155411 := by decide +kernel
private theorem endpoint_11_53_p10 : receiptWindow endpoint_11_53_flag endpoint_11_53_sources 0 10 258539941863155411 = some 258539941863155411 :=
  join_receipt_window endpoint_11_53_flag endpoint_11_53_sources 0 8 2 258539941863155411 258539941863155411 258539941863155411 endpoint_11_53_p8 endpoint_11_53_w8
def endpoint_11_53 : CertifiedEndpoint :=
  ⟨⟨11, 53, 3635⟩, 258539941863155411, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_11_53_flag endpoint_11_53_sources 10 258539941863155411 258539941863155411 rfl endpoint_11_53_base endpoint_11_53_p10) (by decide)⟩
private def endpoint_11_54_flag : Flag := ⟨11, 54, 3593⟩
private def endpoint_11_54_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_54_base : receiptBase endpoint_11_54_flag endpoint_11_54_sources = some 262671192572172403 := by decide +kernel
private theorem endpoint_11_54_w0 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 2 262671192572172403 = some 262671192572172403 := by decide +kernel
private theorem endpoint_11_54_w2 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 2 2 262671192572172403 = some 262671192572172403 := by decide +kernel
private theorem endpoint_11_54_p4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 4 262671192572172403 = some 262671192572172403 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 2 2 262671192572172403 262671192572172403 262671192572172403 endpoint_11_54_w0 endpoint_11_54_w2
private theorem endpoint_11_54_w4 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 4 2 262671192572172403 = some 262671192572172403 := by decide +kernel
private theorem endpoint_11_54_p6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 6 262671192572172403 = some 262671192572172403 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 4 2 262671192572172403 262671192572172403 262671192572172403 endpoint_11_54_p4 endpoint_11_54_w4
private theorem endpoint_11_54_w6 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 6 2 262671192572172403 = some 262671192572172403 := by decide +kernel
private theorem endpoint_11_54_p8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 8 262671192572172403 = some 262671192572172403 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 6 2 262671192572172403 262671192572172403 262671192572172403 endpoint_11_54_p6 endpoint_11_54_w6
private theorem endpoint_11_54_w8 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 8 2 262671192572172403 = some 262671192572172403 := by decide +kernel
private theorem endpoint_11_54_p10 : receiptWindow endpoint_11_54_flag endpoint_11_54_sources 0 10 262671192572172403 = some 262671192572172403 :=
  join_receipt_window endpoint_11_54_flag endpoint_11_54_sources 0 8 2 262671192572172403 262671192572172403 262671192572172403 endpoint_11_54_p8 endpoint_11_54_w8
def endpoint_11_54 : CertifiedEndpoint :=
  ⟨⟨11, 54, 3593⟩, 262671192572172403, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_54_flag endpoint_11_54_sources 10 262671192572172403 262671192572172403 rfl endpoint_11_54_base endpoint_11_54_p10) (by decide)⟩
private def endpoint_11_55_flag : Flag := ⟨11, 55, 3551⟩
private def endpoint_11_55_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_11_55_base : receiptBase endpoint_11_55_flag endpoint_11_55_sources = some 263785808515529661 := by decide +kernel
private theorem endpoint_11_55_w0 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 2 263785808515529661 = some 263785808515529661 := by decide +kernel
private theorem endpoint_11_55_w2 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 2 2 263785808515529661 = some 263785808515529661 := by decide +kernel
private theorem endpoint_11_55_p4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 4 263785808515529661 = some 263785808515529661 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 2 2 263785808515529661 263785808515529661 263785808515529661 endpoint_11_55_w0 endpoint_11_55_w2
private theorem endpoint_11_55_w4 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 4 2 263785808515529661 = some 263785808515529661 := by decide +kernel
private theorem endpoint_11_55_p6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 6 263785808515529661 = some 263785808515529661 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 4 2 263785808515529661 263785808515529661 263785808515529661 endpoint_11_55_p4 endpoint_11_55_w4
private theorem endpoint_11_55_w6 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 6 2 263785808515529661 = some 263785808515529661 := by decide +kernel
private theorem endpoint_11_55_p8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 8 263785808515529661 = some 263785808515529661 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 6 2 263785808515529661 263785808515529661 263785808515529661 endpoint_11_55_p6 endpoint_11_55_w6
private theorem endpoint_11_55_w8 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 8 2 263785808515529661 = some 263785808515529661 := by decide +kernel
private theorem endpoint_11_55_p10 : receiptWindow endpoint_11_55_flag endpoint_11_55_sources 0 10 263785808515529661 = some 263785808515529661 :=
  join_receipt_window endpoint_11_55_flag endpoint_11_55_sources 0 8 2 263785808515529661 263785808515529661 263785808515529661 endpoint_11_55_p8 endpoint_11_55_w8
def endpoint_11_55 : CertifiedEndpoint :=
  ⟨⟨11, 55, 3551⟩, 263785808515529661, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_11_55_flag endpoint_11_55_sources 10 263785808515529661 263785808515529661 rfl endpoint_11_55_base endpoint_11_55_p10) (by decide)⟩
private def endpoint_11_56_flag : Flag := ⟨11, 56, 3507⟩
private def endpoint_11_56_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_56_base : receiptBase endpoint_11_56_flag endpoint_11_56_sources = some 261161909352722534 := by decide +kernel
private theorem endpoint_11_56_w0 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 2 261161909352722534 = some 261161909352722534 := by decide +kernel
private theorem endpoint_11_56_w2 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 2 2 261161909352722534 = some 261161909352722534 := by decide +kernel
private theorem endpoint_11_56_p4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 4 261161909352722534 = some 261161909352722534 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 2 2 261161909352722534 261161909352722534 261161909352722534 endpoint_11_56_w0 endpoint_11_56_w2
private theorem endpoint_11_56_w4 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 4 2 261161909352722534 = some 261161909352722534 := by decide +kernel
private theorem endpoint_11_56_p6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 6 261161909352722534 = some 261161909352722534 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 4 2 261161909352722534 261161909352722534 261161909352722534 endpoint_11_56_p4 endpoint_11_56_w4
private theorem endpoint_11_56_w6 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 6 2 261161909352722534 = some 261161909352722534 := by decide +kernel
private theorem endpoint_11_56_p8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 8 261161909352722534 = some 261161909352722534 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 6 2 261161909352722534 261161909352722534 261161909352722534 endpoint_11_56_p6 endpoint_11_56_w6
private theorem endpoint_11_56_w8 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 8 2 261161909352722534 = some 261161909352722534 := by decide +kernel
private theorem endpoint_11_56_p10 : receiptWindow endpoint_11_56_flag endpoint_11_56_sources 0 10 261161909352722534 = some 261161909352722534 :=
  join_receipt_window endpoint_11_56_flag endpoint_11_56_sources 0 8 2 261161909352722534 261161909352722534 261161909352722534 endpoint_11_56_p8 endpoint_11_56_w8
def endpoint_11_56 : CertifiedEndpoint :=
  ⟨⟨11, 56, 3507⟩, 261161909352722534, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_56_flag endpoint_11_56_sources 10 261161909352722534 261161909352722534 rfl endpoint_11_56_base endpoint_11_56_p10) (by decide)⟩
private def endpoint_11_57_flag : Flag := ⟨11, 57, 3462⟩
private def endpoint_11_57_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_57_base : receiptBase endpoint_11_57_flag endpoint_11_57_sources = some 261889567027619153 := by decide +kernel
private theorem endpoint_11_57_w0 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 2 261889567027619153 = some 261889567027619153 := by decide +kernel
private theorem endpoint_11_57_w2 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 2 2 261889567027619153 = some 261889567027619153 := by decide +kernel
private theorem endpoint_11_57_p4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 4 261889567027619153 = some 261889567027619153 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 2 2 261889567027619153 261889567027619153 261889567027619153 endpoint_11_57_w0 endpoint_11_57_w2
private theorem endpoint_11_57_w4 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 4 2 261889567027619153 = some 261889567027619153 := by decide +kernel
private theorem endpoint_11_57_p6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 6 261889567027619153 = some 261889567027619153 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 4 2 261889567027619153 261889567027619153 261889567027619153 endpoint_11_57_p4 endpoint_11_57_w4
private theorem endpoint_11_57_w6 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 6 2 261889567027619153 = some 261889567027619153 := by decide +kernel
private theorem endpoint_11_57_p8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 8 261889567027619153 = some 261889567027619153 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 6 2 261889567027619153 261889567027619153 261889567027619153 endpoint_11_57_p6 endpoint_11_57_w6
private theorem endpoint_11_57_w8 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 8 2 261889567027619153 = some 261889567027619153 := by decide +kernel
private theorem endpoint_11_57_p10 : receiptWindow endpoint_11_57_flag endpoint_11_57_sources 0 10 261889567027619153 = some 261889567027619153 :=
  join_receipt_window endpoint_11_57_flag endpoint_11_57_sources 0 8 2 261889567027619153 261889567027619153 261889567027619153 endpoint_11_57_p8 endpoint_11_57_w8
def endpoint_11_57 : CertifiedEndpoint :=
  ⟨⟨11, 57, 3462⟩, 261889567027619153, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_57_flag endpoint_11_57_sources 10 261889567027619153 261889567027619153 rfl endpoint_11_57_base endpoint_11_57_p10) (by decide)⟩
private def endpoint_11_58_flag : Flag := ⟨11, 58, 3415⟩
private def endpoint_11_58_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_11_58_base : receiptBase endpoint_11_58_flag endpoint_11_58_sources = some 262361502643683881 := by decide +kernel
private theorem endpoint_11_58_w0 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 2 262361502643683881 = some 262361502643683881 := by decide +kernel
private theorem endpoint_11_58_w2 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 2 2 262361502643683881 = some 262361502643683881 := by decide +kernel
private theorem endpoint_11_58_p4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 4 262361502643683881 = some 262361502643683881 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 2 2 262361502643683881 262361502643683881 262361502643683881 endpoint_11_58_w0 endpoint_11_58_w2
private theorem endpoint_11_58_w4 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 4 2 262361502643683881 = some 262361502643683881 := by decide +kernel
private theorem endpoint_11_58_p6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 6 262361502643683881 = some 262361502643683881 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 4 2 262361502643683881 262361502643683881 262361502643683881 endpoint_11_58_p4 endpoint_11_58_w4
private theorem endpoint_11_58_w6 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 6 2 262361502643683881 = some 262361502643683881 := by decide +kernel
private theorem endpoint_11_58_p8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 8 262361502643683881 = some 262361502643683881 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 6 2 262361502643683881 262361502643683881 262361502643683881 endpoint_11_58_p6 endpoint_11_58_w6
private theorem endpoint_11_58_w8 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 8 2 262361502643683881 = some 262361502643683881 := by decide +kernel
private theorem endpoint_11_58_p10 : receiptWindow endpoint_11_58_flag endpoint_11_58_sources 0 10 262361502643683881 = some 262361502643683881 :=
  join_receipt_window endpoint_11_58_flag endpoint_11_58_sources 0 8 2 262361502643683881 262361502643683881 262361502643683881 endpoint_11_58_p8 endpoint_11_58_w8
def endpoint_11_58 : CertifiedEndpoint :=
  ⟨⟨11, 58, 3415⟩, 262361502643683881, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_11_58_flag endpoint_11_58_sources 10 262361502643683881 262361502643683881 rfl endpoint_11_58_base endpoint_11_58_p10) (by decide)⟩

def endpointBlock07 : List CertifiedEndpoint := [
  endpoint_10_18, endpoint_10_19, endpoint_10_20, endpoint_10_21, endpoint_10_22, endpoint_10_23, endpoint_10_24,
  endpoint_10_25, endpoint_10_26, endpoint_10_27, endpoint_10_28, endpoint_10_29, endpoint_10_30, endpoint_10_31,
  endpoint_10_32, endpoint_10_33, endpoint_10_34, endpoint_10_35, endpoint_10_36, endpoint_10_37, endpoint_10_38,
  endpoint_10_39, endpoint_10_40, endpoint_10_41, endpoint_10_42, endpoint_10_43, endpoint_10_44, endpoint_10_45,
  endpoint_10_46, endpoint_10_47, endpoint_10_48, endpoint_10_49, endpoint_10_50, endpoint_10_51, endpoint_10_52,
  endpoint_10_53, endpoint_10_54, endpoint_10_55, endpoint_10_56, endpoint_10_57, endpoint_10_58, endpoint_10_59,
  endpoint_10_60, endpoint_10_61, endpoint_10_62, endpoint_10_63, endpoint_10_64, endpoint_10_65, endpoint_10_66,
  endpoint_10_67, endpoint_10_68, endpoint_10_69, endpoint_10_70, endpoint_10_71, endpoint_10_72, endpoint_10_73,
  endpoint_10_74, endpoint_10_75, endpoint_10_76, endpoint_10_77, endpoint_10_78, endpoint_10_79, endpoint_10_80,
  endpoint_10_81, endpoint_10_82, endpoint_10_83, endpoint_10_84, endpoint_10_85, endpoint_10_86, endpoint_10_87,
  endpoint_10_88, endpoint_10_89, endpoint_10_90, endpoint_10_91, endpoint_10_92, endpoint_10_93, endpoint_11_11,
  endpoint_11_12, endpoint_11_13, endpoint_11_14, endpoint_11_15, endpoint_11_16, endpoint_11_17, endpoint_11_18,
  endpoint_11_19, endpoint_11_20, endpoint_11_21, endpoint_11_22, endpoint_11_23, endpoint_11_24, endpoint_11_25,
  endpoint_11_26, endpoint_11_27, endpoint_11_28, endpoint_11_29, endpoint_11_30, endpoint_11_31, endpoint_11_32,
  endpoint_11_33, endpoint_11_34, endpoint_11_35, endpoint_11_36, endpoint_11_37, endpoint_11_38, endpoint_11_39,
  endpoint_11_40, endpoint_11_41, endpoint_11_42, endpoint_11_43, endpoint_11_44, endpoint_11_45, endpoint_11_46,
  endpoint_11_47, endpoint_11_48, endpoint_11_49, endpoint_11_50, endpoint_11_51, endpoint_11_52, endpoint_11_53,
  endpoint_11_54, endpoint_11_55, endpoint_11_56, endpoint_11_57, endpoint_11_58
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
