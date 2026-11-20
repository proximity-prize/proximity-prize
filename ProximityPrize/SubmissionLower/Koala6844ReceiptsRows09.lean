import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_12_86 : CertifiedEndpoint :=
  ⟨⟨12, 86, 588⟩, 128031144986445896, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_87 : CertifiedEndpoint :=
  ⟨⟨12, 87, 452⟩, 96980971732670633, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_88 : CertifiedEndpoint :=
  ⟨⟨12, 88, 313⟩, 64392663410356259, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_12_89 : CertifiedEndpoint :=
  ⟨⟨12, 89, 171⟩, 30239470294318928, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_13 : CertifiedEndpoint :=
  ⟨⟨13, 13, 4482⟩, 106147058073477547, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_14 : CertifiedEndpoint :=
  ⟨⟨13, 14, 4459⟩, 110296641741690028, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_15 : CertifiedEndpoint :=
  ⟨⟨13, 15, 4435⟩, 114371774538570504, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_16 : CertifiedEndpoint :=
  ⟨⟨13, 16, 4411⟩, 127948435411903435, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_17 : CertifiedEndpoint :=
  ⟨⟨13, 17, 4387⟩, 141366831380435412, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_18 : CertifiedEndpoint :=
  ⟨⟨13, 18, 4363⟩, 154626962444166435, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_19 : CertifiedEndpoint :=
  ⟨⟨13, 19, 4338⟩, 167690061224592957, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_20 : CertifiedEndpoint :=
  ⟨⟨13, 20, 4313⟩, 180588435308185833, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_21 : CertifiedEndpoint :=
  ⟨⟨13, 21, 4288⟩, 193322084694945063, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_22 : CertifiedEndpoint :=
  ⟨⟨13, 22, 4263⟩, 205891009384870647, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_23 : CertifiedEndpoint :=
  ⟨⟨13, 23, 4237⟩, 218243522415393654, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_24 : CertifiedEndpoint :=
  ⟨⟨13, 24, 4211⟩, 230424850957050323, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_25 : CertifiedEndpoint :=
  ⟨⟨13, 25, 4185⟩, 242434995009840654, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_26 : CertifiedEndpoint :=
  ⟨⟨13, 26, 4158⟩, 254212577923146678, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_13_27_flag : Flag := ⟨13, 27, 4131⟩
private def endpoint_13_27_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_27_base : receiptBase endpoint_13_27_flag endpoint_13_27_sources = some 185087152732050548 := by decide +kernel
private theorem endpoint_13_27_w0 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 2 185087152732050548 = some 185087152732050548 := by decide +kernel
private theorem endpoint_13_27_w2 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 2 2 185087152732050548 = some 185087152732050548 := by decide +kernel
private theorem endpoint_13_27_p4 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 4 185087152732050548 = some 185087152732050548 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 2 2 185087152732050548 185087152732050548 185087152732050548 endpoint_13_27_w0 endpoint_13_27_w2
private theorem endpoint_13_27_w4 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 4 2 185087152732050548 = some 185087152732050548 := by decide +kernel
private theorem endpoint_13_27_p6 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 6 185087152732050548 = some 185087152732050548 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 4 2 185087152732050548 185087152732050548 185087152732050548 endpoint_13_27_p4 endpoint_13_27_w4
private theorem endpoint_13_27_w6 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 6 2 185087152732050548 = some 185087152732050548 := by decide +kernel
private theorem endpoint_13_27_p8 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 8 185087152732050548 = some 185087152732050548 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 6 2 185087152732050548 185087152732050548 185087152732050548 endpoint_13_27_p6 endpoint_13_27_w6
private theorem endpoint_13_27_w8 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 8 2 185087152732050548 = some 185087152732050548 := by decide +kernel
private theorem endpoint_13_27_p10 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 10 185087152732050548 = some 185087152732050548 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 8 2 185087152732050548 185087152732050548 185087152732050548 endpoint_13_27_p8 endpoint_13_27_w8
private theorem endpoint_13_27_w10 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 10 2 185087152732050548 = some 185087152732050548 := by decide +kernel
private theorem endpoint_13_27_p12 : receiptWindow endpoint_13_27_flag endpoint_13_27_sources 0 12 185087152732050548 = some 185087152732050548 :=
  join_receipt_window endpoint_13_27_flag endpoint_13_27_sources 0 10 2 185087152732050548 185087152732050548 185087152732050548 endpoint_13_27_p10 endpoint_13_27_w10
def endpoint_13_27 : CertifiedEndpoint :=
  ⟨⟨13, 27, 4131⟩, 185087152732050548, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_27_flag endpoint_13_27_sources 12 185087152732050548 185087152732050548 rfl endpoint_13_27_base endpoint_13_27_p12) (by decide)⟩
private def endpoint_13_28_flag : Flag := ⟨13, 28, 4104⟩
private def endpoint_13_28_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_28_base : receiptBase endpoint_13_28_flag endpoint_13_28_sources = some 189365356074888033 := by decide +kernel
private theorem endpoint_13_28_w0 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 2 189365356074888033 = some 189365356074888033 := by decide +kernel
private theorem endpoint_13_28_w2 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 2 2 189365356074888033 = some 189365356074888033 := by decide +kernel
private theorem endpoint_13_28_p4 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 4 189365356074888033 = some 189365356074888033 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 2 2 189365356074888033 189365356074888033 189365356074888033 endpoint_13_28_w0 endpoint_13_28_w2
private theorem endpoint_13_28_w4 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 4 2 189365356074888033 = some 189365356074888033 := by decide +kernel
private theorem endpoint_13_28_p6 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 6 189365356074888033 = some 189365356074888033 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 4 2 189365356074888033 189365356074888033 189365356074888033 endpoint_13_28_p4 endpoint_13_28_w4
private theorem endpoint_13_28_w6 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 6 2 189365356074888033 = some 189365356074888033 := by decide +kernel
private theorem endpoint_13_28_p8 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 8 189365356074888033 = some 189365356074888033 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 6 2 189365356074888033 189365356074888033 189365356074888033 endpoint_13_28_p6 endpoint_13_28_w6
private theorem endpoint_13_28_w8 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 8 2 189365356074888033 = some 189365356074888033 := by decide +kernel
private theorem endpoint_13_28_p10 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 10 189365356074888033 = some 189365356074888033 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 8 2 189365356074888033 189365356074888033 189365356074888033 endpoint_13_28_p8 endpoint_13_28_w8
private theorem endpoint_13_28_w10 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 10 2 189365356074888033 = some 189365356074888033 := by decide +kernel
private theorem endpoint_13_28_p12 : receiptWindow endpoint_13_28_flag endpoint_13_28_sources 0 12 189365356074888033 = some 189365356074888033 :=
  join_receipt_window endpoint_13_28_flag endpoint_13_28_sources 0 10 2 189365356074888033 189365356074888033 189365356074888033 endpoint_13_28_p10 endpoint_13_28_w10
def endpoint_13_28 : CertifiedEndpoint :=
  ⟨⟨13, 28, 4104⟩, 189365356074888033, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_28_flag endpoint_13_28_sources 12 189365356074888033 189365356074888033 rfl endpoint_13_28_base endpoint_13_28_p12) (by decide)⟩
private def endpoint_13_29_flag : Flag := ⟨13, 29, 4076⟩
private def endpoint_13_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_29_base : receiptBase endpoint_13_29_flag endpoint_13_29_sources = some 193524897294227745 := by decide +kernel
private theorem endpoint_13_29_w0 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 2 193524897294227745 = some 193524897294227745 := by decide +kernel
private theorem endpoint_13_29_w2 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 2 2 193524897294227745 = some 193524897294227745 := by decide +kernel
private theorem endpoint_13_29_p4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 4 193524897294227745 = some 193524897294227745 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 2 2 193524897294227745 193524897294227745 193524897294227745 endpoint_13_29_w0 endpoint_13_29_w2
private theorem endpoint_13_29_w4 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 4 2 193524897294227745 = some 193524897294227745 := by decide +kernel
private theorem endpoint_13_29_p6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 6 193524897294227745 = some 193524897294227745 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 4 2 193524897294227745 193524897294227745 193524897294227745 endpoint_13_29_p4 endpoint_13_29_w4
private theorem endpoint_13_29_w6 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 6 2 193524897294227745 = some 193524897294227745 := by decide +kernel
private theorem endpoint_13_29_p8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 8 193524897294227745 = some 193524897294227745 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 6 2 193524897294227745 193524897294227745 193524897294227745 endpoint_13_29_p6 endpoint_13_29_w6
private theorem endpoint_13_29_w8 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 8 2 193524897294227745 = some 193524897294227745 := by decide +kernel
private theorem endpoint_13_29_p10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 10 193524897294227745 = some 193524897294227745 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 8 2 193524897294227745 193524897294227745 193524897294227745 endpoint_13_29_p8 endpoint_13_29_w8
private theorem endpoint_13_29_w10 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 10 2 193524897294227745 = some 193524897294227745 := by decide +kernel
private theorem endpoint_13_29_p12 : receiptWindow endpoint_13_29_flag endpoint_13_29_sources 0 12 193524897294227745 = some 193524897294227745 :=
  join_receipt_window endpoint_13_29_flag endpoint_13_29_sources 0 10 2 193524897294227745 193524897294227745 193524897294227745 endpoint_13_29_p10 endpoint_13_29_w10
def endpoint_13_29 : CertifiedEndpoint :=
  ⟨⟨13, 29, 4076⟩, 193524897294227745, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_29_flag endpoint_13_29_sources 12 193524897294227745 193524897294227745 rfl endpoint_13_29_base endpoint_13_29_p12) (by decide)⟩
private def endpoint_13_30_flag : Flag := ⟨13, 30, 4047⟩
private def endpoint_13_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_30_base : receiptBase endpoint_13_30_flag endpoint_13_30_sources = some 197561859472528219 := by decide +kernel
private theorem endpoint_13_30_w0 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 2 197561859472528219 = some 197561859472528219 := by decide +kernel
private theorem endpoint_13_30_w2 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 2 2 197561859472528219 = some 197561859472528219 := by decide +kernel
private theorem endpoint_13_30_p4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 4 197561859472528219 = some 197561859472528219 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 2 2 197561859472528219 197561859472528219 197561859472528219 endpoint_13_30_w0 endpoint_13_30_w2
private theorem endpoint_13_30_w4 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 4 2 197561859472528219 = some 197561859472528219 := by decide +kernel
private theorem endpoint_13_30_p6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 6 197561859472528219 = some 197561859472528219 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 4 2 197561859472528219 197561859472528219 197561859472528219 endpoint_13_30_p4 endpoint_13_30_w4
private theorem endpoint_13_30_w6 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 6 2 197561859472528219 = some 197561859472528219 := by decide +kernel
private theorem endpoint_13_30_p8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 8 197561859472528219 = some 197561859472528219 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 6 2 197561859472528219 197561859472528219 197561859472528219 endpoint_13_30_p6 endpoint_13_30_w6
private theorem endpoint_13_30_w8 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 8 2 197561859472528219 = some 197561859472528219 := by decide +kernel
private theorem endpoint_13_30_p10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 10 197561859472528219 = some 197561859472528219 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 8 2 197561859472528219 197561859472528219 197561859472528219 endpoint_13_30_p8 endpoint_13_30_w8
private theorem endpoint_13_30_w10 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 10 2 197561859472528219 = some 197561859472528219 := by decide +kernel
private theorem endpoint_13_30_p12 : receiptWindow endpoint_13_30_flag endpoint_13_30_sources 0 12 197561859472528219 = some 197561859472528219 :=
  join_receipt_window endpoint_13_30_flag endpoint_13_30_sources 0 10 2 197561859472528219 197561859472528219 197561859472528219 endpoint_13_30_p10 endpoint_13_30_w10
def endpoint_13_30 : CertifiedEndpoint :=
  ⟨⟨13, 30, 4047⟩, 197561859472528219, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_30_flag endpoint_13_30_sources 12 197561859472528219 197561859472528219 rfl endpoint_13_30_base endpoint_13_30_p12) (by decide)⟩
private def endpoint_13_31_flag : Flag := ⟨13, 31, 4019⟩
private def endpoint_13_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_31_base : receiptBase endpoint_13_31_flag endpoint_13_31_sources = some 201571211689666640 := by decide +kernel
private theorem endpoint_13_31_w0 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 2 201571211689666640 = some 201571211689666640 := by decide +kernel
private theorem endpoint_13_31_w2 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 2 2 201571211689666640 = some 201571211689666640 := by decide +kernel
private theorem endpoint_13_31_p4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 4 201571211689666640 = some 201571211689666640 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 2 2 201571211689666640 201571211689666640 201571211689666640 endpoint_13_31_w0 endpoint_13_31_w2
private theorem endpoint_13_31_w4 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 4 2 201571211689666640 = some 201571211689666640 := by decide +kernel
private theorem endpoint_13_31_p6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 6 201571211689666640 = some 201571211689666640 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 4 2 201571211689666640 201571211689666640 201571211689666640 endpoint_13_31_p4 endpoint_13_31_w4
private theorem endpoint_13_31_w6 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 6 2 201571211689666640 = some 201571211689666640 := by decide +kernel
private theorem endpoint_13_31_p8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 8 201571211689666640 = some 201571211689666640 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 6 2 201571211689666640 201571211689666640 201571211689666640 endpoint_13_31_p6 endpoint_13_31_w6
private theorem endpoint_13_31_w8 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 8 2 201571211689666640 = some 201571211689666640 := by decide +kernel
private theorem endpoint_13_31_p10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 10 201571211689666640 = some 201571211689666640 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 8 2 201571211689666640 201571211689666640 201571211689666640 endpoint_13_31_p8 endpoint_13_31_w8
private theorem endpoint_13_31_w10 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 10 2 201571211689666640 = some 201571211689666640 := by decide +kernel
private theorem endpoint_13_31_p12 : receiptWindow endpoint_13_31_flag endpoint_13_31_sources 0 12 201571211689666640 = some 201571211689666640 :=
  join_receipt_window endpoint_13_31_flag endpoint_13_31_sources 0 10 2 201571211689666640 201571211689666640 201571211689666640 endpoint_13_31_p10 endpoint_13_31_w10
def endpoint_13_31 : CertifiedEndpoint :=
  ⟨⟨13, 31, 4019⟩, 201571211689666640, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_31_flag endpoint_13_31_sources 12 201571211689666640 201571211689666640 rfl endpoint_13_31_base endpoint_13_31_p12) (by decide)⟩
private def endpoint_13_32_flag : Flag := ⟨13, 32, 3990⟩
private def endpoint_13_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_32_base : receiptBase endpoint_13_32_flag endpoint_13_32_sources = some 205455373587404847 := by decide +kernel
private theorem endpoint_13_32_w0 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 2 205455373587404847 = some 205455373587404847 := by decide +kernel
private theorem endpoint_13_32_w2 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 2 2 205455373587404847 = some 205455373587404847 := by decide +kernel
private theorem endpoint_13_32_p4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 4 205455373587404847 = some 205455373587404847 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 2 2 205455373587404847 205455373587404847 205455373587404847 endpoint_13_32_w0 endpoint_13_32_w2
private theorem endpoint_13_32_w4 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 4 2 205455373587404847 = some 205455373587404847 := by decide +kernel
private theorem endpoint_13_32_p6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 6 205455373587404847 = some 205455373587404847 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 4 2 205455373587404847 205455373587404847 205455373587404847 endpoint_13_32_p4 endpoint_13_32_w4
private theorem endpoint_13_32_w6 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 6 2 205455373587404847 = some 205455373587404847 := by decide +kernel
private theorem endpoint_13_32_p8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 8 205455373587404847 = some 205455373587404847 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 6 2 205455373587404847 205455373587404847 205455373587404847 endpoint_13_32_p6 endpoint_13_32_w6
private theorem endpoint_13_32_w8 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 8 2 205455373587404847 = some 205455373587404847 := by decide +kernel
private theorem endpoint_13_32_p10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 10 205455373587404847 = some 205455373587404847 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 8 2 205455373587404847 205455373587404847 205455373587404847 endpoint_13_32_p8 endpoint_13_32_w8
private theorem endpoint_13_32_w10 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 10 2 205455373587404847 = some 205455373587404847 := by decide +kernel
private theorem endpoint_13_32_p12 : receiptWindow endpoint_13_32_flag endpoint_13_32_sources 0 12 205455373587404847 = some 205455373587404847 :=
  join_receipt_window endpoint_13_32_flag endpoint_13_32_sources 0 10 2 205455373587404847 205455373587404847 205455373587404847 endpoint_13_32_p10 endpoint_13_32_w10
def endpoint_13_32 : CertifiedEndpoint :=
  ⟨⟨13, 32, 3990⟩, 205455373587404847, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_32_flag endpoint_13_32_sources 12 205455373587404847 205455373587404847 rfl endpoint_13_32_base endpoint_13_32_p12) (by decide)⟩
private def endpoint_13_33_flag : Flag := ⟨13, 33, 3960⟩
private def endpoint_13_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_33_base : receiptBase endpoint_13_33_flag endpoint_13_33_sources = some 209210428248201375 := by decide +kernel
private theorem endpoint_13_33_w0 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 2 209210428248201375 = some 209210428248201375 := by decide +kernel
private theorem endpoint_13_33_w2 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 2 2 209210428248201375 = some 209210428248201375 := by decide +kernel
private theorem endpoint_13_33_p4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 4 209210428248201375 = some 209210428248201375 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 2 2 209210428248201375 209210428248201375 209210428248201375 endpoint_13_33_w0 endpoint_13_33_w2
private theorem endpoint_13_33_w4 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 4 2 209210428248201375 = some 209210428248201375 := by decide +kernel
private theorem endpoint_13_33_p6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 6 209210428248201375 = some 209210428248201375 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 4 2 209210428248201375 209210428248201375 209210428248201375 endpoint_13_33_p4 endpoint_13_33_w4
private theorem endpoint_13_33_w6 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 6 2 209210428248201375 = some 209210428248201375 := by decide +kernel
private theorem endpoint_13_33_p8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 8 209210428248201375 = some 209210428248201375 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 6 2 209210428248201375 209210428248201375 209210428248201375 endpoint_13_33_p6 endpoint_13_33_w6
private theorem endpoint_13_33_w8 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 8 2 209210428248201375 = some 209210428248201375 := by decide +kernel
private theorem endpoint_13_33_p10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 10 209210428248201375 = some 209210428248201375 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 8 2 209210428248201375 209210428248201375 209210428248201375 endpoint_13_33_p8 endpoint_13_33_w8
private theorem endpoint_13_33_w10 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 10 2 209210428248201375 = some 209210428248201375 := by decide +kernel
private theorem endpoint_13_33_p12 : receiptWindow endpoint_13_33_flag endpoint_13_33_sources 0 12 209210428248201375 = some 209210428248201375 :=
  join_receipt_window endpoint_13_33_flag endpoint_13_33_sources 0 10 2 209210428248201375 209210428248201375 209210428248201375 endpoint_13_33_p10 endpoint_13_33_w10
def endpoint_13_33 : CertifiedEndpoint :=
  ⟨⟨13, 33, 3960⟩, 209210428248201375, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_33_flag endpoint_13_33_sources 12 209210428248201375 209210428248201375 rfl endpoint_13_33_base endpoint_13_33_p12) (by decide)⟩
private def endpoint_13_34_flag : Flag := ⟨13, 34, 3930⟩
private def endpoint_13_34_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_13_34_base : receiptBase endpoint_13_34_flag endpoint_13_34_sources = some 212885818670765550 := by decide +kernel
private theorem endpoint_13_34_w0 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 2 212885818670765550 = some 212885818670765550 := by decide +kernel
private theorem endpoint_13_34_w2 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 2 2 212885818670765550 = some 212885818670765550 := by decide +kernel
private theorem endpoint_13_34_p4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 4 212885818670765550 = some 212885818670765550 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 2 2 212885818670765550 212885818670765550 212885818670765550 endpoint_13_34_w0 endpoint_13_34_w2
private theorem endpoint_13_34_w4 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 4 2 212885818670765550 = some 212885818670765550 := by decide +kernel
private theorem endpoint_13_34_p6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 6 212885818670765550 = some 212885818670765550 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 4 2 212885818670765550 212885818670765550 212885818670765550 endpoint_13_34_p4 endpoint_13_34_w4
private theorem endpoint_13_34_w6 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 6 2 212885818670765550 = some 212885818670765550 := by decide +kernel
private theorem endpoint_13_34_p8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 8 212885818670765550 = some 212885818670765550 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 6 2 212885818670765550 212885818670765550 212885818670765550 endpoint_13_34_p6 endpoint_13_34_w6
private theorem endpoint_13_34_w8 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 8 2 212885818670765550 = some 212885818670765550 := by decide +kernel
private theorem endpoint_13_34_p10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 10 212885818670765550 = some 212885818670765550 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 8 2 212885818670765550 212885818670765550 212885818670765550 endpoint_13_34_p8 endpoint_13_34_w8
private theorem endpoint_13_34_w10 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 10 2 212885818670765550 = some 212885818670765550 := by decide +kernel
private theorem endpoint_13_34_p12 : receiptWindow endpoint_13_34_flag endpoint_13_34_sources 0 12 212885818670765550 = some 212885818670765550 :=
  join_receipt_window endpoint_13_34_flag endpoint_13_34_sources 0 10 2 212885818670765550 212885818670765550 212885818670765550 endpoint_13_34_p10 endpoint_13_34_w10
def endpoint_13_34 : CertifiedEndpoint :=
  ⟨⟨13, 34, 3930⟩, 212885818670765550, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_13_34_flag endpoint_13_34_sources 12 212885818670765550 212885818670765550 rfl endpoint_13_34_base endpoint_13_34_p12) (by decide)⟩
private def endpoint_13_35_flag : Flag := ⟨13, 35, 3900⟩
private def endpoint_13_35_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_35_base : receiptBase endpoint_13_35_flag endpoint_13_35_sources = some 217152654483820826 := by decide +kernel
private theorem endpoint_13_35_w0 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 2 217152654483820826 = some 217152654483820826 := by decide +kernel
private theorem endpoint_13_35_w2 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 2 2 217152654483820826 = some 217152654483820826 := by decide +kernel
private theorem endpoint_13_35_p4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 4 217152654483820826 = some 217152654483820826 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 2 2 217152654483820826 217152654483820826 217152654483820826 endpoint_13_35_w0 endpoint_13_35_w2
private theorem endpoint_13_35_w4 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 4 2 217152654483820826 = some 217152654483820826 := by decide +kernel
private theorem endpoint_13_35_p6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 6 217152654483820826 = some 217152654483820826 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 4 2 217152654483820826 217152654483820826 217152654483820826 endpoint_13_35_p4 endpoint_13_35_w4
private theorem endpoint_13_35_w6 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 6 2 217152654483820826 = some 217152654483820826 := by decide +kernel
private theorem endpoint_13_35_p8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 8 217152654483820826 = some 217152654483820826 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 6 2 217152654483820826 217152654483820826 217152654483820826 endpoint_13_35_p6 endpoint_13_35_w6
private theorem endpoint_13_35_w8 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 8 2 217152654483820826 = some 217152654483820826 := by decide +kernel
private theorem endpoint_13_35_p10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 10 217152654483820826 = some 217152654483820826 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 8 2 217152654483820826 217152654483820826 217152654483820826 endpoint_13_35_p8 endpoint_13_35_w8
private theorem endpoint_13_35_w10 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 10 2 217152654483820826 = some 217152654483820826 := by decide +kernel
private theorem endpoint_13_35_p12 : receiptWindow endpoint_13_35_flag endpoint_13_35_sources 0 12 217152654483820826 = some 217152654483820826 :=
  join_receipt_window endpoint_13_35_flag endpoint_13_35_sources 0 10 2 217152654483820826 217152654483820826 217152654483820826 endpoint_13_35_p10 endpoint_13_35_w10
def endpoint_13_35 : CertifiedEndpoint :=
  ⟨⟨13, 35, 3900⟩, 217152654483820826, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_35_flag endpoint_13_35_sources 12 217152654483820826 217152654483820826 rfl endpoint_13_35_base endpoint_13_35_p12) (by decide)⟩
private def endpoint_13_36_flag : Flag := ⟨13, 36, 3869⟩
private def endpoint_13_36_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_36_base : receiptBase endpoint_13_36_flag endpoint_13_36_sources = some 220517339098069627 := by decide +kernel
private theorem endpoint_13_36_w0 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 2 220517339098069627 = some 220517339098069627 := by decide +kernel
private theorem endpoint_13_36_w2 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 2 2 220517339098069627 = some 220517339098069627 := by decide +kernel
private theorem endpoint_13_36_p4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 4 220517339098069627 = some 220517339098069627 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 2 2 220517339098069627 220517339098069627 220517339098069627 endpoint_13_36_w0 endpoint_13_36_w2
private theorem endpoint_13_36_w4 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 4 2 220517339098069627 = some 220517339098069627 := by decide +kernel
private theorem endpoint_13_36_p6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 6 220517339098069627 = some 220517339098069627 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 4 2 220517339098069627 220517339098069627 220517339098069627 endpoint_13_36_p4 endpoint_13_36_w4
private theorem endpoint_13_36_w6 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 6 2 220517339098069627 = some 220517339098069627 := by decide +kernel
private theorem endpoint_13_36_p8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 8 220517339098069627 = some 220517339098069627 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 6 2 220517339098069627 220517339098069627 220517339098069627 endpoint_13_36_p6 endpoint_13_36_w6
private theorem endpoint_13_36_w8 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 8 2 220517339098069627 = some 220517339098069627 := by decide +kernel
private theorem endpoint_13_36_p10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 10 220517339098069627 = some 220517339098069627 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 8 2 220517339098069627 220517339098069627 220517339098069627 endpoint_13_36_p8 endpoint_13_36_w8
private theorem endpoint_13_36_w10 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 10 2 220517339098069627 = some 220517339098069627 := by decide +kernel
private theorem endpoint_13_36_p12 : receiptWindow endpoint_13_36_flag endpoint_13_36_sources 0 12 220517339098069627 = some 220517339098069627 :=
  join_receipt_window endpoint_13_36_flag endpoint_13_36_sources 0 10 2 220517339098069627 220517339098069627 220517339098069627 endpoint_13_36_p10 endpoint_13_36_w10
def endpoint_13_36 : CertifiedEndpoint :=
  ⟨⟨13, 36, 3869⟩, 220517339098069627, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_36_flag endpoint_13_36_sources 12 220517339098069627 220517339098069627 rfl endpoint_13_36_base endpoint_13_36_p12) (by decide)⟩
private def endpoint_13_37_flag : Flag := ⟨13, 37, 3837⟩
private def endpoint_13_37_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_37_base : receiptBase endpoint_13_37_flag endpoint_13_37_sources = some 223743548673336021 := by decide +kernel
private theorem endpoint_13_37_w0 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 2 223743548673336021 = some 223743548673336021 := by decide +kernel
private theorem endpoint_13_37_w2 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 2 2 223743548673336021 = some 223743548673336021 := by decide +kernel
private theorem endpoint_13_37_p4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 4 223743548673336021 = some 223743548673336021 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 2 2 223743548673336021 223743548673336021 223743548673336021 endpoint_13_37_w0 endpoint_13_37_w2
private theorem endpoint_13_37_w4 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 4 2 223743548673336021 = some 223743548673336021 := by decide +kernel
private theorem endpoint_13_37_p6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 6 223743548673336021 = some 223743548673336021 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 4 2 223743548673336021 223743548673336021 223743548673336021 endpoint_13_37_p4 endpoint_13_37_w4
private theorem endpoint_13_37_w6 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 6 2 223743548673336021 = some 223743548673336021 := by decide +kernel
private theorem endpoint_13_37_p8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 8 223743548673336021 = some 223743548673336021 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 6 2 223743548673336021 223743548673336021 223743548673336021 endpoint_13_37_p6 endpoint_13_37_w6
private theorem endpoint_13_37_w8 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 8 2 223743548673336021 = some 223743548673336021 := by decide +kernel
private theorem endpoint_13_37_p10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 10 223743548673336021 = some 223743548673336021 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 8 2 223743548673336021 223743548673336021 223743548673336021 endpoint_13_37_p8 endpoint_13_37_w8
private theorem endpoint_13_37_w10 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 10 2 223743548673336021 = some 223743548673336021 := by decide +kernel
private theorem endpoint_13_37_p12 : receiptWindow endpoint_13_37_flag endpoint_13_37_sources 0 12 223743548673336021 = some 223743548673336021 :=
  join_receipt_window endpoint_13_37_flag endpoint_13_37_sources 0 10 2 223743548673336021 223743548673336021 223743548673336021 endpoint_13_37_p10 endpoint_13_37_w10
def endpoint_13_37 : CertifiedEndpoint :=
  ⟨⟨13, 37, 3837⟩, 223743548673336021, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_37_flag endpoint_13_37_sources 12 223743548673336021 223743548673336021 rfl endpoint_13_37_base endpoint_13_37_p12) (by decide)⟩
private def endpoint_13_38_flag : Flag := ⟨13, 38, 3805⟩
private def endpoint_13_38_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_38_base : receiptBase endpoint_13_38_flag endpoint_13_38_sources = some 226886208181911366 := by decide +kernel
private theorem endpoint_13_38_w0 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 2 226886208181911366 = some 226886208181911366 := by decide +kernel
private theorem endpoint_13_38_w2 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 2 2 226886208181911366 = some 226886208181911366 := by decide +kernel
private theorem endpoint_13_38_p4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 4 226886208181911366 = some 226886208181911366 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 2 2 226886208181911366 226886208181911366 226886208181911366 endpoint_13_38_w0 endpoint_13_38_w2
private theorem endpoint_13_38_w4 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 4 2 226886208181911366 = some 226886208181911366 := by decide +kernel
private theorem endpoint_13_38_p6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 6 226886208181911366 = some 226886208181911366 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 4 2 226886208181911366 226886208181911366 226886208181911366 endpoint_13_38_p4 endpoint_13_38_w4
private theorem endpoint_13_38_w6 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 6 2 226886208181911366 = some 226886208181911366 := by decide +kernel
private theorem endpoint_13_38_p8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 8 226886208181911366 = some 226886208181911366 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 6 2 226886208181911366 226886208181911366 226886208181911366 endpoint_13_38_p6 endpoint_13_38_w6
private theorem endpoint_13_38_w8 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 8 2 226886208181911366 = some 226886208181911366 := by decide +kernel
private theorem endpoint_13_38_p10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 10 226886208181911366 = some 226886208181911366 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 8 2 226886208181911366 226886208181911366 226886208181911366 endpoint_13_38_p8 endpoint_13_38_w8
private theorem endpoint_13_38_w10 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 10 2 226886208181911366 = some 226886208181911366 := by decide +kernel
private theorem endpoint_13_38_p12 : receiptWindow endpoint_13_38_flag endpoint_13_38_sources 0 12 226886208181911366 = some 226886208181911366 :=
  join_receipt_window endpoint_13_38_flag endpoint_13_38_sources 0 10 2 226886208181911366 226886208181911366 226886208181911366 endpoint_13_38_p10 endpoint_13_38_w10
def endpoint_13_38 : CertifiedEndpoint :=
  ⟨⟨13, 38, 3805⟩, 226886208181911366, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_38_flag endpoint_13_38_sources 12 226886208181911366 226886208181911366 rfl endpoint_13_38_base endpoint_13_38_p12) (by decide)⟩
private def endpoint_13_39_flag : Flag := ⟨13, 39, 3773⟩
private def endpoint_13_39_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_13_39_base : receiptBase endpoint_13_39_flag endpoint_13_39_sources = some 229945317623795661 := by decide +kernel
private theorem endpoint_13_39_w0 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 2 229945317623795661 = some 229945317623795661 := by decide +kernel
private theorem endpoint_13_39_w2 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 2 2 229945317623795661 = some 229945317623795661 := by decide +kernel
private theorem endpoint_13_39_p4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 4 229945317623795661 = some 229945317623795661 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 2 2 229945317623795661 229945317623795661 229945317623795661 endpoint_13_39_w0 endpoint_13_39_w2
private theorem endpoint_13_39_w4 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 4 2 229945317623795661 = some 229945317623795661 := by decide +kernel
private theorem endpoint_13_39_p6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 6 229945317623795661 = some 229945317623795661 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 4 2 229945317623795661 229945317623795661 229945317623795661 endpoint_13_39_p4 endpoint_13_39_w4
private theorem endpoint_13_39_w6 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 6 2 229945317623795661 = some 229945317623795661 := by decide +kernel
private theorem endpoint_13_39_p8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 8 229945317623795661 = some 229945317623795661 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 6 2 229945317623795661 229945317623795661 229945317623795661 endpoint_13_39_p6 endpoint_13_39_w6
private theorem endpoint_13_39_w8 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 8 2 229945317623795661 = some 229945317623795661 := by decide +kernel
private theorem endpoint_13_39_p10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 10 229945317623795661 = some 229945317623795661 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 8 2 229945317623795661 229945317623795661 229945317623795661 endpoint_13_39_p8 endpoint_13_39_w8
private theorem endpoint_13_39_w10 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 10 2 229945317623795661 = some 229945317623795661 := by decide +kernel
private theorem endpoint_13_39_p12 : receiptWindow endpoint_13_39_flag endpoint_13_39_sources 0 12 229945317623795661 = some 229945317623795661 :=
  join_receipt_window endpoint_13_39_flag endpoint_13_39_sources 0 10 2 229945317623795661 229945317623795661 229945317623795661 endpoint_13_39_p10 endpoint_13_39_w10
def endpoint_13_39 : CertifiedEndpoint :=
  ⟨⟨13, 39, 3773⟩, 229945317623795661, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_13_39_flag endpoint_13_39_sources 12 229945317623795661 229945317623795661 rfl endpoint_13_39_base endpoint_13_39_p12) (by decide)⟩
private def endpoint_13_40_flag : Flag := ⟨13, 40, 3740⟩
private def endpoint_13_40_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_40_base : receiptBase endpoint_13_40_flag endpoint_13_40_sources = some 233309077711045740 := by decide +kernel
private theorem endpoint_13_40_w0 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 2 233309077711045740 = some 233309077711045740 := by decide +kernel
private theorem endpoint_13_40_w2 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 2 2 233309077711045740 = some 233309077711045740 := by decide +kernel
private theorem endpoint_13_40_p4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 4 233309077711045740 = some 233309077711045740 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 2 2 233309077711045740 233309077711045740 233309077711045740 endpoint_13_40_w0 endpoint_13_40_w2
private theorem endpoint_13_40_w4 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 4 2 233309077711045740 = some 233309077711045740 := by decide +kernel
private theorem endpoint_13_40_p6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 6 233309077711045740 = some 233309077711045740 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 4 2 233309077711045740 233309077711045740 233309077711045740 endpoint_13_40_p4 endpoint_13_40_w4
private theorem endpoint_13_40_w6 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 6 2 233309077711045740 = some 233309077711045740 := by decide +kernel
private theorem endpoint_13_40_p8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 8 233309077711045740 = some 233309077711045740 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 6 2 233309077711045740 233309077711045740 233309077711045740 endpoint_13_40_p6 endpoint_13_40_w6
private theorem endpoint_13_40_w8 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 8 2 233309077711045740 = some 233309077711045740 := by decide +kernel
private theorem endpoint_13_40_p10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 10 233309077711045740 = some 233309077711045740 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 8 2 233309077711045740 233309077711045740 233309077711045740 endpoint_13_40_p8 endpoint_13_40_w8
private theorem endpoint_13_40_w10 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 10 2 233309077711045740 = some 233309077711045740 := by decide +kernel
private theorem endpoint_13_40_p12 : receiptWindow endpoint_13_40_flag endpoint_13_40_sources 0 12 233309077711045740 = some 233309077711045740 :=
  join_receipt_window endpoint_13_40_flag endpoint_13_40_sources 0 10 2 233309077711045740 233309077711045740 233309077711045740 endpoint_13_40_p10 endpoint_13_40_w10
def endpoint_13_40 : CertifiedEndpoint :=
  ⟨⟨13, 40, 3740⟩, 233309077711045740, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_40_flag endpoint_13_40_sources 12 233309077711045740 233309077711045740 rfl endpoint_13_40_base endpoint_13_40_p12) (by decide)⟩
private def endpoint_13_41_flag : Flag := ⟨13, 41, 3706⟩
private def endpoint_13_41_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_41_base : receiptBase endpoint_13_41_flag endpoint_13_41_sources = some 236086767048757429 := by decide +kernel
private theorem endpoint_13_41_w0 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 2 236086767048757429 = some 236086767048757429 := by decide +kernel
private theorem endpoint_13_41_w2 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 2 2 236086767048757429 = some 236086767048757429 := by decide +kernel
private theorem endpoint_13_41_p4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 4 236086767048757429 = some 236086767048757429 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 2 2 236086767048757429 236086767048757429 236086767048757429 endpoint_13_41_w0 endpoint_13_41_w2
private theorem endpoint_13_41_w4 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 4 2 236086767048757429 = some 236086767048757429 := by decide +kernel
private theorem endpoint_13_41_p6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 6 236086767048757429 = some 236086767048757429 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 4 2 236086767048757429 236086767048757429 236086767048757429 endpoint_13_41_p4 endpoint_13_41_w4
private theorem endpoint_13_41_w6 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 6 2 236086767048757429 = some 236086767048757429 := by decide +kernel
private theorem endpoint_13_41_p8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 8 236086767048757429 = some 236086767048757429 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 6 2 236086767048757429 236086767048757429 236086767048757429 endpoint_13_41_p6 endpoint_13_41_w6
private theorem endpoint_13_41_w8 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 8 2 236086767048757429 = some 236086767048757429 := by decide +kernel
private theorem endpoint_13_41_p10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 10 236086767048757429 = some 236086767048757429 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 8 2 236086767048757429 236086767048757429 236086767048757429 endpoint_13_41_p8 endpoint_13_41_w8
private theorem endpoint_13_41_w10 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 10 2 236086767048757429 = some 236086767048757429 := by decide +kernel
private theorem endpoint_13_41_p12 : receiptWindow endpoint_13_41_flag endpoint_13_41_sources 0 12 236086767048757429 = some 236086767048757429 :=
  join_receipt_window endpoint_13_41_flag endpoint_13_41_sources 0 10 2 236086767048757429 236086767048757429 236086767048757429 endpoint_13_41_p10 endpoint_13_41_w10
def endpoint_13_41 : CertifiedEndpoint :=
  ⟨⟨13, 41, 3706⟩, 236086767048757429, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_41_flag endpoint_13_41_sources 12 236086767048757429 236086767048757429 rfl endpoint_13_41_base endpoint_13_41_p12) (by decide)⟩
private def endpoint_13_42_flag : Flag := ⟨13, 42, 3671⟩
private def endpoint_13_42_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_42_base : receiptBase endpoint_13_42_flag endpoint_13_42_sources = some 238711396570103471 := by decide +kernel
private theorem endpoint_13_42_w0 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 2 238711396570103471 = some 238711396570103471 := by decide +kernel
private theorem endpoint_13_42_w2 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 2 2 238711396570103471 = some 238711396570103471 := by decide +kernel
private theorem endpoint_13_42_p4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 4 238711396570103471 = some 238711396570103471 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 2 2 238711396570103471 238711396570103471 238711396570103471 endpoint_13_42_w0 endpoint_13_42_w2
private theorem endpoint_13_42_w4 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 4 2 238711396570103471 = some 238711396570103471 := by decide +kernel
private theorem endpoint_13_42_p6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 6 238711396570103471 = some 238711396570103471 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 4 2 238711396570103471 238711396570103471 238711396570103471 endpoint_13_42_p4 endpoint_13_42_w4
private theorem endpoint_13_42_w6 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 6 2 238711396570103471 = some 238711396570103471 := by decide +kernel
private theorem endpoint_13_42_p8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 8 238711396570103471 = some 238711396570103471 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 6 2 238711396570103471 238711396570103471 238711396570103471 endpoint_13_42_p6 endpoint_13_42_w6
private theorem endpoint_13_42_w8 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 8 2 238711396570103471 = some 238711396570103471 := by decide +kernel
private theorem endpoint_13_42_p10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 10 238711396570103471 = some 238711396570103471 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 8 2 238711396570103471 238711396570103471 238711396570103471 endpoint_13_42_p8 endpoint_13_42_w8
private theorem endpoint_13_42_w10 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 10 2 238711396570103471 = some 238711396570103471 := by decide +kernel
private theorem endpoint_13_42_p12 : receiptWindow endpoint_13_42_flag endpoint_13_42_sources 0 12 238711396570103471 = some 238711396570103471 :=
  join_receipt_window endpoint_13_42_flag endpoint_13_42_sources 0 10 2 238711396570103471 238711396570103471 238711396570103471 endpoint_13_42_p10 endpoint_13_42_w10
def endpoint_13_42 : CertifiedEndpoint :=
  ⟨⟨13, 42, 3671⟩, 238711396570103471, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_42_flag endpoint_13_42_sources 12 238711396570103471 238711396570103471 rfl endpoint_13_42_base endpoint_13_42_p12) (by decide)⟩
private def endpoint_13_43_flag : Flag := ⟨13, 43, 3636⟩
private def endpoint_13_43_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_43_base : receiptBase endpoint_13_43_flag endpoint_13_43_sources = some 241244439685424228 := by decide +kernel
private theorem endpoint_13_43_w0 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 2 241244439685424228 = some 241244439685424228 := by decide +kernel
private theorem endpoint_13_43_w2 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 2 2 241244439685424228 = some 241244439685424228 := by decide +kernel
private theorem endpoint_13_43_p4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 4 241244439685424228 = some 241244439685424228 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 2 2 241244439685424228 241244439685424228 241244439685424228 endpoint_13_43_w0 endpoint_13_43_w2
private theorem endpoint_13_43_w4 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 4 2 241244439685424228 = some 241244439685424228 := by decide +kernel
private theorem endpoint_13_43_p6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 6 241244439685424228 = some 241244439685424228 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 4 2 241244439685424228 241244439685424228 241244439685424228 endpoint_13_43_p4 endpoint_13_43_w4
private theorem endpoint_13_43_w6 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 6 2 241244439685424228 = some 241244439685424228 := by decide +kernel
private theorem endpoint_13_43_p8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 8 241244439685424228 = some 241244439685424228 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 6 2 241244439685424228 241244439685424228 241244439685424228 endpoint_13_43_p6 endpoint_13_43_w6
private theorem endpoint_13_43_w8 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 8 2 241244439685424228 = some 241244439685424228 := by decide +kernel
private theorem endpoint_13_43_p10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 10 241244439685424228 = some 241244439685424228 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 8 2 241244439685424228 241244439685424228 241244439685424228 endpoint_13_43_p8 endpoint_13_43_w8
private theorem endpoint_13_43_w10 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 10 2 241244439685424228 = some 241244439685424228 := by decide +kernel
private theorem endpoint_13_43_p12 : receiptWindow endpoint_13_43_flag endpoint_13_43_sources 0 12 241244439685424228 = some 241244439685424228 :=
  join_receipt_window endpoint_13_43_flag endpoint_13_43_sources 0 10 2 241244439685424228 241244439685424228 241244439685424228 endpoint_13_43_p10 endpoint_13_43_w10
def endpoint_13_43 : CertifiedEndpoint :=
  ⟨⟨13, 43, 3636⟩, 241244439685424228, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_43_flag endpoint_13_43_sources 12 241244439685424228 241244439685424228 rfl endpoint_13_43_base endpoint_13_43_p12) (by decide)⟩
private def endpoint_13_44_flag : Flag := ⟨13, 44, 3600⟩
private def endpoint_13_44_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_44_base : receiptBase endpoint_13_44_flag endpoint_13_44_sources = some 243619263440355663 := by decide +kernel
private theorem endpoint_13_44_w0 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 2 243619263440355663 = some 243619263440355663 := by decide +kernel
private theorem endpoint_13_44_w2 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 2 2 243619263440355663 = some 243619263440355663 := by decide +kernel
private theorem endpoint_13_44_p4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 4 243619263440355663 = some 243619263440355663 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 2 2 243619263440355663 243619263440355663 243619263440355663 endpoint_13_44_w0 endpoint_13_44_w2
private theorem endpoint_13_44_w4 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 4 2 243619263440355663 = some 243619263440355663 := by decide +kernel
private theorem endpoint_13_44_p6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 6 243619263440355663 = some 243619263440355663 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 4 2 243619263440355663 243619263440355663 243619263440355663 endpoint_13_44_p4 endpoint_13_44_w4
private theorem endpoint_13_44_w6 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 6 2 243619263440355663 = some 243619263440355663 := by decide +kernel
private theorem endpoint_13_44_p8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 8 243619263440355663 = some 243619263440355663 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 6 2 243619263440355663 243619263440355663 243619263440355663 endpoint_13_44_p6 endpoint_13_44_w6
private theorem endpoint_13_44_w8 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 8 2 243619263440355663 = some 243619263440355663 := by decide +kernel
private theorem endpoint_13_44_p10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 10 243619263440355663 = some 243619263440355663 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 8 2 243619263440355663 243619263440355663 243619263440355663 endpoint_13_44_p8 endpoint_13_44_w8
private theorem endpoint_13_44_w10 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 10 2 243619263440355663 = some 243619263440355663 := by decide +kernel
private theorem endpoint_13_44_p12 : receiptWindow endpoint_13_44_flag endpoint_13_44_sources 0 12 243619263440355663 = some 243619263440355663 :=
  join_receipt_window endpoint_13_44_flag endpoint_13_44_sources 0 10 2 243619263440355663 243619263440355663 243619263440355663 endpoint_13_44_p10 endpoint_13_44_w10
def endpoint_13_44 : CertifiedEndpoint :=
  ⟨⟨13, 44, 3600⟩, 243619263440355663, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_44_flag endpoint_13_44_sources 12 243619263440355663 243619263440355663 rfl endpoint_13_44_base endpoint_13_44_p12) (by decide)⟩
private def endpoint_13_45_flag : Flag := ⟨13, 45, 3563⟩
private def endpoint_13_45_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_45_base : receiptBase endpoint_13_45_flag endpoint_13_45_sources = some 245831998176880016 := by decide +kernel
private theorem endpoint_13_45_w0 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 2 245831998176880016 = some 245831998176880016 := by decide +kernel
private theorem endpoint_13_45_w2 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 2 2 245831998176880016 = some 245831998176880016 := by decide +kernel
private theorem endpoint_13_45_p4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 4 245831998176880016 = some 245831998176880016 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 2 2 245831998176880016 245831998176880016 245831998176880016 endpoint_13_45_w0 endpoint_13_45_w2
private theorem endpoint_13_45_w4 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 4 2 245831998176880016 = some 245831998176880016 := by decide +kernel
private theorem endpoint_13_45_p6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 6 245831998176880016 = some 245831998176880016 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 4 2 245831998176880016 245831998176880016 245831998176880016 endpoint_13_45_p4 endpoint_13_45_w4
private theorem endpoint_13_45_w6 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 6 2 245831998176880016 = some 245831998176880016 := by decide +kernel
private theorem endpoint_13_45_p8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 8 245831998176880016 = some 245831998176880016 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 6 2 245831998176880016 245831998176880016 245831998176880016 endpoint_13_45_p6 endpoint_13_45_w6
private theorem endpoint_13_45_w8 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 8 2 245831998176880016 = some 245831998176880016 := by decide +kernel
private theorem endpoint_13_45_p10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 10 245831998176880016 = some 245831998176880016 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 8 2 245831998176880016 245831998176880016 245831998176880016 endpoint_13_45_p8 endpoint_13_45_w8
private theorem endpoint_13_45_w10 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 10 2 245831998176880016 = some 245831998176880016 := by decide +kernel
private theorem endpoint_13_45_p12 : receiptWindow endpoint_13_45_flag endpoint_13_45_sources 0 12 245831998176880016 = some 245831998176880016 :=
  join_receipt_window endpoint_13_45_flag endpoint_13_45_sources 0 10 2 245831998176880016 245831998176880016 245831998176880016 endpoint_13_45_p10 endpoint_13_45_w10
def endpoint_13_45 : CertifiedEndpoint :=
  ⟨⟨13, 45, 3563⟩, 245831998176880016, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_45_flag endpoint_13_45_sources 12 245831998176880016 245831998176880016 rfl endpoint_13_45_base endpoint_13_45_p12) (by decide)⟩
private def endpoint_13_46_flag : Flag := ⟨13, 46, 3525⟩
private def endpoint_13_46_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_46_base : receiptBase endpoint_13_46_flag endpoint_13_46_sources = some 247878774236979531 := by decide +kernel
private theorem endpoint_13_46_w0 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 2 247878774236979531 = some 247917781797157082 := by decide +kernel
private theorem endpoint_13_46_w2 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 2 2 247917781797157082 = some 247917781797157082 := by decide +kernel
private theorem endpoint_13_46_p4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 4 247878774236979531 = some 247917781797157082 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 2 2 247878774236979531 247917781797157082 247917781797157082 endpoint_13_46_w0 endpoint_13_46_w2
private theorem endpoint_13_46_w4 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 4 2 247917781797157082 = some 247917781797157082 := by decide +kernel
private theorem endpoint_13_46_p6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 6 247878774236979531 = some 247917781797157082 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 4 2 247878774236979531 247917781797157082 247917781797157082 endpoint_13_46_p4 endpoint_13_46_w4
private theorem endpoint_13_46_w6 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 6 2 247917781797157082 = some 247917781797157082 := by decide +kernel
private theorem endpoint_13_46_p8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 8 247878774236979531 = some 247917781797157082 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 6 2 247878774236979531 247917781797157082 247917781797157082 endpoint_13_46_p6 endpoint_13_46_w6
private theorem endpoint_13_46_w8 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 8 2 247917781797157082 = some 247917781797157082 := by decide +kernel
private theorem endpoint_13_46_p10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 10 247878774236979531 = some 247917781797157082 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 8 2 247878774236979531 247917781797157082 247917781797157082 endpoint_13_46_p8 endpoint_13_46_w8
private theorem endpoint_13_46_w10 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 10 2 247917781797157082 = some 247917781797157082 := by decide +kernel
private theorem endpoint_13_46_p12 : receiptWindow endpoint_13_46_flag endpoint_13_46_sources 0 12 247878774236979531 = some 247917781797157082 :=
  join_receipt_window endpoint_13_46_flag endpoint_13_46_sources 0 10 2 247878774236979531 247917781797157082 247917781797157082 endpoint_13_46_p10 endpoint_13_46_w10
def endpoint_13_46 : CertifiedEndpoint :=
  ⟨⟨13, 46, 3525⟩, 247917781797157082, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_46_flag endpoint_13_46_sources 12 247878774236979531 247917781797157082 rfl endpoint_13_46_base endpoint_13_46_p12) (by decide)⟩
private def endpoint_13_47_flag : Flag := ⟨13, 47, 3486⟩
private def endpoint_13_47_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_13_47_base : receiptBase endpoint_13_47_flag endpoint_13_47_sources = some 249755721962636449 := by decide +kernel
private theorem endpoint_13_47_w0 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 2 249755721962636449 = some 252808771837208925 := by decide +kernel
private theorem endpoint_13_47_w2 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 2 2 252808771837208925 = some 252808771837208925 := by decide +kernel
private theorem endpoint_13_47_p4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 4 249755721962636449 = some 252808771837208925 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 2 2 249755721962636449 252808771837208925 252808771837208925 endpoint_13_47_w0 endpoint_13_47_w2
private theorem endpoint_13_47_w4 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 4 2 252808771837208925 = some 252808771837208925 := by decide +kernel
private theorem endpoint_13_47_p6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 6 249755721962636449 = some 252808771837208925 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 4 2 249755721962636449 252808771837208925 252808771837208925 endpoint_13_47_p4 endpoint_13_47_w4
private theorem endpoint_13_47_w6 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 6 2 252808771837208925 = some 252808771837208925 := by decide +kernel
private theorem endpoint_13_47_p8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 8 249755721962636449 = some 252808771837208925 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 6 2 249755721962636449 252808771837208925 252808771837208925 endpoint_13_47_p6 endpoint_13_47_w6
private theorem endpoint_13_47_w8 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 8 2 252808771837208925 = some 252808771837208925 := by decide +kernel
private theorem endpoint_13_47_p10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 10 249755721962636449 = some 252808771837208925 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 8 2 249755721962636449 252808771837208925 252808771837208925 endpoint_13_47_p8 endpoint_13_47_w8
private theorem endpoint_13_47_w10 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 10 2 252808771837208925 = some 252808771837208925 := by decide +kernel
private theorem endpoint_13_47_p12 : receiptWindow endpoint_13_47_flag endpoint_13_47_sources 0 12 249755721962636449 = some 252808771837208925 :=
  join_receipt_window endpoint_13_47_flag endpoint_13_47_sources 0 10 2 249755721962636449 252808771837208925 252808771837208925 endpoint_13_47_p10 endpoint_13_47_w10
def endpoint_13_47 : CertifiedEndpoint :=
  ⟨⟨13, 47, 3486⟩, 252808771837208925, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_13_47_flag endpoint_13_47_sources 12 249755721962636449 252808771837208925 rfl endpoint_13_47_base endpoint_13_47_p12) (by decide)⟩
private def endpoint_13_48_flag : Flag := ⟨13, 48, 3447⟩
private def endpoint_13_48_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_48_base : receiptBase endpoint_13_48_flag endpoint_13_48_sources = some 252357168437469313 := by decide +kernel
private theorem endpoint_13_48_w0 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 2 252357168437469313 = some 253458272180112686 := by decide +kernel
private theorem endpoint_13_48_w2 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 2 2 253458272180112686 = some 253458272180112686 := by decide +kernel
private theorem endpoint_13_48_p4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 4 252357168437469313 = some 253458272180112686 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 2 2 252357168437469313 253458272180112686 253458272180112686 endpoint_13_48_w0 endpoint_13_48_w2
private theorem endpoint_13_48_w4 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 4 2 253458272180112686 = some 253458272180112686 := by decide +kernel
private theorem endpoint_13_48_p6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 6 252357168437469313 = some 253458272180112686 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 4 2 252357168437469313 253458272180112686 253458272180112686 endpoint_13_48_p4 endpoint_13_48_w4
private theorem endpoint_13_48_w6 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 6 2 253458272180112686 = some 253458272180112686 := by decide +kernel
private theorem endpoint_13_48_p8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 8 252357168437469313 = some 253458272180112686 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 6 2 252357168437469313 253458272180112686 253458272180112686 endpoint_13_48_p6 endpoint_13_48_w6
private theorem endpoint_13_48_w8 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 8 2 253458272180112686 = some 253458272180112686 := by decide +kernel
private theorem endpoint_13_48_p10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 10 252357168437469313 = some 253458272180112686 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 8 2 252357168437469313 253458272180112686 253458272180112686 endpoint_13_48_p8 endpoint_13_48_w8
private theorem endpoint_13_48_w10 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 10 2 253458272180112686 = some 253458272180112686 := by decide +kernel
private theorem endpoint_13_48_p12 : receiptWindow endpoint_13_48_flag endpoint_13_48_sources 0 12 252357168437469313 = some 253458272180112686 :=
  join_receipt_window endpoint_13_48_flag endpoint_13_48_sources 0 10 2 252357168437469313 253458272180112686 253458272180112686 endpoint_13_48_p10 endpoint_13_48_w10
def endpoint_13_48 : CertifiedEndpoint :=
  ⟨⟨13, 48, 3447⟩, 253458272180112686, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_48_flag endpoint_13_48_sources 12 252357168437469313 253458272180112686 rfl endpoint_13_48_base endpoint_13_48_p12) (by decide)⟩
private def endpoint_13_49_flag : Flag := ⟨13, 49, 3406⟩
private def endpoint_13_49_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_49_base : receiptBase endpoint_13_49_flag endpoint_13_49_sources = some 253894615781749377 := by decide +kernel
private theorem endpoint_13_49_w0 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 2 253894615781749377 = some 258009684935325234 := by decide +kernel
private theorem endpoint_13_49_w2 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 2 2 258009684935325234 = some 258009684935325234 := by decide +kernel
private theorem endpoint_13_49_p4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 4 253894615781749377 = some 258009684935325234 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 2 2 253894615781749377 258009684935325234 258009684935325234 endpoint_13_49_w0 endpoint_13_49_w2
private theorem endpoint_13_49_w4 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 4 2 258009684935325234 = some 258009684935325234 := by decide +kernel
private theorem endpoint_13_49_p6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 6 253894615781749377 = some 258009684935325234 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 4 2 253894615781749377 258009684935325234 258009684935325234 endpoint_13_49_p4 endpoint_13_49_w4
private theorem endpoint_13_49_w6 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 6 2 258009684935325234 = some 258009684935325234 := by decide +kernel
private theorem endpoint_13_49_p8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 8 253894615781749377 = some 258009684935325234 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 6 2 253894615781749377 258009684935325234 258009684935325234 endpoint_13_49_p6 endpoint_13_49_w6
private theorem endpoint_13_49_w8 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 8 2 258009684935325234 = some 258009684935325234 := by decide +kernel
private theorem endpoint_13_49_p10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 10 253894615781749377 = some 258009684935325234 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 8 2 253894615781749377 258009684935325234 258009684935325234 endpoint_13_49_p8 endpoint_13_49_w8
private theorem endpoint_13_49_w10 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 10 2 258009684935325234 = some 258009684935325234 := by decide +kernel
private theorem endpoint_13_49_p12 : receiptWindow endpoint_13_49_flag endpoint_13_49_sources 0 12 253894615781749377 = some 258009684935325234 :=
  join_receipt_window endpoint_13_49_flag endpoint_13_49_sources 0 10 2 253894615781749377 258009684935325234 258009684935325234 endpoint_13_49_p10 endpoint_13_49_w10
def endpoint_13_49 : CertifiedEndpoint :=
  ⟨⟨13, 49, 3406⟩, 258009684935325234, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_49_flag endpoint_13_49_sources 12 253894615781749377 258009684935325234 rfl endpoint_13_49_base endpoint_13_49_p12) (by decide)⟩
private def endpoint_13_50_flag : Flag := ⟨13, 50, 3364⟩
private def endpoint_13_50_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_13_50_base : receiptBase endpoint_13_50_flag endpoint_13_50_sources = some 255249549002405162 := by decide +kernel
private theorem endpoint_13_50_w0 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 2 255249549002405162 = some 262437493976995220 := by decide +kernel
private theorem endpoint_13_50_w2 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 2 2 262437493976995220 = some 262437493976995220 := by decide +kernel
private theorem endpoint_13_50_p4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 4 255249549002405162 = some 262437493976995220 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 2 2 255249549002405162 262437493976995220 262437493976995220 endpoint_13_50_w0 endpoint_13_50_w2
private theorem endpoint_13_50_w4 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 4 2 262437493976995220 = some 262437493976995220 := by decide +kernel
private theorem endpoint_13_50_p6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 6 255249549002405162 = some 262437493976995220 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 4 2 255249549002405162 262437493976995220 262437493976995220 endpoint_13_50_p4 endpoint_13_50_w4
private theorem endpoint_13_50_w6 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 6 2 262437493976995220 = some 262437493976995220 := by decide +kernel
private theorem endpoint_13_50_p8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 8 255249549002405162 = some 262437493976995220 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 6 2 255249549002405162 262437493976995220 262437493976995220 endpoint_13_50_p6 endpoint_13_50_w6
private theorem endpoint_13_50_w8 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 8 2 262437493976995220 = some 262437493976995220 := by decide +kernel
private theorem endpoint_13_50_p10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 10 255249549002405162 = some 262437493976995220 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 8 2 255249549002405162 262437493976995220 262437493976995220 endpoint_13_50_p8 endpoint_13_50_w8
private theorem endpoint_13_50_w10 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 10 2 262437493976995220 = some 262437493976995220 := by decide +kernel
private theorem endpoint_13_50_p12 : receiptWindow endpoint_13_50_flag endpoint_13_50_sources 0 12 255249549002405162 = some 262437493976995220 :=
  join_receipt_window endpoint_13_50_flag endpoint_13_50_sources 0 10 2 255249549002405162 262437493976995220 262437493976995220 endpoint_13_50_p10 endpoint_13_50_w10
def endpoint_13_50 : CertifiedEndpoint :=
  ⟨⟨13, 50, 3364⟩, 262437493976995220, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_13_50_flag endpoint_13_50_sources 12 255249549002405162 262437493976995220 rfl endpoint_13_50_base endpoint_13_50_p12) (by decide)⟩
private def endpoint_13_51_flag : Flag := ⟨13, 51, 3321⟩
private def endpoint_13_51_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_51_base : receiptBase endpoint_13_51_flag endpoint_13_51_sources = some 258540517524133012 := by decide +kernel
private theorem endpoint_13_51_w0 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 2 258540517524133012 = some 259465653326139294 := by decide +kernel
private theorem endpoint_13_51_w2 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 2 2 259465653326139294 = some 259465653326139294 := by decide +kernel
private theorem endpoint_13_51_p4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 4 258540517524133012 = some 259465653326139294 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 2 2 258540517524133012 259465653326139294 259465653326139294 endpoint_13_51_w0 endpoint_13_51_w2
private theorem endpoint_13_51_w4 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 4 2 259465653326139294 = some 259465653326139294 := by decide +kernel
private theorem endpoint_13_51_p6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 6 258540517524133012 = some 259465653326139294 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 4 2 258540517524133012 259465653326139294 259465653326139294 endpoint_13_51_p4 endpoint_13_51_w4
private theorem endpoint_13_51_w6 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 6 2 259465653326139294 = some 259465653326139294 := by decide +kernel
private theorem endpoint_13_51_p8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 8 258540517524133012 = some 259465653326139294 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 6 2 258540517524133012 259465653326139294 259465653326139294 endpoint_13_51_p6 endpoint_13_51_w6
private theorem endpoint_13_51_w8 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 8 2 259465653326139294 = some 259465653326139294 := by decide +kernel
private theorem endpoint_13_51_p10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 10 258540517524133012 = some 259465653326139294 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 8 2 258540517524133012 259465653326139294 259465653326139294 endpoint_13_51_p8 endpoint_13_51_w8
private theorem endpoint_13_51_w10 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 10 2 259465653326139294 = some 259465653326139294 := by decide +kernel
private theorem endpoint_13_51_p12 : receiptWindow endpoint_13_51_flag endpoint_13_51_sources 0 12 258540517524133012 = some 259465653326139294 :=
  join_receipt_window endpoint_13_51_flag endpoint_13_51_sources 0 10 2 258540517524133012 259465653326139294 259465653326139294 endpoint_13_51_p10 endpoint_13_51_w10
def endpoint_13_51 : CertifiedEndpoint :=
  ⟨⟨13, 51, 3321⟩, 259465653326139294, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_51_flag endpoint_13_51_sources 12 258540517524133012 259465653326139294 rfl endpoint_13_51_base endpoint_13_51_p12) (by decide)⟩
private def endpoint_13_52_flag : Flag := ⟨13, 52, 3277⟩
private def endpoint_13_52_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_13_52_base : receiptBase endpoint_13_52_flag endpoint_13_52_sources = some 259458423050056357 := by decide +kernel
private theorem endpoint_13_52_w0 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 2 259458423050056357 = some 263471393882388536 := by decide +kernel
private theorem endpoint_13_52_w2 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 2 2 263471393882388536 = some 263471393882388536 := by decide +kernel
private theorem endpoint_13_52_p4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 4 259458423050056357 = some 263471393882388536 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 2 2 259458423050056357 263471393882388536 263471393882388536 endpoint_13_52_w0 endpoint_13_52_w2
private theorem endpoint_13_52_w4 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 4 2 263471393882388536 = some 263471393882388536 := by decide +kernel
private theorem endpoint_13_52_p6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 6 259458423050056357 = some 263471393882388536 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 4 2 259458423050056357 263471393882388536 263471393882388536 endpoint_13_52_p4 endpoint_13_52_w4
private theorem endpoint_13_52_w6 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 6 2 263471393882388536 = some 263471393882388536 := by decide +kernel
private theorem endpoint_13_52_p8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 8 259458423050056357 = some 263471393882388536 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 6 2 259458423050056357 263471393882388536 263471393882388536 endpoint_13_52_p6 endpoint_13_52_w6
private theorem endpoint_13_52_w8 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 8 2 263471393882388536 = some 263471393882388536 := by decide +kernel
private theorem endpoint_13_52_p10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 10 259458423050056357 = some 263471393882388536 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 8 2 259458423050056357 263471393882388536 263471393882388536 endpoint_13_52_p8 endpoint_13_52_w8
private theorem endpoint_13_52_w10 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 10 2 263471393882388536 = some 263471393882388536 := by decide +kernel
private theorem endpoint_13_52_p12 : receiptWindow endpoint_13_52_flag endpoint_13_52_sources 0 12 259458423050056357 = some 263471393882388536 :=
  join_receipt_window endpoint_13_52_flag endpoint_13_52_sources 0 10 2 259458423050056357 263471393882388536 263471393882388536 endpoint_13_52_p10 endpoint_13_52_w10
def endpoint_13_52 : CertifiedEndpoint :=
  ⟨⟨13, 52, 3277⟩, 263471393882388536, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_13_52_flag endpoint_13_52_sources 12 259458423050056357 263471393882388536 rfl endpoint_13_52_base endpoint_13_52_p12) (by decide)⟩
private def endpoint_13_53_flag : Flag := ⟨13, 53, 3231⟩
private def endpoint_13_53_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_53_base : receiptBase endpoint_13_53_flag endpoint_13_53_sources = some 261050147211800495 := by decide +kernel
private theorem endpoint_13_53_w0 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 2 261050147211800495 = some 261050147211800495 := by decide +kernel
private theorem endpoint_13_53_w2 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 2 2 261050147211800495 = some 261050147211800495 := by decide +kernel
private theorem endpoint_13_53_p4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 4 261050147211800495 = some 261050147211800495 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 2 2 261050147211800495 261050147211800495 261050147211800495 endpoint_13_53_w0 endpoint_13_53_w2
private theorem endpoint_13_53_w4 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 4 2 261050147211800495 = some 261050147211800495 := by decide +kernel
private theorem endpoint_13_53_p6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 6 261050147211800495 = some 261050147211800495 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 4 2 261050147211800495 261050147211800495 261050147211800495 endpoint_13_53_p4 endpoint_13_53_w4
private theorem endpoint_13_53_w6 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 6 2 261050147211800495 = some 261050147211800495 := by decide +kernel
private theorem endpoint_13_53_p8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 8 261050147211800495 = some 261050147211800495 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 6 2 261050147211800495 261050147211800495 261050147211800495 endpoint_13_53_p6 endpoint_13_53_w6
private theorem endpoint_13_53_w8 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 8 2 261050147211800495 = some 261050147211800495 := by decide +kernel
private theorem endpoint_13_53_p10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 10 261050147211800495 = some 261050147211800495 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 8 2 261050147211800495 261050147211800495 261050147211800495 endpoint_13_53_p8 endpoint_13_53_w8
private theorem endpoint_13_53_w10 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 10 2 261050147211800495 = some 261050147211800495 := by decide +kernel
private theorem endpoint_13_53_p12 : receiptWindow endpoint_13_53_flag endpoint_13_53_sources 0 12 261050147211800495 = some 261050147211800495 :=
  join_receipt_window endpoint_13_53_flag endpoint_13_53_sources 0 10 2 261050147211800495 261050147211800495 261050147211800495 endpoint_13_53_p10 endpoint_13_53_w10
def endpoint_13_53 : CertifiedEndpoint :=
  ⟨⟨13, 53, 3231⟩, 261050147211800495, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_53_flag endpoint_13_53_sources 12 261050147211800495 261050147211800495 rfl endpoint_13_53_base endpoint_13_53_p12) (by decide)⟩
private def endpoint_13_54_flag : Flag := ⟨13, 54, 3184⟩
private def endpoint_13_54_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_13_54_base : receiptBase endpoint_13_54_flag endpoint_13_54_sources = some 261499503270909566 := by decide +kernel
private theorem endpoint_13_54_w0 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 2 261499503270909566 = some 263127966224431656 := by decide +kernel
private theorem endpoint_13_54_w2 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 2 2 263127966224431656 = some 263127966224431656 := by decide +kernel
private theorem endpoint_13_54_p4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 4 261499503270909566 = some 263127966224431656 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 2 2 261499503270909566 263127966224431656 263127966224431656 endpoint_13_54_w0 endpoint_13_54_w2
private theorem endpoint_13_54_w4 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 4 2 263127966224431656 = some 263127966224431656 := by decide +kernel
private theorem endpoint_13_54_p6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 6 261499503270909566 = some 263127966224431656 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 4 2 261499503270909566 263127966224431656 263127966224431656 endpoint_13_54_p4 endpoint_13_54_w4
private theorem endpoint_13_54_w6 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 6 2 263127966224431656 = some 263127966224431656 := by decide +kernel
private theorem endpoint_13_54_p8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 8 261499503270909566 = some 263127966224431656 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 6 2 261499503270909566 263127966224431656 263127966224431656 endpoint_13_54_p6 endpoint_13_54_w6
private theorem endpoint_13_54_w8 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 8 2 263127966224431656 = some 263127966224431656 := by decide +kernel
private theorem endpoint_13_54_p10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 10 261499503270909566 = some 263127966224431656 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 8 2 261499503270909566 263127966224431656 263127966224431656 endpoint_13_54_p8 endpoint_13_54_w8
private theorem endpoint_13_54_w10 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 10 2 263127966224431656 = some 263127966224431656 := by decide +kernel
private theorem endpoint_13_54_p12 : receiptWindow endpoint_13_54_flag endpoint_13_54_sources 0 12 261499503270909566 = some 263127966224431656 :=
  join_receipt_window endpoint_13_54_flag endpoint_13_54_sources 0 10 2 261499503270909566 263127966224431656 263127966224431656 endpoint_13_54_p10 endpoint_13_54_w10
def endpoint_13_54 : CertifiedEndpoint :=
  ⟨⟨13, 54, 3184⟩, 263127966224431656, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_13_54_flag endpoint_13_54_sources 12 261499503270909566 263127966224431656 rfl endpoint_13_54_base endpoint_13_54_p12) (by decide)⟩
private def endpoint_13_55_flag : Flag := ⟨13, 55, 3135⟩
private def endpoint_13_55_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_13_55_base : receiptBase endpoint_13_55_flag endpoint_13_55_sources = some 262679892073323717 := by decide +kernel
private theorem endpoint_13_55_w0 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 2 262679892073323717 = some 262679892073323717 := by decide +kernel
private theorem endpoint_13_55_w2 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 2 2 262679892073323717 = some 262679892073323717 := by decide +kernel
private theorem endpoint_13_55_p4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 4 262679892073323717 = some 262679892073323717 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 2 2 262679892073323717 262679892073323717 262679892073323717 endpoint_13_55_w0 endpoint_13_55_w2
private theorem endpoint_13_55_w4 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 4 2 262679892073323717 = some 262679892073323717 := by decide +kernel
private theorem endpoint_13_55_p6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 6 262679892073323717 = some 262679892073323717 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 4 2 262679892073323717 262679892073323717 262679892073323717 endpoint_13_55_p4 endpoint_13_55_w4
private theorem endpoint_13_55_w6 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 6 2 262679892073323717 = some 262679892073323717 := by decide +kernel
private theorem endpoint_13_55_p8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 8 262679892073323717 = some 262679892073323717 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 6 2 262679892073323717 262679892073323717 262679892073323717 endpoint_13_55_p6 endpoint_13_55_w6
private theorem endpoint_13_55_w8 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 8 2 262679892073323717 = some 262679892073323717 := by decide +kernel
private theorem endpoint_13_55_p10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 10 262679892073323717 = some 262679892073323717 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 8 2 262679892073323717 262679892073323717 262679892073323717 endpoint_13_55_p8 endpoint_13_55_w8
private theorem endpoint_13_55_w10 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 10 2 262679892073323717 = some 262679892073323717 := by decide +kernel
private theorem endpoint_13_55_p12 : receiptWindow endpoint_13_55_flag endpoint_13_55_sources 0 12 262679892073323717 = some 262679892073323717 :=
  join_receipt_window endpoint_13_55_flag endpoint_13_55_sources 0 10 2 262679892073323717 262679892073323717 262679892073323717 endpoint_13_55_p10 endpoint_13_55_w10
def endpoint_13_55 : CertifiedEndpoint :=
  ⟨⟨13, 55, 3135⟩, 262679892073323717, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_13_55_flag endpoint_13_55_sources 12 262679892073323717 262679892073323717 rfl endpoint_13_55_base endpoint_13_55_p12) (by decide)⟩
private def endpoint_13_56_flag : Flag := ⟨13, 56, 3084⟩
private def endpoint_13_56_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_13_56_base : receiptBase endpoint_13_56_flag endpoint_13_56_sources = some 262549062563624251 := by decide +kernel
private theorem endpoint_13_56_w0 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 2 262549062563624251 = some 263851924633589418 := by decide +kernel
private theorem endpoint_13_56_w2 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 2 2 263851924633589418 = some 263851924633589418 := by decide +kernel
private theorem endpoint_13_56_p4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 4 262549062563624251 = some 263851924633589418 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 2 2 262549062563624251 263851924633589418 263851924633589418 endpoint_13_56_w0 endpoint_13_56_w2
private theorem endpoint_13_56_w4 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 4 2 263851924633589418 = some 263851924633589418 := by decide +kernel
private theorem endpoint_13_56_p6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 6 262549062563624251 = some 263851924633589418 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 4 2 262549062563624251 263851924633589418 263851924633589418 endpoint_13_56_p4 endpoint_13_56_w4
private theorem endpoint_13_56_w6 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 6 2 263851924633589418 = some 263851924633589418 := by decide +kernel
private theorem endpoint_13_56_p8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 8 262549062563624251 = some 263851924633589418 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 6 2 262549062563624251 263851924633589418 263851924633589418 endpoint_13_56_p6 endpoint_13_56_w6
private theorem endpoint_13_56_w8 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 8 2 263851924633589418 = some 263851924633589418 := by decide +kernel
private theorem endpoint_13_56_p10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 10 262549062563624251 = some 263851924633589418 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 8 2 262549062563624251 263851924633589418 263851924633589418 endpoint_13_56_p8 endpoint_13_56_w8
private theorem endpoint_13_56_w10 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 10 2 263851924633589418 = some 263851924633589418 := by decide +kernel
private theorem endpoint_13_56_p12 : receiptWindow endpoint_13_56_flag endpoint_13_56_sources 0 12 262549062563624251 = some 263851924633589418 :=
  join_receipt_window endpoint_13_56_flag endpoint_13_56_sources 0 10 2 262549062563624251 263851924633589418 263851924633589418 endpoint_13_56_p10 endpoint_13_56_w10
def endpoint_13_56 : CertifiedEndpoint :=
  ⟨⟨13, 56, 3084⟩, 263851924633589418, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_13_56_flag endpoint_13_56_sources 12 262549062563624251 263851924633589418 rfl endpoint_13_56_base endpoint_13_56_p12) (by decide)⟩
private def endpoint_13_57_flag : Flag := ⟨13, 57, 3032⟩
private def endpoint_13_57_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_13_57_base : receiptBase endpoint_13_57_flag endpoint_13_57_sources = some 263273445423164961 := by decide +kernel
private theorem endpoint_13_57_w0 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 2 263273445423164961 = some 263273445423164961 := by decide +kernel
private theorem endpoint_13_57_w2 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 2 2 263273445423164961 = some 263273445423164961 := by decide +kernel
private theorem endpoint_13_57_p4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 4 263273445423164961 = some 263273445423164961 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 2 2 263273445423164961 263273445423164961 263273445423164961 endpoint_13_57_w0 endpoint_13_57_w2
private theorem endpoint_13_57_w4 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 4 2 263273445423164961 = some 263273445423164961 := by decide +kernel
private theorem endpoint_13_57_p6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 6 263273445423164961 = some 263273445423164961 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 4 2 263273445423164961 263273445423164961 263273445423164961 endpoint_13_57_p4 endpoint_13_57_w4
private theorem endpoint_13_57_w6 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 6 2 263273445423164961 = some 263273445423164961 := by decide +kernel
private theorem endpoint_13_57_p8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 8 263273445423164961 = some 263273445423164961 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 6 2 263273445423164961 263273445423164961 263273445423164961 endpoint_13_57_p6 endpoint_13_57_w6
private theorem endpoint_13_57_w8 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 8 2 263273445423164961 = some 263273445423164961 := by decide +kernel
private theorem endpoint_13_57_p10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 10 263273445423164961 = some 263273445423164961 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 8 2 263273445423164961 263273445423164961 263273445423164961 endpoint_13_57_p8 endpoint_13_57_w8
private theorem endpoint_13_57_w10 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 10 2 263273445423164961 = some 263273445423164961 := by decide +kernel
private theorem endpoint_13_57_p12 : receiptWindow endpoint_13_57_flag endpoint_13_57_sources 0 12 263273445423164961 = some 263273445423164961 :=
  join_receipt_window endpoint_13_57_flag endpoint_13_57_sources 0 10 2 263273445423164961 263273445423164961 263273445423164961 endpoint_13_57_p10 endpoint_13_57_w10
def endpoint_13_57 : CertifiedEndpoint :=
  ⟨⟨13, 57, 3032⟩, 263273445423164961, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_13_57_flag endpoint_13_57_sources 12 263273445423164961 263273445423164961 rfl endpoint_13_57_base endpoint_13_57_p12) (by decide)⟩
private def endpoint_13_58_flag : Flag := ⟨13, 58, 2977⟩
private def endpoint_13_58_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_58_base : receiptBase endpoint_13_58_flag endpoint_13_58_sources = some 264643458266762352 := by decide +kernel
private theorem endpoint_13_58_w0 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 2 264643458266762352 = some 264643458266762352 := by decide +kernel
private theorem endpoint_13_58_w2 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 2 2 264643458266762352 = some 264643458266762352 := by decide +kernel
private theorem endpoint_13_58_p4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 4 264643458266762352 = some 264643458266762352 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 2 2 264643458266762352 264643458266762352 264643458266762352 endpoint_13_58_w0 endpoint_13_58_w2
private theorem endpoint_13_58_w4 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 4 2 264643458266762352 = some 264643458266762352 := by decide +kernel
private theorem endpoint_13_58_p6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 6 264643458266762352 = some 264643458266762352 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 4 2 264643458266762352 264643458266762352 264643458266762352 endpoint_13_58_p4 endpoint_13_58_w4
private theorem endpoint_13_58_w6 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 6 2 264643458266762352 = some 264643458266762352 := by decide +kernel
private theorem endpoint_13_58_p8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 8 264643458266762352 = some 264643458266762352 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 6 2 264643458266762352 264643458266762352 264643458266762352 endpoint_13_58_p6 endpoint_13_58_w6
private theorem endpoint_13_58_w8 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 8 2 264643458266762352 = some 264643458266762352 := by decide +kernel
private theorem endpoint_13_58_p10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 10 264643458266762352 = some 264643458266762352 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 8 2 264643458266762352 264643458266762352 264643458266762352 endpoint_13_58_p8 endpoint_13_58_w8
private theorem endpoint_13_58_w10 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 10 2 264643458266762352 = some 264643458266762352 := by decide +kernel
private theorem endpoint_13_58_p12 : receiptWindow endpoint_13_58_flag endpoint_13_58_sources 0 12 264643458266762352 = some 264643458266762352 :=
  join_receipt_window endpoint_13_58_flag endpoint_13_58_sources 0 10 2 264643458266762352 264643458266762352 264643458266762352 endpoint_13_58_p10 endpoint_13_58_w10
def endpoint_13_58 : CertifiedEndpoint :=
  ⟨⟨13, 58, 2977⟩, 264643458266762352, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_58_flag endpoint_13_58_sources 12 264643458266762352 264643458266762352 rfl endpoint_13_58_base endpoint_13_58_p12) (by decide)⟩
private def endpoint_13_59_flag : Flag := ⟨13, 59, 2921⟩
private def endpoint_13_59_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_59_base : receiptBase endpoint_13_59_flag endpoint_13_59_sources = some 263662547291153507 := by decide +kernel
private theorem endpoint_13_59_w0 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 2 263662547291153507 = some 263662547291153507 := by decide +kernel
private theorem endpoint_13_59_w2 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 2 2 263662547291153507 = some 263662547291153507 := by decide +kernel
private theorem endpoint_13_59_p4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 4 263662547291153507 = some 263662547291153507 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 2 2 263662547291153507 263662547291153507 263662547291153507 endpoint_13_59_w0 endpoint_13_59_w2
private theorem endpoint_13_59_w4 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 4 2 263662547291153507 = some 263662547291153507 := by decide +kernel
private theorem endpoint_13_59_p6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 6 263662547291153507 = some 263662547291153507 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 4 2 263662547291153507 263662547291153507 263662547291153507 endpoint_13_59_p4 endpoint_13_59_w4
private theorem endpoint_13_59_w6 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 6 2 263662547291153507 = some 263662547291153507 := by decide +kernel
private theorem endpoint_13_59_p8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 8 263662547291153507 = some 263662547291153507 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 6 2 263662547291153507 263662547291153507 263662547291153507 endpoint_13_59_p6 endpoint_13_59_w6
private theorem endpoint_13_59_w8 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 8 2 263662547291153507 = some 263662547291153507 := by decide +kernel
private theorem endpoint_13_59_p10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 10 263662547291153507 = some 263662547291153507 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 8 2 263662547291153507 263662547291153507 263662547291153507 endpoint_13_59_p8 endpoint_13_59_w8
private theorem endpoint_13_59_w10 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 10 2 263662547291153507 = some 263662547291153507 := by decide +kernel
private theorem endpoint_13_59_p12 : receiptWindow endpoint_13_59_flag endpoint_13_59_sources 0 12 263662547291153507 = some 263662547291153507 :=
  join_receipt_window endpoint_13_59_flag endpoint_13_59_sources 0 10 2 263662547291153507 263662547291153507 263662547291153507 endpoint_13_59_p10 endpoint_13_59_w10
def endpoint_13_59 : CertifiedEndpoint :=
  ⟨⟨13, 59, 2921⟩, 263662547291153507, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_59_flag endpoint_13_59_sources 12 263662547291153507 263662547291153507 rfl endpoint_13_59_base endpoint_13_59_p12) (by decide)⟩
private def endpoint_13_60_flag : Flag := ⟨13, 60, 2862⟩
private def endpoint_13_60_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_60_base : receiptBase endpoint_13_60_flag endpoint_13_60_sources = some 262258636459527980 := by decide +kernel
private theorem endpoint_13_60_w0 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 2 262258636459527980 = some 262258636459527980 := by decide +kernel
private theorem endpoint_13_60_w2 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 2 2 262258636459527980 = some 262258636459527980 := by decide +kernel
private theorem endpoint_13_60_p4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 4 262258636459527980 = some 262258636459527980 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 2 2 262258636459527980 262258636459527980 262258636459527980 endpoint_13_60_w0 endpoint_13_60_w2
private theorem endpoint_13_60_w4 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 4 2 262258636459527980 = some 262258636459527980 := by decide +kernel
private theorem endpoint_13_60_p6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 6 262258636459527980 = some 262258636459527980 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 4 2 262258636459527980 262258636459527980 262258636459527980 endpoint_13_60_p4 endpoint_13_60_w4
private theorem endpoint_13_60_w6 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 6 2 262258636459527980 = some 262258636459527980 := by decide +kernel
private theorem endpoint_13_60_p8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 8 262258636459527980 = some 262258636459527980 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 6 2 262258636459527980 262258636459527980 262258636459527980 endpoint_13_60_p6 endpoint_13_60_w6
private theorem endpoint_13_60_w8 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 8 2 262258636459527980 = some 262258636459527980 := by decide +kernel
private theorem endpoint_13_60_p10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 10 262258636459527980 = some 262258636459527980 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 8 2 262258636459527980 262258636459527980 262258636459527980 endpoint_13_60_p8 endpoint_13_60_w8
private theorem endpoint_13_60_w10 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 10 2 262258636459527980 = some 262258636459527980 := by decide +kernel
private theorem endpoint_13_60_p12 : receiptWindow endpoint_13_60_flag endpoint_13_60_sources 0 12 262258636459527980 = some 262258636459527980 :=
  join_receipt_window endpoint_13_60_flag endpoint_13_60_sources 0 10 2 262258636459527980 262258636459527980 262258636459527980 endpoint_13_60_p10 endpoint_13_60_w10
def endpoint_13_60 : CertifiedEndpoint :=
  ⟨⟨13, 60, 2862⟩, 262258636459527980, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_60_flag endpoint_13_60_sources 12 262258636459527980 262258636459527980 rfl endpoint_13_60_base endpoint_13_60_p12) (by decide)⟩
private def endpoint_13_61_flag : Flag := ⟨13, 61, 2800⟩
private def endpoint_13_61_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_61_base : receiptBase endpoint_13_61_flag endpoint_13_61_sources = some 260419671336935831 := by decide +kernel
private theorem endpoint_13_61_w0 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 2 260419671336935831 = some 261324214843212026 := by decide +kernel
private theorem endpoint_13_61_w2 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 2 2 261324214843212026 = some 261324214843212026 := by decide +kernel
private theorem endpoint_13_61_p4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 4 260419671336935831 = some 261324214843212026 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 2 2 260419671336935831 261324214843212026 261324214843212026 endpoint_13_61_w0 endpoint_13_61_w2
private theorem endpoint_13_61_w4 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 4 2 261324214843212026 = some 261324214843212026 := by decide +kernel
private theorem endpoint_13_61_p6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 6 260419671336935831 = some 261324214843212026 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 4 2 260419671336935831 261324214843212026 261324214843212026 endpoint_13_61_p4 endpoint_13_61_w4
private theorem endpoint_13_61_w6 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 6 2 261324214843212026 = some 261324214843212026 := by decide +kernel
private theorem endpoint_13_61_p8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 8 260419671336935831 = some 261324214843212026 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 6 2 260419671336935831 261324214843212026 261324214843212026 endpoint_13_61_p6 endpoint_13_61_w6
private theorem endpoint_13_61_w8 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 8 2 261324214843212026 = some 261324214843212026 := by decide +kernel
private theorem endpoint_13_61_p10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 10 260419671336935831 = some 261324214843212026 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 8 2 260419671336935831 261324214843212026 261324214843212026 endpoint_13_61_p8 endpoint_13_61_w8
private theorem endpoint_13_61_w10 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 10 2 261324214843212026 = some 261324214843212026 := by decide +kernel
private theorem endpoint_13_61_p12 : receiptWindow endpoint_13_61_flag endpoint_13_61_sources 0 12 260419671336935831 = some 261324214843212026 :=
  join_receipt_window endpoint_13_61_flag endpoint_13_61_sources 0 10 2 260419671336935831 261324214843212026 261324214843212026 endpoint_13_61_p10 endpoint_13_61_w10
def endpoint_13_61 : CertifiedEndpoint :=
  ⟨⟨13, 61, 2800⟩, 261324214843212026, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_61_flag endpoint_13_61_sources 12 260419671336935831 261324214843212026 rfl endpoint_13_61_base endpoint_13_61_p12) (by decide)⟩
private def endpoint_13_62_flag : Flag := ⟨13, 62, 2736⟩
private def endpoint_13_62_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_62_base : receiptBase endpoint_13_62_flag endpoint_13_62_sources = some 258226826161186638 := by decide +kernel
private theorem endpoint_13_62_w0 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 2 258226826161186638 = some 262755314963642616 := by decide +kernel
private theorem endpoint_13_62_w2 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 2 2 262755314963642616 = some 262755314963642616 := by decide +kernel
private theorem endpoint_13_62_p4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 4 258226826161186638 = some 262755314963642616 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 2 2 258226826161186638 262755314963642616 262755314963642616 endpoint_13_62_w0 endpoint_13_62_w2
private theorem endpoint_13_62_w4 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 4 2 262755314963642616 = some 262755314963642616 := by decide +kernel
private theorem endpoint_13_62_p6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 6 258226826161186638 = some 262755314963642616 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 4 2 258226826161186638 262755314963642616 262755314963642616 endpoint_13_62_p4 endpoint_13_62_w4
private theorem endpoint_13_62_w6 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 6 2 262755314963642616 = some 262755314963642616 := by decide +kernel
private theorem endpoint_13_62_p8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 8 258226826161186638 = some 262755314963642616 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 6 2 258226826161186638 262755314963642616 262755314963642616 endpoint_13_62_p6 endpoint_13_62_w6
private theorem endpoint_13_62_w8 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 8 2 262755314963642616 = some 262755314963642616 := by decide +kernel
private theorem endpoint_13_62_p10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 10 258226826161186638 = some 262755314963642616 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 8 2 258226826161186638 262755314963642616 262755314963642616 endpoint_13_62_p8 endpoint_13_62_w8
private theorem endpoint_13_62_w10 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 10 2 262755314963642616 = some 262755314963642616 := by decide +kernel
private theorem endpoint_13_62_p12 : receiptWindow endpoint_13_62_flag endpoint_13_62_sources 0 12 258226826161186638 = some 262755314963642616 :=
  join_receipt_window endpoint_13_62_flag endpoint_13_62_sources 0 10 2 258226826161186638 262755314963642616 262755314963642616 endpoint_13_62_p10 endpoint_13_62_w10
def endpoint_13_62 : CertifiedEndpoint :=
  ⟨⟨13, 62, 2736⟩, 262755314963642616, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_62_flag endpoint_13_62_sources 12 258226826161186638 262755314963642616 rfl endpoint_13_62_base endpoint_13_62_p12) (by decide)⟩
private def endpoint_13_63_flag : Flag := ⟨13, 63, 2670⟩
private def endpoint_13_63_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_63_base : receiptBase endpoint_13_63_flag endpoint_13_63_sources = some 255672064642313774 := by decide +kernel
private theorem endpoint_13_63_w0 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 2 255672064642313774 = some 263951886720525606 := by decide +kernel
private theorem endpoint_13_63_w2 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 2 2 263951886720525606 = some 263951886720525606 := by decide +kernel
private theorem endpoint_13_63_p4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 4 255672064642313774 = some 263951886720525606 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 2 2 255672064642313774 263951886720525606 263951886720525606 endpoint_13_63_w0 endpoint_13_63_w2
private theorem endpoint_13_63_w4 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 4 2 263951886720525606 = some 263951886720525606 := by decide +kernel
private theorem endpoint_13_63_p6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 6 255672064642313774 = some 263951886720525606 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 4 2 255672064642313774 263951886720525606 263951886720525606 endpoint_13_63_p4 endpoint_13_63_w4
private theorem endpoint_13_63_w6 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 6 2 263951886720525606 = some 263951886720525606 := by decide +kernel
private theorem endpoint_13_63_p8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 8 255672064642313774 = some 263951886720525606 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 6 2 255672064642313774 263951886720525606 263951886720525606 endpoint_13_63_p6 endpoint_13_63_w6
private theorem endpoint_13_63_w8 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 8 2 263951886720525606 = some 263951886720525606 := by decide +kernel
private theorem endpoint_13_63_p10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 10 255672064642313774 = some 263951886720525606 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 8 2 255672064642313774 263951886720525606 263951886720525606 endpoint_13_63_p8 endpoint_13_63_w8
private theorem endpoint_13_63_w10 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 10 2 263951886720525606 = some 263951886720525606 := by decide +kernel
private theorem endpoint_13_63_p12 : receiptWindow endpoint_13_63_flag endpoint_13_63_sources 0 12 255672064642313774 = some 263951886720525606 :=
  join_receipt_window endpoint_13_63_flag endpoint_13_63_sources 0 10 2 255672064642313774 263951886720525606 263951886720525606 endpoint_13_63_p10 endpoint_13_63_w10
def endpoint_13_63 : CertifiedEndpoint :=
  ⟨⟨13, 63, 2670⟩, 263951886720525606, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_63_flag endpoint_13_63_sources 12 255672064642313774 263951886720525606 rfl endpoint_13_63_base endpoint_13_63_p12) (by decide)⟩
private def endpoint_13_64_flag : Flag := ⟨13, 64, 2601⟩
private def endpoint_13_64_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_13_64_base : receiptBase endpoint_13_64_flag endpoint_13_64_sources = some 252651443054268894 := by decide +kernel
private theorem endpoint_13_64_w0 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 2 252651443054268894 = some 264853481197478194 := by decide +kernel
private theorem endpoint_13_64_w2 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 2 2 264853481197478194 = some 264853481197478194 := by decide +kernel
private theorem endpoint_13_64_p4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 4 252651443054268894 = some 264853481197478194 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 2 2 252651443054268894 264853481197478194 264853481197478194 endpoint_13_64_w0 endpoint_13_64_w2
private theorem endpoint_13_64_w4 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 4 2 264853481197478194 = some 264853481197478194 := by decide +kernel
private theorem endpoint_13_64_p6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 6 252651443054268894 = some 264853481197478194 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 4 2 252651443054268894 264853481197478194 264853481197478194 endpoint_13_64_p4 endpoint_13_64_w4
private theorem endpoint_13_64_w6 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 6 2 264853481197478194 = some 264853481197478194 := by decide +kernel
private theorem endpoint_13_64_p8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 8 252651443054268894 = some 264853481197478194 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 6 2 252651443054268894 264853481197478194 264853481197478194 endpoint_13_64_p6 endpoint_13_64_w6
private theorem endpoint_13_64_w8 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 8 2 264853481197478194 = some 264853481197478194 := by decide +kernel
private theorem endpoint_13_64_p10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 10 252651443054268894 = some 264853481197478194 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 8 2 252651443054268894 264853481197478194 264853481197478194 endpoint_13_64_p8 endpoint_13_64_w8
private theorem endpoint_13_64_w10 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 10 2 264853481197478194 = some 264853481197478194 := by decide +kernel
private theorem endpoint_13_64_p12 : receiptWindow endpoint_13_64_flag endpoint_13_64_sources 0 12 252651443054268894 = some 264853481197478194 :=
  join_receipt_window endpoint_13_64_flag endpoint_13_64_sources 0 10 2 252651443054268894 264853481197478194 264853481197478194 endpoint_13_64_p10 endpoint_13_64_w10
def endpoint_13_64 : CertifiedEndpoint :=
  ⟨⟨13, 64, 2601⟩, 264853481197478194, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_13_64_flag endpoint_13_64_sources 12 252651443054268894 264853481197478194 rfl endpoint_13_64_base endpoint_13_64_p12) (by decide)⟩
private def endpoint_13_65_flag : Flag := ⟨13, 65, 2529⟩
private def endpoint_13_65_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_65_base : receiptBase endpoint_13_65_flag endpoint_13_65_sources = some 254992977927225704 := by decide +kernel
private theorem endpoint_13_65_w0 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 2 254992977927225704 = some 254992977927225704 := by decide +kernel
private theorem endpoint_13_65_w2 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 2 2 254992977927225704 = some 254992977927225704 := by decide +kernel
private theorem endpoint_13_65_p4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 4 254992977927225704 = some 254992977927225704 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 2 2 254992977927225704 254992977927225704 254992977927225704 endpoint_13_65_w0 endpoint_13_65_w2
private theorem endpoint_13_65_w4 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 4 2 254992977927225704 = some 254992977927225704 := by decide +kernel
private theorem endpoint_13_65_p6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 6 254992977927225704 = some 254992977927225704 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 4 2 254992977927225704 254992977927225704 254992977927225704 endpoint_13_65_p4 endpoint_13_65_w4
private theorem endpoint_13_65_w6 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 6 2 254992977927225704 = some 254992977927225704 := by decide +kernel
private theorem endpoint_13_65_p8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 8 254992977927225704 = some 254992977927225704 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 6 2 254992977927225704 254992977927225704 254992977927225704 endpoint_13_65_p6 endpoint_13_65_w6
private theorem endpoint_13_65_w8 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 8 2 254992977927225704 = some 254992977927225704 := by decide +kernel
private theorem endpoint_13_65_p10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 10 254992977927225704 = some 254992977927225704 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 8 2 254992977927225704 254992977927225704 254992977927225704 endpoint_13_65_p8 endpoint_13_65_w8
private theorem endpoint_13_65_w10 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 10 2 254992977927225704 = some 254992977927225704 := by decide +kernel
private theorem endpoint_13_65_p12 : receiptWindow endpoint_13_65_flag endpoint_13_65_sources 0 12 254992977927225704 = some 254992977927225704 :=
  join_receipt_window endpoint_13_65_flag endpoint_13_65_sources 0 10 2 254992977927225704 254992977927225704 254992977927225704 endpoint_13_65_p10 endpoint_13_65_w10
def endpoint_13_65 : CertifiedEndpoint :=
  ⟨⟨13, 65, 2529⟩, 254992977927225704, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_65_flag endpoint_13_65_sources 12 254992977927225704 254992977927225704 rfl endpoint_13_65_base endpoint_13_65_p12) (by decide)⟩
private def endpoint_13_66_flag : Flag := ⟨13, 66, 2455⟩
private def endpoint_13_66_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_66_base : receiptBase endpoint_13_66_flag endpoint_13_66_sources = some 251058423548727378 := by decide +kernel
private theorem endpoint_13_66_w0 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 2 251058423548727378 = some 253087085542645230 := by decide +kernel
private theorem endpoint_13_66_w2 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 2 2 253087085542645230 = some 253087085542645230 := by decide +kernel
private theorem endpoint_13_66_p4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 4 251058423548727378 = some 253087085542645230 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 2 2 251058423548727378 253087085542645230 253087085542645230 endpoint_13_66_w0 endpoint_13_66_w2
private theorem endpoint_13_66_w4 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 4 2 253087085542645230 = some 253087085542645230 := by decide +kernel
private theorem endpoint_13_66_p6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 6 251058423548727378 = some 253087085542645230 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 4 2 251058423548727378 253087085542645230 253087085542645230 endpoint_13_66_p4 endpoint_13_66_w4
private theorem endpoint_13_66_w6 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 6 2 253087085542645230 = some 253087085542645230 := by decide +kernel
private theorem endpoint_13_66_p8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 8 251058423548727378 = some 253087085542645230 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 6 2 251058423548727378 253087085542645230 253087085542645230 endpoint_13_66_p6 endpoint_13_66_w6
private theorem endpoint_13_66_w8 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 8 2 253087085542645230 = some 253087085542645230 := by decide +kernel
private theorem endpoint_13_66_p10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 10 251058423548727378 = some 253087085542645230 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 8 2 251058423548727378 253087085542645230 253087085542645230 endpoint_13_66_p8 endpoint_13_66_w8
private theorem endpoint_13_66_w10 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 10 2 253087085542645230 = some 253087085542645230 := by decide +kernel
private theorem endpoint_13_66_p12 : receiptWindow endpoint_13_66_flag endpoint_13_66_sources 0 12 251058423548727378 = some 253087085542645230 :=
  join_receipt_window endpoint_13_66_flag endpoint_13_66_sources 0 10 2 251058423548727378 253087085542645230 253087085542645230 endpoint_13_66_p10 endpoint_13_66_w10
def endpoint_13_66 : CertifiedEndpoint :=
  ⟨⟨13, 66, 2455⟩, 253087085542645230, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_66_flag endpoint_13_66_sources 12 251058423548727378 253087085542645230 rfl endpoint_13_66_base endpoint_13_66_p12) (by decide)⟩
private def endpoint_13_67_flag : Flag := ⟨13, 67, 2377⟩
private def endpoint_13_67_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_67_base : receiptBase endpoint_13_67_flag endpoint_13_67_sources = some 246519013966694313 := by decide +kernel
private theorem endpoint_13_67_w0 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 2 246519013966694313 = some 252836139272777825 := by decide +kernel
private theorem endpoint_13_67_w2 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 2 2 252836139272777825 = some 252836139272777825 := by decide +kernel
private theorem endpoint_13_67_p4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 4 246519013966694313 = some 252836139272777825 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 2 2 246519013966694313 252836139272777825 252836139272777825 endpoint_13_67_w0 endpoint_13_67_w2
private theorem endpoint_13_67_w4 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 4 2 252836139272777825 = some 252836139272777825 := by decide +kernel
private theorem endpoint_13_67_p6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 6 246519013966694313 = some 252836139272777825 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 4 2 246519013966694313 252836139272777825 252836139272777825 endpoint_13_67_p4 endpoint_13_67_w4
private theorem endpoint_13_67_w6 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 6 2 252836139272777825 = some 252836139272777825 := by decide +kernel
private theorem endpoint_13_67_p8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 8 246519013966694313 = some 252836139272777825 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 6 2 246519013966694313 252836139272777825 252836139272777825 endpoint_13_67_p6 endpoint_13_67_w6
private theorem endpoint_13_67_w8 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 8 2 252836139272777825 = some 252836139272777825 := by decide +kernel
private theorem endpoint_13_67_p10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 10 246519013966694313 = some 252836139272777825 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 8 2 246519013966694313 252836139272777825 252836139272777825 endpoint_13_67_p8 endpoint_13_67_w8
private theorem endpoint_13_67_w10 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 10 2 252836139272777825 = some 252836139272777825 := by decide +kernel
private theorem endpoint_13_67_p12 : receiptWindow endpoint_13_67_flag endpoint_13_67_sources 0 12 246519013966694313 = some 252836139272777825 :=
  join_receipt_window endpoint_13_67_flag endpoint_13_67_sources 0 10 2 246519013966694313 252836139272777825 252836139272777825 endpoint_13_67_p10 endpoint_13_67_w10
def endpoint_13_67 : CertifiedEndpoint :=
  ⟨⟨13, 67, 2377⟩, 252836139272777825, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_67_flag endpoint_13_67_sources 12 246519013966694313 252836139272777825 rfl endpoint_13_67_base endpoint_13_67_p12) (by decide)⟩
private def endpoint_13_68_flag : Flag := ⟨13, 68, 2297⟩
private def endpoint_13_68_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_13_68_base : receiptBase endpoint_13_68_flag endpoint_13_68_sources = some 241563814058449969 := by decide +kernel
private theorem endpoint_13_68_w0 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 2 241563814058449969 = some 252313778526331186 := by decide +kernel
private theorem endpoint_13_68_w2 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 2 2 252313778526331186 = some 252313778526331186 := by decide +kernel
private theorem endpoint_13_68_p4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 4 241563814058449969 = some 252313778526331186 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 2 2 241563814058449969 252313778526331186 252313778526331186 endpoint_13_68_w0 endpoint_13_68_w2
private theorem endpoint_13_68_w4 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 4 2 252313778526331186 = some 252313778526331186 := by decide +kernel
private theorem endpoint_13_68_p6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 6 241563814058449969 = some 252313778526331186 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 4 2 241563814058449969 252313778526331186 252313778526331186 endpoint_13_68_p4 endpoint_13_68_w4
private theorem endpoint_13_68_w6 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 6 2 252313778526331186 = some 252313778526331186 := by decide +kernel
private theorem endpoint_13_68_p8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 8 241563814058449969 = some 252313778526331186 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 6 2 241563814058449969 252313778526331186 252313778526331186 endpoint_13_68_p6 endpoint_13_68_w6
private theorem endpoint_13_68_w8 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 8 2 252313778526331186 = some 252313778526331186 := by decide +kernel
private theorem endpoint_13_68_p10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 10 241563814058449969 = some 252313778526331186 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 8 2 241563814058449969 252313778526331186 252313778526331186 endpoint_13_68_p8 endpoint_13_68_w8
private theorem endpoint_13_68_w10 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 10 2 252313778526331186 = some 252313778526331186 := by decide +kernel
private theorem endpoint_13_68_p12 : receiptWindow endpoint_13_68_flag endpoint_13_68_sources 0 12 241563814058449969 = some 252313778526331186 :=
  join_receipt_window endpoint_13_68_flag endpoint_13_68_sources 0 10 2 241563814058449969 252313778526331186 252313778526331186 endpoint_13_68_p10 endpoint_13_68_w10
def endpoint_13_68 : CertifiedEndpoint :=
  ⟨⟨13, 68, 2297⟩, 252313778526331186, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_13_68_flag endpoint_13_68_sources 12 241563814058449969 252313778526331186 rfl endpoint_13_68_base endpoint_13_68_p12) (by decide)⟩
private def endpoint_13_69_flag : Flag := ⟨13, 69, 2214⟩
private def endpoint_13_69_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_13_69_base : receiptBase endpoint_13_69_flag endpoint_13_69_sources = some 237396289118378806 := by decide +kernel
private theorem endpoint_13_69_w0 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 2 237396289118378806 = some 238594560096500776 := by decide +kernel
private theorem endpoint_13_69_w2 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 2 2 238594560096500776 = some 238594560096500776 := by decide +kernel
private theorem endpoint_13_69_p4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 4 237396289118378806 = some 238594560096500776 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 2 2 237396289118378806 238594560096500776 238594560096500776 endpoint_13_69_w0 endpoint_13_69_w2
private theorem endpoint_13_69_w4 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 4 2 238594560096500776 = some 238594560096500776 := by decide +kernel
private theorem endpoint_13_69_p6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 6 237396289118378806 = some 238594560096500776 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 4 2 237396289118378806 238594560096500776 238594560096500776 endpoint_13_69_p4 endpoint_13_69_w4
private theorem endpoint_13_69_w6 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 6 2 238594560096500776 = some 238594560096500776 := by decide +kernel
private theorem endpoint_13_69_p8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 8 237396289118378806 = some 238594560096500776 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 6 2 237396289118378806 238594560096500776 238594560096500776 endpoint_13_69_p6 endpoint_13_69_w6
private theorem endpoint_13_69_w8 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 8 2 238594560096500776 = some 238594560096500776 := by decide +kernel
private theorem endpoint_13_69_p10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 10 237396289118378806 = some 238594560096500776 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 8 2 237396289118378806 238594560096500776 238594560096500776 endpoint_13_69_p8 endpoint_13_69_w8
private theorem endpoint_13_69_w10 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 10 2 238594560096500776 = some 238594560096500776 := by decide +kernel
private theorem endpoint_13_69_p12 : receiptWindow endpoint_13_69_flag endpoint_13_69_sources 0 12 237396289118378806 = some 238594560096500776 :=
  join_receipt_window endpoint_13_69_flag endpoint_13_69_sources 0 10 2 237396289118378806 238594560096500776 238594560096500776 endpoint_13_69_p10 endpoint_13_69_w10
def endpoint_13_69 : CertifiedEndpoint :=
  ⟨⟨13, 69, 2214⟩, 238594560096500776, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_13_69_flag endpoint_13_69_sources 12 237396289118378806 238594560096500776 rfl endpoint_13_69_base endpoint_13_69_p12) (by decide)⟩
private def endpoint_13_70_flag : Flag := ⟨13, 70, 2128⟩
private def endpoint_13_70_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_13_70_base : receiptBase endpoint_13_70_flag endpoint_13_70_sources = some 231353561506551637 := by decide +kernel
private theorem endpoint_13_70_w0 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 2 231353561506551637 = some 237181873039400944 := by decide +kernel
private theorem endpoint_13_70_w2 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 2 2 237181873039400944 = some 237181873039400944 := by decide +kernel
private theorem endpoint_13_70_p4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 4 231353561506551637 = some 237181873039400944 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 2 2 231353561506551637 237181873039400944 237181873039400944 endpoint_13_70_w0 endpoint_13_70_w2
private theorem endpoint_13_70_w4 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 4 2 237181873039400944 = some 237181873039400944 := by decide +kernel
private theorem endpoint_13_70_p6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 6 231353561506551637 = some 237181873039400944 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 4 2 231353561506551637 237181873039400944 237181873039400944 endpoint_13_70_p4 endpoint_13_70_w4
private theorem endpoint_13_70_w6 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 6 2 237181873039400944 = some 237181873039400944 := by decide +kernel
private theorem endpoint_13_70_p8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 8 231353561506551637 = some 237181873039400944 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 6 2 231353561506551637 237181873039400944 237181873039400944 endpoint_13_70_p6 endpoint_13_70_w6
private theorem endpoint_13_70_w8 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 8 2 237181873039400944 = some 237181873039400944 := by decide +kernel
private theorem endpoint_13_70_p10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 10 231353561506551637 = some 237181873039400944 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 8 2 231353561506551637 237181873039400944 237181873039400944 endpoint_13_70_p8 endpoint_13_70_w8
private theorem endpoint_13_70_w10 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 10 2 237181873039400944 = some 237181873039400944 := by decide +kernel
private theorem endpoint_13_70_p12 : receiptWindow endpoint_13_70_flag endpoint_13_70_sources 0 12 231353561506551637 = some 237181873039400944 :=
  join_receipt_window endpoint_13_70_flag endpoint_13_70_sources 0 10 2 231353561506551637 237181873039400944 237181873039400944 endpoint_13_70_p10 endpoint_13_70_w10
def endpoint_13_70 : CertifiedEndpoint :=
  ⟨⟨13, 70, 2128⟩, 237181873039400944, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_13_70_flag endpoint_13_70_sources 12 231353561506551637 237181873039400944 rfl endpoint_13_70_base endpoint_13_70_p12) (by decide)⟩
private def endpoint_13_71_flag : Flag := ⟨13, 71, 2039⟩
private def endpoint_13_71_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_71_base : receiptBase endpoint_13_71_flag endpoint_13_71_sources = some 226139189632363947 := by decide +kernel
private theorem endpoint_13_71_w0 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 2 226139189632363947 = some 228904428098149630 := by decide +kernel
private theorem endpoint_13_71_w2 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 2 2 228904428098149630 = some 228904428098149630 := by decide +kernel
private theorem endpoint_13_71_p4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 4 226139189632363947 = some 228904428098149630 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 2 2 226139189632363947 228904428098149630 228904428098149630 endpoint_13_71_w0 endpoint_13_71_w2
private theorem endpoint_13_71_w4 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 4 2 228904428098149630 = some 228904428098149630 := by decide +kernel
private theorem endpoint_13_71_p6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 6 226139189632363947 = some 228904428098149630 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 4 2 226139189632363947 228904428098149630 228904428098149630 endpoint_13_71_p4 endpoint_13_71_w4
private theorem endpoint_13_71_w6 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 6 2 228904428098149630 = some 228904428098149630 := by decide +kernel
private theorem endpoint_13_71_p8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 8 226139189632363947 = some 228904428098149630 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 6 2 226139189632363947 228904428098149630 228904428098149630 endpoint_13_71_p6 endpoint_13_71_w6
private theorem endpoint_13_71_w8 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 8 2 228904428098149630 = some 228904428098149630 := by decide +kernel
private theorem endpoint_13_71_p10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 10 226139189632363947 = some 228904428098149630 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 8 2 226139189632363947 228904428098149630 228904428098149630 endpoint_13_71_p8 endpoint_13_71_w8
private theorem endpoint_13_71_w10 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 10 2 228904428098149630 = some 228904428098149630 := by decide +kernel
private theorem endpoint_13_71_p12 : receiptWindow endpoint_13_71_flag endpoint_13_71_sources 0 12 226139189632363947 = some 228904428098149630 :=
  join_receipt_window endpoint_13_71_flag endpoint_13_71_sources 0 10 2 226139189632363947 228904428098149630 228904428098149630 endpoint_13_71_p10 endpoint_13_71_w10
def endpoint_13_71 : CertifiedEndpoint :=
  ⟨⟨13, 71, 2039⟩, 228904428098149630, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_71_flag endpoint_13_71_sources 12 226139189632363947 228904428098149630 rfl endpoint_13_71_base endpoint_13_71_p12) (by decide)⟩
private def endpoint_13_72_flag : Flag := ⟨13, 72, 1948⟩
private def endpoint_13_72_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_13_72_base : receiptBase endpoint_13_72_flag endpoint_13_72_sources = some 218890641488901003 := by decide +kernel
private theorem endpoint_13_72_w0 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 2 218890641488901003 = some 226734940021096648 := by decide +kernel
private theorem endpoint_13_72_w2 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 2 2 226734940021096648 = some 226734940021096648 := by decide +kernel
private theorem endpoint_13_72_p4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 4 218890641488901003 = some 226734940021096648 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 2 2 218890641488901003 226734940021096648 226734940021096648 endpoint_13_72_w0 endpoint_13_72_w2
private theorem endpoint_13_72_w4 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 4 2 226734940021096648 = some 226734940021096648 := by decide +kernel
private theorem endpoint_13_72_p6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 6 218890641488901003 = some 226734940021096648 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 4 2 218890641488901003 226734940021096648 226734940021096648 endpoint_13_72_p4 endpoint_13_72_w4
private theorem endpoint_13_72_w6 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 6 2 226734940021096648 = some 226734940021096648 := by decide +kernel
private theorem endpoint_13_72_p8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 8 218890641488901003 = some 226734940021096648 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 6 2 218890641488901003 226734940021096648 226734940021096648 endpoint_13_72_p6 endpoint_13_72_w6
private theorem endpoint_13_72_w8 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 8 2 226734940021096648 = some 226734940021096648 := by decide +kernel
private theorem endpoint_13_72_p10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 10 218890641488901003 = some 226734940021096648 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 8 2 218890641488901003 226734940021096648 226734940021096648 endpoint_13_72_p8 endpoint_13_72_w8
private theorem endpoint_13_72_w10 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 10 2 226734940021096648 = some 226734940021096648 := by decide +kernel
private theorem endpoint_13_72_p12 : receiptWindow endpoint_13_72_flag endpoint_13_72_sources 0 12 218890641488901003 = some 226734940021096648 :=
  join_receipt_window endpoint_13_72_flag endpoint_13_72_sources 0 10 2 218890641488901003 226734940021096648 226734940021096648 endpoint_13_72_p10 endpoint_13_72_w10
def endpoint_13_72 : CertifiedEndpoint :=
  ⟨⟨13, 72, 1948⟩, 226734940021096648, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_13_72_flag endpoint_13_72_sources 12 218890641488901003 226734940021096648 rfl endpoint_13_72_base endpoint_13_72_p12) (by decide)⟩
private def endpoint_13_73_flag : Flag := ⟨13, 73, 1853⟩
private def endpoint_13_73_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_73_base : receiptBase endpoint_13_73_flag endpoint_13_73_sources = some 212485658576402826 := by decide +kernel
private theorem endpoint_13_73_w0 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 2 212485658576402826 = some 212485658576402826 := by decide +kernel
private theorem endpoint_13_73_w2 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 2 2 212485658576402826 = some 212485658576402826 := by decide +kernel
private theorem endpoint_13_73_p4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 4 212485658576402826 = some 212485658576402826 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 2 2 212485658576402826 212485658576402826 212485658576402826 endpoint_13_73_w0 endpoint_13_73_w2
private theorem endpoint_13_73_w4 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 4 2 212485658576402826 = some 212485658576402826 := by decide +kernel
private theorem endpoint_13_73_p6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 6 212485658576402826 = some 212485658576402826 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 4 2 212485658576402826 212485658576402826 212485658576402826 endpoint_13_73_p4 endpoint_13_73_w4
private theorem endpoint_13_73_w6 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 6 2 212485658576402826 = some 212485658576402826 := by decide +kernel
private theorem endpoint_13_73_p8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 8 212485658576402826 = some 212485658576402826 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 6 2 212485658576402826 212485658576402826 212485658576402826 endpoint_13_73_p6 endpoint_13_73_w6
private theorem endpoint_13_73_w8 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 8 2 212485658576402826 = some 212485658576402826 := by decide +kernel
private theorem endpoint_13_73_p10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 10 212485658576402826 = some 212485658576402826 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 8 2 212485658576402826 212485658576402826 212485658576402826 endpoint_13_73_p8 endpoint_13_73_w8
private theorem endpoint_13_73_w10 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 10 2 212485658576402826 = some 212485658576402826 := by decide +kernel
private theorem endpoint_13_73_p12 : receiptWindow endpoint_13_73_flag endpoint_13_73_sources 0 12 212485658576402826 = some 212485658576402826 :=
  join_receipt_window endpoint_13_73_flag endpoint_13_73_sources 0 10 2 212485658576402826 212485658576402826 212485658576402826 endpoint_13_73_p10 endpoint_13_73_w10
def endpoint_13_73 : CertifiedEndpoint :=
  ⟨⟨13, 73, 1853⟩, 212485658576402826, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_73_flag endpoint_13_73_sources 12 212485658576402826 212485658576402826 rfl endpoint_13_73_base endpoint_13_73_p12) (by decide)⟩
private def endpoint_13_74_flag : Flag := ⟨13, 74, 1755⟩
private def endpoint_13_74_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_74_base : receiptBase endpoint_13_74_flag endpoint_13_74_sources = some 203827875678821712 := by decide +kernel
private theorem endpoint_13_74_w0 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 2 203827875678821712 = some 205644527900569050 := by decide +kernel
private theorem endpoint_13_74_w2 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 2 2 205644527900569050 = some 205644527900569050 := by decide +kernel
private theorem endpoint_13_74_p4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 4 203827875678821712 = some 205644527900569050 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 2 2 203827875678821712 205644527900569050 205644527900569050 endpoint_13_74_w0 endpoint_13_74_w2
private theorem endpoint_13_74_w4 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 4 2 205644527900569050 = some 205644527900569050 := by decide +kernel
private theorem endpoint_13_74_p6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 6 203827875678821712 = some 205644527900569050 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 4 2 203827875678821712 205644527900569050 205644527900569050 endpoint_13_74_p4 endpoint_13_74_w4
private theorem endpoint_13_74_w6 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 6 2 205644527900569050 = some 205644527900569050 := by decide +kernel
private theorem endpoint_13_74_p8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 8 203827875678821712 = some 205644527900569050 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 6 2 203827875678821712 205644527900569050 205644527900569050 endpoint_13_74_p6 endpoint_13_74_w6
private theorem endpoint_13_74_w8 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 8 2 205644527900569050 = some 205644527900569050 := by decide +kernel
private theorem endpoint_13_74_p10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 10 203827875678821712 = some 205644527900569050 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 8 2 203827875678821712 205644527900569050 205644527900569050 endpoint_13_74_p8 endpoint_13_74_w8
private theorem endpoint_13_74_w10 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 10 2 205644527900569050 = some 205644527900569050 := by decide +kernel
private theorem endpoint_13_74_p12 : receiptWindow endpoint_13_74_flag endpoint_13_74_sources 0 12 203827875678821712 = some 205644527900569050 :=
  join_receipt_window endpoint_13_74_flag endpoint_13_74_sources 0 10 2 203827875678821712 205644527900569050 205644527900569050 endpoint_13_74_p10 endpoint_13_74_w10
def endpoint_13_74 : CertifiedEndpoint :=
  ⟨⟨13, 74, 1755⟩, 205644527900569050, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_74_flag endpoint_13_74_sources 12 203827875678821712 205644527900569050 rfl endpoint_13_74_base endpoint_13_74_p12) (by decide)⟩
private def endpoint_13_75_flag : Flag := ⟨13, 75, 1654⟩
private def endpoint_13_75_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_13_75_base : receiptBase endpoint_13_75_flag endpoint_13_75_sources = some 194548535380267376 := by decide +kernel
private theorem endpoint_13_75_w0 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 2 194548535380267376 = some 202040252441067749 := by decide +kernel
private theorem endpoint_13_75_w2 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 2 2 202040252441067749 = some 202040252441067749 := by decide +kernel
private theorem endpoint_13_75_p4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 4 194548535380267376 = some 202040252441067749 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 2 2 194548535380267376 202040252441067749 202040252441067749 endpoint_13_75_w0 endpoint_13_75_w2
private theorem endpoint_13_75_w4 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 4 2 202040252441067749 = some 202040252441067749 := by decide +kernel
private theorem endpoint_13_75_p6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 6 194548535380267376 = some 202040252441067749 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 4 2 194548535380267376 202040252441067749 202040252441067749 endpoint_13_75_p4 endpoint_13_75_w4
private theorem endpoint_13_75_w6 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 6 2 202040252441067749 = some 202040252441067749 := by decide +kernel
private theorem endpoint_13_75_p8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 8 194548535380267376 = some 202040252441067749 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 6 2 194548535380267376 202040252441067749 202040252441067749 endpoint_13_75_p6 endpoint_13_75_w6
private theorem endpoint_13_75_w8 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 8 2 202040252441067749 = some 202040252441067749 := by decide +kernel
private theorem endpoint_13_75_p10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 10 194548535380267376 = some 202040252441067749 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 8 2 194548535380267376 202040252441067749 202040252441067749 endpoint_13_75_p8 endpoint_13_75_w8
private theorem endpoint_13_75_w10 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 10 2 202040252441067749 = some 202040252441067749 := by decide +kernel
private theorem endpoint_13_75_p12 : receiptWindow endpoint_13_75_flag endpoint_13_75_sources 0 12 194548535380267376 = some 202040252441067749 :=
  join_receipt_window endpoint_13_75_flag endpoint_13_75_sources 0 10 2 194548535380267376 202040252441067749 202040252441067749 endpoint_13_75_p10 endpoint_13_75_w10
def endpoint_13_75 : CertifiedEndpoint :=
  ⟨⟨13, 75, 1654⟩, 202040252441067749, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_13_75_flag endpoint_13_75_sources 12 194548535380267376 202040252441067749 rfl endpoint_13_75_base endpoint_13_75_p12) (by decide)⟩
private def endpoint_13_76_flag : Flag := ⟨13, 76, 1551⟩
private def endpoint_13_76_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_76_base : receiptBase endpoint_13_76_flag endpoint_13_76_sources = some 187618912162819337 := by decide +kernel
private theorem endpoint_13_76_w0 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 2 187618912162819337 = some 187618912162819337 := by decide +kernel
private theorem endpoint_13_76_w2 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 2 2 187618912162819337 = some 187618912162819337 := by decide +kernel
private theorem endpoint_13_76_p4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 4 187618912162819337 = some 187618912162819337 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 2 2 187618912162819337 187618912162819337 187618912162819337 endpoint_13_76_w0 endpoint_13_76_w2
private theorem endpoint_13_76_w4 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 4 2 187618912162819337 = some 187618912162819337 := by decide +kernel
private theorem endpoint_13_76_p6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 6 187618912162819337 = some 187618912162819337 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 4 2 187618912162819337 187618912162819337 187618912162819337 endpoint_13_76_p4 endpoint_13_76_w4
private theorem endpoint_13_76_w6 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 6 2 187618912162819337 = some 187618912162819337 := by decide +kernel
private theorem endpoint_13_76_p8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 8 187618912162819337 = some 187618912162819337 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 6 2 187618912162819337 187618912162819337 187618912162819337 endpoint_13_76_p6 endpoint_13_76_w6
private theorem endpoint_13_76_w8 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 8 2 187618912162819337 = some 187618912162819337 := by decide +kernel
private theorem endpoint_13_76_p10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 10 187618912162819337 = some 187618912162819337 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 8 2 187618912162819337 187618912162819337 187618912162819337 endpoint_13_76_p8 endpoint_13_76_w8
private theorem endpoint_13_76_w10 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 10 2 187618912162819337 = some 187618912162819337 := by decide +kernel
private theorem endpoint_13_76_p12 : receiptWindow endpoint_13_76_flag endpoint_13_76_sources 0 12 187618912162819337 = some 187618912162819337 :=
  join_receipt_window endpoint_13_76_flag endpoint_13_76_sources 0 10 2 187618912162819337 187618912162819337 187618912162819337 endpoint_13_76_p10 endpoint_13_76_w10
def endpoint_13_76 : CertifiedEndpoint :=
  ⟨⟨13, 76, 1551⟩, 187618912162819337, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_76_flag endpoint_13_76_sources 12 187618912162819337 187618912162819337 rfl endpoint_13_76_base endpoint_13_76_p12) (by decide)⟩
private def endpoint_13_77_flag : Flag := ⟨13, 77, 1444⟩
private def endpoint_13_77_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_13_77_base : receiptBase endpoint_13_77_flag endpoint_13_77_sources = some 176823196340812308 := by decide +kernel
private theorem endpoint_13_77_w0 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 2 176823196340812308 = some 177495199260755075 := by decide +kernel
private theorem endpoint_13_77_w2 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 2 2 177495199260755075 = some 177495199260755075 := by decide +kernel
private theorem endpoint_13_77_p4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 4 176823196340812308 = some 177495199260755075 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 2 2 176823196340812308 177495199260755075 177495199260755075 endpoint_13_77_w0 endpoint_13_77_w2
private theorem endpoint_13_77_w4 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 4 2 177495199260755075 = some 177495199260755075 := by decide +kernel
private theorem endpoint_13_77_p6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 6 176823196340812308 = some 177495199260755075 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 4 2 176823196340812308 177495199260755075 177495199260755075 endpoint_13_77_p4 endpoint_13_77_w4
private theorem endpoint_13_77_w6 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 6 2 177495199260755075 = some 177495199260755075 := by decide +kernel
private theorem endpoint_13_77_p8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 8 176823196340812308 = some 177495199260755075 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 6 2 176823196340812308 177495199260755075 177495199260755075 endpoint_13_77_p6 endpoint_13_77_w6
private theorem endpoint_13_77_w8 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 8 2 177495199260755075 = some 177495199260755075 := by decide +kernel
private theorem endpoint_13_77_p10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 10 176823196340812308 = some 177495199260755075 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 8 2 176823196340812308 177495199260755075 177495199260755075 endpoint_13_77_p8 endpoint_13_77_w8
private theorem endpoint_13_77_w10 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 10 2 177495199260755075 = some 177495199260755075 := by decide +kernel
private theorem endpoint_13_77_p12 : receiptWindow endpoint_13_77_flag endpoint_13_77_sources 0 12 176823196340812308 = some 177495199260755075 :=
  join_receipt_window endpoint_13_77_flag endpoint_13_77_sources 0 10 2 176823196340812308 177495199260755075 177495199260755075 endpoint_13_77_p10 endpoint_13_77_w10
def endpoint_13_77 : CertifiedEndpoint :=
  ⟨⟨13, 77, 1444⟩, 177495199260755075, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_13_77_flag endpoint_13_77_sources 12 176823196340812308 177495199260755075 rfl endpoint_13_77_base endpoint_13_77_p12) (by decide)⟩
private def endpoint_13_78_flag : Flag := ⟨13, 78, 1334⟩
private def endpoint_13_78_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_13_78_base : receiptBase endpoint_13_78_flag endpoint_13_78_sources = some 165758878845589626 := by decide +kernel
private theorem endpoint_13_78_w0 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 2 165758878845589626 = some 169748194967763044 := by decide +kernel
private theorem endpoint_13_78_w2 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 2 2 169748194967763044 = some 169748194967763044 := by decide +kernel
private theorem endpoint_13_78_p4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 4 165758878845589626 = some 169748194967763044 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 2 2 165758878845589626 169748194967763044 169748194967763044 endpoint_13_78_w0 endpoint_13_78_w2
private theorem endpoint_13_78_w4 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 4 2 169748194967763044 = some 169748194967763044 := by decide +kernel
private theorem endpoint_13_78_p6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 6 165758878845589626 = some 169748194967763044 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 4 2 165758878845589626 169748194967763044 169748194967763044 endpoint_13_78_p4 endpoint_13_78_w4
private theorem endpoint_13_78_w6 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 6 2 169748194967763044 = some 169748194967763044 := by decide +kernel
private theorem endpoint_13_78_p8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 8 165758878845589626 = some 169748194967763044 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 6 2 165758878845589626 169748194967763044 169748194967763044 endpoint_13_78_p6 endpoint_13_78_w6
private theorem endpoint_13_78_w8 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 8 2 169748194967763044 = some 169748194967763044 := by decide +kernel
private theorem endpoint_13_78_p10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 10 165758878845589626 = some 169748194967763044 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 8 2 165758878845589626 169748194967763044 169748194967763044 endpoint_13_78_p8 endpoint_13_78_w8
private theorem endpoint_13_78_w10 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 10 2 169748194967763044 = some 169748194967763044 := by decide +kernel
private theorem endpoint_13_78_p12 : receiptWindow endpoint_13_78_flag endpoint_13_78_sources 0 12 165758878845589626 = some 169748194967763044 :=
  join_receipt_window endpoint_13_78_flag endpoint_13_78_sources 0 10 2 165758878845589626 169748194967763044 169748194967763044 endpoint_13_78_p10 endpoint_13_78_w10
def endpoint_13_78 : CertifiedEndpoint :=
  ⟨⟨13, 78, 1334⟩, 169748194967763044, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_13_78_flag endpoint_13_78_sources 12 165758878845589626 169748194967763044 rfl endpoint_13_78_base endpoint_13_78_p12) (by decide)⟩
private def endpoint_13_79_flag : Flag := ⟨13, 79, 1221⟩
private def endpoint_13_79_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_13_79_base : receiptBase endpoint_13_79_flag endpoint_13_79_sources = some 154499662406002150 := by decide +kernel
private theorem endpoint_13_79_w0 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 2 154499662406002150 = some 157190947461816504 := by decide +kernel
private theorem endpoint_13_79_w2 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 2 2 157190947461816504 = some 157190947461816504 := by decide +kernel
private theorem endpoint_13_79_p4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 4 154499662406002150 = some 157190947461816504 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 2 2 154499662406002150 157190947461816504 157190947461816504 endpoint_13_79_w0 endpoint_13_79_w2
private theorem endpoint_13_79_w4 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 4 2 157190947461816504 = some 157190947461816504 := by decide +kernel
private theorem endpoint_13_79_p6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 6 154499662406002150 = some 157190947461816504 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 4 2 154499662406002150 157190947461816504 157190947461816504 endpoint_13_79_p4 endpoint_13_79_w4
private theorem endpoint_13_79_w6 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 6 2 157190947461816504 = some 157190947461816504 := by decide +kernel
private theorem endpoint_13_79_p8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 8 154499662406002150 = some 157190947461816504 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 6 2 154499662406002150 157190947461816504 157190947461816504 endpoint_13_79_p6 endpoint_13_79_w6
private theorem endpoint_13_79_w8 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 8 2 157190947461816504 = some 157190947461816504 := by decide +kernel
private theorem endpoint_13_79_p10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 10 154499662406002150 = some 157190947461816504 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 8 2 154499662406002150 157190947461816504 157190947461816504 endpoint_13_79_p8 endpoint_13_79_w8
private theorem endpoint_13_79_w10 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 10 2 157190947461816504 = some 157190947461816504 := by decide +kernel
private theorem endpoint_13_79_p12 : receiptWindow endpoint_13_79_flag endpoint_13_79_sources 0 12 154499662406002150 = some 157190947461816504 :=
  join_receipt_window endpoint_13_79_flag endpoint_13_79_sources 0 10 2 154499662406002150 157190947461816504 157190947461816504 endpoint_13_79_p10 endpoint_13_79_w10
def endpoint_13_79 : CertifiedEndpoint :=
  ⟨⟨13, 79, 1221⟩, 157190947461816504, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_13_79_flag endpoint_13_79_sources 12 154499662406002150 157190947461816504 rfl endpoint_13_79_base endpoint_13_79_p12) (by decide)⟩
def endpoint_13_80 : CertifiedEndpoint :=
  ⟨⟨13, 80, 1105⟩, 250313596483070889, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_81 : CertifiedEndpoint :=
  ⟨⟨13, 81, 986⟩, 225179134101294485, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_82 : CertifiedEndpoint :=
  ⟨⟨13, 82, 864⟩, 198545974089011352, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_83 : CertifiedEndpoint :=
  ⟨⟨13, 83, 739⟩, 170385047382074376, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_84 : CertifiedEndpoint :=
  ⟨⟨13, 84, 610⟩, 140418574296770406, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_85 : CertifiedEndpoint :=
  ⟨⟨13, 85, 479⟩, 109111677112068056, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_86 : CertifiedEndpoint :=
  ⟨⟨13, 86, 344⟩, 75934635628671792, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_13_87 : CertifiedEndpoint :=
  ⟨⟨13, 87, 206⟩, 41107091402000537, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_14 : CertifiedEndpoint :=
  ⟨⟨14, 14, 4331⟩, 118246637167392271, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_15 : CertifiedEndpoint :=
  ⟨⟨14, 15, 4307⟩, 122492224016863576, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_16 : CertifiedEndpoint :=
  ⟨⟨14, 16, 4282⟩, 126653318110853702, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_17 : CertifiedEndpoint :=
  ⟨⟨14, 17, 4257⟩, 140701156574785746, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_18 : CertifiedEndpoint :=
  ⟨⟨14, 18, 4232⟩, 154571127421092292, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_19 : CertifiedEndpoint :=
  ⟨⟨14, 19, 4207⟩, 168263230649773340, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_20 : CertifiedEndpoint :=
  ⟨⟨14, 20, 4181⟩, 181733862627383447, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_21 : CertifiedEndpoint :=
  ⟨⟨14, 21, 4155⟩, 195019651786676860, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_22 : CertifiedEndpoint :=
  ⟨⟨14, 22, 4129⟩, 208120598127653579, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_23 : CertifiedEndpoint :=
  ⟨⟨14, 23, 4102⟩, 220982635215831367, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_24 : CertifiedEndpoint :=
  ⟨⟨14, 24, 4075⟩, 233652854285001265, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_25 : CertifiedEndpoint :=
  ⟨⟨14, 25, 4048⟩, 246131255335163273, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_26 : CertifiedEndpoint :=
  ⟨⟨14, 26, 4020⟩, 258353309130798360, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_14_27_flag : Flag := ⟨14, 27, 3992⟩
private def endpoint_14_27_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_27_base : receiptBase endpoint_14_27_flag endpoint_14_27_sources = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_w0 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 2 187524719573664495 = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_w2 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 2 2 187524719573664495 = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_p4 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 4 187524719573664495 = some 187524719573664495 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 2 2 187524719573664495 187524719573664495 187524719573664495 endpoint_14_27_w0 endpoint_14_27_w2
private theorem endpoint_14_27_w4 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 4 2 187524719573664495 = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_p6 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 6 187524719573664495 = some 187524719573664495 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 4 2 187524719573664495 187524719573664495 187524719573664495 endpoint_14_27_p4 endpoint_14_27_w4
private theorem endpoint_14_27_w6 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 6 2 187524719573664495 = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_p8 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 8 187524719573664495 = some 187524719573664495 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 6 2 187524719573664495 187524719573664495 187524719573664495 endpoint_14_27_p6 endpoint_14_27_w6
private theorem endpoint_14_27_w8 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 8 2 187524719573664495 = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_p10 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 10 187524719573664495 = some 187524719573664495 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 8 2 187524719573664495 187524719573664495 187524719573664495 endpoint_14_27_p8 endpoint_14_27_w8
private theorem endpoint_14_27_w10 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 10 2 187524719573664495 = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_p12 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 12 187524719573664495 = some 187524719573664495 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 10 2 187524719573664495 187524719573664495 187524719573664495 endpoint_14_27_p10 endpoint_14_27_w10
private theorem endpoint_14_27_w12 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 12 1 187524719573664495 = some 187524719573664495 := by decide +kernel
private theorem endpoint_14_27_p13 : receiptWindow endpoint_14_27_flag endpoint_14_27_sources 0 13 187524719573664495 = some 187524719573664495 :=
  join_receipt_window endpoint_14_27_flag endpoint_14_27_sources 0 12 1 187524719573664495 187524719573664495 187524719573664495 endpoint_14_27_p12 endpoint_14_27_w12
def endpoint_14_27 : CertifiedEndpoint :=
  ⟨⟨14, 27, 3992⟩, 187524719573664495, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_27_flag endpoint_14_27_sources 13 187524719573664495 187524719573664495 rfl endpoint_14_27_base endpoint_14_27_p13) (by decide)⟩
private def endpoint_14_28_flag : Flag := ⟨14, 28, 3963⟩
private def endpoint_14_28_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_28_base : receiptBase endpoint_14_28_flag endpoint_14_28_sources = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_w0 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 2 191751216238046992 = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_w2 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 2 2 191751216238046992 = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_p4 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 4 191751216238046992 = some 191751216238046992 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 2 2 191751216238046992 191751216238046992 191751216238046992 endpoint_14_28_w0 endpoint_14_28_w2
private theorem endpoint_14_28_w4 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 4 2 191751216238046992 = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_p6 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 6 191751216238046992 = some 191751216238046992 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 4 2 191751216238046992 191751216238046992 191751216238046992 endpoint_14_28_p4 endpoint_14_28_w4
private theorem endpoint_14_28_w6 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 6 2 191751216238046992 = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_p8 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 8 191751216238046992 = some 191751216238046992 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 6 2 191751216238046992 191751216238046992 191751216238046992 endpoint_14_28_p6 endpoint_14_28_w6
private theorem endpoint_14_28_w8 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 8 2 191751216238046992 = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_p10 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 10 191751216238046992 = some 191751216238046992 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 8 2 191751216238046992 191751216238046992 191751216238046992 endpoint_14_28_p8 endpoint_14_28_w8
private theorem endpoint_14_28_w10 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 10 2 191751216238046992 = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_p12 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 12 191751216238046992 = some 191751216238046992 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 10 2 191751216238046992 191751216238046992 191751216238046992 endpoint_14_28_p10 endpoint_14_28_w10
private theorem endpoint_14_28_w12 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 12 1 191751216238046992 = some 191751216238046992 := by decide +kernel
private theorem endpoint_14_28_p13 : receiptWindow endpoint_14_28_flag endpoint_14_28_sources 0 13 191751216238046992 = some 191751216238046992 :=
  join_receipt_window endpoint_14_28_flag endpoint_14_28_sources 0 12 1 191751216238046992 191751216238046992 191751216238046992 endpoint_14_28_p12 endpoint_14_28_w12
def endpoint_14_28 : CertifiedEndpoint :=
  ⟨⟨14, 28, 3963⟩, 191751216238046992, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_28_flag endpoint_14_28_sources 13 191751216238046992 191751216238046992 rfl endpoint_14_28_base endpoint_14_28_p13) (by decide)⟩
private def endpoint_14_29_flag : Flag := ⟨14, 29, 3934⟩
private def endpoint_14_29_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_29_base : receiptBase endpoint_14_29_flag endpoint_14_29_sources = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_w0 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 2 195896605431564704 = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_w2 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 2 2 195896605431564704 = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_p4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 4 195896605431564704 = some 195896605431564704 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 2 2 195896605431564704 195896605431564704 195896605431564704 endpoint_14_29_w0 endpoint_14_29_w2
private theorem endpoint_14_29_w4 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 4 2 195896605431564704 = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_p6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 6 195896605431564704 = some 195896605431564704 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 4 2 195896605431564704 195896605431564704 195896605431564704 endpoint_14_29_p4 endpoint_14_29_w4
private theorem endpoint_14_29_w6 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 6 2 195896605431564704 = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_p8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 8 195896605431564704 = some 195896605431564704 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 6 2 195896605431564704 195896605431564704 195896605431564704 endpoint_14_29_p6 endpoint_14_29_w6
private theorem endpoint_14_29_w8 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 8 2 195896605431564704 = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_p10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 10 195896605431564704 = some 195896605431564704 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 8 2 195896605431564704 195896605431564704 195896605431564704 endpoint_14_29_p8 endpoint_14_29_w8
private theorem endpoint_14_29_w10 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 10 2 195896605431564704 = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_p12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 12 195896605431564704 = some 195896605431564704 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 10 2 195896605431564704 195896605431564704 195896605431564704 endpoint_14_29_p10 endpoint_14_29_w10
private theorem endpoint_14_29_w12 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 12 1 195896605431564704 = some 195896605431564704 := by decide +kernel
private theorem endpoint_14_29_p13 : receiptWindow endpoint_14_29_flag endpoint_14_29_sources 0 13 195896605431564704 = some 195896605431564704 :=
  join_receipt_window endpoint_14_29_flag endpoint_14_29_sources 0 12 1 195896605431564704 195896605431564704 195896605431564704 endpoint_14_29_p12 endpoint_14_29_w12
def endpoint_14_29 : CertifiedEndpoint :=
  ⟨⟨14, 29, 3934⟩, 195896605431564704, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_29_flag endpoint_14_29_sources 13 195896605431564704 195896605431564704 rfl endpoint_14_29_base endpoint_14_29_p13) (by decide)⟩
private def endpoint_14_30_flag : Flag := ⟨14, 30, 3905⟩
private def endpoint_14_30_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_30_base : receiptBase endpoint_14_30_flag endpoint_14_30_sources = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_w0 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 2 199960887154217631 = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_w2 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 2 2 199960887154217631 = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_p4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 4 199960887154217631 = some 199960887154217631 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 2 2 199960887154217631 199960887154217631 199960887154217631 endpoint_14_30_w0 endpoint_14_30_w2
private theorem endpoint_14_30_w4 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 4 2 199960887154217631 = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_p6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 6 199960887154217631 = some 199960887154217631 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 4 2 199960887154217631 199960887154217631 199960887154217631 endpoint_14_30_p4 endpoint_14_30_w4
private theorem endpoint_14_30_w6 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 6 2 199960887154217631 = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_p8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 8 199960887154217631 = some 199960887154217631 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 6 2 199960887154217631 199960887154217631 199960887154217631 endpoint_14_30_p6 endpoint_14_30_w6
private theorem endpoint_14_30_w8 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 8 2 199960887154217631 = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_p10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 10 199960887154217631 = some 199960887154217631 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 8 2 199960887154217631 199960887154217631 199960887154217631 endpoint_14_30_p8 endpoint_14_30_w8
private theorem endpoint_14_30_w10 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 10 2 199960887154217631 = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_p12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 12 199960887154217631 = some 199960887154217631 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 10 2 199960887154217631 199960887154217631 199960887154217631 endpoint_14_30_p10 endpoint_14_30_w10
private theorem endpoint_14_30_w12 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 12 1 199960887154217631 = some 199960887154217631 := by decide +kernel
private theorem endpoint_14_30_p13 : receiptWindow endpoint_14_30_flag endpoint_14_30_sources 0 13 199960887154217631 = some 199960887154217631 :=
  join_receipt_window endpoint_14_30_flag endpoint_14_30_sources 0 12 1 199960887154217631 199960887154217631 199960887154217631 endpoint_14_30_p12 endpoint_14_30_w12
def endpoint_14_30 : CertifiedEndpoint :=
  ⟨⟨14, 30, 3905⟩, 199960887154217631, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_30_flag endpoint_14_30_sources 13 199960887154217631 199960887154217631 rfl endpoint_14_30_base endpoint_14_30_p13) (by decide)⟩
private def endpoint_14_31_flag : Flag := ⟨14, 31, 3875⟩
private def endpoint_14_31_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_31_base : receiptBase endpoint_14_31_flag endpoint_14_31_sources = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_w0 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 2 203892222661050221 = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_w2 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 2 2 203892222661050221 = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_p4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 4 203892222661050221 = some 203892222661050221 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 2 2 203892222661050221 203892222661050221 203892222661050221 endpoint_14_31_w0 endpoint_14_31_w2
private theorem endpoint_14_31_w4 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 4 2 203892222661050221 = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_p6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 6 203892222661050221 = some 203892222661050221 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 4 2 203892222661050221 203892222661050221 203892222661050221 endpoint_14_31_p4 endpoint_14_31_w4
private theorem endpoint_14_31_w6 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 6 2 203892222661050221 = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_p8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 8 203892222661050221 = some 203892222661050221 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 6 2 203892222661050221 203892222661050221 203892222661050221 endpoint_14_31_p6 endpoint_14_31_w6
private theorem endpoint_14_31_w8 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 8 2 203892222661050221 = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_p10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 10 203892222661050221 = some 203892222661050221 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 8 2 203892222661050221 203892222661050221 203892222661050221 endpoint_14_31_p8 endpoint_14_31_w8
private theorem endpoint_14_31_w10 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 10 2 203892222661050221 = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_p12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 12 203892222661050221 = some 203892222661050221 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 10 2 203892222661050221 203892222661050221 203892222661050221 endpoint_14_31_p10 endpoint_14_31_w10
private theorem endpoint_14_31_w12 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 12 1 203892222661050221 = some 203892222661050221 := by decide +kernel
private theorem endpoint_14_31_p13 : receiptWindow endpoint_14_31_flag endpoint_14_31_sources 0 13 203892222661050221 = some 203892222661050221 :=
  join_receipt_window endpoint_14_31_flag endpoint_14_31_sources 0 12 1 203892222661050221 203892222661050221 203892222661050221 endpoint_14_31_p12 endpoint_14_31_w12
def endpoint_14_31 : CertifiedEndpoint :=
  ⟨⟨14, 31, 3875⟩, 203892222661050221, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_31_flag endpoint_14_31_sources 13 203892222661050221 203892222661050221 rfl endpoint_14_31_base endpoint_14_31_p13) (by decide)⟩
private def endpoint_14_32_flag : Flag := ⟨14, 32, 3844⟩
private def endpoint_14_32_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_32_base : receiptBase endpoint_14_32_flag endpoint_14_32_sources = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_w0 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 2 207686488872945073 = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_w2 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 2 2 207686488872945073 = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_p4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 4 207686488872945073 = some 207686488872945073 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 2 2 207686488872945073 207686488872945073 207686488872945073 endpoint_14_32_w0 endpoint_14_32_w2
private theorem endpoint_14_32_w4 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 4 2 207686488872945073 = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_p6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 6 207686488872945073 = some 207686488872945073 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 4 2 207686488872945073 207686488872945073 207686488872945073 endpoint_14_32_p4 endpoint_14_32_w4
private theorem endpoint_14_32_w6 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 6 2 207686488872945073 = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_p8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 8 207686488872945073 = some 207686488872945073 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 6 2 207686488872945073 207686488872945073 207686488872945073 endpoint_14_32_p6 endpoint_14_32_w6
private theorem endpoint_14_32_w8 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 8 2 207686488872945073 = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_p10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 10 207686488872945073 = some 207686488872945073 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 8 2 207686488872945073 207686488872945073 207686488872945073 endpoint_14_32_p8 endpoint_14_32_w8
private theorem endpoint_14_32_w10 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 10 2 207686488872945073 = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_p12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 12 207686488872945073 = some 207686488872945073 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 10 2 207686488872945073 207686488872945073 207686488872945073 endpoint_14_32_p10 endpoint_14_32_w10
private theorem endpoint_14_32_w12 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 12 1 207686488872945073 = some 207686488872945073 := by decide +kernel
private theorem endpoint_14_32_p13 : receiptWindow endpoint_14_32_flag endpoint_14_32_sources 0 13 207686488872945073 = some 207686488872945073 :=
  join_receipt_window endpoint_14_32_flag endpoint_14_32_sources 0 12 1 207686488872945073 207686488872945073 207686488872945073 endpoint_14_32_p12 endpoint_14_32_w12
def endpoint_14_32 : CertifiedEndpoint :=
  ⟨⟨14, 32, 3844⟩, 207686488872945073, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_32_flag endpoint_14_32_sources 13 207686488872945073 207686488872945073 rfl endpoint_14_32_base endpoint_14_32_p13) (by decide)⟩
private def endpoint_14_33_flag : Flag := ⟨14, 33, 3814⟩
private def endpoint_14_33_sources : Sources := ⟨contact10, contact01, contact10⟩
private theorem endpoint_14_33_base : receiptBase endpoint_14_33_flag endpoint_14_33_sources = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_w0 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 2 211448737639519091 = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_w2 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 2 2 211448737639519091 = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_p4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 4 211448737639519091 = some 211448737639519091 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 2 2 211448737639519091 211448737639519091 211448737639519091 endpoint_14_33_w0 endpoint_14_33_w2
private theorem endpoint_14_33_w4 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 4 2 211448737639519091 = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_p6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 6 211448737639519091 = some 211448737639519091 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 4 2 211448737639519091 211448737639519091 211448737639519091 endpoint_14_33_p4 endpoint_14_33_w4
private theorem endpoint_14_33_w6 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 6 2 211448737639519091 = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_p8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 8 211448737639519091 = some 211448737639519091 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 6 2 211448737639519091 211448737639519091 211448737639519091 endpoint_14_33_p6 endpoint_14_33_w6
private theorem endpoint_14_33_w8 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 8 2 211448737639519091 = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_p10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 10 211448737639519091 = some 211448737639519091 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 8 2 211448737639519091 211448737639519091 211448737639519091 endpoint_14_33_p8 endpoint_14_33_w8
private theorem endpoint_14_33_w10 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 10 2 211448737639519091 = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_p12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 12 211448737639519091 = some 211448737639519091 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 10 2 211448737639519091 211448737639519091 211448737639519091 endpoint_14_33_p10 endpoint_14_33_w10
private theorem endpoint_14_33_w12 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 12 1 211448737639519091 = some 211448737639519091 := by decide +kernel
private theorem endpoint_14_33_p13 : receiptWindow endpoint_14_33_flag endpoint_14_33_sources 0 13 211448737639519091 = some 211448737639519091 :=
  join_receipt_window endpoint_14_33_flag endpoint_14_33_sources 0 12 1 211448737639519091 211448737639519091 211448737639519091 endpoint_14_33_p12 endpoint_14_33_w12
def endpoint_14_33 : CertifiedEndpoint :=
  ⟨⟨14, 33, 3814⟩, 211448737639519091, .terminal ⟨contact10, contact01, contact10⟩ (finish_receipt_window endpoint_14_33_flag endpoint_14_33_sources 13 211448737639519091 211448737639519091 rfl endpoint_14_33_base endpoint_14_33_p13) (by decide)⟩
private def endpoint_14_34_flag : Flag := ⟨14, 34, 3782⟩
private def endpoint_14_34_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_34_base : receiptBase endpoint_14_34_flag endpoint_14_34_sources = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_w0 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 2 216334891285984904 = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_w2 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 2 2 216334891285984904 = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_p4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 4 216334891285984904 = some 216334891285984904 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 2 2 216334891285984904 216334891285984904 216334891285984904 endpoint_14_34_w0 endpoint_14_34_w2
private theorem endpoint_14_34_w4 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 4 2 216334891285984904 = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_p6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 6 216334891285984904 = some 216334891285984904 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 4 2 216334891285984904 216334891285984904 216334891285984904 endpoint_14_34_p4 endpoint_14_34_w4
private theorem endpoint_14_34_w6 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 6 2 216334891285984904 = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_p8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 8 216334891285984904 = some 216334891285984904 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 6 2 216334891285984904 216334891285984904 216334891285984904 endpoint_14_34_p6 endpoint_14_34_w6
private theorem endpoint_14_34_w8 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 8 2 216334891285984904 = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_p10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 10 216334891285984904 = some 216334891285984904 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 8 2 216334891285984904 216334891285984904 216334891285984904 endpoint_14_34_p8 endpoint_14_34_w8
private theorem endpoint_14_34_w10 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 10 2 216334891285984904 = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_p12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 12 216334891285984904 = some 216334891285984904 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 10 2 216334891285984904 216334891285984904 216334891285984904 endpoint_14_34_p10 endpoint_14_34_w10
private theorem endpoint_14_34_w12 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 12 1 216334891285984904 = some 216334891285984904 := by decide +kernel
private theorem endpoint_14_34_p13 : receiptWindow endpoint_14_34_flag endpoint_14_34_sources 0 13 216334891285984904 = some 216334891285984904 :=
  join_receipt_window endpoint_14_34_flag endpoint_14_34_sources 0 12 1 216334891285984904 216334891285984904 216334891285984904 endpoint_14_34_p12 endpoint_14_34_w12
def endpoint_14_34 : CertifiedEndpoint :=
  ⟨⟨14, 34, 3782⟩, 216334891285984904, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_34_flag endpoint_14_34_sources 13 216334891285984904 216334891285984904 rfl endpoint_14_34_base endpoint_14_34_p13) (by decide)⟩
private def endpoint_14_35_flag : Flag := ⟨14, 35, 3750⟩
private def endpoint_14_35_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_35_base : receiptBase endpoint_14_35_flag endpoint_14_35_sources = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_w0 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 2 219728551223715404 = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_w2 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 2 2 219728551223715404 = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_p4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 4 219728551223715404 = some 219728551223715404 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 2 2 219728551223715404 219728551223715404 219728551223715404 endpoint_14_35_w0 endpoint_14_35_w2
private theorem endpoint_14_35_w4 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 4 2 219728551223715404 = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_p6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 6 219728551223715404 = some 219728551223715404 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 4 2 219728551223715404 219728551223715404 219728551223715404 endpoint_14_35_p4 endpoint_14_35_w4
private theorem endpoint_14_35_w6 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 6 2 219728551223715404 = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_p8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 8 219728551223715404 = some 219728551223715404 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 6 2 219728551223715404 219728551223715404 219728551223715404 endpoint_14_35_p6 endpoint_14_35_w6
private theorem endpoint_14_35_w8 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 8 2 219728551223715404 = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_p10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 10 219728551223715404 = some 219728551223715404 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 8 2 219728551223715404 219728551223715404 219728551223715404 endpoint_14_35_p8 endpoint_14_35_w8
private theorem endpoint_14_35_w10 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 10 2 219728551223715404 = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_p12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 12 219728551223715404 = some 219728551223715404 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 10 2 219728551223715404 219728551223715404 219728551223715404 endpoint_14_35_p10 endpoint_14_35_w10
private theorem endpoint_14_35_w12 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 12 1 219728551223715404 = some 219728551223715404 := by decide +kernel
private theorem endpoint_14_35_p13 : receiptWindow endpoint_14_35_flag endpoint_14_35_sources 0 13 219728551223715404 = some 219728551223715404 :=
  join_receipt_window endpoint_14_35_flag endpoint_14_35_sources 0 12 1 219728551223715404 219728551223715404 219728551223715404 endpoint_14_35_p12 endpoint_14_35_w12
def endpoint_14_35 : CertifiedEndpoint :=
  ⟨⟨14, 35, 3750⟩, 219728551223715404, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_35_flag endpoint_14_35_sources 13 219728551223715404 219728551223715404 rfl endpoint_14_35_base endpoint_14_35_p13) (by decide)⟩
private def endpoint_14_36_flag : Flag := ⟨14, 36, 3718⟩
private def endpoint_14_36_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_36_base : receiptBase endpoint_14_36_flag endpoint_14_36_sources = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_w0 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 2 223033897237310854 = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_w2 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 2 2 223033897237310854 = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_p4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 4 223033897237310854 = some 223033897237310854 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 2 2 223033897237310854 223033897237310854 223033897237310854 endpoint_14_36_w0 endpoint_14_36_w2
private theorem endpoint_14_36_w4 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 4 2 223033897237310854 = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_p6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 6 223033897237310854 = some 223033897237310854 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 4 2 223033897237310854 223033897237310854 223033897237310854 endpoint_14_36_p4 endpoint_14_36_w4
private theorem endpoint_14_36_w6 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 6 2 223033897237310854 = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_p8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 8 223033897237310854 = some 223033897237310854 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 6 2 223033897237310854 223033897237310854 223033897237310854 endpoint_14_36_p6 endpoint_14_36_w6
private theorem endpoint_14_36_w8 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 8 2 223033897237310854 = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_p10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 10 223033897237310854 = some 223033897237310854 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 8 2 223033897237310854 223033897237310854 223033897237310854 endpoint_14_36_p8 endpoint_14_36_w8
private theorem endpoint_14_36_w10 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 10 2 223033897237310854 = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_p12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 12 223033897237310854 = some 223033897237310854 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 10 2 223033897237310854 223033897237310854 223033897237310854 endpoint_14_36_p10 endpoint_14_36_w10
private theorem endpoint_14_36_w12 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 12 1 223033897237310854 = some 223033897237310854 := by decide +kernel
private theorem endpoint_14_36_p13 : receiptWindow endpoint_14_36_flag endpoint_14_36_sources 0 13 223033897237310854 = some 223033897237310854 :=
  join_receipt_window endpoint_14_36_flag endpoint_14_36_sources 0 12 1 223033897237310854 223033897237310854 223033897237310854 endpoint_14_36_p12 endpoint_14_36_w12
def endpoint_14_36 : CertifiedEndpoint :=
  ⟨⟨14, 36, 3718⟩, 223033897237310854, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_36_flag endpoint_14_36_sources 13 223033897237310854 223033897237310854 rfl endpoint_14_36_base endpoint_14_36_p13) (by decide)⟩
private def endpoint_14_37_flag : Flag := ⟨14, 37, 3685⟩
private def endpoint_14_37_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_37_base : receiptBase endpoint_14_37_flag endpoint_14_37_sources = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_w0 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 2 226190446640828549 = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_w2 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 2 2 226190446640828549 = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_p4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 4 226190446640828549 = some 226190446640828549 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 2 2 226190446640828549 226190446640828549 226190446640828549 endpoint_14_37_w0 endpoint_14_37_w2
private theorem endpoint_14_37_w4 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 4 2 226190446640828549 = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_p6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 6 226190446640828549 = some 226190446640828549 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 4 2 226190446640828549 226190446640828549 226190446640828549 endpoint_14_37_p4 endpoint_14_37_w4
private theorem endpoint_14_37_w6 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 6 2 226190446640828549 = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_p8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 8 226190446640828549 = some 226190446640828549 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 6 2 226190446640828549 226190446640828549 226190446640828549 endpoint_14_37_p6 endpoint_14_37_w6
private theorem endpoint_14_37_w8 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 8 2 226190446640828549 = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_p10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 10 226190446640828549 = some 226190446640828549 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 8 2 226190446640828549 226190446640828549 226190446640828549 endpoint_14_37_p8 endpoint_14_37_w8
private theorem endpoint_14_37_w10 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 10 2 226190446640828549 = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_p12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 12 226190446640828549 = some 226190446640828549 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 10 2 226190446640828549 226190446640828549 226190446640828549 endpoint_14_37_p10 endpoint_14_37_w10
private theorem endpoint_14_37_w12 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 12 1 226190446640828549 = some 226190446640828549 := by decide +kernel
private theorem endpoint_14_37_p13 : receiptWindow endpoint_14_37_flag endpoint_14_37_sources 0 13 226190446640828549 = some 226190446640828549 :=
  join_receipt_window endpoint_14_37_flag endpoint_14_37_sources 0 12 1 226190446640828549 226190446640828549 226190446640828549 endpoint_14_37_p12 endpoint_14_37_w12
def endpoint_14_37 : CertifiedEndpoint :=
  ⟨⟨14, 37, 3685⟩, 226190446640828549, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_37_flag endpoint_14_37_sources 13 226190446640828549 226190446640828549 rfl endpoint_14_37_base endpoint_14_37_p13) (by decide)⟩
private def endpoint_14_38_flag : Flag := ⟨14, 38, 3651⟩
private def endpoint_14_38_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_38_base : receiptBase endpoint_14_38_flag endpoint_14_38_sources = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_w0 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 2 229194123614674794 = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_w2 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 2 2 229194123614674794 = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_p4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 4 229194123614674794 = some 229194123614674794 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 2 2 229194123614674794 229194123614674794 229194123614674794 endpoint_14_38_w0 endpoint_14_38_w2
private theorem endpoint_14_38_w4 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 4 2 229194123614674794 = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_p6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 6 229194123614674794 = some 229194123614674794 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 4 2 229194123614674794 229194123614674794 229194123614674794 endpoint_14_38_p4 endpoint_14_38_w4
private theorem endpoint_14_38_w6 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 6 2 229194123614674794 = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_p8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 8 229194123614674794 = some 229194123614674794 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 6 2 229194123614674794 229194123614674794 229194123614674794 endpoint_14_38_p6 endpoint_14_38_w6
private theorem endpoint_14_38_w8 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 8 2 229194123614674794 = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_p10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 10 229194123614674794 = some 229194123614674794 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 8 2 229194123614674794 229194123614674794 229194123614674794 endpoint_14_38_p8 endpoint_14_38_w8
private theorem endpoint_14_38_w10 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 10 2 229194123614674794 = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_p12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 12 229194123614674794 = some 229194123614674794 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 10 2 229194123614674794 229194123614674794 229194123614674794 endpoint_14_38_p10 endpoint_14_38_w10
private theorem endpoint_14_38_w12 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 12 1 229194123614674794 = some 229194123614674794 := by decide +kernel
private theorem endpoint_14_38_p13 : receiptWindow endpoint_14_38_flag endpoint_14_38_sources 0 13 229194123614674794 = some 229194123614674794 :=
  join_receipt_window endpoint_14_38_flag endpoint_14_38_sources 0 12 1 229194123614674794 229194123614674794 229194123614674794 endpoint_14_38_p12 endpoint_14_38_w12
def endpoint_14_38 : CertifiedEndpoint :=
  ⟨⟨14, 38, 3651⟩, 229194123614674794, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_38_flag endpoint_14_38_sources 13 229194123614674794 229194123614674794 rfl endpoint_14_38_base endpoint_14_38_p13) (by decide)⟩
private def endpoint_14_39_flag : Flag := ⟨14, 39, 3616⟩
private def endpoint_14_39_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_14_39_base : receiptBase endpoint_14_39_flag endpoint_14_39_sources = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_w0 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 2 232040852339255896 = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_w2 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 2 2 232040852339255896 = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_p4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 4 232040852339255896 = some 232040852339255896 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 2 2 232040852339255896 232040852339255896 232040852339255896 endpoint_14_39_w0 endpoint_14_39_w2
private theorem endpoint_14_39_w4 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 4 2 232040852339255896 = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_p6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 6 232040852339255896 = some 232040852339255896 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 4 2 232040852339255896 232040852339255896 232040852339255896 endpoint_14_39_p4 endpoint_14_39_w4
private theorem endpoint_14_39_w6 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 6 2 232040852339255896 = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_p8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 8 232040852339255896 = some 232040852339255896 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 6 2 232040852339255896 232040852339255896 232040852339255896 endpoint_14_39_p6 endpoint_14_39_w6
private theorem endpoint_14_39_w8 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 8 2 232040852339255896 = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_p10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 10 232040852339255896 = some 232040852339255896 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 8 2 232040852339255896 232040852339255896 232040852339255896 endpoint_14_39_p8 endpoint_14_39_w8
private theorem endpoint_14_39_w10 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 10 2 232040852339255896 = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_p12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 12 232040852339255896 = some 232040852339255896 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 10 2 232040852339255896 232040852339255896 232040852339255896 endpoint_14_39_p10 endpoint_14_39_w10
private theorem endpoint_14_39_w12 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 12 1 232040852339255896 = some 232040852339255896 := by decide +kernel
private theorem endpoint_14_39_p13 : receiptWindow endpoint_14_39_flag endpoint_14_39_sources 0 13 232040852339255896 = some 232040852339255896 :=
  join_receipt_window endpoint_14_39_flag endpoint_14_39_sources 0 12 1 232040852339255896 232040852339255896 232040852339255896 endpoint_14_39_p12 endpoint_14_39_w12
def endpoint_14_39 : CertifiedEndpoint :=
  ⟨⟨14, 39, 3616⟩, 232040852339255896, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_14_39_flag endpoint_14_39_sources 13 232040852339255896 232040852339255896 rfl endpoint_14_39_base endpoint_14_39_p13) (by decide)⟩
private def endpoint_14_40_flag : Flag := ⟨14, 40, 3581⟩
private def endpoint_14_40_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_40_base : receiptBase endpoint_14_40_flag endpoint_14_40_sources = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_w0 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 2 235421629447999156 = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_w2 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 2 2 235421629447999156 = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_p4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 4 235421629447999156 = some 235421629447999156 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 2 2 235421629447999156 235421629447999156 235421629447999156 endpoint_14_40_w0 endpoint_14_40_w2
private theorem endpoint_14_40_w4 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 4 2 235421629447999156 = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_p6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 6 235421629447999156 = some 235421629447999156 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 4 2 235421629447999156 235421629447999156 235421629447999156 endpoint_14_40_p4 endpoint_14_40_w4
private theorem endpoint_14_40_w6 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 6 2 235421629447999156 = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_p8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 8 235421629447999156 = some 235421629447999156 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 6 2 235421629447999156 235421629447999156 235421629447999156 endpoint_14_40_p6 endpoint_14_40_w6
private theorem endpoint_14_40_w8 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 8 2 235421629447999156 = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_p10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 10 235421629447999156 = some 235421629447999156 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 8 2 235421629447999156 235421629447999156 235421629447999156 endpoint_14_40_p8 endpoint_14_40_w8
private theorem endpoint_14_40_w10 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 10 2 235421629447999156 = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_p12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 12 235421629447999156 = some 235421629447999156 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 10 2 235421629447999156 235421629447999156 235421629447999156 endpoint_14_40_p10 endpoint_14_40_w10
private theorem endpoint_14_40_w12 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 12 1 235421629447999156 = some 235421629447999156 := by decide +kernel
private theorem endpoint_14_40_p13 : receiptWindow endpoint_14_40_flag endpoint_14_40_sources 0 13 235421629447999156 = some 235421629447999156 :=
  join_receipt_window endpoint_14_40_flag endpoint_14_40_sources 0 12 1 235421629447999156 235421629447999156 235421629447999156 endpoint_14_40_p12 endpoint_14_40_w12
def endpoint_14_40 : CertifiedEndpoint :=
  ⟨⟨14, 40, 3581⟩, 235421629447999156, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_40_flag endpoint_14_40_sources 13 235421629447999156 235421629447999156 rfl endpoint_14_40_base endpoint_14_40_p13) (by decide)⟩
private def endpoint_14_41_flag : Flag := ⟨14, 41, 3545⟩
private def endpoint_14_41_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_41_base : receiptBase endpoint_14_41_flag endpoint_14_41_sources = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_w0 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 2 238025247821298865 = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_w2 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 2 2 238025247821298865 = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_p4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 4 238025247821298865 = some 238025247821298865 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 2 2 238025247821298865 238025247821298865 238025247821298865 endpoint_14_41_w0 endpoint_14_41_w2
private theorem endpoint_14_41_w4 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 4 2 238025247821298865 = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_p6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 6 238025247821298865 = some 238025247821298865 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 4 2 238025247821298865 238025247821298865 238025247821298865 endpoint_14_41_p4 endpoint_14_41_w4
private theorem endpoint_14_41_w6 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 6 2 238025247821298865 = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_p8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 8 238025247821298865 = some 238025247821298865 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 6 2 238025247821298865 238025247821298865 238025247821298865 endpoint_14_41_p6 endpoint_14_41_w6
private theorem endpoint_14_41_w8 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 8 2 238025247821298865 = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_p10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 10 238025247821298865 = some 238025247821298865 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 8 2 238025247821298865 238025247821298865 238025247821298865 endpoint_14_41_p8 endpoint_14_41_w8
private theorem endpoint_14_41_w10 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 10 2 238025247821298865 = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_p12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 12 238025247821298865 = some 238025247821298865 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 10 2 238025247821298865 238025247821298865 238025247821298865 endpoint_14_41_p10 endpoint_14_41_w10
private theorem endpoint_14_41_w12 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 12 1 238025247821298865 = some 238025247821298865 := by decide +kernel
private theorem endpoint_14_41_p13 : receiptWindow endpoint_14_41_flag endpoint_14_41_sources 0 13 238025247821298865 = some 238025247821298865 :=
  join_receipt_window endpoint_14_41_flag endpoint_14_41_sources 0 12 1 238025247821298865 238025247821298865 238025247821298865 endpoint_14_41_p12 endpoint_14_41_w12
def endpoint_14_41 : CertifiedEndpoint :=
  ⟨⟨14, 41, 3545⟩, 238025247821298865, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_41_flag endpoint_14_41_sources 13 238025247821298865 238025247821298865 rfl endpoint_14_41_base endpoint_14_41_p13) (by decide)⟩
private def endpoint_14_42_flag : Flag := ⟨14, 42, 3509⟩
private def endpoint_14_42_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_42_base : receiptBase endpoint_14_42_flag endpoint_14_42_sources = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_w0 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 2 240529026364993975 = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_w2 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 2 2 240529026364993975 = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_p4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 4 240529026364993975 = some 240529026364993975 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 2 2 240529026364993975 240529026364993975 240529026364993975 endpoint_14_42_w0 endpoint_14_42_w2
private theorem endpoint_14_42_w4 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 4 2 240529026364993975 = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_p6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 6 240529026364993975 = some 240529026364993975 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 4 2 240529026364993975 240529026364993975 240529026364993975 endpoint_14_42_p4 endpoint_14_42_w4
private theorem endpoint_14_42_w6 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 6 2 240529026364993975 = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_p8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 8 240529026364993975 = some 240529026364993975 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 6 2 240529026364993975 240529026364993975 240529026364993975 endpoint_14_42_p6 endpoint_14_42_w6
private theorem endpoint_14_42_w8 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 8 2 240529026364993975 = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_p10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 10 240529026364993975 = some 240529026364993975 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 8 2 240529026364993975 240529026364993975 240529026364993975 endpoint_14_42_p8 endpoint_14_42_w8
private theorem endpoint_14_42_w10 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 10 2 240529026364993975 = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_p12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 12 240529026364993975 = some 240529026364993975 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 10 2 240529026364993975 240529026364993975 240529026364993975 endpoint_14_42_p10 endpoint_14_42_w10
private theorem endpoint_14_42_w12 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 12 1 240529026364993975 = some 240529026364993975 := by decide +kernel
private theorem endpoint_14_42_p13 : receiptWindow endpoint_14_42_flag endpoint_14_42_sources 0 13 240529026364993975 = some 240529026364993975 :=
  join_receipt_window endpoint_14_42_flag endpoint_14_42_sources 0 12 1 240529026364993975 240529026364993975 240529026364993975 endpoint_14_42_p12 endpoint_14_42_w12
def endpoint_14_42 : CertifiedEndpoint :=
  ⟨⟨14, 42, 3509⟩, 240529026364993975, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_42_flag endpoint_14_42_sources 13 240529026364993975 240529026364993975 rfl endpoint_14_42_base endpoint_14_42_p13) (by decide)⟩
private def endpoint_14_43_flag : Flag := ⟨14, 43, 3471⟩
private def endpoint_14_43_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_14_43_base : receiptBase endpoint_14_43_flag endpoint_14_43_sources = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_w0 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 2 242795180931252213 = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_w2 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 2 2 242795180931252213 = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_p4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 4 242795180931252213 = some 242795180931252213 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 2 2 242795180931252213 242795180931252213 242795180931252213 endpoint_14_43_w0 endpoint_14_43_w2
private theorem endpoint_14_43_w4 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 4 2 242795180931252213 = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_p6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 6 242795180931252213 = some 242795180931252213 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 4 2 242795180931252213 242795180931252213 242795180931252213 endpoint_14_43_p4 endpoint_14_43_w4
private theorem endpoint_14_43_w6 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 6 2 242795180931252213 = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_p8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 8 242795180931252213 = some 242795180931252213 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 6 2 242795180931252213 242795180931252213 242795180931252213 endpoint_14_43_p6 endpoint_14_43_w6
private theorem endpoint_14_43_w8 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 8 2 242795180931252213 = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_p10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 10 242795180931252213 = some 242795180931252213 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 8 2 242795180931252213 242795180931252213 242795180931252213 endpoint_14_43_p8 endpoint_14_43_w8
private theorem endpoint_14_43_w10 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 10 2 242795180931252213 = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_p12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 12 242795180931252213 = some 242795180931252213 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 10 2 242795180931252213 242795180931252213 242795180931252213 endpoint_14_43_p10 endpoint_14_43_w10
private theorem endpoint_14_43_w12 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 12 1 242795180931252213 = some 242795180931252213 := by decide +kernel
private theorem endpoint_14_43_p13 : receiptWindow endpoint_14_43_flag endpoint_14_43_sources 0 13 242795180931252213 = some 242795180931252213 :=
  join_receipt_window endpoint_14_43_flag endpoint_14_43_sources 0 12 1 242795180931252213 242795180931252213 242795180931252213 endpoint_14_43_p12 endpoint_14_43_w12
def endpoint_14_43 : CertifiedEndpoint :=
  ⟨⟨14, 43, 3471⟩, 242795180931252213, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_14_43_flag endpoint_14_43_sources 13 242795180931252213 242795180931252213 rfl endpoint_14_43_base endpoint_14_43_p13) (by decide)⟩
private def endpoint_14_44_flag : Flag := ⟨14, 44, 3433⟩
private def endpoint_14_44_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_14_44_base : receiptBase endpoint_14_44_flag endpoint_14_44_sources = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_w0 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 2 246287349561180280 = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_w2 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 2 2 246287349561180280 = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_p4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 4 246287349561180280 = some 246287349561180280 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 2 2 246287349561180280 246287349561180280 246287349561180280 endpoint_14_44_w0 endpoint_14_44_w2
private theorem endpoint_14_44_w4 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 4 2 246287349561180280 = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_p6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 6 246287349561180280 = some 246287349561180280 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 4 2 246287349561180280 246287349561180280 246287349561180280 endpoint_14_44_p4 endpoint_14_44_w4
private theorem endpoint_14_44_w6 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 6 2 246287349561180280 = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_p8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 8 246287349561180280 = some 246287349561180280 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 6 2 246287349561180280 246287349561180280 246287349561180280 endpoint_14_44_p6 endpoint_14_44_w6
private theorem endpoint_14_44_w8 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 8 2 246287349561180280 = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_p10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 10 246287349561180280 = some 246287349561180280 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 8 2 246287349561180280 246287349561180280 246287349561180280 endpoint_14_44_p8 endpoint_14_44_w8
private theorem endpoint_14_44_w10 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 10 2 246287349561180280 = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_p12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 12 246287349561180280 = some 246287349561180280 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 10 2 246287349561180280 246287349561180280 246287349561180280 endpoint_14_44_p10 endpoint_14_44_w10
private theorem endpoint_14_44_w12 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 12 1 246287349561180280 = some 246287349561180280 := by decide +kernel
private theorem endpoint_14_44_p13 : receiptWindow endpoint_14_44_flag endpoint_14_44_sources 0 13 246287349561180280 = some 246287349561180280 :=
  join_receipt_window endpoint_14_44_flag endpoint_14_44_sources 0 12 1 246287349561180280 246287349561180280 246287349561180280 endpoint_14_44_p12 endpoint_14_44_w12
def endpoint_14_44 : CertifiedEndpoint :=
  ⟨⟨14, 44, 3433⟩, 246287349561180280, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_14_44_flag endpoint_14_44_sources 13 246287349561180280 246287349561180280 rfl endpoint_14_44_base endpoint_14_44_p13) (by decide)⟩
private def endpoint_14_45_flag : Flag := ⟨14, 45, 3394⟩
private def endpoint_14_45_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_45_base : receiptBase endpoint_14_45_flag endpoint_14_45_sources = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_w0 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 2 249513923654123829 = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_w2 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 2 2 249513923654123829 = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_p4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 4 249513923654123829 = some 249513923654123829 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 2 2 249513923654123829 249513923654123829 249513923654123829 endpoint_14_45_w0 endpoint_14_45_w2
private theorem endpoint_14_45_w4 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 4 2 249513923654123829 = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_p6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 6 249513923654123829 = some 249513923654123829 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 4 2 249513923654123829 249513923654123829 249513923654123829 endpoint_14_45_p4 endpoint_14_45_w4
private theorem endpoint_14_45_w6 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 6 2 249513923654123829 = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_p8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 8 249513923654123829 = some 249513923654123829 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 6 2 249513923654123829 249513923654123829 249513923654123829 endpoint_14_45_p6 endpoint_14_45_w6
private theorem endpoint_14_45_w8 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 8 2 249513923654123829 = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_p10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 10 249513923654123829 = some 249513923654123829 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 8 2 249513923654123829 249513923654123829 249513923654123829 endpoint_14_45_p8 endpoint_14_45_w8
private theorem endpoint_14_45_w10 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 10 2 249513923654123829 = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_p12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 12 249513923654123829 = some 249513923654123829 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 10 2 249513923654123829 249513923654123829 249513923654123829 endpoint_14_45_p10 endpoint_14_45_w10
private theorem endpoint_14_45_w12 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 12 1 249513923654123829 = some 249513923654123829 := by decide +kernel
private theorem endpoint_14_45_p13 : receiptWindow endpoint_14_45_flag endpoint_14_45_sources 0 13 249513923654123829 = some 249513923654123829 :=
  join_receipt_window endpoint_14_45_flag endpoint_14_45_sources 0 12 1 249513923654123829 249513923654123829 249513923654123829 endpoint_14_45_p12 endpoint_14_45_w12
def endpoint_14_45 : CertifiedEndpoint :=
  ⟨⟨14, 45, 3394⟩, 249513923654123829, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_45_flag endpoint_14_45_sources 13 249513923654123829 249513923654123829 rfl endpoint_14_45_base endpoint_14_45_p13) (by decide)⟩
private def endpoint_14_46_flag : Flag := ⟨14, 46, 3353⟩
private def endpoint_14_46_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_46_base : receiptBase endpoint_14_46_flag endpoint_14_46_sources = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_w0 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 2 251180141296062276 = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_w2 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 2 2 251180141296062276 = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_p4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 4 251180141296062276 = some 251180141296062276 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 2 2 251180141296062276 251180141296062276 251180141296062276 endpoint_14_46_w0 endpoint_14_46_w2
private theorem endpoint_14_46_w4 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 4 2 251180141296062276 = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_p6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 6 251180141296062276 = some 251180141296062276 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 4 2 251180141296062276 251180141296062276 251180141296062276 endpoint_14_46_p4 endpoint_14_46_w4
private theorem endpoint_14_46_w6 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 6 2 251180141296062276 = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_p8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 8 251180141296062276 = some 251180141296062276 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 6 2 251180141296062276 251180141296062276 251180141296062276 endpoint_14_46_p6 endpoint_14_46_w6
private theorem endpoint_14_46_w8 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 8 2 251180141296062276 = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_p10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 10 251180141296062276 = some 251180141296062276 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 8 2 251180141296062276 251180141296062276 251180141296062276 endpoint_14_46_p8 endpoint_14_46_w8
private theorem endpoint_14_46_w10 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 10 2 251180141296062276 = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_p12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 12 251180141296062276 = some 251180141296062276 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 10 2 251180141296062276 251180141296062276 251180141296062276 endpoint_14_46_p10 endpoint_14_46_w10
private theorem endpoint_14_46_w12 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 12 1 251180141296062276 = some 251180141296062276 := by decide +kernel
private theorem endpoint_14_46_p13 : receiptWindow endpoint_14_46_flag endpoint_14_46_sources 0 13 251180141296062276 = some 251180141296062276 :=
  join_receipt_window endpoint_14_46_flag endpoint_14_46_sources 0 12 1 251180141296062276 251180141296062276 251180141296062276 endpoint_14_46_p12 endpoint_14_46_w12
def endpoint_14_46 : CertifiedEndpoint :=
  ⟨⟨14, 46, 3353⟩, 251180141296062276, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_46_flag endpoint_14_46_sources 13 251180141296062276 251180141296062276 rfl endpoint_14_46_base endpoint_14_46_p13) (by decide)⟩
private def endpoint_14_47_flag : Flag := ⟨14, 47, 3312⟩
private def endpoint_14_47_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_14_47_base : receiptBase endpoint_14_47_flag endpoint_14_47_sources = some 252733221506923970 := by decide +kernel
private theorem endpoint_14_47_w0 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 2 252733221506923970 = some 252741018474981495 := by decide +kernel
private theorem endpoint_14_47_w2 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 2 2 252741018474981495 = some 252741018474981495 := by decide +kernel
private theorem endpoint_14_47_p4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 4 252733221506923970 = some 252741018474981495 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 2 2 252733221506923970 252741018474981495 252741018474981495 endpoint_14_47_w0 endpoint_14_47_w2
private theorem endpoint_14_47_w4 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 4 2 252741018474981495 = some 252741018474981495 := by decide +kernel
private theorem endpoint_14_47_p6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 6 252733221506923970 = some 252741018474981495 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 4 2 252733221506923970 252741018474981495 252741018474981495 endpoint_14_47_p4 endpoint_14_47_w4
private theorem endpoint_14_47_w6 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 6 2 252741018474981495 = some 252741018474981495 := by decide +kernel
private theorem endpoint_14_47_p8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 8 252733221506923970 = some 252741018474981495 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 6 2 252733221506923970 252741018474981495 252741018474981495 endpoint_14_47_p6 endpoint_14_47_w6
private theorem endpoint_14_47_w8 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 8 2 252741018474981495 = some 252741018474981495 := by decide +kernel
private theorem endpoint_14_47_p10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 10 252733221506923970 = some 252741018474981495 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 8 2 252733221506923970 252741018474981495 252741018474981495 endpoint_14_47_p8 endpoint_14_47_w8
private theorem endpoint_14_47_w10 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 10 2 252741018474981495 = some 252741018474981495 := by decide +kernel
private theorem endpoint_14_47_p12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 12 252733221506923970 = some 252741018474981495 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 10 2 252733221506923970 252741018474981495 252741018474981495 endpoint_14_47_p10 endpoint_14_47_w10
private theorem endpoint_14_47_w12 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 12 1 252741018474981495 = some 252741018474981495 := by decide +kernel
private theorem endpoint_14_47_p13 : receiptWindow endpoint_14_47_flag endpoint_14_47_sources 0 13 252733221506923970 = some 252741018474981495 :=
  join_receipt_window endpoint_14_47_flag endpoint_14_47_sources 0 12 1 252733221506923970 252741018474981495 252741018474981495 endpoint_14_47_p12 endpoint_14_47_w12
def endpoint_14_47 : CertifiedEndpoint :=
  ⟨⟨14, 47, 3312⟩, 252741018474981495, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_14_47_flag endpoint_14_47_sources 13 252733221506923970 252741018474981495 rfl endpoint_14_47_base endpoint_14_47_p13) (by decide)⟩
private def endpoint_14_48_flag : Flag := ⟨14, 48, 3270⟩
private def endpoint_14_48_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_48_base : receiptBase endpoint_14_48_flag endpoint_14_48_sources = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_w0 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 2 254900963027944514 = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_w2 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 2 2 254900963027944514 = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_p4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 4 254900963027944514 = some 254900963027944514 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 2 2 254900963027944514 254900963027944514 254900963027944514 endpoint_14_48_w0 endpoint_14_48_w2
private theorem endpoint_14_48_w4 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 4 2 254900963027944514 = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_p6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 6 254900963027944514 = some 254900963027944514 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 4 2 254900963027944514 254900963027944514 254900963027944514 endpoint_14_48_p4 endpoint_14_48_w4
private theorem endpoint_14_48_w6 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 6 2 254900963027944514 = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_p8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 8 254900963027944514 = some 254900963027944514 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 6 2 254900963027944514 254900963027944514 254900963027944514 endpoint_14_48_p6 endpoint_14_48_w6
private theorem endpoint_14_48_w8 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 8 2 254900963027944514 = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_p10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 10 254900963027944514 = some 254900963027944514 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 8 2 254900963027944514 254900963027944514 254900963027944514 endpoint_14_48_p8 endpoint_14_48_w8
private theorem endpoint_14_48_w10 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 10 2 254900963027944514 = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_p12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 12 254900963027944514 = some 254900963027944514 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 10 2 254900963027944514 254900963027944514 254900963027944514 endpoint_14_48_p10 endpoint_14_48_w10
private theorem endpoint_14_48_w12 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 12 1 254900963027944514 = some 254900963027944514 := by decide +kernel
private theorem endpoint_14_48_p13 : receiptWindow endpoint_14_48_flag endpoint_14_48_sources 0 13 254900963027944514 = some 254900963027944514 :=
  join_receipt_window endpoint_14_48_flag endpoint_14_48_sources 0 12 1 254900963027944514 254900963027944514 254900963027944514 endpoint_14_48_p12 endpoint_14_48_w12
def endpoint_14_48 : CertifiedEndpoint :=
  ⟨⟨14, 48, 3270⟩, 254900963027944514, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_48_flag endpoint_14_48_sources 13 254900963027944514 254900963027944514 rfl endpoint_14_48_base endpoint_14_48_p13) (by decide)⟩
private def endpoint_14_49_flag : Flag := ⟨14, 49, 3226⟩
private def endpoint_14_49_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_49_base : receiptBase endpoint_14_49_flag endpoint_14_49_sources = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_w0 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 2 256002421427823317 = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_w2 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 2 2 256002421427823317 = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_p4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 4 256002421427823317 = some 256002421427823317 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 2 2 256002421427823317 256002421427823317 256002421427823317 endpoint_14_49_w0 endpoint_14_49_w2
private theorem endpoint_14_49_w4 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 4 2 256002421427823317 = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_p6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 6 256002421427823317 = some 256002421427823317 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 4 2 256002421427823317 256002421427823317 256002421427823317 endpoint_14_49_p4 endpoint_14_49_w4
private theorem endpoint_14_49_w6 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 6 2 256002421427823317 = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_p8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 8 256002421427823317 = some 256002421427823317 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 6 2 256002421427823317 256002421427823317 256002421427823317 endpoint_14_49_p6 endpoint_14_49_w6
private theorem endpoint_14_49_w8 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 8 2 256002421427823317 = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_p10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 10 256002421427823317 = some 256002421427823317 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 8 2 256002421427823317 256002421427823317 256002421427823317 endpoint_14_49_p8 endpoint_14_49_w8
private theorem endpoint_14_49_w10 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 10 2 256002421427823317 = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_p12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 12 256002421427823317 = some 256002421427823317 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 10 2 256002421427823317 256002421427823317 256002421427823317 endpoint_14_49_p10 endpoint_14_49_w10
private theorem endpoint_14_49_w12 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 12 1 256002421427823317 = some 256002421427823317 := by decide +kernel
private theorem endpoint_14_49_p13 : receiptWindow endpoint_14_49_flag endpoint_14_49_sources 0 13 256002421427823317 = some 256002421427823317 :=
  join_receipt_window endpoint_14_49_flag endpoint_14_49_sources 0 12 1 256002421427823317 256002421427823317 256002421427823317 endpoint_14_49_p12 endpoint_14_49_w12
def endpoint_14_49 : CertifiedEndpoint :=
  ⟨⟨14, 49, 3226⟩, 256002421427823317, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_49_flag endpoint_14_49_sources 13 256002421427823317 256002421427823317 rfl endpoint_14_49_base endpoint_14_49_p13) (by decide)⟩
private def endpoint_14_50_flag : Flag := ⟨14, 50, 3181⟩
private def endpoint_14_50_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_50_base : receiptBase endpoint_14_50_flag endpoint_14_50_sources = some 256902089100495797 := by decide +kernel
private theorem endpoint_14_50_w0 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 2 256902089100495797 = some 258477121946562258 := by decide +kernel
private theorem endpoint_14_50_w2 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 2 2 258477121946562258 = some 258477121946562258 := by decide +kernel
private theorem endpoint_14_50_p4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 4 256902089100495797 = some 258477121946562258 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 2 2 256902089100495797 258477121946562258 258477121946562258 endpoint_14_50_w0 endpoint_14_50_w2
private theorem endpoint_14_50_w4 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 4 2 258477121946562258 = some 258477121946562258 := by decide +kernel
private theorem endpoint_14_50_p6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 6 256902089100495797 = some 258477121946562258 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 4 2 256902089100495797 258477121946562258 258477121946562258 endpoint_14_50_p4 endpoint_14_50_w4
private theorem endpoint_14_50_w6 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 6 2 258477121946562258 = some 258477121946562258 := by decide +kernel
private theorem endpoint_14_50_p8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 8 256902089100495797 = some 258477121946562258 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 6 2 256902089100495797 258477121946562258 258477121946562258 endpoint_14_50_p6 endpoint_14_50_w6
private theorem endpoint_14_50_w8 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 8 2 258477121946562258 = some 258477121946562258 := by decide +kernel
private theorem endpoint_14_50_p10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 10 256902089100495797 = some 258477121946562258 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 8 2 256902089100495797 258477121946562258 258477121946562258 endpoint_14_50_p8 endpoint_14_50_w8
private theorem endpoint_14_50_w10 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 10 2 258477121946562258 = some 258477121946562258 := by decide +kernel
private theorem endpoint_14_50_p12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 12 256902089100495797 = some 258477121946562258 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 10 2 256902089100495797 258477121946562258 258477121946562258 endpoint_14_50_p10 endpoint_14_50_w10
private theorem endpoint_14_50_w12 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 12 1 258477121946562258 = some 258477121946562258 := by decide +kernel
private theorem endpoint_14_50_p13 : receiptWindow endpoint_14_50_flag endpoint_14_50_sources 0 13 256902089100495797 = some 258477121946562258 :=
  join_receipt_window endpoint_14_50_flag endpoint_14_50_sources 0 12 1 256902089100495797 258477121946562258 258477121946562258 endpoint_14_50_p12 endpoint_14_50_w12
def endpoint_14_50 : CertifiedEndpoint :=
  ⟨⟨14, 50, 3181⟩, 258477121946562258, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_50_flag endpoint_14_50_sources 13 256902089100495797 258477121946562258 rfl endpoint_14_50_base endpoint_14_50_p13) (by decide)⟩
private def endpoint_14_51_flag : Flag := ⟨14, 51, 3135⟩
private def endpoint_14_51_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_14_51_base : receiptBase endpoint_14_51_flag endpoint_14_51_sources = some 257595849739037129 := by decide +kernel
private theorem endpoint_14_51_w0 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 2 257595849739037129 = some 262482303834097918 := by decide +kernel
private theorem endpoint_14_51_w2 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 2 2 262482303834097918 = some 262482303834097918 := by decide +kernel
private theorem endpoint_14_51_p4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 4 257595849739037129 = some 262482303834097918 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 2 2 257595849739037129 262482303834097918 262482303834097918 endpoint_14_51_w0 endpoint_14_51_w2
private theorem endpoint_14_51_w4 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 4 2 262482303834097918 = some 262482303834097918 := by decide +kernel
private theorem endpoint_14_51_p6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 6 257595849739037129 = some 262482303834097918 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 4 2 257595849739037129 262482303834097918 262482303834097918 endpoint_14_51_p4 endpoint_14_51_w4
private theorem endpoint_14_51_w6 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 6 2 262482303834097918 = some 262482303834097918 := by decide +kernel
private theorem endpoint_14_51_p8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 8 257595849739037129 = some 262482303834097918 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 6 2 257595849739037129 262482303834097918 262482303834097918 endpoint_14_51_p6 endpoint_14_51_w6
private theorem endpoint_14_51_w8 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 8 2 262482303834097918 = some 262482303834097918 := by decide +kernel
private theorem endpoint_14_51_p10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 10 257595849739037129 = some 262482303834097918 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 8 2 257595849739037129 262482303834097918 262482303834097918 endpoint_14_51_p8 endpoint_14_51_w8
private theorem endpoint_14_51_w10 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 10 2 262482303834097918 = some 262482303834097918 := by decide +kernel
private theorem endpoint_14_51_p12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 12 257595849739037129 = some 262482303834097918 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 10 2 257595849739037129 262482303834097918 262482303834097918 endpoint_14_51_p10 endpoint_14_51_w10
private theorem endpoint_14_51_w12 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 12 1 262482303834097918 = some 262482303834097918 := by decide +kernel
private theorem endpoint_14_51_p13 : receiptWindow endpoint_14_51_flag endpoint_14_51_sources 0 13 257595849739037129 = some 262482303834097918 :=
  join_receipt_window endpoint_14_51_flag endpoint_14_51_sources 0 12 1 257595849739037129 262482303834097918 262482303834097918 endpoint_14_51_p12 endpoint_14_51_w12
def endpoint_14_51 : CertifiedEndpoint :=
  ⟨⟨14, 51, 3135⟩, 262482303834097918, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_14_51_flag endpoint_14_51_sources 13 257595849739037129 262482303834097918 rfl endpoint_14_51_base endpoint_14_51_p13) (by decide)⟩
private def endpoint_14_52_flag : Flag := ⟨14, 52, 3087⟩
private def endpoint_14_52_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_52_base : receiptBase endpoint_14_52_flag endpoint_14_52_sources = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_w0 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 2 261679054616715835 = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_w2 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 2 2 261679054616715835 = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_p4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 4 261679054616715835 = some 261679054616715835 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 2 2 261679054616715835 261679054616715835 261679054616715835 endpoint_14_52_w0 endpoint_14_52_w2
private theorem endpoint_14_52_w4 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 4 2 261679054616715835 = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_p6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 6 261679054616715835 = some 261679054616715835 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 4 2 261679054616715835 261679054616715835 261679054616715835 endpoint_14_52_p4 endpoint_14_52_w4
private theorem endpoint_14_52_w6 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 6 2 261679054616715835 = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_p8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 8 261679054616715835 = some 261679054616715835 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 6 2 261679054616715835 261679054616715835 261679054616715835 endpoint_14_52_p6 endpoint_14_52_w6
private theorem endpoint_14_52_w8 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 8 2 261679054616715835 = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_p10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 10 261679054616715835 = some 261679054616715835 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 8 2 261679054616715835 261679054616715835 261679054616715835 endpoint_14_52_p8 endpoint_14_52_w8
private theorem endpoint_14_52_w10 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 10 2 261679054616715835 = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_p12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 12 261679054616715835 = some 261679054616715835 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 10 2 261679054616715835 261679054616715835 261679054616715835 endpoint_14_52_p10 endpoint_14_52_w10
private theorem endpoint_14_52_w12 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 12 1 261679054616715835 = some 261679054616715835 := by decide +kernel
private theorem endpoint_14_52_p13 : receiptWindow endpoint_14_52_flag endpoint_14_52_sources 0 13 261679054616715835 = some 261679054616715835 :=
  join_receipt_window endpoint_14_52_flag endpoint_14_52_sources 0 12 1 261679054616715835 261679054616715835 261679054616715835 endpoint_14_52_p12 endpoint_14_52_w12
def endpoint_14_52 : CertifiedEndpoint :=
  ⟨⟨14, 52, 3087⟩, 261679054616715835, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_52_flag endpoint_14_52_sources 13 261679054616715835 261679054616715835 rfl endpoint_14_52_base endpoint_14_52_p13) (by decide)⟩
private def endpoint_14_53_flag : Flag := ⟨14, 53, 3038⟩
private def endpoint_14_53_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_14_53_base : receiptBase endpoint_14_53_flag endpoint_14_53_sources = some 259084071504587826 := by decide +kernel
private theorem endpoint_14_53_w0 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 2 259084071504587826 = some 264150233561234844 := by decide +kernel
private theorem endpoint_14_53_w2 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 2 2 264150233561234844 = some 264150233561234844 := by decide +kernel
private theorem endpoint_14_53_p4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 4 259084071504587826 = some 264150233561234844 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 2 2 259084071504587826 264150233561234844 264150233561234844 endpoint_14_53_w0 endpoint_14_53_w2
private theorem endpoint_14_53_w4 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 4 2 264150233561234844 = some 264150233561234844 := by decide +kernel
private theorem endpoint_14_53_p6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 6 259084071504587826 = some 264150233561234844 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 4 2 259084071504587826 264150233561234844 264150233561234844 endpoint_14_53_p4 endpoint_14_53_w4
private theorem endpoint_14_53_w6 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 6 2 264150233561234844 = some 264150233561234844 := by decide +kernel
private theorem endpoint_14_53_p8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 8 259084071504587826 = some 264150233561234844 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 6 2 259084071504587826 264150233561234844 264150233561234844 endpoint_14_53_p6 endpoint_14_53_w6
private theorem endpoint_14_53_w8 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 8 2 264150233561234844 = some 264150233561234844 := by decide +kernel
private theorem endpoint_14_53_p10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 10 259084071504587826 = some 264150233561234844 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 8 2 259084071504587826 264150233561234844 264150233561234844 endpoint_14_53_p8 endpoint_14_53_w8
private theorem endpoint_14_53_w10 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 10 2 264150233561234844 = some 264150233561234844 := by decide +kernel
private theorem endpoint_14_53_p12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 12 259084071504587826 = some 264150233561234844 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 10 2 259084071504587826 264150233561234844 264150233561234844 endpoint_14_53_p10 endpoint_14_53_w10
private theorem endpoint_14_53_w12 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 12 1 264150233561234844 = some 264150233561234844 := by decide +kernel
private theorem endpoint_14_53_p13 : receiptWindow endpoint_14_53_flag endpoint_14_53_sources 0 13 259084071504587826 = some 264150233561234844 :=
  join_receipt_window endpoint_14_53_flag endpoint_14_53_sources 0 12 1 259084071504587826 264150233561234844 264150233561234844 endpoint_14_53_p12 endpoint_14_53_w12
def endpoint_14_53 : CertifiedEndpoint :=
  ⟨⟨14, 53, 3038⟩, 264150233561234844, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_14_53_flag endpoint_14_53_sources 13 259084071504587826 264150233561234844 rfl endpoint_14_53_base endpoint_14_53_p13) (by decide)⟩
private def endpoint_14_54_flag : Flag := ⟨14, 54, 2987⟩
private def endpoint_14_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_54_base : receiptBase endpoint_14_54_flag endpoint_14_54_sources = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_w0 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 2 261793072593916023 = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_w2 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 2 2 261793072593916023 = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_p4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 4 261793072593916023 = some 261793072593916023 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 2 2 261793072593916023 261793072593916023 261793072593916023 endpoint_14_54_w0 endpoint_14_54_w2
private theorem endpoint_14_54_w4 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 4 2 261793072593916023 = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_p6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 6 261793072593916023 = some 261793072593916023 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 4 2 261793072593916023 261793072593916023 261793072593916023 endpoint_14_54_p4 endpoint_14_54_w4
private theorem endpoint_14_54_w6 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 6 2 261793072593916023 = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_p8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 8 261793072593916023 = some 261793072593916023 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 6 2 261793072593916023 261793072593916023 261793072593916023 endpoint_14_54_p6 endpoint_14_54_w6
private theorem endpoint_14_54_w8 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 8 2 261793072593916023 = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_p10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 10 261793072593916023 = some 261793072593916023 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 8 2 261793072593916023 261793072593916023 261793072593916023 endpoint_14_54_p8 endpoint_14_54_w8
private theorem endpoint_14_54_w10 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 10 2 261793072593916023 = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_p12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 12 261793072593916023 = some 261793072593916023 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 10 2 261793072593916023 261793072593916023 261793072593916023 endpoint_14_54_p10 endpoint_14_54_w10
private theorem endpoint_14_54_w12 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 12 1 261793072593916023 = some 261793072593916023 := by decide +kernel
private theorem endpoint_14_54_p13 : receiptWindow endpoint_14_54_flag endpoint_14_54_sources 0 13 261793072593916023 = some 261793072593916023 :=
  join_receipt_window endpoint_14_54_flag endpoint_14_54_sources 0 12 1 261793072593916023 261793072593916023 261793072593916023 endpoint_14_54_p12 endpoint_14_54_w12
def endpoint_14_54 : CertifiedEndpoint :=
  ⟨⟨14, 54, 2987⟩, 261793072593916023, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_54_flag endpoint_14_54_sources 13 261793072593916023 261793072593916023 rfl endpoint_14_54_base endpoint_14_54_p13) (by decide)⟩
private def endpoint_14_55_flag : Flag := ⟨14, 55, 2935⟩
private def endpoint_14_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_14_55_base : receiptBase endpoint_14_55_flag endpoint_14_55_sources = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_w0 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 2 261460760064505390 = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_w2 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 2 2 261460760064505390 = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_p4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 4 261460760064505390 = some 261460760064505390 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 2 2 261460760064505390 261460760064505390 261460760064505390 endpoint_14_55_w0 endpoint_14_55_w2
private theorem endpoint_14_55_w4 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 4 2 261460760064505390 = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_p6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 6 261460760064505390 = some 261460760064505390 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 4 2 261460760064505390 261460760064505390 261460760064505390 endpoint_14_55_p4 endpoint_14_55_w4
private theorem endpoint_14_55_w6 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 6 2 261460760064505390 = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_p8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 8 261460760064505390 = some 261460760064505390 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 6 2 261460760064505390 261460760064505390 261460760064505390 endpoint_14_55_p6 endpoint_14_55_w6
private theorem endpoint_14_55_w8 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 8 2 261460760064505390 = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_p10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 10 261460760064505390 = some 261460760064505390 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 8 2 261460760064505390 261460760064505390 261460760064505390 endpoint_14_55_p8 endpoint_14_55_w8
private theorem endpoint_14_55_w10 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 10 2 261460760064505390 = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_p12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 12 261460760064505390 = some 261460760064505390 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 10 2 261460760064505390 261460760064505390 261460760064505390 endpoint_14_55_p10 endpoint_14_55_w10
private theorem endpoint_14_55_w12 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 12 1 261460760064505390 = some 261460760064505390 := by decide +kernel
private theorem endpoint_14_55_p13 : receiptWindow endpoint_14_55_flag endpoint_14_55_sources 0 13 261460760064505390 = some 261460760064505390 :=
  join_receipt_window endpoint_14_55_flag endpoint_14_55_sources 0 12 1 261460760064505390 261460760064505390 261460760064505390 endpoint_14_55_p12 endpoint_14_55_w12
def endpoint_14_55 : CertifiedEndpoint :=
  ⟨⟨14, 55, 2935⟩, 261460760064505390, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_14_55_flag endpoint_14_55_sources 13 261460760064505390 261460760064505390 rfl endpoint_14_55_base endpoint_14_55_p13) (by decide)⟩

def endpointBlock09 : List CertifiedEndpoint := [
  endpoint_12_86, endpoint_12_87, endpoint_12_88, endpoint_12_89, endpoint_13_13, endpoint_13_14, endpoint_13_15,
  endpoint_13_16, endpoint_13_17, endpoint_13_18, endpoint_13_19, endpoint_13_20, endpoint_13_21, endpoint_13_22,
  endpoint_13_23, endpoint_13_24, endpoint_13_25, endpoint_13_26, endpoint_13_27, endpoint_13_28, endpoint_13_29,
  endpoint_13_30, endpoint_13_31, endpoint_13_32, endpoint_13_33, endpoint_13_34, endpoint_13_35, endpoint_13_36,
  endpoint_13_37, endpoint_13_38, endpoint_13_39, endpoint_13_40, endpoint_13_41, endpoint_13_42, endpoint_13_43,
  endpoint_13_44, endpoint_13_45, endpoint_13_46, endpoint_13_47, endpoint_13_48, endpoint_13_49, endpoint_13_50,
  endpoint_13_51, endpoint_13_52, endpoint_13_53, endpoint_13_54, endpoint_13_55, endpoint_13_56, endpoint_13_57,
  endpoint_13_58, endpoint_13_59, endpoint_13_60, endpoint_13_61, endpoint_13_62, endpoint_13_63, endpoint_13_64,
  endpoint_13_65, endpoint_13_66, endpoint_13_67, endpoint_13_68, endpoint_13_69, endpoint_13_70, endpoint_13_71,
  endpoint_13_72, endpoint_13_73, endpoint_13_74, endpoint_13_75, endpoint_13_76, endpoint_13_77, endpoint_13_78,
  endpoint_13_79, endpoint_13_80, endpoint_13_81, endpoint_13_82, endpoint_13_83, endpoint_13_84, endpoint_13_85,
  endpoint_13_86, endpoint_13_87, endpoint_14_14, endpoint_14_15, endpoint_14_16, endpoint_14_17, endpoint_14_18,
  endpoint_14_19, endpoint_14_20, endpoint_14_21, endpoint_14_22, endpoint_14_23, endpoint_14_24, endpoint_14_25,
  endpoint_14_26, endpoint_14_27, endpoint_14_28, endpoint_14_29, endpoint_14_30, endpoint_14_31, endpoint_14_32,
  endpoint_14_33, endpoint_14_34, endpoint_14_35, endpoint_14_36, endpoint_14_37, endpoint_14_38, endpoint_14_39,
  endpoint_14_40, endpoint_14_41, endpoint_14_42, endpoint_14_43, endpoint_14_44, endpoint_14_45, endpoint_14_46,
  endpoint_14_47, endpoint_14_48, endpoint_14_49, endpoint_14_50, endpoint_14_51, endpoint_14_52, endpoint_14_53,
  endpoint_14_54, endpoint_14_55
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
