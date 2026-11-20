import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_16_79 : CertifiedEndpoint :=
  ⟨⟨16, 79, 818⟩, 218549922108064343, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_80 : CertifiedEndpoint :=
  ⟨⟨16, 80, 723⟩, 194314885294877505, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_81 : CertifiedEndpoint :=
  ⟨⟨16, 81, 624⟩, 168154366611671149, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_82 : CertifiedEndpoint :=
  ⟨⟨16, 82, 523⟩, 140608789543522273, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_83 : CertifiedEndpoint :=
  ⟨⟨16, 83, 420⟩, 111654136036406265, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_84 : CertifiedEndpoint :=
  ⟨⟨16, 84, 314⟩, 80964152221727198, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_85 : CertifiedEndpoint :=
  ⟨⟨16, 85, 205⟩, 48502811018448154, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_86 : CertifiedEndpoint :=
  ⟨⟨16, 86, 94⟩, 14544327178111734, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_17 : CertifiedEndpoint :=
  ⟨⟨17, 17, 3528⟩, 139973763541960713, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_18 : CertifiedEndpoint :=
  ⟨⟨17, 18, 3503⟩, 143856656280366280, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_19 : CertifiedEndpoint :=
  ⟨⟨17, 19, 3478⟩, 147669539298748697, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_20 : CertifiedEndpoint :=
  ⟨⟨17, 20, 3452⟩, 161186427771742400, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_21 : CertifiedEndpoint :=
  ⟨⟨17, 21, 3426⟩, 174477498438068341, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_22 : CertifiedEndpoint :=
  ⟨⟨17, 22, 3400⟩, 187542751297726520, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_23 : CertifiedEndpoint :=
  ⟨⟨17, 23, 3373⟩, 200322527726470294, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_24 : CertifiedEndpoint :=
  ⟨⟨17, 24, 3346⟩, 212867964921879598, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_25 : CertifiedEndpoint :=
  ⟨⟨17, 25, 3318⟩, 225110882833041081, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_26 : CertifiedEndpoint :=
  ⟨⟨17, 26, 3290⟩, 237110940084201386, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_27 : CertifiedEndpoint :=
  ⟨⟨17, 27, 3261⟩, 248791435197780454, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_28 : CertifiedEndpoint :=
  ⟨⟨17, 28, 3232⟩, 260220548224691636, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_17_29_flag : Flag := ⟨17, 29, 3202⟩
private def endpoint_17_29_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_29_base : receiptBase endpoint_17_29_flag endpoint_17_29_sources = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_w0 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_w2 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 2 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_p4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 4 187037240810388644 = some 187037240810388644 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 2 2 187037240810388644 187037240810388644 187037240810388644 endpoint_17_29_w0 endpoint_17_29_w2
private theorem endpoint_17_29_w4 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 4 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_p6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 6 187037240810388644 = some 187037240810388644 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 4 2 187037240810388644 187037240810388644 187037240810388644 endpoint_17_29_p4 endpoint_17_29_w4
private theorem endpoint_17_29_w6 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 6 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_p8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 8 187037240810388644 = some 187037240810388644 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 6 2 187037240810388644 187037240810388644 187037240810388644 endpoint_17_29_p6 endpoint_17_29_w6
private theorem endpoint_17_29_w8 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 8 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_p10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 10 187037240810388644 = some 187037240810388644 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 8 2 187037240810388644 187037240810388644 187037240810388644 endpoint_17_29_p8 endpoint_17_29_w8
private theorem endpoint_17_29_w10 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 10 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_p12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 12 187037240810388644 = some 187037240810388644 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 10 2 187037240810388644 187037240810388644 187037240810388644 endpoint_17_29_p10 endpoint_17_29_w10
private theorem endpoint_17_29_w12 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 12 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_p14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 14 187037240810388644 = some 187037240810388644 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 12 2 187037240810388644 187037240810388644 187037240810388644 endpoint_17_29_p12 endpoint_17_29_w12
private theorem endpoint_17_29_w14 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 14 2 187037240810388644 = some 187037240810388644 := by decide +kernel
private theorem endpoint_17_29_p16 : receiptWindow endpoint_17_29_flag endpoint_17_29_sources 0 16 187037240810388644 = some 187037240810388644 :=
  join_receipt_window endpoint_17_29_flag endpoint_17_29_sources 0 14 2 187037240810388644 187037240810388644 187037240810388644 endpoint_17_29_p14 endpoint_17_29_w14
def endpoint_17_29 : CertifiedEndpoint :=
  ⟨⟨17, 29, 3202⟩, 187037240810388644, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_29_flag endpoint_17_29_sources 16 187037240810388644 187037240810388644 rfl endpoint_17_29_base endpoint_17_29_p16) (by decide)⟩
private def endpoint_17_30_flag : Flag := ⟨17, 30, 3172⟩
private def endpoint_17_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_30_base : receiptBase endpoint_17_30_flag endpoint_17_30_sources = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_w0 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_w2 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 2 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_p4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 4 190515230858089713 = some 190515230858089713 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 2 2 190515230858089713 190515230858089713 190515230858089713 endpoint_17_30_w0 endpoint_17_30_w2
private theorem endpoint_17_30_w4 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 4 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_p6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 6 190515230858089713 = some 190515230858089713 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 4 2 190515230858089713 190515230858089713 190515230858089713 endpoint_17_30_p4 endpoint_17_30_w4
private theorem endpoint_17_30_w6 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 6 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_p8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 8 190515230858089713 = some 190515230858089713 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 6 2 190515230858089713 190515230858089713 190515230858089713 endpoint_17_30_p6 endpoint_17_30_w6
private theorem endpoint_17_30_w8 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 8 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_p10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 10 190515230858089713 = some 190515230858089713 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 8 2 190515230858089713 190515230858089713 190515230858089713 endpoint_17_30_p8 endpoint_17_30_w8
private theorem endpoint_17_30_w10 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 10 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_p12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 12 190515230858089713 = some 190515230858089713 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 10 2 190515230858089713 190515230858089713 190515230858089713 endpoint_17_30_p10 endpoint_17_30_w10
private theorem endpoint_17_30_w12 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 12 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_p14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 14 190515230858089713 = some 190515230858089713 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 12 2 190515230858089713 190515230858089713 190515230858089713 endpoint_17_30_p12 endpoint_17_30_w12
private theorem endpoint_17_30_w14 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 14 2 190515230858089713 = some 190515230858089713 := by decide +kernel
private theorem endpoint_17_30_p16 : receiptWindow endpoint_17_30_flag endpoint_17_30_sources 0 16 190515230858089713 = some 190515230858089713 :=
  join_receipt_window endpoint_17_30_flag endpoint_17_30_sources 0 14 2 190515230858089713 190515230858089713 190515230858089713 endpoint_17_30_p14 endpoint_17_30_w14
def endpoint_17_30 : CertifiedEndpoint :=
  ⟨⟨17, 30, 3172⟩, 190515230858089713, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_30_flag endpoint_17_30_sources 16 190515230858089713 190515230858089713 rfl endpoint_17_30_base endpoint_17_30_p16) (by decide)⟩
private def endpoint_17_31_flag : Flag := ⟨17, 31, 3141⟩
private def endpoint_17_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_31_base : receiptBase endpoint_17_31_flag endpoint_17_31_sources = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_w0 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_w2 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 2 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_p4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 4 193833847471858799 = some 193833847471858799 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 2 2 193833847471858799 193833847471858799 193833847471858799 endpoint_17_31_w0 endpoint_17_31_w2
private theorem endpoint_17_31_w4 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 4 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_p6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 6 193833847471858799 = some 193833847471858799 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 4 2 193833847471858799 193833847471858799 193833847471858799 endpoint_17_31_p4 endpoint_17_31_w4
private theorem endpoint_17_31_w6 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 6 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_p8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 8 193833847471858799 = some 193833847471858799 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 6 2 193833847471858799 193833847471858799 193833847471858799 endpoint_17_31_p6 endpoint_17_31_w6
private theorem endpoint_17_31_w8 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 8 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_p10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 10 193833847471858799 = some 193833847471858799 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 8 2 193833847471858799 193833847471858799 193833847471858799 endpoint_17_31_p8 endpoint_17_31_w8
private theorem endpoint_17_31_w10 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 10 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_p12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 12 193833847471858799 = some 193833847471858799 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 10 2 193833847471858799 193833847471858799 193833847471858799 endpoint_17_31_p10 endpoint_17_31_w10
private theorem endpoint_17_31_w12 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 12 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_p14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 14 193833847471858799 = some 193833847471858799 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 12 2 193833847471858799 193833847471858799 193833847471858799 endpoint_17_31_p12 endpoint_17_31_w12
private theorem endpoint_17_31_w14 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 14 2 193833847471858799 = some 193833847471858799 := by decide +kernel
private theorem endpoint_17_31_p16 : receiptWindow endpoint_17_31_flag endpoint_17_31_sources 0 16 193833847471858799 = some 193833847471858799 :=
  join_receipt_window endpoint_17_31_flag endpoint_17_31_sources 0 14 2 193833847471858799 193833847471858799 193833847471858799 endpoint_17_31_p14 endpoint_17_31_w14
def endpoint_17_31 : CertifiedEndpoint :=
  ⟨⟨17, 31, 3141⟩, 193833847471858799, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_31_flag endpoint_17_31_sources 16 193833847471858799 193833847471858799 rfl endpoint_17_31_base endpoint_17_31_p16) (by decide)⟩
private def endpoint_17_32_flag : Flag := ⟨17, 32, 3110⟩
private def endpoint_17_32_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_32_base : receiptBase endpoint_17_32_flag endpoint_17_32_sources = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_w0 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_w2 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 2 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_p4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 4 197050872520598215 = some 197050872520598215 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 2 2 197050872520598215 197050872520598215 197050872520598215 endpoint_17_32_w0 endpoint_17_32_w2
private theorem endpoint_17_32_w4 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 4 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_p6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 6 197050872520598215 = some 197050872520598215 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 4 2 197050872520598215 197050872520598215 197050872520598215 endpoint_17_32_p4 endpoint_17_32_w4
private theorem endpoint_17_32_w6 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 6 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_p8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 8 197050872520598215 = some 197050872520598215 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 6 2 197050872520598215 197050872520598215 197050872520598215 endpoint_17_32_p6 endpoint_17_32_w6
private theorem endpoint_17_32_w8 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 8 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_p10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 10 197050872520598215 = some 197050872520598215 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 8 2 197050872520598215 197050872520598215 197050872520598215 endpoint_17_32_p8 endpoint_17_32_w8
private theorem endpoint_17_32_w10 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 10 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_p12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 12 197050872520598215 = some 197050872520598215 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 10 2 197050872520598215 197050872520598215 197050872520598215 endpoint_17_32_p10 endpoint_17_32_w10
private theorem endpoint_17_32_w12 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 12 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_p14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 14 197050872520598215 = some 197050872520598215 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 12 2 197050872520598215 197050872520598215 197050872520598215 endpoint_17_32_p12 endpoint_17_32_w12
private theorem endpoint_17_32_w14 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 14 2 197050872520598215 = some 197050872520598215 := by decide +kernel
private theorem endpoint_17_32_p16 : receiptWindow endpoint_17_32_flag endpoint_17_32_sources 0 16 197050872520598215 = some 197050872520598215 :=
  join_receipt_window endpoint_17_32_flag endpoint_17_32_sources 0 14 2 197050872520598215 197050872520598215 197050872520598215 endpoint_17_32_p14 endpoint_17_32_w14
def endpoint_17_32 : CertifiedEndpoint :=
  ⟨⟨17, 32, 3110⟩, 197050872520598215, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_32_flag endpoint_17_32_sources 16 197050872520598215 197050872520598215 rfl endpoint_17_32_base endpoint_17_32_p16) (by decide)⟩
private def endpoint_17_33_flag : Flag := ⟨17, 33, 3078⟩
private def endpoint_17_33_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_33_base : receiptBase endpoint_17_33_flag endpoint_17_33_sources = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_w0 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_w2 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 2 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_p4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 4 200102074334411259 = some 200102074334411259 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 2 2 200102074334411259 200102074334411259 200102074334411259 endpoint_17_33_w0 endpoint_17_33_w2
private theorem endpoint_17_33_w4 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 4 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_p6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 6 200102074334411259 = some 200102074334411259 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 4 2 200102074334411259 200102074334411259 200102074334411259 endpoint_17_33_p4 endpoint_17_33_w4
private theorem endpoint_17_33_w6 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 6 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_p8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 8 200102074334411259 = some 200102074334411259 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 6 2 200102074334411259 200102074334411259 200102074334411259 endpoint_17_33_p6 endpoint_17_33_w6
private theorem endpoint_17_33_w8 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 8 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_p10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 10 200102074334411259 = some 200102074334411259 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 8 2 200102074334411259 200102074334411259 200102074334411259 endpoint_17_33_p8 endpoint_17_33_w8
private theorem endpoint_17_33_w10 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 10 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_p12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 12 200102074334411259 = some 200102074334411259 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 10 2 200102074334411259 200102074334411259 200102074334411259 endpoint_17_33_p10 endpoint_17_33_w10
private theorem endpoint_17_33_w12 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 12 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_p14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 14 200102074334411259 = some 200102074334411259 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 12 2 200102074334411259 200102074334411259 200102074334411259 endpoint_17_33_p12 endpoint_17_33_w12
private theorem endpoint_17_33_w14 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 14 2 200102074334411259 = some 200102074334411259 := by decide +kernel
private theorem endpoint_17_33_p16 : receiptWindow endpoint_17_33_flag endpoint_17_33_sources 0 16 200102074334411259 = some 200102074334411259 :=
  join_receipt_window endpoint_17_33_flag endpoint_17_33_sources 0 14 2 200102074334411259 200102074334411259 200102074334411259 endpoint_17_33_p14 endpoint_17_33_w14
def endpoint_17_33 : CertifiedEndpoint :=
  ⟨⟨17, 33, 3078⟩, 200102074334411259, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_33_flag endpoint_17_33_sources 16 200102074334411259 200102074334411259 rfl endpoint_17_33_base endpoint_17_33_p16) (by decide)⟩
private def endpoint_17_34_flag : Flag := ⟨17, 34, 3046⟩
private def endpoint_17_34_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_17_34_base : receiptBase endpoint_17_34_flag endpoint_17_34_sources = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_w0 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_w2 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 2 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_p4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 4 202596637685759092 = some 202596637685759092 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 2 2 202596637685759092 202596637685759092 202596637685759092 endpoint_17_34_w0 endpoint_17_34_w2
private theorem endpoint_17_34_w4 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 4 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_p6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 6 202596637685759092 = some 202596637685759092 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 4 2 202596637685759092 202596637685759092 202596637685759092 endpoint_17_34_p4 endpoint_17_34_w4
private theorem endpoint_17_34_w6 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 6 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_p8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 8 202596637685759092 = some 202596637685759092 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 6 2 202596637685759092 202596637685759092 202596637685759092 endpoint_17_34_p6 endpoint_17_34_w6
private theorem endpoint_17_34_w8 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 8 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_p10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 10 202596637685759092 = some 202596637685759092 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 8 2 202596637685759092 202596637685759092 202596637685759092 endpoint_17_34_p8 endpoint_17_34_w8
private theorem endpoint_17_34_w10 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 10 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_p12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 12 202596637685759092 = some 202596637685759092 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 10 2 202596637685759092 202596637685759092 202596637685759092 endpoint_17_34_p10 endpoint_17_34_w10
private theorem endpoint_17_34_w12 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 12 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_p14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 14 202596637685759092 = some 202596637685759092 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 12 2 202596637685759092 202596637685759092 202596637685759092 endpoint_17_34_p12 endpoint_17_34_w12
private theorem endpoint_17_34_w14 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 14 2 202596637685759092 = some 202596637685759092 := by decide +kernel
private theorem endpoint_17_34_p16 : receiptWindow endpoint_17_34_flag endpoint_17_34_sources 0 16 202596637685759092 = some 202596637685759092 :=
  join_receipt_window endpoint_17_34_flag endpoint_17_34_sources 0 14 2 202596637685759092 202596637685759092 202596637685759092 endpoint_17_34_p14 endpoint_17_34_w14
def endpoint_17_34 : CertifiedEndpoint :=
  ⟨⟨17, 34, 3046⟩, 202596637685759092, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_17_34_flag endpoint_17_34_sources 16 202596637685759092 202596637685759092 rfl endpoint_17_34_base endpoint_17_34_p16) (by decide)⟩
private def endpoint_17_35_flag : Flag := ⟨17, 35, 3013⟩
private def endpoint_17_35_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_35_base : receiptBase endpoint_17_35_flag endpoint_17_35_sources = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_w0 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_w2 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 2 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_p4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 4 205822571995062852 = some 205822571995062852 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 2 2 205822571995062852 205822571995062852 205822571995062852 endpoint_17_35_w0 endpoint_17_35_w2
private theorem endpoint_17_35_w4 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 4 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_p6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 6 205822571995062852 = some 205822571995062852 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 4 2 205822571995062852 205822571995062852 205822571995062852 endpoint_17_35_p4 endpoint_17_35_w4
private theorem endpoint_17_35_w6 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 6 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_p8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 8 205822571995062852 = some 205822571995062852 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 6 2 205822571995062852 205822571995062852 205822571995062852 endpoint_17_35_p6 endpoint_17_35_w6
private theorem endpoint_17_35_w8 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 8 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_p10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 10 205822571995062852 = some 205822571995062852 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 8 2 205822571995062852 205822571995062852 205822571995062852 endpoint_17_35_p8 endpoint_17_35_w8
private theorem endpoint_17_35_w10 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 10 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_p12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 12 205822571995062852 = some 205822571995062852 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 10 2 205822571995062852 205822571995062852 205822571995062852 endpoint_17_35_p10 endpoint_17_35_w10
private theorem endpoint_17_35_w12 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 12 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_p14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 14 205822571995062852 = some 205822571995062852 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 12 2 205822571995062852 205822571995062852 205822571995062852 endpoint_17_35_p12 endpoint_17_35_w12
private theorem endpoint_17_35_w14 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 14 2 205822571995062852 = some 205822571995062852 := by decide +kernel
private theorem endpoint_17_35_p16 : receiptWindow endpoint_17_35_flag endpoint_17_35_sources 0 16 205822571995062852 = some 205822571995062852 :=
  join_receipt_window endpoint_17_35_flag endpoint_17_35_sources 0 14 2 205822571995062852 205822571995062852 205822571995062852 endpoint_17_35_p14 endpoint_17_35_w14
def endpoint_17_35 : CertifiedEndpoint :=
  ⟨⟨17, 35, 3013⟩, 205822571995062852, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_35_flag endpoint_17_35_sources 16 205822571995062852 205822571995062852 rfl endpoint_17_35_base endpoint_17_35_p16) (by decide)⟩
private def endpoint_17_36_flag : Flag := ⟨17, 36, 2979⟩
private def endpoint_17_36_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_36_base : receiptBase endpoint_17_36_flag endpoint_17_36_sources = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_w0 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_w2 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 2 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_p4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 4 208419573920761712 = some 208419573920761712 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 2 2 208419573920761712 208419573920761712 208419573920761712 endpoint_17_36_w0 endpoint_17_36_w2
private theorem endpoint_17_36_w4 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 4 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_p6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 6 208419573920761712 = some 208419573920761712 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 4 2 208419573920761712 208419573920761712 208419573920761712 endpoint_17_36_p4 endpoint_17_36_w4
private theorem endpoint_17_36_w6 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 6 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_p8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 8 208419573920761712 = some 208419573920761712 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 6 2 208419573920761712 208419573920761712 208419573920761712 endpoint_17_36_p6 endpoint_17_36_w6
private theorem endpoint_17_36_w8 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 8 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_p10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 10 208419573920761712 = some 208419573920761712 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 8 2 208419573920761712 208419573920761712 208419573920761712 endpoint_17_36_p8 endpoint_17_36_w8
private theorem endpoint_17_36_w10 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 10 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_p12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 12 208419573920761712 = some 208419573920761712 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 10 2 208419573920761712 208419573920761712 208419573920761712 endpoint_17_36_p10 endpoint_17_36_w10
private theorem endpoint_17_36_w12 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 12 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_p14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 14 208419573920761712 = some 208419573920761712 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 12 2 208419573920761712 208419573920761712 208419573920761712 endpoint_17_36_p12 endpoint_17_36_w12
private theorem endpoint_17_36_w14 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 14 2 208419573920761712 = some 208419573920761712 := by decide +kernel
private theorem endpoint_17_36_p16 : receiptWindow endpoint_17_36_flag endpoint_17_36_sources 0 16 208419573920761712 = some 208419573920761712 :=
  join_receipt_window endpoint_17_36_flag endpoint_17_36_sources 0 14 2 208419573920761712 208419573920761712 208419573920761712 endpoint_17_36_p14 endpoint_17_36_w14
def endpoint_17_36 : CertifiedEndpoint :=
  ⟨⟨17, 36, 2979⟩, 208419573920761712, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_36_flag endpoint_17_36_sources 16 208419573920761712 208419573920761712 rfl endpoint_17_36_base endpoint_17_36_p16) (by decide)⟩
private def endpoint_17_37_flag : Flag := ⟨17, 37, 2945⟩
private def endpoint_17_37_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_37_base : receiptBase endpoint_17_37_flag endpoint_17_37_sources = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_w0 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_w2 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 2 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_p4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 4 210905309579939317 = some 210905309579939317 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 2 2 210905309579939317 210905309579939317 210905309579939317 endpoint_17_37_w0 endpoint_17_37_w2
private theorem endpoint_17_37_w4 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 4 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_p6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 6 210905309579939317 = some 210905309579939317 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 4 2 210905309579939317 210905309579939317 210905309579939317 endpoint_17_37_p4 endpoint_17_37_w4
private theorem endpoint_17_37_w6 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 6 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_p8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 8 210905309579939317 = some 210905309579939317 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 6 2 210905309579939317 210905309579939317 210905309579939317 endpoint_17_37_p6 endpoint_17_37_w6
private theorem endpoint_17_37_w8 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 8 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_p10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 10 210905309579939317 = some 210905309579939317 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 8 2 210905309579939317 210905309579939317 210905309579939317 endpoint_17_37_p8 endpoint_17_37_w8
private theorem endpoint_17_37_w10 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 10 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_p12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 12 210905309579939317 = some 210905309579939317 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 10 2 210905309579939317 210905309579939317 210905309579939317 endpoint_17_37_p10 endpoint_17_37_w10
private theorem endpoint_17_37_w12 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 12 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_p14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 14 210905309579939317 = some 210905309579939317 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 12 2 210905309579939317 210905309579939317 210905309579939317 endpoint_17_37_p12 endpoint_17_37_w12
private theorem endpoint_17_37_w14 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 14 2 210905309579939317 = some 210905309579939317 := by decide +kernel
private theorem endpoint_17_37_p16 : receiptWindow endpoint_17_37_flag endpoint_17_37_sources 0 16 210905309579939317 = some 210905309579939317 :=
  join_receipt_window endpoint_17_37_flag endpoint_17_37_sources 0 14 2 210905309579939317 210905309579939317 210905309579939317 endpoint_17_37_p14 endpoint_17_37_w14
def endpoint_17_37 : CertifiedEndpoint :=
  ⟨⟨17, 37, 2945⟩, 210905309579939317, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_37_flag endpoint_17_37_sources 16 210905309579939317 210905309579939317 rfl endpoint_17_37_base endpoint_17_37_p16) (by decide)⟩
private def endpoint_17_38_flag : Flag := ⟨17, 38, 2910⟩
private def endpoint_17_38_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_38_base : receiptBase endpoint_17_38_flag endpoint_17_38_sources = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_w0 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_w2 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 2 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_p4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 4 213207485051455976 = some 213207485051455976 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 2 2 213207485051455976 213207485051455976 213207485051455976 endpoint_17_38_w0 endpoint_17_38_w2
private theorem endpoint_17_38_w4 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 4 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_p6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 6 213207485051455976 = some 213207485051455976 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 4 2 213207485051455976 213207485051455976 213207485051455976 endpoint_17_38_p4 endpoint_17_38_w4
private theorem endpoint_17_38_w6 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 6 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_p8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 8 213207485051455976 = some 213207485051455976 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 6 2 213207485051455976 213207485051455976 213207485051455976 endpoint_17_38_p6 endpoint_17_38_w6
private theorem endpoint_17_38_w8 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 8 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_p10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 10 213207485051455976 = some 213207485051455976 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 8 2 213207485051455976 213207485051455976 213207485051455976 endpoint_17_38_p8 endpoint_17_38_w8
private theorem endpoint_17_38_w10 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 10 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_p12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 12 213207485051455976 = some 213207485051455976 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 10 2 213207485051455976 213207485051455976 213207485051455976 endpoint_17_38_p10 endpoint_17_38_w10
private theorem endpoint_17_38_w12 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 12 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_p14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 14 213207485051455976 = some 213207485051455976 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 12 2 213207485051455976 213207485051455976 213207485051455976 endpoint_17_38_p12 endpoint_17_38_w12
private theorem endpoint_17_38_w14 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 14 2 213207485051455976 = some 213207485051455976 := by decide +kernel
private theorem endpoint_17_38_p16 : receiptWindow endpoint_17_38_flag endpoint_17_38_sources 0 16 213207485051455976 = some 213207485051455976 :=
  join_receipt_window endpoint_17_38_flag endpoint_17_38_sources 0 14 2 213207485051455976 213207485051455976 213207485051455976 endpoint_17_38_p14 endpoint_17_38_w14
def endpoint_17_38 : CertifiedEndpoint :=
  ⟨⟨17, 38, 2910⟩, 213207485051455976, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_38_flag endpoint_17_38_sources 16 213207485051455976 213207485051455976 rfl endpoint_17_38_base endpoint_17_38_p16) (by decide)⟩
private def endpoint_17_39_flag : Flag := ⟨17, 39, 2874⟩
private def endpoint_17_39_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_39_base : receiptBase endpoint_17_39_flag endpoint_17_39_sources = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_w0 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_w2 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 2 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_p4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 4 215321262984565897 = some 215321262984565897 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 2 2 215321262984565897 215321262984565897 215321262984565897 endpoint_17_39_w0 endpoint_17_39_w2
private theorem endpoint_17_39_w4 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 4 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_p6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 6 215321262984565897 = some 215321262984565897 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 4 2 215321262984565897 215321262984565897 215321262984565897 endpoint_17_39_p4 endpoint_17_39_w4
private theorem endpoint_17_39_w6 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 6 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_p8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 8 215321262984565897 = some 215321262984565897 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 6 2 215321262984565897 215321262984565897 215321262984565897 endpoint_17_39_p6 endpoint_17_39_w6
private theorem endpoint_17_39_w8 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 8 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_p10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 10 215321262984565897 = some 215321262984565897 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 8 2 215321262984565897 215321262984565897 215321262984565897 endpoint_17_39_p8 endpoint_17_39_w8
private theorem endpoint_17_39_w10 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 10 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_p12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 12 215321262984565897 = some 215321262984565897 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 10 2 215321262984565897 215321262984565897 215321262984565897 endpoint_17_39_p10 endpoint_17_39_w10
private theorem endpoint_17_39_w12 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 12 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_p14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 14 215321262984565897 = some 215321262984565897 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 12 2 215321262984565897 215321262984565897 215321262984565897 endpoint_17_39_p12 endpoint_17_39_w12
private theorem endpoint_17_39_w14 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 14 2 215321262984565897 = some 215321262984565897 := by decide +kernel
private theorem endpoint_17_39_p16 : receiptWindow endpoint_17_39_flag endpoint_17_39_sources 0 16 215321262984565897 = some 215321262984565897 :=
  join_receipt_window endpoint_17_39_flag endpoint_17_39_sources 0 14 2 215321262984565897 215321262984565897 215321262984565897 endpoint_17_39_p14 endpoint_17_39_w14
def endpoint_17_39 : CertifiedEndpoint :=
  ⟨⟨17, 39, 2874⟩, 215321262984565897, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_39_flag endpoint_17_39_sources 16 215321262984565897 215321262984565897 rfl endpoint_17_39_base endpoint_17_39_p16) (by decide)⟩
private def endpoint_17_40_flag : Flag := ⟨17, 40, 2837⟩
private def endpoint_17_40_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_17_40_base : receiptBase endpoint_17_40_flag endpoint_17_40_sources = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_w0 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_w2 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 2 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_p4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 4 217241806028523288 = some 217241806028523288 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 2 2 217241806028523288 217241806028523288 217241806028523288 endpoint_17_40_w0 endpoint_17_40_w2
private theorem endpoint_17_40_w4 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 4 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_p6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 6 217241806028523288 = some 217241806028523288 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 4 2 217241806028523288 217241806028523288 217241806028523288 endpoint_17_40_p4 endpoint_17_40_w4
private theorem endpoint_17_40_w6 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 6 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_p8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 8 217241806028523288 = some 217241806028523288 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 6 2 217241806028523288 217241806028523288 217241806028523288 endpoint_17_40_p6 endpoint_17_40_w6
private theorem endpoint_17_40_w8 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 8 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_p10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 10 217241806028523288 = some 217241806028523288 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 8 2 217241806028523288 217241806028523288 217241806028523288 endpoint_17_40_p8 endpoint_17_40_w8
private theorem endpoint_17_40_w10 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 10 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_p12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 12 217241806028523288 = some 217241806028523288 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 10 2 217241806028523288 217241806028523288 217241806028523288 endpoint_17_40_p10 endpoint_17_40_w10
private theorem endpoint_17_40_w12 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 12 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_p14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 14 217241806028523288 = some 217241806028523288 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 12 2 217241806028523288 217241806028523288 217241806028523288 endpoint_17_40_p12 endpoint_17_40_w12
private theorem endpoint_17_40_w14 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 14 2 217241806028523288 = some 217241806028523288 := by decide +kernel
private theorem endpoint_17_40_p16 : receiptWindow endpoint_17_40_flag endpoint_17_40_sources 0 16 217241806028523288 = some 217241806028523288 :=
  join_receipt_window endpoint_17_40_flag endpoint_17_40_sources 0 14 2 217241806028523288 217241806028523288 217241806028523288 endpoint_17_40_p14 endpoint_17_40_w14
def endpoint_17_40 : CertifiedEndpoint :=
  ⟨⟨17, 40, 2837⟩, 217241806028523288, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_17_40_flag endpoint_17_40_sources 16 217241806028523288 217241806028523288 rfl endpoint_17_40_base endpoint_17_40_p16) (by decide)⟩
private def endpoint_17_41_flag : Flag := ⟨17, 41, 2800⟩
private def endpoint_17_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_41_base : receiptBase endpoint_17_41_flag endpoint_17_41_sources = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_w0 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_w2 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 2 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_p4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 4 219711282533635557 = some 219711282533635557 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 2 2 219711282533635557 219711282533635557 219711282533635557 endpoint_17_41_w0 endpoint_17_41_w2
private theorem endpoint_17_41_w4 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 4 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_p6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 6 219711282533635557 = some 219711282533635557 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 4 2 219711282533635557 219711282533635557 219711282533635557 endpoint_17_41_p4 endpoint_17_41_w4
private theorem endpoint_17_41_w6 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 6 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_p8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 8 219711282533635557 = some 219711282533635557 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 6 2 219711282533635557 219711282533635557 219711282533635557 endpoint_17_41_p6 endpoint_17_41_w6
private theorem endpoint_17_41_w8 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 8 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_p10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 10 219711282533635557 = some 219711282533635557 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 8 2 219711282533635557 219711282533635557 219711282533635557 endpoint_17_41_p8 endpoint_17_41_w8
private theorem endpoint_17_41_w10 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 10 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_p12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 12 219711282533635557 = some 219711282533635557 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 10 2 219711282533635557 219711282533635557 219711282533635557 endpoint_17_41_p10 endpoint_17_41_w10
private theorem endpoint_17_41_w12 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 12 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_p14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 14 219711282533635557 = some 219711282533635557 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 12 2 219711282533635557 219711282533635557 219711282533635557 endpoint_17_41_p12 endpoint_17_41_w12
private theorem endpoint_17_41_w14 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 14 2 219711282533635557 = some 219711282533635557 := by decide +kernel
private theorem endpoint_17_41_p16 : receiptWindow endpoint_17_41_flag endpoint_17_41_sources 0 16 219711282533635557 = some 219711282533635557 :=
  join_receipt_window endpoint_17_41_flag endpoint_17_41_sources 0 14 2 219711282533635557 219711282533635557 219711282533635557 endpoint_17_41_p14 endpoint_17_41_w14
def endpoint_17_41 : CertifiedEndpoint :=
  ⟨⟨17, 41, 2800⟩, 219711282533635557, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_41_flag endpoint_17_41_sources 16 219711282533635557 219711282533635557 rfl endpoint_17_41_base endpoint_17_41_p16) (by decide)⟩
private def endpoint_17_42_flag : Flag := ⟨17, 42, 2763⟩
private def endpoint_17_42_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_42_base : receiptBase endpoint_17_42_flag endpoint_17_42_sources = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_w0 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_w2 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 2 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_p4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 4 221379032551662991 = some 221379032551662991 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 2 2 221379032551662991 221379032551662991 221379032551662991 endpoint_17_42_w0 endpoint_17_42_w2
private theorem endpoint_17_42_w4 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 4 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_p6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 6 221379032551662991 = some 221379032551662991 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 4 2 221379032551662991 221379032551662991 221379032551662991 endpoint_17_42_p4 endpoint_17_42_w4
private theorem endpoint_17_42_w6 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 6 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_p8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 8 221379032551662991 = some 221379032551662991 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 6 2 221379032551662991 221379032551662991 221379032551662991 endpoint_17_42_p6 endpoint_17_42_w6
private theorem endpoint_17_42_w8 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 8 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_p10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 10 221379032551662991 = some 221379032551662991 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 8 2 221379032551662991 221379032551662991 221379032551662991 endpoint_17_42_p8 endpoint_17_42_w8
private theorem endpoint_17_42_w10 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 10 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_p12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 12 221379032551662991 = some 221379032551662991 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 10 2 221379032551662991 221379032551662991 221379032551662991 endpoint_17_42_p10 endpoint_17_42_w10
private theorem endpoint_17_42_w12 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 12 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_p14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 14 221379032551662991 = some 221379032551662991 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 12 2 221379032551662991 221379032551662991 221379032551662991 endpoint_17_42_p12 endpoint_17_42_w12
private theorem endpoint_17_42_w14 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 14 2 221379032551662991 = some 221379032551662991 := by decide +kernel
private theorem endpoint_17_42_p16 : receiptWindow endpoint_17_42_flag endpoint_17_42_sources 0 16 221379032551662991 = some 221379032551662991 :=
  join_receipt_window endpoint_17_42_flag endpoint_17_42_sources 0 14 2 221379032551662991 221379032551662991 221379032551662991 endpoint_17_42_p14 endpoint_17_42_w14
def endpoint_17_42 : CertifiedEndpoint :=
  ⟨⟨17, 42, 2763⟩, 221379032551662991, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_42_flag endpoint_17_42_sources 16 221379032551662991 221379032551662991 rfl endpoint_17_42_base endpoint_17_42_p16) (by decide)⟩
private def endpoint_17_43_flag : Flag := ⟨17, 43, 2724⟩
private def endpoint_17_43_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_43_base : receiptBase endpoint_17_43_flag endpoint_17_43_sources = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_w0 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_w2 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 2 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_p4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 4 222764421624015288 = some 222764421624015288 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 2 2 222764421624015288 222764421624015288 222764421624015288 endpoint_17_43_w0 endpoint_17_43_w2
private theorem endpoint_17_43_w4 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 4 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_p6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 6 222764421624015288 = some 222764421624015288 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 4 2 222764421624015288 222764421624015288 222764421624015288 endpoint_17_43_p4 endpoint_17_43_w4
private theorem endpoint_17_43_w6 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 6 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_p8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 8 222764421624015288 = some 222764421624015288 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 6 2 222764421624015288 222764421624015288 222764421624015288 endpoint_17_43_p6 endpoint_17_43_w6
private theorem endpoint_17_43_w8 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 8 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_p10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 10 222764421624015288 = some 222764421624015288 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 8 2 222764421624015288 222764421624015288 222764421624015288 endpoint_17_43_p8 endpoint_17_43_w8
private theorem endpoint_17_43_w10 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 10 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_p12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 12 222764421624015288 = some 222764421624015288 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 10 2 222764421624015288 222764421624015288 222764421624015288 endpoint_17_43_p10 endpoint_17_43_w10
private theorem endpoint_17_43_w12 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 12 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_p14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 14 222764421624015288 = some 222764421624015288 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 12 2 222764421624015288 222764421624015288 222764421624015288 endpoint_17_43_p12 endpoint_17_43_w12
private theorem endpoint_17_43_w14 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 14 2 222764421624015288 = some 222764421624015288 := by decide +kernel
private theorem endpoint_17_43_p16 : receiptWindow endpoint_17_43_flag endpoint_17_43_sources 0 16 222764421624015288 = some 222764421624015288 :=
  join_receipt_window endpoint_17_43_flag endpoint_17_43_sources 0 14 2 222764421624015288 222764421624015288 222764421624015288 endpoint_17_43_p14 endpoint_17_43_w14
def endpoint_17_43 : CertifiedEndpoint :=
  ⟨⟨17, 43, 2724⟩, 222764421624015288, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_43_flag endpoint_17_43_sources 16 222764421624015288 222764421624015288 rfl endpoint_17_43_base endpoint_17_43_p16) (by decide)⟩
private def endpoint_17_44_flag : Flag := ⟨17, 44, 2685⟩
private def endpoint_17_44_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_44_base : receiptBase endpoint_17_44_flag endpoint_17_44_sources = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_w0 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_w2 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 2 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_p4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 4 224022283859204432 = some 224022283859204432 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 2 2 224022283859204432 224022283859204432 224022283859204432 endpoint_17_44_w0 endpoint_17_44_w2
private theorem endpoint_17_44_w4 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 4 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_p6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 6 224022283859204432 = some 224022283859204432 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 4 2 224022283859204432 224022283859204432 224022283859204432 endpoint_17_44_p4 endpoint_17_44_w4
private theorem endpoint_17_44_w6 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 6 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_p8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 8 224022283859204432 = some 224022283859204432 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 6 2 224022283859204432 224022283859204432 224022283859204432 endpoint_17_44_p6 endpoint_17_44_w6
private theorem endpoint_17_44_w8 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 8 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_p10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 10 224022283859204432 = some 224022283859204432 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 8 2 224022283859204432 224022283859204432 224022283859204432 endpoint_17_44_p8 endpoint_17_44_w8
private theorem endpoint_17_44_w10 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 10 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_p12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 12 224022283859204432 = some 224022283859204432 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 10 2 224022283859204432 224022283859204432 224022283859204432 endpoint_17_44_p10 endpoint_17_44_w10
private theorem endpoint_17_44_w12 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 12 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_p14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 14 224022283859204432 = some 224022283859204432 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 12 2 224022283859204432 224022283859204432 224022283859204432 endpoint_17_44_p12 endpoint_17_44_w12
private theorem endpoint_17_44_w14 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 14 2 224022283859204432 = some 224022283859204432 := by decide +kernel
private theorem endpoint_17_44_p16 : receiptWindow endpoint_17_44_flag endpoint_17_44_sources 0 16 224022283859204432 = some 224022283859204432 :=
  join_receipt_window endpoint_17_44_flag endpoint_17_44_sources 0 14 2 224022283859204432 224022283859204432 224022283859204432 endpoint_17_44_p14 endpoint_17_44_w14
def endpoint_17_44 : CertifiedEndpoint :=
  ⟨⟨17, 44, 2685⟩, 224022283859204432, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_44_flag endpoint_17_44_sources 16 224022283859204432 224022283859204432 rfl endpoint_17_44_base endpoint_17_44_p16) (by decide)⟩
private def endpoint_17_45_flag : Flag := ⟨17, 45, 2644⟩
private def endpoint_17_45_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_45_base : receiptBase endpoint_17_45_flag endpoint_17_45_sources = some 224984871038625968 := by decide +kernel
private theorem endpoint_17_45_w0 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 2 224984871038625968 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_w2 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 2 2 227313029052237615 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_p4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 4 224984871038625968 = some 227313029052237615 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 2 2 224984871038625968 227313029052237615 227313029052237615 endpoint_17_45_w0 endpoint_17_45_w2
private theorem endpoint_17_45_w4 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 4 2 227313029052237615 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_p6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 6 224984871038625968 = some 227313029052237615 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 4 2 224984871038625968 227313029052237615 227313029052237615 endpoint_17_45_p4 endpoint_17_45_w4
private theorem endpoint_17_45_w6 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 6 2 227313029052237615 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_p8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 8 224984871038625968 = some 227313029052237615 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 6 2 224984871038625968 227313029052237615 227313029052237615 endpoint_17_45_p6 endpoint_17_45_w6
private theorem endpoint_17_45_w8 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 8 2 227313029052237615 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_p10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 10 224984871038625968 = some 227313029052237615 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 8 2 224984871038625968 227313029052237615 227313029052237615 endpoint_17_45_p8 endpoint_17_45_w8
private theorem endpoint_17_45_w10 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 10 2 227313029052237615 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_p12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 12 224984871038625968 = some 227313029052237615 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 10 2 224984871038625968 227313029052237615 227313029052237615 endpoint_17_45_p10 endpoint_17_45_w10
private theorem endpoint_17_45_w12 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 12 2 227313029052237615 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_p14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 14 224984871038625968 = some 227313029052237615 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 12 2 224984871038625968 227313029052237615 227313029052237615 endpoint_17_45_p12 endpoint_17_45_w12
private theorem endpoint_17_45_w14 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 14 2 227313029052237615 = some 227313029052237615 := by decide +kernel
private theorem endpoint_17_45_p16 : receiptWindow endpoint_17_45_flag endpoint_17_45_sources 0 16 224984871038625968 = some 227313029052237615 :=
  join_receipt_window endpoint_17_45_flag endpoint_17_45_sources 0 14 2 224984871038625968 227313029052237615 227313029052237615 endpoint_17_45_p14 endpoint_17_45_w14
def endpoint_17_45 : CertifiedEndpoint :=
  ⟨⟨17, 45, 2644⟩, 227313029052237615, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_45_flag endpoint_17_45_sources 16 224984871038625968 227313029052237615 rfl endpoint_17_45_base endpoint_17_45_p16) (by decide)⟩
private def endpoint_17_46_flag : Flag := ⟨17, 46, 2603⟩
private def endpoint_17_46_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_46_base : receiptBase endpoint_17_46_flag endpoint_17_46_sources = some 225813474325838114 := by decide +kernel
private theorem endpoint_17_46_w0 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 2 225813474325838114 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_w2 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 2 2 231689794512002630 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_p4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 4 225813474325838114 = some 231689794512002630 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 2 2 225813474325838114 231689794512002630 231689794512002630 endpoint_17_46_w0 endpoint_17_46_w2
private theorem endpoint_17_46_w4 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 4 2 231689794512002630 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_p6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 6 225813474325838114 = some 231689794512002630 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 4 2 225813474325838114 231689794512002630 231689794512002630 endpoint_17_46_p4 endpoint_17_46_w4
private theorem endpoint_17_46_w6 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 6 2 231689794512002630 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_p8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 8 225813474325838114 = some 231689794512002630 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 6 2 225813474325838114 231689794512002630 231689794512002630 endpoint_17_46_p6 endpoint_17_46_w6
private theorem endpoint_17_46_w8 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 8 2 231689794512002630 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_p10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 10 225813474325838114 = some 231689794512002630 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 8 2 225813474325838114 231689794512002630 231689794512002630 endpoint_17_46_p8 endpoint_17_46_w8
private theorem endpoint_17_46_w10 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 10 2 231689794512002630 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_p12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 12 225813474325838114 = some 231689794512002630 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 10 2 225813474325838114 231689794512002630 231689794512002630 endpoint_17_46_p10 endpoint_17_46_w10
private theorem endpoint_17_46_w12 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 12 2 231689794512002630 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_p14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 14 225813474325838114 = some 231689794512002630 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 12 2 225813474325838114 231689794512002630 231689794512002630 endpoint_17_46_p12 endpoint_17_46_w12
private theorem endpoint_17_46_w14 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 14 2 231689794512002630 = some 231689794512002630 := by decide +kernel
private theorem endpoint_17_46_p16 : receiptWindow endpoint_17_46_flag endpoint_17_46_sources 0 16 225813474325838114 = some 231689794512002630 :=
  join_receipt_window endpoint_17_46_flag endpoint_17_46_sources 0 14 2 225813474325838114 231689794512002630 231689794512002630 endpoint_17_46_p14 endpoint_17_46_w14
def endpoint_17_46 : CertifiedEndpoint :=
  ⟨⟨17, 46, 2603⟩, 231689794512002630, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_46_flag endpoint_17_46_sources 16 225813474325838114 231689794512002630 rfl endpoint_17_46_base endpoint_17_46_p16) (by decide)⟩
private def endpoint_17_47_flag : Flag := ⟨17, 47, 2561⟩
private def endpoint_17_47_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_47_base : receiptBase endpoint_17_47_flag endpoint_17_47_sources = some 226420991084015526 := by decide +kernel
private theorem endpoint_17_47_w0 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 2 226420991084015526 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_w2 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 2 2 235905803882846076 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_p4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 4 226420991084015526 = some 235905803882846076 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 2 2 226420991084015526 235905803882846076 235905803882846076 endpoint_17_47_w0 endpoint_17_47_w2
private theorem endpoint_17_47_w4 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 4 2 235905803882846076 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_p6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 6 226420991084015526 = some 235905803882846076 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 4 2 226420991084015526 235905803882846076 235905803882846076 endpoint_17_47_p4 endpoint_17_47_w4
private theorem endpoint_17_47_w6 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 6 2 235905803882846076 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_p8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 8 226420991084015526 = some 235905803882846076 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 6 2 226420991084015526 235905803882846076 235905803882846076 endpoint_17_47_p6 endpoint_17_47_w6
private theorem endpoint_17_47_w8 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 8 2 235905803882846076 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_p10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 10 226420991084015526 = some 235905803882846076 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 8 2 226420991084015526 235905803882846076 235905803882846076 endpoint_17_47_p8 endpoint_17_47_w8
private theorem endpoint_17_47_w10 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 10 2 235905803882846076 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_p12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 12 226420991084015526 = some 235905803882846076 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 10 2 226420991084015526 235905803882846076 235905803882846076 endpoint_17_47_p10 endpoint_17_47_w10
private theorem endpoint_17_47_w12 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 12 2 235905803882846076 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_p14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 14 226420991084015526 = some 235905803882846076 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 12 2 226420991084015526 235905803882846076 235905803882846076 endpoint_17_47_p12 endpoint_17_47_w12
private theorem endpoint_17_47_w14 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 14 2 235905803882846076 = some 235905803882846076 := by decide +kernel
private theorem endpoint_17_47_p16 : receiptWindow endpoint_17_47_flag endpoint_17_47_sources 0 16 226420991084015526 = some 235905803882846076 :=
  join_receipt_window endpoint_17_47_flag endpoint_17_47_sources 0 14 2 226420991084015526 235905803882846076 235905803882846076 endpoint_17_47_p14 endpoint_17_47_w14
def endpoint_17_47 : CertifiedEndpoint :=
  ⟨⟨17, 47, 2561⟩, 235905803882846076, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_47_flag endpoint_17_47_sources 16 226420991084015526 235905803882846076 rfl endpoint_17_47_base endpoint_17_47_p16) (by decide)⟩
private def endpoint_17_48_flag : Flag := ⟨17, 48, 2519⟩
private def endpoint_17_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_17_48_base : receiptBase endpoint_17_48_flag endpoint_17_48_sources = some 226891295422460430 := by decide +kernel
private theorem endpoint_17_48_w0 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 2 226891295422460430 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_w2 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 2 2 240007409636265584 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_p4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 4 226891295422460430 = some 240007409636265584 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 2 2 226891295422460430 240007409636265584 240007409636265584 endpoint_17_48_w0 endpoint_17_48_w2
private theorem endpoint_17_48_w4 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 4 2 240007409636265584 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_p6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 6 226891295422460430 = some 240007409636265584 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 4 2 226891295422460430 240007409636265584 240007409636265584 endpoint_17_48_p4 endpoint_17_48_w4
private theorem endpoint_17_48_w6 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 6 2 240007409636265584 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_p8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 8 226891295422460430 = some 240007409636265584 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 6 2 226891295422460430 240007409636265584 240007409636265584 endpoint_17_48_p6 endpoint_17_48_w6
private theorem endpoint_17_48_w8 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 8 2 240007409636265584 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_p10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 10 226891295422460430 = some 240007409636265584 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 8 2 226891295422460430 240007409636265584 240007409636265584 endpoint_17_48_p8 endpoint_17_48_w8
private theorem endpoint_17_48_w10 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 10 2 240007409636265584 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_p12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 12 226891295422460430 = some 240007409636265584 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 10 2 226891295422460430 240007409636265584 240007409636265584 endpoint_17_48_p10 endpoint_17_48_w10
private theorem endpoint_17_48_w12 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 12 2 240007409636265584 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_p14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 14 226891295422460430 = some 240007409636265584 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 12 2 226891295422460430 240007409636265584 240007409636265584 endpoint_17_48_p12 endpoint_17_48_w12
private theorem endpoint_17_48_w14 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 14 2 240007409636265584 = some 240007409636265584 := by decide +kernel
private theorem endpoint_17_48_p16 : receiptWindow endpoint_17_48_flag endpoint_17_48_sources 0 16 226891295422460430 = some 240007409636265584 :=
  join_receipt_window endpoint_17_48_flag endpoint_17_48_sources 0 14 2 226891295422460430 240007409636265584 240007409636265584 endpoint_17_48_p14 endpoint_17_48_w14
def endpoint_17_48 : CertifiedEndpoint :=
  ⟨⟨17, 48, 2519⟩, 240007409636265584, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_17_48_flag endpoint_17_48_sources 16 226891295422460430 240007409636265584 rfl endpoint_17_48_base endpoint_17_48_p16) (by decide)⟩
private def endpoint_17_49_flag : Flag := ⟨17, 49, 2475⟩
private def endpoint_17_49_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_17_49_base : receiptBase endpoint_17_49_flag endpoint_17_49_sources = some 232636254148204111 := by decide +kernel
private theorem endpoint_17_49_w0 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 2 232636254148204111 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_w2 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 2 2 236625397694666184 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_p4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 4 232636254148204111 = some 236625397694666184 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 2 2 232636254148204111 236625397694666184 236625397694666184 endpoint_17_49_w0 endpoint_17_49_w2
private theorem endpoint_17_49_w4 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 4 2 236625397694666184 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_p6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 6 232636254148204111 = some 236625397694666184 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 4 2 232636254148204111 236625397694666184 236625397694666184 endpoint_17_49_p4 endpoint_17_49_w4
private theorem endpoint_17_49_w6 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 6 2 236625397694666184 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_p8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 8 232636254148204111 = some 236625397694666184 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 6 2 232636254148204111 236625397694666184 236625397694666184 endpoint_17_49_p6 endpoint_17_49_w6
private theorem endpoint_17_49_w8 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 8 2 236625397694666184 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_p10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 10 232636254148204111 = some 236625397694666184 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 8 2 232636254148204111 236625397694666184 236625397694666184 endpoint_17_49_p8 endpoint_17_49_w8
private theorem endpoint_17_49_w10 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 10 2 236625397694666184 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_p12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 12 232636254148204111 = some 236625397694666184 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 10 2 232636254148204111 236625397694666184 236625397694666184 endpoint_17_49_p10 endpoint_17_49_w10
private theorem endpoint_17_49_w12 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 12 2 236625397694666184 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_p14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 14 232636254148204111 = some 236625397694666184 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 12 2 232636254148204111 236625397694666184 236625397694666184 endpoint_17_49_p12 endpoint_17_49_w12
private theorem endpoint_17_49_w14 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 14 2 236625397694666184 = some 236625397694666184 := by decide +kernel
private theorem endpoint_17_49_p16 : receiptWindow endpoint_17_49_flag endpoint_17_49_sources 0 16 232636254148204111 = some 236625397694666184 :=
  join_receipt_window endpoint_17_49_flag endpoint_17_49_sources 0 14 2 232636254148204111 236625397694666184 236625397694666184 endpoint_17_49_p14 endpoint_17_49_w14
def endpoint_17_49 : CertifiedEndpoint :=
  ⟨⟨17, 49, 2475⟩, 236625397694666184, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_17_49_flag endpoint_17_49_sources 16 232636254148204111 236625397694666184 rfl endpoint_17_49_base endpoint_17_49_p16) (by decide)⟩
private def endpoint_17_50_flag : Flag := ⟨17, 50, 2430⟩
private def endpoint_17_50_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_50_base : receiptBase endpoint_17_50_flag endpoint_17_50_sources = some 232940261137221195 := by decide +kernel
private theorem endpoint_17_50_w0 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 2 232940261137221195 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_w2 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 2 2 235553216741278356 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_p4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 4 232940261137221195 = some 235553216741278356 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 2 2 232940261137221195 235553216741278356 235553216741278356 endpoint_17_50_w0 endpoint_17_50_w2
private theorem endpoint_17_50_w4 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 4 2 235553216741278356 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_p6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 6 232940261137221195 = some 235553216741278356 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 4 2 232940261137221195 235553216741278356 235553216741278356 endpoint_17_50_p4 endpoint_17_50_w4
private theorem endpoint_17_50_w6 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 6 2 235553216741278356 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_p8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 8 232940261137221195 = some 235553216741278356 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 6 2 232940261137221195 235553216741278356 235553216741278356 endpoint_17_50_p6 endpoint_17_50_w6
private theorem endpoint_17_50_w8 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 8 2 235553216741278356 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_p10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 10 232940261137221195 = some 235553216741278356 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 8 2 232940261137221195 235553216741278356 235553216741278356 endpoint_17_50_p8 endpoint_17_50_w8
private theorem endpoint_17_50_w10 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 10 2 235553216741278356 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_p12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 12 232940261137221195 = some 235553216741278356 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 10 2 232940261137221195 235553216741278356 235553216741278356 endpoint_17_50_p10 endpoint_17_50_w10
private theorem endpoint_17_50_w12 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 12 2 235553216741278356 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_p14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 14 232940261137221195 = some 235553216741278356 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 12 2 232940261137221195 235553216741278356 235553216741278356 endpoint_17_50_p12 endpoint_17_50_w12
private theorem endpoint_17_50_w14 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 14 2 235553216741278356 = some 235553216741278356 := by decide +kernel
private theorem endpoint_17_50_p16 : receiptWindow endpoint_17_50_flag endpoint_17_50_sources 0 16 232940261137221195 = some 235553216741278356 :=
  join_receipt_window endpoint_17_50_flag endpoint_17_50_sources 0 14 2 232940261137221195 235553216741278356 235553216741278356 endpoint_17_50_p14 endpoint_17_50_w14
def endpoint_17_50 : CertifiedEndpoint :=
  ⟨⟨17, 50, 2430⟩, 235553216741278356, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_50_flag endpoint_17_50_sources 16 232940261137221195 235553216741278356 rfl endpoint_17_50_base endpoint_17_50_p16) (by decide)⟩
private def endpoint_17_51_flag : Flag := ⟨17, 51, 2385⟩
private def endpoint_17_51_sources : Sources := ⟨contact11, contact11, contact29⟩
private theorem endpoint_17_51_base : receiptBase endpoint_17_51_flag endpoint_17_51_sources = some 232734201925014349 := by decide +kernel
private theorem endpoint_17_51_w0 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 2 232734201925014349 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_w2 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 2 2 238846566724773910 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_p4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 4 232734201925014349 = some 238846566724773910 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 2 2 232734201925014349 238846566724773910 238846566724773910 endpoint_17_51_w0 endpoint_17_51_w2
private theorem endpoint_17_51_w4 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 4 2 238846566724773910 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_p6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 6 232734201925014349 = some 238846566724773910 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 4 2 232734201925014349 238846566724773910 238846566724773910 endpoint_17_51_p4 endpoint_17_51_w4
private theorem endpoint_17_51_w6 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 6 2 238846566724773910 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_p8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 8 232734201925014349 = some 238846566724773910 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 6 2 232734201925014349 238846566724773910 238846566724773910 endpoint_17_51_p6 endpoint_17_51_w6
private theorem endpoint_17_51_w8 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 8 2 238846566724773910 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_p10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 10 232734201925014349 = some 238846566724773910 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 8 2 232734201925014349 238846566724773910 238846566724773910 endpoint_17_51_p8 endpoint_17_51_w8
private theorem endpoint_17_51_w10 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 10 2 238846566724773910 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_p12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 12 232734201925014349 = some 238846566724773910 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 10 2 232734201925014349 238846566724773910 238846566724773910 endpoint_17_51_p10 endpoint_17_51_w10
private theorem endpoint_17_51_w12 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 12 2 238846566724773910 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_p14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 14 232734201925014349 = some 238846566724773910 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 12 2 232734201925014349 238846566724773910 238846566724773910 endpoint_17_51_p12 endpoint_17_51_w12
private theorem endpoint_17_51_w14 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 14 2 238846566724773910 = some 238846566724773910 := by decide +kernel
private theorem endpoint_17_51_p16 : receiptWindow endpoint_17_51_flag endpoint_17_51_sources 0 16 232734201925014349 = some 238846566724773910 :=
  join_receipt_window endpoint_17_51_flag endpoint_17_51_sources 0 14 2 232734201925014349 238846566724773910 238846566724773910 endpoint_17_51_p14 endpoint_17_51_w14
def endpoint_17_51 : CertifiedEndpoint :=
  ⟨⟨17, 51, 2385⟩, 238846566724773910, .terminal ⟨contact11, contact11, contact29⟩ (finish_receipt_window endpoint_17_51_flag endpoint_17_51_sources 16 232734201925014349 238846566724773910 rfl endpoint_17_51_base endpoint_17_51_p16) (by decide)⟩
private def endpoint_17_52_flag : Flag := ⟨17, 52, 2338⟩
private def endpoint_17_52_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_52_base : receiptBase endpoint_17_52_flag endpoint_17_52_sources = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_w0 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_w2 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 2 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_p4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 4 232972019505731199 = some 232972019505731199 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 2 2 232972019505731199 232972019505731199 232972019505731199 endpoint_17_52_w0 endpoint_17_52_w2
private theorem endpoint_17_52_w4 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 4 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_p6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 6 232972019505731199 = some 232972019505731199 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 4 2 232972019505731199 232972019505731199 232972019505731199 endpoint_17_52_p4 endpoint_17_52_w4
private theorem endpoint_17_52_w6 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 6 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_p8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 8 232972019505731199 = some 232972019505731199 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 6 2 232972019505731199 232972019505731199 232972019505731199 endpoint_17_52_p6 endpoint_17_52_w6
private theorem endpoint_17_52_w8 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 8 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_p10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 10 232972019505731199 = some 232972019505731199 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 8 2 232972019505731199 232972019505731199 232972019505731199 endpoint_17_52_p8 endpoint_17_52_w8
private theorem endpoint_17_52_w10 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 10 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_p12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 12 232972019505731199 = some 232972019505731199 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 10 2 232972019505731199 232972019505731199 232972019505731199 endpoint_17_52_p10 endpoint_17_52_w10
private theorem endpoint_17_52_w12 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 12 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_p14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 14 232972019505731199 = some 232972019505731199 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 12 2 232972019505731199 232972019505731199 232972019505731199 endpoint_17_52_p12 endpoint_17_52_w12
private theorem endpoint_17_52_w14 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 14 2 232972019505731199 = some 232972019505731199 := by decide +kernel
private theorem endpoint_17_52_p16 : receiptWindow endpoint_17_52_flag endpoint_17_52_sources 0 16 232972019505731199 = some 232972019505731199 :=
  join_receipt_window endpoint_17_52_flag endpoint_17_52_sources 0 14 2 232972019505731199 232972019505731199 232972019505731199 endpoint_17_52_p14 endpoint_17_52_w14
def endpoint_17_52 : CertifiedEndpoint :=
  ⟨⟨17, 52, 2338⟩, 232972019505731199, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_52_flag endpoint_17_52_sources 16 232972019505731199 232972019505731199 rfl endpoint_17_52_base endpoint_17_52_p16) (by decide)⟩
private def endpoint_17_53_flag : Flag := ⟨17, 53, 2291⟩
private def endpoint_17_53_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_17_53_base : receiptBase endpoint_17_53_flag endpoint_17_53_sources = some 232268237933877134 := by decide +kernel
private theorem endpoint_17_53_w0 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 2 232268237933877134 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_w2 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 2 2 232725335243400183 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_p4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 4 232268237933877134 = some 232725335243400183 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 2 2 232268237933877134 232725335243400183 232725335243400183 endpoint_17_53_w0 endpoint_17_53_w2
private theorem endpoint_17_53_w4 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 4 2 232725335243400183 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_p6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 6 232268237933877134 = some 232725335243400183 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 4 2 232268237933877134 232725335243400183 232725335243400183 endpoint_17_53_p4 endpoint_17_53_w4
private theorem endpoint_17_53_w6 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 6 2 232725335243400183 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_p8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 8 232268237933877134 = some 232725335243400183 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 6 2 232268237933877134 232725335243400183 232725335243400183 endpoint_17_53_p6 endpoint_17_53_w6
private theorem endpoint_17_53_w8 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 8 2 232725335243400183 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_p10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 10 232268237933877134 = some 232725335243400183 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 8 2 232268237933877134 232725335243400183 232725335243400183 endpoint_17_53_p8 endpoint_17_53_w8
private theorem endpoint_17_53_w10 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 10 2 232725335243400183 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_p12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 12 232268237933877134 = some 232725335243400183 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 10 2 232268237933877134 232725335243400183 232725335243400183 endpoint_17_53_p10 endpoint_17_53_w10
private theorem endpoint_17_53_w12 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 12 2 232725335243400183 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_p14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 14 232268237933877134 = some 232725335243400183 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 12 2 232268237933877134 232725335243400183 232725335243400183 endpoint_17_53_p12 endpoint_17_53_w12
private theorem endpoint_17_53_w14 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 14 2 232725335243400183 = some 232725335243400183 := by decide +kernel
private theorem endpoint_17_53_p16 : receiptWindow endpoint_17_53_flag endpoint_17_53_sources 0 16 232268237933877134 = some 232725335243400183 :=
  join_receipt_window endpoint_17_53_flag endpoint_17_53_sources 0 14 2 232268237933877134 232725335243400183 232725335243400183 endpoint_17_53_p14 endpoint_17_53_w14
def endpoint_17_53 : CertifiedEndpoint :=
  ⟨⟨17, 53, 2291⟩, 232725335243400183, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_17_53_flag endpoint_17_53_sources 16 232268237933877134 232725335243400183 rfl endpoint_17_53_base endpoint_17_53_p16) (by decide)⟩
private def endpoint_17_54_flag : Flag := ⟨17, 54, 2242⟩
private def endpoint_17_54_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_54_base : receiptBase endpoint_17_54_flag endpoint_17_54_sources = some 231275087865691810 := by decide +kernel
private theorem endpoint_17_54_w0 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 2 231275087865691810 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_w2 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 2 2 235136897744292948 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_p4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 4 231275087865691810 = some 235136897744292948 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 2 2 231275087865691810 235136897744292948 235136897744292948 endpoint_17_54_w0 endpoint_17_54_w2
private theorem endpoint_17_54_w4 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 4 2 235136897744292948 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_p6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 6 231275087865691810 = some 235136897744292948 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 4 2 231275087865691810 235136897744292948 235136897744292948 endpoint_17_54_p4 endpoint_17_54_w4
private theorem endpoint_17_54_w6 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 6 2 235136897744292948 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_p8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 8 231275087865691810 = some 235136897744292948 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 6 2 231275087865691810 235136897744292948 235136897744292948 endpoint_17_54_p6 endpoint_17_54_w6
private theorem endpoint_17_54_w8 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 8 2 235136897744292948 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_p10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 10 231275087865691810 = some 235136897744292948 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 8 2 231275087865691810 235136897744292948 235136897744292948 endpoint_17_54_p8 endpoint_17_54_w8
private theorem endpoint_17_54_w10 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 10 2 235136897744292948 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_p12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 12 231275087865691810 = some 235136897744292948 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 10 2 231275087865691810 235136897744292948 235136897744292948 endpoint_17_54_p10 endpoint_17_54_w10
private theorem endpoint_17_54_w12 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 12 2 235136897744292948 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_p14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 14 231275087865691810 = some 235136897744292948 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 12 2 231275087865691810 235136897744292948 235136897744292948 endpoint_17_54_p12 endpoint_17_54_w12
private theorem endpoint_17_54_w14 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 14 2 235136897744292948 = some 235136897744292948 := by decide +kernel
private theorem endpoint_17_54_p16 : receiptWindow endpoint_17_54_flag endpoint_17_54_sources 0 16 231275087865691810 = some 235136897744292948 :=
  join_receipt_window endpoint_17_54_flag endpoint_17_54_sources 0 14 2 231275087865691810 235136897744292948 235136897744292948 endpoint_17_54_p14 endpoint_17_54_w14
def endpoint_17_54 : CertifiedEndpoint :=
  ⟨⟨17, 54, 2242⟩, 235136897744292948, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_54_flag endpoint_17_54_sources 16 231275087865691810 235136897744292948 rfl endpoint_17_54_base endpoint_17_54_p16) (by decide)⟩
private def endpoint_17_55_flag : Flag := ⟨17, 55, 2192⟩
private def endpoint_17_55_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_17_55_base : receiptBase endpoint_17_55_flag endpoint_17_55_sources = some 229918304829105633 := by decide +kernel
private theorem endpoint_17_55_w0 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 2 229918304829105633 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_w2 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 2 2 237356161125287048 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_p4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 4 229918304829105633 = some 237356161125287048 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 2 2 229918304829105633 237356161125287048 237356161125287048 endpoint_17_55_w0 endpoint_17_55_w2
private theorem endpoint_17_55_w4 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 4 2 237356161125287048 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_p6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 6 229918304829105633 = some 237356161125287048 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 4 2 229918304829105633 237356161125287048 237356161125287048 endpoint_17_55_p4 endpoint_17_55_w4
private theorem endpoint_17_55_w6 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 6 2 237356161125287048 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_p8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 8 229918304829105633 = some 237356161125287048 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 6 2 229918304829105633 237356161125287048 237356161125287048 endpoint_17_55_p6 endpoint_17_55_w6
private theorem endpoint_17_55_w8 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 8 2 237356161125287048 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_p10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 10 229918304829105633 = some 237356161125287048 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 8 2 229918304829105633 237356161125287048 237356161125287048 endpoint_17_55_p8 endpoint_17_55_w8
private theorem endpoint_17_55_w10 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 10 2 237356161125287048 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_p12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 12 229918304829105633 = some 237356161125287048 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 10 2 229918304829105633 237356161125287048 237356161125287048 endpoint_17_55_p10 endpoint_17_55_w10
private theorem endpoint_17_55_w12 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 12 2 237356161125287048 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_p14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 14 229918304829105633 = some 237356161125287048 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 12 2 229918304829105633 237356161125287048 237356161125287048 endpoint_17_55_p12 endpoint_17_55_w12
private theorem endpoint_17_55_w14 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 14 2 237356161125287048 = some 237356161125287048 := by decide +kernel
private theorem endpoint_17_55_p16 : receiptWindow endpoint_17_55_flag endpoint_17_55_sources 0 16 229918304829105633 = some 237356161125287048 :=
  join_receipt_window endpoint_17_55_flag endpoint_17_55_sources 0 14 2 229918304829105633 237356161125287048 237356161125287048 endpoint_17_55_p14 endpoint_17_55_w14
def endpoint_17_55 : CertifiedEndpoint :=
  ⟨⟨17, 55, 2192⟩, 237356161125287048, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_17_55_flag endpoint_17_55_sources 16 229918304829105633 237356161125287048 rfl endpoint_17_55_base endpoint_17_55_p16) (by decide)⟩
private def endpoint_17_56_flag : Flag := ⟨17, 56, 2141⟩
private def endpoint_17_56_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_56_base : receiptBase endpoint_17_56_flag endpoint_17_56_sources = some 229362958161651510 := by decide +kernel
private theorem endpoint_17_56_w0 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 2 229362958161651510 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_w2 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 2 2 232969814785624728 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_p4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 4 229362958161651510 = some 232969814785624728 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 2 2 229362958161651510 232969814785624728 232969814785624728 endpoint_17_56_w0 endpoint_17_56_w2
private theorem endpoint_17_56_w4 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 4 2 232969814785624728 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_p6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 6 229362958161651510 = some 232969814785624728 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 4 2 229362958161651510 232969814785624728 232969814785624728 endpoint_17_56_p4 endpoint_17_56_w4
private theorem endpoint_17_56_w6 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 6 2 232969814785624728 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_p8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 8 229362958161651510 = some 232969814785624728 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 6 2 229362958161651510 232969814785624728 232969814785624728 endpoint_17_56_p6 endpoint_17_56_w6
private theorem endpoint_17_56_w8 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 8 2 232969814785624728 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_p10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 10 229362958161651510 = some 232969814785624728 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 8 2 229362958161651510 232969814785624728 232969814785624728 endpoint_17_56_p8 endpoint_17_56_w8
private theorem endpoint_17_56_w10 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 10 2 232969814785624728 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_p12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 12 229362958161651510 = some 232969814785624728 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 10 2 229362958161651510 232969814785624728 232969814785624728 endpoint_17_56_p10 endpoint_17_56_w10
private theorem endpoint_17_56_w12 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 12 2 232969814785624728 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_p14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 14 229362958161651510 = some 232969814785624728 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 12 2 229362958161651510 232969814785624728 232969814785624728 endpoint_17_56_p12 endpoint_17_56_w12
private theorem endpoint_17_56_w14 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 14 2 232969814785624728 = some 232969814785624728 := by decide +kernel
private theorem endpoint_17_56_p16 : receiptWindow endpoint_17_56_flag endpoint_17_56_sources 0 16 229362958161651510 = some 232969814785624728 :=
  join_receipt_window endpoint_17_56_flag endpoint_17_56_sources 0 14 2 229362958161651510 232969814785624728 232969814785624728 endpoint_17_56_p14 endpoint_17_56_w14
def endpoint_17_56 : CertifiedEndpoint :=
  ⟨⟨17, 56, 2141⟩, 232969814785624728, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_56_flag endpoint_17_56_sources 16 229362958161651510 232969814785624728 rfl endpoint_17_56_base endpoint_17_56_p16) (by decide)⟩
private def endpoint_17_57_flag : Flag := ⟨17, 57, 2089⟩
private def endpoint_17_57_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_57_base : receiptBase endpoint_17_57_flag endpoint_17_57_sources = some 227442554160624271 := by decide +kernel
private theorem endpoint_17_57_w0 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 2 227442554160624271 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_w2 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 2 2 234655526771822214 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_p4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 4 227442554160624271 = some 234655526771822214 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 2 2 227442554160624271 234655526771822214 234655526771822214 endpoint_17_57_w0 endpoint_17_57_w2
private theorem endpoint_17_57_w4 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 4 2 234655526771822214 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_p6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 6 227442554160624271 = some 234655526771822214 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 4 2 227442554160624271 234655526771822214 234655526771822214 endpoint_17_57_p4 endpoint_17_57_w4
private theorem endpoint_17_57_w6 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 6 2 234655526771822214 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_p8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 8 227442554160624271 = some 234655526771822214 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 6 2 227442554160624271 234655526771822214 234655526771822214 endpoint_17_57_p6 endpoint_17_57_w6
private theorem endpoint_17_57_w8 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 8 2 234655526771822214 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_p10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 10 227442554160624271 = some 234655526771822214 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 8 2 227442554160624271 234655526771822214 234655526771822214 endpoint_17_57_p8 endpoint_17_57_w8
private theorem endpoint_17_57_w10 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 10 2 234655526771822214 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_p12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 12 227442554160624271 = some 234655526771822214 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 10 2 227442554160624271 234655526771822214 234655526771822214 endpoint_17_57_p10 endpoint_17_57_w10
private theorem endpoint_17_57_w12 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 12 2 234655526771822214 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_p14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 14 227442554160624271 = some 234655526771822214 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 12 2 227442554160624271 234655526771822214 234655526771822214 endpoint_17_57_p12 endpoint_17_57_w12
private theorem endpoint_17_57_w14 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 14 2 234655526771822214 = some 234655526771822214 := by decide +kernel
private theorem endpoint_17_57_p16 : receiptWindow endpoint_17_57_flag endpoint_17_57_sources 0 16 227442554160624271 = some 234655526771822214 :=
  join_receipt_window endpoint_17_57_flag endpoint_17_57_sources 0 14 2 227442554160624271 234655526771822214 234655526771822214 endpoint_17_57_p14 endpoint_17_57_w14
def endpoint_17_57 : CertifiedEndpoint :=
  ⟨⟨17, 57, 2089⟩, 234655526771822214, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_57_flag endpoint_17_57_sources 16 227442554160624271 234655526771822214 rfl endpoint_17_57_base endpoint_17_57_p16) (by decide)⟩
private def endpoint_17_58_flag : Flag := ⟨17, 58, 2036⟩
private def endpoint_17_58_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_17_58_base : receiptBase endpoint_17_58_flag endpoint_17_58_sources = some 225240171321016207 := by decide +kernel
private theorem endpoint_17_58_w0 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 2 225240171321016207 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_w2 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 2 2 236137111001504624 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_p4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 4 225240171321016207 = some 236137111001504624 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 2 2 225240171321016207 236137111001504624 236137111001504624 endpoint_17_58_w0 endpoint_17_58_w2
private theorem endpoint_17_58_w4 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 4 2 236137111001504624 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_p6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 6 225240171321016207 = some 236137111001504624 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 4 2 225240171321016207 236137111001504624 236137111001504624 endpoint_17_58_p4 endpoint_17_58_w4
private theorem endpoint_17_58_w6 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 6 2 236137111001504624 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_p8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 8 225240171321016207 = some 236137111001504624 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 6 2 225240171321016207 236137111001504624 236137111001504624 endpoint_17_58_p6 endpoint_17_58_w6
private theorem endpoint_17_58_w8 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 8 2 236137111001504624 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_p10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 10 225240171321016207 = some 236137111001504624 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 8 2 225240171321016207 236137111001504624 236137111001504624 endpoint_17_58_p8 endpoint_17_58_w8
private theorem endpoint_17_58_w10 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 10 2 236137111001504624 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_p12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 12 225240171321016207 = some 236137111001504624 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 10 2 225240171321016207 236137111001504624 236137111001504624 endpoint_17_58_p10 endpoint_17_58_w10
private theorem endpoint_17_58_w12 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 12 2 236137111001504624 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_p14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 14 225240171321016207 = some 236137111001504624 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 12 2 225240171321016207 236137111001504624 236137111001504624 endpoint_17_58_p12 endpoint_17_58_w12
private theorem endpoint_17_58_w14 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 14 2 236137111001504624 = some 236137111001504624 := by decide +kernel
private theorem endpoint_17_58_p16 : receiptWindow endpoint_17_58_flag endpoint_17_58_sources 0 16 225240171321016207 = some 236137111001504624 :=
  join_receipt_window endpoint_17_58_flag endpoint_17_58_sources 0 14 2 225240171321016207 236137111001504624 236137111001504624 endpoint_17_58_p14 endpoint_17_58_w14
def endpoint_17_58 : CertifiedEndpoint :=
  ⟨⟨17, 58, 2036⟩, 236137111001504624, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_17_58_flag endpoint_17_58_sources 16 225240171321016207 236137111001504624 rfl endpoint_17_58_base endpoint_17_58_p16) (by decide)⟩
private def endpoint_17_59_flag : Flag := ⟨17, 59, 1981⟩
private def endpoint_17_59_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_59_base : receiptBase endpoint_17_59_flag endpoint_17_59_sources = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_w0 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_w2 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 2 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_p4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 4 225471434569413776 = some 225471434569413776 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 2 2 225471434569413776 225471434569413776 225471434569413776 endpoint_17_59_w0 endpoint_17_59_w2
private theorem endpoint_17_59_w4 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 4 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_p6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 6 225471434569413776 = some 225471434569413776 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 4 2 225471434569413776 225471434569413776 225471434569413776 endpoint_17_59_p4 endpoint_17_59_w4
private theorem endpoint_17_59_w6 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 6 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_p8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 8 225471434569413776 = some 225471434569413776 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 6 2 225471434569413776 225471434569413776 225471434569413776 endpoint_17_59_p6 endpoint_17_59_w6
private theorem endpoint_17_59_w8 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 8 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_p10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 10 225471434569413776 = some 225471434569413776 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 8 2 225471434569413776 225471434569413776 225471434569413776 endpoint_17_59_p8 endpoint_17_59_w8
private theorem endpoint_17_59_w10 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 10 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_p12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 12 225471434569413776 = some 225471434569413776 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 10 2 225471434569413776 225471434569413776 225471434569413776 endpoint_17_59_p10 endpoint_17_59_w10
private theorem endpoint_17_59_w12 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 12 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_p14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 14 225471434569413776 = some 225471434569413776 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 12 2 225471434569413776 225471434569413776 225471434569413776 endpoint_17_59_p12 endpoint_17_59_w12
private theorem endpoint_17_59_w14 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 14 2 225471434569413776 = some 225471434569413776 := by decide +kernel
private theorem endpoint_17_59_p16 : receiptWindow endpoint_17_59_flag endpoint_17_59_sources 0 16 225471434569413776 = some 225471434569413776 :=
  join_receipt_window endpoint_17_59_flag endpoint_17_59_sources 0 14 2 225471434569413776 225471434569413776 225471434569413776 endpoint_17_59_p14 endpoint_17_59_w14
def endpoint_17_59 : CertifiedEndpoint :=
  ⟨⟨17, 59, 1981⟩, 225471434569413776, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_59_flag endpoint_17_59_sources 16 225471434569413776 225471434569413776 rfl endpoint_17_59_base endpoint_17_59_p16) (by decide)⟩
private def endpoint_17_60_flag : Flag := ⟨17, 60, 1925⟩
private def endpoint_17_60_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_60_base : receiptBase endpoint_17_60_flag endpoint_17_60_sources = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_w0 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_w2 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 2 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_p4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 4 222431642259512670 = some 222431642259512670 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 2 2 222431642259512670 222431642259512670 222431642259512670 endpoint_17_60_w0 endpoint_17_60_w2
private theorem endpoint_17_60_w4 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 4 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_p6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 6 222431642259512670 = some 222431642259512670 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 4 2 222431642259512670 222431642259512670 222431642259512670 endpoint_17_60_p4 endpoint_17_60_w4
private theorem endpoint_17_60_w6 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 6 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_p8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 8 222431642259512670 = some 222431642259512670 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 6 2 222431642259512670 222431642259512670 222431642259512670 endpoint_17_60_p6 endpoint_17_60_w6
private theorem endpoint_17_60_w8 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 8 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_p10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 10 222431642259512670 = some 222431642259512670 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 8 2 222431642259512670 222431642259512670 222431642259512670 endpoint_17_60_p8 endpoint_17_60_w8
private theorem endpoint_17_60_w10 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 10 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_p12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 12 222431642259512670 = some 222431642259512670 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 10 2 222431642259512670 222431642259512670 222431642259512670 endpoint_17_60_p10 endpoint_17_60_w10
private theorem endpoint_17_60_w12 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 12 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_p14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 14 222431642259512670 = some 222431642259512670 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 12 2 222431642259512670 222431642259512670 222431642259512670 endpoint_17_60_p12 endpoint_17_60_w12
private theorem endpoint_17_60_w14 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 14 2 222431642259512670 = some 222431642259512670 := by decide +kernel
private theorem endpoint_17_60_p16 : receiptWindow endpoint_17_60_flag endpoint_17_60_sources 0 16 222431642259512670 = some 222431642259512670 :=
  join_receipt_window endpoint_17_60_flag endpoint_17_60_sources 0 14 2 222431642259512670 222431642259512670 222431642259512670 endpoint_17_60_p14 endpoint_17_60_w14
def endpoint_17_60 : CertifiedEndpoint :=
  ⟨⟨17, 60, 1925⟩, 222431642259512670, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_60_flag endpoint_17_60_sources 16 222431642259512670 222431642259512670 rfl endpoint_17_60_base endpoint_17_60_p16) (by decide)⟩
private def endpoint_17_61_flag : Flag := ⟨17, 61, 1868⟩
private def endpoint_17_61_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_61_base : receiptBase endpoint_17_61_flag endpoint_17_61_sources = some 219085268319135940 := by decide +kernel
private theorem endpoint_17_61_w0 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 2 219085268319135940 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_w2 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 2 2 222143195116026317 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_p4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 4 219085268319135940 = some 222143195116026317 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 2 2 219085268319135940 222143195116026317 222143195116026317 endpoint_17_61_w0 endpoint_17_61_w2
private theorem endpoint_17_61_w4 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 4 2 222143195116026317 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_p6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 6 219085268319135940 = some 222143195116026317 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 4 2 219085268319135940 222143195116026317 222143195116026317 endpoint_17_61_p4 endpoint_17_61_w4
private theorem endpoint_17_61_w6 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 6 2 222143195116026317 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_p8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 8 219085268319135940 = some 222143195116026317 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 6 2 219085268319135940 222143195116026317 222143195116026317 endpoint_17_61_p6 endpoint_17_61_w6
private theorem endpoint_17_61_w8 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 8 2 222143195116026317 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_p10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 10 219085268319135940 = some 222143195116026317 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 8 2 219085268319135940 222143195116026317 222143195116026317 endpoint_17_61_p8 endpoint_17_61_w8
private theorem endpoint_17_61_w10 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 10 2 222143195116026317 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_p12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 12 219085268319135940 = some 222143195116026317 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 10 2 219085268319135940 222143195116026317 222143195116026317 endpoint_17_61_p10 endpoint_17_61_w10
private theorem endpoint_17_61_w12 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 12 2 222143195116026317 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_p14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 14 219085268319135940 = some 222143195116026317 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 12 2 219085268319135940 222143195116026317 222143195116026317 endpoint_17_61_p12 endpoint_17_61_w12
private theorem endpoint_17_61_w14 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 14 2 222143195116026317 = some 222143195116026317 := by decide +kernel
private theorem endpoint_17_61_p16 : receiptWindow endpoint_17_61_flag endpoint_17_61_sources 0 16 219085268319135940 = some 222143195116026317 :=
  join_receipt_window endpoint_17_61_flag endpoint_17_61_sources 0 14 2 219085268319135940 222143195116026317 222143195116026317 endpoint_17_61_p14 endpoint_17_61_w14
def endpoint_17_61 : CertifiedEndpoint :=
  ⟨⟨17, 61, 1868⟩, 222143195116026317, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_61_flag endpoint_17_61_sources 16 219085268319135940 222143195116026317 rfl endpoint_17_61_base endpoint_17_61_p16) (by decide)⟩
private def endpoint_17_62_flag : Flag := ⟨17, 62, 1809⟩
private def endpoint_17_62_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_17_62_base : receiptBase endpoint_17_62_flag endpoint_17_62_sources = some 215309643200137269 := by decide +kernel
private theorem endpoint_17_62_w0 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 2 215309643200137269 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_w2 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 2 2 222299482390808562 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_p4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 4 215309643200137269 = some 222299482390808562 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 2 2 215309643200137269 222299482390808562 222299482390808562 endpoint_17_62_w0 endpoint_17_62_w2
private theorem endpoint_17_62_w4 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 4 2 222299482390808562 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_p6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 6 215309643200137269 = some 222299482390808562 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 4 2 215309643200137269 222299482390808562 222299482390808562 endpoint_17_62_p4 endpoint_17_62_w4
private theorem endpoint_17_62_w6 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 6 2 222299482390808562 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_p8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 8 215309643200137269 = some 222299482390808562 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 6 2 215309643200137269 222299482390808562 222299482390808562 endpoint_17_62_p6 endpoint_17_62_w6
private theorem endpoint_17_62_w8 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 8 2 222299482390808562 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_p10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 10 215309643200137269 = some 222299482390808562 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 8 2 215309643200137269 222299482390808562 222299482390808562 endpoint_17_62_p8 endpoint_17_62_w8
private theorem endpoint_17_62_w10 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 10 2 222299482390808562 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_p12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 12 215309643200137269 = some 222299482390808562 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 10 2 215309643200137269 222299482390808562 222299482390808562 endpoint_17_62_p10 endpoint_17_62_w10
private theorem endpoint_17_62_w12 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 12 2 222299482390808562 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_p14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 14 215309643200137269 = some 222299482390808562 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 12 2 215309643200137269 222299482390808562 222299482390808562 endpoint_17_62_p12 endpoint_17_62_w12
private theorem endpoint_17_62_w14 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 14 2 222299482390808562 = some 222299482390808562 := by decide +kernel
private theorem endpoint_17_62_p16 : receiptWindow endpoint_17_62_flag endpoint_17_62_sources 0 16 215309643200137269 = some 222299482390808562 :=
  join_receipt_window endpoint_17_62_flag endpoint_17_62_sources 0 14 2 215309643200137269 222299482390808562 222299482390808562 endpoint_17_62_p14 endpoint_17_62_w14
def endpoint_17_62 : CertifiedEndpoint :=
  ⟨⟨17, 62, 1809⟩, 222299482390808562, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_17_62_flag endpoint_17_62_sources 16 215309643200137269 222299482390808562 rfl endpoint_17_62_base endpoint_17_62_p16) (by decide)⟩
private def endpoint_17_63_flag : Flag := ⟨17, 63, 1749⟩
private def endpoint_17_63_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_63_base : receiptBase endpoint_17_63_flag endpoint_17_63_sources = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_w0 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_w2 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 2 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_p4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 4 212953183852914102 = some 212953183852914102 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 2 2 212953183852914102 212953183852914102 212953183852914102 endpoint_17_63_w0 endpoint_17_63_w2
private theorem endpoint_17_63_w4 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 4 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_p6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 6 212953183852914102 = some 212953183852914102 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 4 2 212953183852914102 212953183852914102 212953183852914102 endpoint_17_63_p4 endpoint_17_63_w4
private theorem endpoint_17_63_w6 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 6 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_p8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 8 212953183852914102 = some 212953183852914102 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 6 2 212953183852914102 212953183852914102 212953183852914102 endpoint_17_63_p6 endpoint_17_63_w6
private theorem endpoint_17_63_w8 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 8 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_p10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 10 212953183852914102 = some 212953183852914102 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 8 2 212953183852914102 212953183852914102 212953183852914102 endpoint_17_63_p8 endpoint_17_63_w8
private theorem endpoint_17_63_w10 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 10 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_p12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 12 212953183852914102 = some 212953183852914102 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 10 2 212953183852914102 212953183852914102 212953183852914102 endpoint_17_63_p10 endpoint_17_63_w10
private theorem endpoint_17_63_w12 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 12 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_p14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 14 212953183852914102 = some 212953183852914102 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 12 2 212953183852914102 212953183852914102 212953183852914102 endpoint_17_63_p12 endpoint_17_63_w12
private theorem endpoint_17_63_w14 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 14 2 212953183852914102 = some 212953183852914102 := by decide +kernel
private theorem endpoint_17_63_p16 : receiptWindow endpoint_17_63_flag endpoint_17_63_sources 0 16 212953183852914102 = some 212953183852914102 :=
  join_receipt_window endpoint_17_63_flag endpoint_17_63_sources 0 14 2 212953183852914102 212953183852914102 212953183852914102 endpoint_17_63_p14 endpoint_17_63_w14
def endpoint_17_63 : CertifiedEndpoint :=
  ⟨⟨17, 63, 1749⟩, 212953183852914102, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_63_flag endpoint_17_63_sources 16 212953183852914102 212953183852914102 rfl endpoint_17_63_base endpoint_17_63_p16) (by decide)⟩
private def endpoint_17_64_flag : Flag := ⟨17, 64, 1687⟩
private def endpoint_17_64_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_64_base : receiptBase endpoint_17_64_flag endpoint_17_64_sources = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_w0 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_w2 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 2 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_p4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 4 208359140682702503 = some 208359140682702503 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 2 2 208359140682702503 208359140682702503 208359140682702503 endpoint_17_64_w0 endpoint_17_64_w2
private theorem endpoint_17_64_w4 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 4 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_p6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 6 208359140682702503 = some 208359140682702503 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 4 2 208359140682702503 208359140682702503 208359140682702503 endpoint_17_64_p4 endpoint_17_64_w4
private theorem endpoint_17_64_w6 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 6 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_p8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 8 208359140682702503 = some 208359140682702503 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 6 2 208359140682702503 208359140682702503 208359140682702503 endpoint_17_64_p6 endpoint_17_64_w6
private theorem endpoint_17_64_w8 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 8 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_p10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 10 208359140682702503 = some 208359140682702503 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 8 2 208359140682702503 208359140682702503 208359140682702503 endpoint_17_64_p8 endpoint_17_64_w8
private theorem endpoint_17_64_w10 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 10 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_p12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 12 208359140682702503 = some 208359140682702503 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 10 2 208359140682702503 208359140682702503 208359140682702503 endpoint_17_64_p10 endpoint_17_64_w10
private theorem endpoint_17_64_w12 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 12 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_p14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 14 208359140682702503 = some 208359140682702503 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 12 2 208359140682702503 208359140682702503 208359140682702503 endpoint_17_64_p12 endpoint_17_64_w12
private theorem endpoint_17_64_w14 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 14 2 208359140682702503 = some 208359140682702503 := by decide +kernel
private theorem endpoint_17_64_p16 : receiptWindow endpoint_17_64_flag endpoint_17_64_sources 0 16 208359140682702503 = some 208359140682702503 :=
  join_receipt_window endpoint_17_64_flag endpoint_17_64_sources 0 14 2 208359140682702503 208359140682702503 208359140682702503 endpoint_17_64_p14 endpoint_17_64_w14
def endpoint_17_64 : CertifiedEndpoint :=
  ⟨⟨17, 64, 1687⟩, 208359140682702503, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_64_flag endpoint_17_64_sources 16 208359140682702503 208359140682702503 rfl endpoint_17_64_base endpoint_17_64_p16) (by decide)⟩
private def endpoint_17_65_flag : Flag := ⟨17, 65, 1624⟩
private def endpoint_17_65_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_65_base : receiptBase endpoint_17_65_flag endpoint_17_65_sources = some 203429478817162192 := by decide +kernel
private theorem endpoint_17_65_w0 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 2 203429478817162192 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_w2 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 2 2 205196361720880590 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_p4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 4 203429478817162192 = some 205196361720880590 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 2 2 203429478817162192 205196361720880590 205196361720880590 endpoint_17_65_w0 endpoint_17_65_w2
private theorem endpoint_17_65_w4 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 4 2 205196361720880590 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_p6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 6 203429478817162192 = some 205196361720880590 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 4 2 203429478817162192 205196361720880590 205196361720880590 endpoint_17_65_p4 endpoint_17_65_w4
private theorem endpoint_17_65_w6 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 6 2 205196361720880590 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_p8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 8 203429478817162192 = some 205196361720880590 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 6 2 203429478817162192 205196361720880590 205196361720880590 endpoint_17_65_p6 endpoint_17_65_w6
private theorem endpoint_17_65_w8 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 8 2 205196361720880590 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_p10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 10 203429478817162192 = some 205196361720880590 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 8 2 203429478817162192 205196361720880590 205196361720880590 endpoint_17_65_p8 endpoint_17_65_w8
private theorem endpoint_17_65_w10 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 10 2 205196361720880590 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_p12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 12 203429478817162192 = some 205196361720880590 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 10 2 203429478817162192 205196361720880590 205196361720880590 endpoint_17_65_p10 endpoint_17_65_w10
private theorem endpoint_17_65_w12 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 12 2 205196361720880590 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_p14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 14 203429478817162192 = some 205196361720880590 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 12 2 203429478817162192 205196361720880590 205196361720880590 endpoint_17_65_p12 endpoint_17_65_w12
private theorem endpoint_17_65_w14 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 14 2 205196361720880590 = some 205196361720880590 := by decide +kernel
private theorem endpoint_17_65_p16 : receiptWindow endpoint_17_65_flag endpoint_17_65_sources 0 16 203429478817162192 = some 205196361720880590 :=
  join_receipt_window endpoint_17_65_flag endpoint_17_65_sources 0 14 2 203429478817162192 205196361720880590 205196361720880590 endpoint_17_65_p14 endpoint_17_65_w14
def endpoint_17_65 : CertifiedEndpoint :=
  ⟨⟨17, 65, 1624⟩, 205196361720880590, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_65_flag endpoint_17_65_sources 16 203429478817162192 205196361720880590 rfl endpoint_17_65_base endpoint_17_65_p16) (by decide)⟩
private def endpoint_17_66_flag : Flag := ⟨17, 66, 1559⟩
private def endpoint_17_66_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_17_66_base : receiptBase endpoint_17_66_flag endpoint_17_66_sources = some 198033700469484758 := by decide +kernel
private theorem endpoint_17_66_w0 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 2 198033700469484758 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_w2 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 2 2 203974367981489606 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_p4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 4 198033700469484758 = some 203974367981489606 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 2 2 198033700469484758 203974367981489606 203974367981489606 endpoint_17_66_w0 endpoint_17_66_w2
private theorem endpoint_17_66_w4 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 4 2 203974367981489606 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_p6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 6 198033700469484758 = some 203974367981489606 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 4 2 198033700469484758 203974367981489606 203974367981489606 endpoint_17_66_p4 endpoint_17_66_w4
private theorem endpoint_17_66_w6 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 6 2 203974367981489606 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_p8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 8 198033700469484758 = some 203974367981489606 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 6 2 198033700469484758 203974367981489606 203974367981489606 endpoint_17_66_p6 endpoint_17_66_w6
private theorem endpoint_17_66_w8 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 8 2 203974367981489606 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_p10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 10 198033700469484758 = some 203974367981489606 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 8 2 198033700469484758 203974367981489606 203974367981489606 endpoint_17_66_p8 endpoint_17_66_w8
private theorem endpoint_17_66_w10 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 10 2 203974367981489606 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_p12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 12 198033700469484758 = some 203974367981489606 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 10 2 198033700469484758 203974367981489606 203974367981489606 endpoint_17_66_p10 endpoint_17_66_w10
private theorem endpoint_17_66_w12 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 12 2 203974367981489606 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_p14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 14 198033700469484758 = some 203974367981489606 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 12 2 198033700469484758 203974367981489606 203974367981489606 endpoint_17_66_p12 endpoint_17_66_w12
private theorem endpoint_17_66_w14 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 14 2 203974367981489606 = some 203974367981489606 := by decide +kernel
private theorem endpoint_17_66_p16 : receiptWindow endpoint_17_66_flag endpoint_17_66_sources 0 16 198033700469484758 = some 203974367981489606 :=
  join_receipt_window endpoint_17_66_flag endpoint_17_66_sources 0 14 2 198033700469484758 203974367981489606 203974367981489606 endpoint_17_66_p14 endpoint_17_66_w14
def endpoint_17_66 : CertifiedEndpoint :=
  ⟨⟨17, 66, 1559⟩, 203974367981489606, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_17_66_flag endpoint_17_66_sources 16 198033700469484758 203974367981489606 rfl endpoint_17_66_base endpoint_17_66_p16) (by decide)⟩
private def endpoint_17_67_flag : Flag := ⟨17, 67, 1492⟩
private def endpoint_17_67_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_17_67_base : receiptBase endpoint_17_67_flag endpoint_17_67_sources = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_w0 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_w2 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 2 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_p4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 4 193884930609046858 = some 193884930609046858 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 2 2 193884930609046858 193884930609046858 193884930609046858 endpoint_17_67_w0 endpoint_17_67_w2
private theorem endpoint_17_67_w4 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 4 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_p6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 6 193884930609046858 = some 193884930609046858 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 4 2 193884930609046858 193884930609046858 193884930609046858 endpoint_17_67_p4 endpoint_17_67_w4
private theorem endpoint_17_67_w6 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 6 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_p8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 8 193884930609046858 = some 193884930609046858 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 6 2 193884930609046858 193884930609046858 193884930609046858 endpoint_17_67_p6 endpoint_17_67_w6
private theorem endpoint_17_67_w8 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 8 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_p10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 10 193884930609046858 = some 193884930609046858 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 8 2 193884930609046858 193884930609046858 193884930609046858 endpoint_17_67_p8 endpoint_17_67_w8
private theorem endpoint_17_67_w10 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 10 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_p12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 12 193884930609046858 = some 193884930609046858 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 10 2 193884930609046858 193884930609046858 193884930609046858 endpoint_17_67_p10 endpoint_17_67_w10
private theorem endpoint_17_67_w12 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 12 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_p14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 14 193884930609046858 = some 193884930609046858 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 12 2 193884930609046858 193884930609046858 193884930609046858 endpoint_17_67_p12 endpoint_17_67_w12
private theorem endpoint_17_67_w14 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 14 2 193884930609046858 = some 193884930609046858 := by decide +kernel
private theorem endpoint_17_67_p16 : receiptWindow endpoint_17_67_flag endpoint_17_67_sources 0 16 193884930609046858 = some 193884930609046858 :=
  join_receipt_window endpoint_17_67_flag endpoint_17_67_sources 0 14 2 193884930609046858 193884930609046858 193884930609046858 endpoint_17_67_p14 endpoint_17_67_w14
def endpoint_17_67 : CertifiedEndpoint :=
  ⟨⟨17, 67, 1492⟩, 193884930609046858, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_17_67_flag endpoint_17_67_sources 16 193884930609046858 193884930609046858 rfl endpoint_17_67_base endpoint_17_67_p16) (by decide)⟩
private def endpoint_17_68_flag : Flag := ⟨17, 68, 1424⟩
private def endpoint_17_68_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_17_68_base : receiptBase endpoint_17_68_flag endpoint_17_68_sources = some 187836507340153102 := by decide +kernel
private theorem endpoint_17_68_w0 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 2 187836507340153102 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_w2 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 2 2 189725136781963596 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_p4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 4 187836507340153102 = some 189725136781963596 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 2 2 187836507340153102 189725136781963596 189725136781963596 endpoint_17_68_w0 endpoint_17_68_w2
private theorem endpoint_17_68_w4 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 4 2 189725136781963596 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_p6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 6 187836507340153102 = some 189725136781963596 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 4 2 187836507340153102 189725136781963596 189725136781963596 endpoint_17_68_p4 endpoint_17_68_w4
private theorem endpoint_17_68_w6 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 6 2 189725136781963596 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_p8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 8 187836507340153102 = some 189725136781963596 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 6 2 187836507340153102 189725136781963596 189725136781963596 endpoint_17_68_p6 endpoint_17_68_w6
private theorem endpoint_17_68_w8 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 8 2 189725136781963596 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_p10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 10 187836507340153102 = some 189725136781963596 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 8 2 187836507340153102 189725136781963596 189725136781963596 endpoint_17_68_p8 endpoint_17_68_w8
private theorem endpoint_17_68_w10 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 10 2 189725136781963596 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_p12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 12 187836507340153102 = some 189725136781963596 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 10 2 187836507340153102 189725136781963596 189725136781963596 endpoint_17_68_p10 endpoint_17_68_w10
private theorem endpoint_17_68_w12 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 12 2 189725136781963596 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_p14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 14 187836507340153102 = some 189725136781963596 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 12 2 187836507340153102 189725136781963596 189725136781963596 endpoint_17_68_p12 endpoint_17_68_w12
private theorem endpoint_17_68_w14 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 14 2 189725136781963596 = some 189725136781963596 := by decide +kernel
private theorem endpoint_17_68_p16 : receiptWindow endpoint_17_68_flag endpoint_17_68_sources 0 16 187836507340153102 = some 189725136781963596 :=
  join_receipt_window endpoint_17_68_flag endpoint_17_68_sources 0 14 2 187836507340153102 189725136781963596 189725136781963596 endpoint_17_68_p14 endpoint_17_68_w14
def endpoint_17_68 : CertifiedEndpoint :=
  ⟨⟨17, 68, 1424⟩, 189725136781963596, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_17_68_flag endpoint_17_68_sources 16 187836507340153102 189725136781963596 rfl endpoint_17_68_base endpoint_17_68_p16) (by decide)⟩
private def endpoint_17_69_flag : Flag := ⟨17, 69, 1354⟩
private def endpoint_17_69_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_69_base : receiptBase endpoint_17_69_flag endpoint_17_69_sources = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_w0 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_w2 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 2 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_p4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 4 182677138786538878 = some 182677138786538878 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 2 2 182677138786538878 182677138786538878 182677138786538878 endpoint_17_69_w0 endpoint_17_69_w2
private theorem endpoint_17_69_w4 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 4 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_p6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 6 182677138786538878 = some 182677138786538878 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 4 2 182677138786538878 182677138786538878 182677138786538878 endpoint_17_69_p4 endpoint_17_69_w4
private theorem endpoint_17_69_w6 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 6 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_p8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 8 182677138786538878 = some 182677138786538878 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 6 2 182677138786538878 182677138786538878 182677138786538878 endpoint_17_69_p6 endpoint_17_69_w6
private theorem endpoint_17_69_w8 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 8 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_p10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 10 182677138786538878 = some 182677138786538878 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 8 2 182677138786538878 182677138786538878 182677138786538878 endpoint_17_69_p8 endpoint_17_69_w8
private theorem endpoint_17_69_w10 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 10 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_p12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 12 182677138786538878 = some 182677138786538878 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 10 2 182677138786538878 182677138786538878 182677138786538878 endpoint_17_69_p10 endpoint_17_69_w10
private theorem endpoint_17_69_w12 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 12 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_p14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 14 182677138786538878 = some 182677138786538878 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 12 2 182677138786538878 182677138786538878 182677138786538878 endpoint_17_69_p12 endpoint_17_69_w12
private theorem endpoint_17_69_w14 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 14 2 182677138786538878 = some 182677138786538878 := by decide +kernel
private theorem endpoint_17_69_p16 : receiptWindow endpoint_17_69_flag endpoint_17_69_sources 0 16 182677138786538878 = some 182677138786538878 :=
  join_receipt_window endpoint_17_69_flag endpoint_17_69_sources 0 14 2 182677138786538878 182677138786538878 182677138786538878 endpoint_17_69_p14 endpoint_17_69_w14
def endpoint_17_69 : CertifiedEndpoint :=
  ⟨⟨17, 69, 1354⟩, 182677138786538878, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_69_flag endpoint_17_69_sources 16 182677138786538878 182677138786538878 rfl endpoint_17_69_base endpoint_17_69_p16) (by decide)⟩
private def endpoint_17_70_flag : Flag := ⟨17, 70, 1282⟩
private def endpoint_17_70_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_70_base : receiptBase endpoint_17_70_flag endpoint_17_70_sources = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_w0 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_w2 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 2 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_p4 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 4 175280898258607673 = some 175280898258607673 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 2 2 175280898258607673 175280898258607673 175280898258607673 endpoint_17_70_w0 endpoint_17_70_w2
private theorem endpoint_17_70_w4 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 4 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_p6 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 6 175280898258607673 = some 175280898258607673 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 4 2 175280898258607673 175280898258607673 175280898258607673 endpoint_17_70_p4 endpoint_17_70_w4
private theorem endpoint_17_70_w6 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 6 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_p8 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 8 175280898258607673 = some 175280898258607673 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 6 2 175280898258607673 175280898258607673 175280898258607673 endpoint_17_70_p6 endpoint_17_70_w6
private theorem endpoint_17_70_w8 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 8 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_p10 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 10 175280898258607673 = some 175280898258607673 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 8 2 175280898258607673 175280898258607673 175280898258607673 endpoint_17_70_p8 endpoint_17_70_w8
private theorem endpoint_17_70_w10 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 10 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_p12 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 12 175280898258607673 = some 175280898258607673 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 10 2 175280898258607673 175280898258607673 175280898258607673 endpoint_17_70_p10 endpoint_17_70_w10
private theorem endpoint_17_70_w12 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 12 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_p14 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 14 175280898258607673 = some 175280898258607673 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 12 2 175280898258607673 175280898258607673 175280898258607673 endpoint_17_70_p12 endpoint_17_70_w12
private theorem endpoint_17_70_w14 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 14 2 175280898258607673 = some 175280898258607673 := by decide +kernel
private theorem endpoint_17_70_p16 : receiptWindow endpoint_17_70_flag endpoint_17_70_sources 0 16 175280898258607673 = some 175280898258607673 :=
  join_receipt_window endpoint_17_70_flag endpoint_17_70_sources 0 14 2 175280898258607673 175280898258607673 175280898258607673 endpoint_17_70_p14 endpoint_17_70_w14
def endpoint_17_70 : CertifiedEndpoint :=
  ⟨⟨17, 70, 1282⟩, 175280898258607673, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_70_flag endpoint_17_70_sources 16 175280898258607673 175280898258607673 rfl endpoint_17_70_base endpoint_17_70_p16) (by decide)⟩
private def endpoint_17_71_flag : Flag := ⟨17, 71, 1207⟩
private def endpoint_17_71_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_71_base : receiptBase endpoint_17_71_flag endpoint_17_71_sources = some 167229914525780631 := by decide +kernel
private theorem endpoint_17_71_w0 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 2 167229914525780631 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_w2 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 2 2 171818741443195947 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_p4 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 4 167229914525780631 = some 171818741443195947 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 2 2 167229914525780631 171818741443195947 171818741443195947 endpoint_17_71_w0 endpoint_17_71_w2
private theorem endpoint_17_71_w4 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 4 2 171818741443195947 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_p6 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 6 167229914525780631 = some 171818741443195947 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 4 2 167229914525780631 171818741443195947 171818741443195947 endpoint_17_71_p4 endpoint_17_71_w4
private theorem endpoint_17_71_w6 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 6 2 171818741443195947 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_p8 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 8 167229914525780631 = some 171818741443195947 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 6 2 167229914525780631 171818741443195947 171818741443195947 endpoint_17_71_p6 endpoint_17_71_w6
private theorem endpoint_17_71_w8 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 8 2 171818741443195947 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_p10 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 10 167229914525780631 = some 171818741443195947 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 8 2 167229914525780631 171818741443195947 171818741443195947 endpoint_17_71_p8 endpoint_17_71_w8
private theorem endpoint_17_71_w10 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 10 2 171818741443195947 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_p12 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 12 167229914525780631 = some 171818741443195947 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 10 2 167229914525780631 171818741443195947 171818741443195947 endpoint_17_71_p10 endpoint_17_71_w10
private theorem endpoint_17_71_w12 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 12 2 171818741443195947 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_p14 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 14 167229914525780631 = some 171818741443195947 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 12 2 167229914525780631 171818741443195947 171818741443195947 endpoint_17_71_p12 endpoint_17_71_w12
private theorem endpoint_17_71_w14 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 14 2 171818741443195947 = some 171818741443195947 := by decide +kernel
private theorem endpoint_17_71_p16 : receiptWindow endpoint_17_71_flag endpoint_17_71_sources 0 16 167229914525780631 = some 171818741443195947 :=
  join_receipt_window endpoint_17_71_flag endpoint_17_71_sources 0 14 2 167229914525780631 171818741443195947 171818741443195947 endpoint_17_71_p14 endpoint_17_71_w14
def endpoint_17_71 : CertifiedEndpoint :=
  ⟨⟨17, 71, 1207⟩, 171818741443195947, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_71_flag endpoint_17_71_sources 16 167229914525780631 171818741443195947 rfl endpoint_17_71_base endpoint_17_71_p16) (by decide)⟩
private def endpoint_17_72_flag : Flag := ⟨17, 72, 1131⟩
private def endpoint_17_72_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_72_base : receiptBase endpoint_17_72_flag endpoint_17_72_sources = some 158784948144183984 := by decide +kernel
private theorem endpoint_17_72_w0 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 2 158784948144183984 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_w2 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 2 2 168267717384379450 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_p4 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 4 158784948144183984 = some 168267717384379450 :=
  join_receipt_window endpoint_17_72_flag endpoint_17_72_sources 0 2 2 158784948144183984 168267717384379450 168267717384379450 endpoint_17_72_w0 endpoint_17_72_w2
private theorem endpoint_17_72_w4 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 4 2 168267717384379450 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_p6 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 6 158784948144183984 = some 168267717384379450 :=
  join_receipt_window endpoint_17_72_flag endpoint_17_72_sources 0 4 2 158784948144183984 168267717384379450 168267717384379450 endpoint_17_72_p4 endpoint_17_72_w4
private theorem endpoint_17_72_w6 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 6 2 168267717384379450 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_p8 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 8 158784948144183984 = some 168267717384379450 :=
  join_receipt_window endpoint_17_72_flag endpoint_17_72_sources 0 6 2 158784948144183984 168267717384379450 168267717384379450 endpoint_17_72_p6 endpoint_17_72_w6
private theorem endpoint_17_72_w8 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 8 2 168267717384379450 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_p10 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 10 158784948144183984 = some 168267717384379450 :=
  join_receipt_window endpoint_17_72_flag endpoint_17_72_sources 0 8 2 158784948144183984 168267717384379450 168267717384379450 endpoint_17_72_p8 endpoint_17_72_w8
private theorem endpoint_17_72_w10 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 10 2 168267717384379450 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_p12 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 12 158784948144183984 = some 168267717384379450 :=
  join_receipt_window endpoint_17_72_flag endpoint_17_72_sources 0 10 2 158784948144183984 168267717384379450 168267717384379450 endpoint_17_72_p10 endpoint_17_72_w10
private theorem endpoint_17_72_w12 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 12 2 168267717384379450 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_p14 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 14 158784948144183984 = some 168267717384379450 :=
  join_receipt_window endpoint_17_72_flag endpoint_17_72_sources 0 12 2 158784948144183984 168267717384379450 168267717384379450 endpoint_17_72_p12 endpoint_17_72_w12
private theorem endpoint_17_72_w14 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 14 2 168267717384379450 = some 168267717384379450 := by decide +kernel
private theorem endpoint_17_72_p16 : receiptWindow endpoint_17_72_flag endpoint_17_72_sources 0 16 158784948144183984 = some 168267717384379450 :=
  join_receipt_window endpoint_17_72_flag endpoint_17_72_sources 0 14 2 158784948144183984 168267717384379450 168267717384379450 endpoint_17_72_p14 endpoint_17_72_w14
def endpoint_17_72 : CertifiedEndpoint :=
  ⟨⟨17, 72, 1131⟩, 168267717384379450, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_72_flag endpoint_17_72_sources 16 158784948144183984 168267717384379450 rfl endpoint_17_72_base endpoint_17_72_p16) (by decide)⟩
private def endpoint_17_73_flag : Flag := ⟨17, 73, 1053⟩
private def endpoint_17_73_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_17_73_base : receiptBase endpoint_17_73_flag endpoint_17_73_sources = some 149801209702950724 := by decide +kernel
private theorem endpoint_17_73_w0 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 2 149801209702950724 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_w2 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 2 2 164346612438428757 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_p4 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 4 149801209702950724 = some 164346612438428757 :=
  join_receipt_window endpoint_17_73_flag endpoint_17_73_sources 0 2 2 149801209702950724 164346612438428757 164346612438428757 endpoint_17_73_w0 endpoint_17_73_w2
private theorem endpoint_17_73_w4 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 4 2 164346612438428757 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_p6 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 6 149801209702950724 = some 164346612438428757 :=
  join_receipt_window endpoint_17_73_flag endpoint_17_73_sources 0 4 2 149801209702950724 164346612438428757 164346612438428757 endpoint_17_73_p4 endpoint_17_73_w4
private theorem endpoint_17_73_w6 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 6 2 164346612438428757 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_p8 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 8 149801209702950724 = some 164346612438428757 :=
  join_receipt_window endpoint_17_73_flag endpoint_17_73_sources 0 6 2 149801209702950724 164346612438428757 164346612438428757 endpoint_17_73_p6 endpoint_17_73_w6
private theorem endpoint_17_73_w8 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 8 2 164346612438428757 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_p10 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 10 149801209702950724 = some 164346612438428757 :=
  join_receipt_window endpoint_17_73_flag endpoint_17_73_sources 0 8 2 149801209702950724 164346612438428757 164346612438428757 endpoint_17_73_p8 endpoint_17_73_w8
private theorem endpoint_17_73_w10 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 10 2 164346612438428757 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_p12 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 12 149801209702950724 = some 164346612438428757 :=
  join_receipt_window endpoint_17_73_flag endpoint_17_73_sources 0 10 2 149801209702950724 164346612438428757 164346612438428757 endpoint_17_73_p10 endpoint_17_73_w10
private theorem endpoint_17_73_w12 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 12 2 164346612438428757 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_p14 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 14 149801209702950724 = some 164346612438428757 :=
  join_receipt_window endpoint_17_73_flag endpoint_17_73_sources 0 12 2 149801209702950724 164346612438428757 164346612438428757 endpoint_17_73_p12 endpoint_17_73_w12
private theorem endpoint_17_73_w14 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 14 2 164346612438428757 = some 164346612438428757 := by decide +kernel
private theorem endpoint_17_73_p16 : receiptWindow endpoint_17_73_flag endpoint_17_73_sources 0 16 149801209702950724 = some 164346612438428757 :=
  join_receipt_window endpoint_17_73_flag endpoint_17_73_sources 0 14 2 149801209702950724 164346612438428757 164346612438428757 endpoint_17_73_p14 endpoint_17_73_w14
def endpoint_17_73 : CertifiedEndpoint :=
  ⟨⟨17, 73, 1053⟩, 164346612438428757, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_17_73_flag endpoint_17_73_sources 16 149801209702950724 164346612438428757 rfl endpoint_17_73_base endpoint_17_73_p16) (by decide)⟩
def endpoint_17_74 : CertifiedEndpoint :=
  ⟨⟨17, 74, 972⟩, 257755377841253820, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_75 : CertifiedEndpoint :=
  ⟨⟨17, 75, 889⟩, 238238463498711802, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_76 : CertifiedEndpoint :=
  ⟨⟨17, 76, 804⟩, 217439057167670856, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_77 : CertifiedEndpoint :=
  ⟨⟨17, 77, 716⟩, 195041857423883099, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_78 : CertifiedEndpoint :=
  ⟨⟨17, 78, 625⟩, 171008517847348345, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_79 : CertifiedEndpoint :=
  ⟨⟨17, 79, 532⟩, 145598950588980875, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_80 : CertifiedEndpoint :=
  ⟨⟨17, 80, 436⟩, 118485072084532744, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_81 : CertifiedEndpoint :=
  ⟨⟨17, 81, 338⟩, 89935315911584941, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_82 : CertifiedEndpoint :=
  ⟨⟨17, 82, 237⟩, 59613077079222813, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_17_83 : CertifiedEndpoint :=
  ⟨⟨17, 83, 133⟩, 27480009167446174, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_18 : CertifiedEndpoint :=
  ⟨⟨18, 18, 3315⟩, 146868031686673719, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_19 : CertifiedEndpoint :=
  ⟨⟨18, 19, 3288⟩, 150523637380848532, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_20 : CertifiedEndpoint :=
  ⟨⟨18, 20, 3259⟩, 154004089847761561, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_21 : CertifiedEndpoint :=
  ⟨⟨18, 21, 3231⟩, 167181813029614680, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_22 : CertifiedEndpoint :=
  ⟨⟨18, 22, 3202⟩, 180045497543518922, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_23 : CertifiedEndpoint :=
  ⟨⟨18, 23, 3172⟩, 192581588136486469, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_24 : CertifiedEndpoint :=
  ⟨⟨18, 24, 3142⟩, 204842055252035050, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_25 : CertifiedEndpoint :=
  ⟨⟨18, 25, 3112⟩, 216826898890164665, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_26 : CertifiedEndpoint :=
  ⟨⟨18, 26, 3080⟩, 228386993987213796, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_27 : CertifiedEndpoint :=
  ⟨⟨18, 27, 3049⟩, 239732472885686902, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_28 : CertifiedEndpoint :=
  ⟨⟨18, 28, 3017⟩, 250709692104259859, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_29 : CertifiedEndpoint :=
  ⟨⟨18, 29, 2984⟩, 261305096389944849, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_18_30_flag : Flag := ⟨18, 30, 2951⟩
private def endpoint_18_30_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_30_base : receiptBase endpoint_18_30_flag endpoint_18_30_sources = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_w0 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_w2 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 2 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 4 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 2 2 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_w0 endpoint_18_30_w2
private theorem endpoint_18_30_w4 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 4 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 6 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 4 2 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_p4 endpoint_18_30_w4
private theorem endpoint_18_30_w6 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 6 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 8 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 6 2 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_p6 endpoint_18_30_w6
private theorem endpoint_18_30_w8 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 8 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 10 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 8 2 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_p8 endpoint_18_30_w8
private theorem endpoint_18_30_w10 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 10 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 12 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 10 2 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_p10 endpoint_18_30_w10
private theorem endpoint_18_30_w12 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 12 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 14 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 12 2 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_p12 endpoint_18_30_w12
private theorem endpoint_18_30_w14 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 14 2 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 16 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 14 2 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_p14 endpoint_18_30_w14
private theorem endpoint_18_30_w16 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 16 1 183756393254412298 = some 183756393254412298 := by decide +kernel
private theorem endpoint_18_30_p17 : receiptWindow endpoint_18_30_flag endpoint_18_30_sources 0 17 183756393254412298 = some 183756393254412298 :=
  join_receipt_window endpoint_18_30_flag endpoint_18_30_sources 0 16 1 183756393254412298 183756393254412298 183756393254412298 endpoint_18_30_p16 endpoint_18_30_w16
def endpoint_18_30 : CertifiedEndpoint :=
  ⟨⟨18, 30, 2951⟩, 183756393254412298, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_30_flag endpoint_18_30_sources 17 183756393254412298 183756393254412298 rfl endpoint_18_30_base endpoint_18_30_p17) (by decide)⟩
private def endpoint_18_31_flag : Flag := ⟨18, 31, 2918⟩
private def endpoint_18_31_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_18_31_base : receiptBase endpoint_18_31_flag endpoint_18_31_sources = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_w0 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_w2 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 2 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 4 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 2 2 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_w0 endpoint_18_31_w2
private theorem endpoint_18_31_w4 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 4 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 6 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 4 2 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_p4 endpoint_18_31_w4
private theorem endpoint_18_31_w6 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 6 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 8 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 6 2 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_p6 endpoint_18_31_w6
private theorem endpoint_18_31_w8 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 8 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 10 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 8 2 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_p8 endpoint_18_31_w8
private theorem endpoint_18_31_w10 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 10 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 12 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 10 2 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_p10 endpoint_18_31_w10
private theorem endpoint_18_31_w12 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 12 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 14 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 12 2 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_p12 endpoint_18_31_w12
private theorem endpoint_18_31_w14 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 14 2 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 16 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 14 2 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_p14 endpoint_18_31_w14
private theorem endpoint_18_31_w16 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 16 1 186733185423179352 = some 186733185423179352 := by decide +kernel
private theorem endpoint_18_31_p17 : receiptWindow endpoint_18_31_flag endpoint_18_31_sources 0 17 186733185423179352 = some 186733185423179352 :=
  join_receipt_window endpoint_18_31_flag endpoint_18_31_sources 0 16 1 186733185423179352 186733185423179352 186733185423179352 endpoint_18_31_p16 endpoint_18_31_w16
def endpoint_18_31 : CertifiedEndpoint :=
  ⟨⟨18, 31, 2918⟩, 186733185423179352, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_18_31_flag endpoint_18_31_sources 17 186733185423179352 186733185423179352 rfl endpoint_18_31_base endpoint_18_31_p17) (by decide)⟩
private def endpoint_18_32_flag : Flag := ⟨18, 32, 2883⟩
private def endpoint_18_32_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_32_base : receiptBase endpoint_18_32_flag endpoint_18_32_sources = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_w0 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_w2 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 2 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 4 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 2 2 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_w0 endpoint_18_32_w2
private theorem endpoint_18_32_w4 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 4 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 6 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 4 2 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_p4 endpoint_18_32_w4
private theorem endpoint_18_32_w6 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 6 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 8 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 6 2 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_p6 endpoint_18_32_w6
private theorem endpoint_18_32_w8 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 8 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 10 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 8 2 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_p8 endpoint_18_32_w8
private theorem endpoint_18_32_w10 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 10 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 12 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 10 2 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_p10 endpoint_18_32_w10
private theorem endpoint_18_32_w12 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 12 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 14 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 12 2 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_p12 endpoint_18_32_w12
private theorem endpoint_18_32_w14 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 14 2 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 16 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 14 2 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_p14 endpoint_18_32_w14
private theorem endpoint_18_32_w16 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 16 1 189719006049575762 = some 189719006049575762 := by decide +kernel
private theorem endpoint_18_32_p17 : receiptWindow endpoint_18_32_flag endpoint_18_32_sources 0 17 189719006049575762 = some 189719006049575762 :=
  join_receipt_window endpoint_18_32_flag endpoint_18_32_sources 0 16 1 189719006049575762 189719006049575762 189719006049575762 endpoint_18_32_p16 endpoint_18_32_w16
def endpoint_18_32 : CertifiedEndpoint :=
  ⟨⟨18, 32, 2883⟩, 189719006049575762, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_32_flag endpoint_18_32_sources 17 189719006049575762 189719006049575762 rfl endpoint_18_32_base endpoint_18_32_p17) (by decide)⟩
private def endpoint_18_33_flag : Flag := ⟨18, 33, 2849⟩
private def endpoint_18_33_sources : Sources := ⟨contact32, contact08, contact04⟩
private theorem endpoint_18_33_base : receiptBase endpoint_18_33_flag endpoint_18_33_sources = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_w0 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_w2 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 2 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 4 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 2 2 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_w0 endpoint_18_33_w2
private theorem endpoint_18_33_w4 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 4 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 6 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 4 2 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_p4 endpoint_18_33_w4
private theorem endpoint_18_33_w6 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 6 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 8 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 6 2 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_p6 endpoint_18_33_w6
private theorem endpoint_18_33_w8 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 8 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 10 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 8 2 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_p8 endpoint_18_33_w8
private theorem endpoint_18_33_w10 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 10 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 12 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 10 2 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_p10 endpoint_18_33_w10
private theorem endpoint_18_33_w12 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 12 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 14 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 12 2 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_p12 endpoint_18_33_w12
private theorem endpoint_18_33_w14 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 14 2 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 16 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 14 2 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_p14 endpoint_18_33_w14
private theorem endpoint_18_33_w16 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 16 1 192415222470081878 = some 192415222470081878 := by decide +kernel
private theorem endpoint_18_33_p17 : receiptWindow endpoint_18_33_flag endpoint_18_33_sources 0 17 192415222470081878 = some 192415222470081878 :=
  join_receipt_window endpoint_18_33_flag endpoint_18_33_sources 0 16 1 192415222470081878 192415222470081878 192415222470081878 endpoint_18_33_p16 endpoint_18_33_w16
def endpoint_18_33 : CertifiedEndpoint :=
  ⟨⟨18, 33, 2849⟩, 192415222470081878, .terminal ⟨contact32, contact08, contact04⟩ (finish_receipt_window endpoint_18_33_flag endpoint_18_33_sources 17 192415222470081878 192415222470081878 rfl endpoint_18_33_base endpoint_18_33_p17) (by decide)⟩
private def endpoint_18_34_flag : Flag := ⟨18, 34, 2813⟩
private def endpoint_18_34_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_34_base : receiptBase endpoint_18_34_flag endpoint_18_34_sources = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_w0 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_w2 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 2 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 4 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 2 2 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_w0 endpoint_18_34_w2
private theorem endpoint_18_34_w4 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 4 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 6 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 4 2 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_p4 endpoint_18_34_w4
private theorem endpoint_18_34_w6 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 6 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 8 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 6 2 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_p6 endpoint_18_34_w6
private theorem endpoint_18_34_w8 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 8 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 10 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 8 2 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_p8 endpoint_18_34_w8
private theorem endpoint_18_34_w10 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 10 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 12 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 10 2 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_p10 endpoint_18_34_w10
private theorem endpoint_18_34_w12 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 12 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 14 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 12 2 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_p12 endpoint_18_34_w12
private theorem endpoint_18_34_w14 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 14 2 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 16 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 14 2 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_p14 endpoint_18_34_w14
private theorem endpoint_18_34_w16 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 16 1 195289090891378131 = some 195289090891378131 := by decide +kernel
private theorem endpoint_18_34_p17 : receiptWindow endpoint_18_34_flag endpoint_18_34_sources 0 17 195289090891378131 = some 195289090891378131 :=
  join_receipt_window endpoint_18_34_flag endpoint_18_34_sources 0 16 1 195289090891378131 195289090891378131 195289090891378131 endpoint_18_34_p16 endpoint_18_34_w16
def endpoint_18_34 : CertifiedEndpoint :=
  ⟨⟨18, 34, 2813⟩, 195289090891378131, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_34_flag endpoint_18_34_sources 17 195289090891378131 195289090891378131 rfl endpoint_18_34_base endpoint_18_34_p17) (by decide)⟩
private def endpoint_18_35_flag : Flag := ⟨18, 35, 2777⟩
private def endpoint_18_35_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_35_base : receiptBase endpoint_18_35_flag endpoint_18_35_sources = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_w0 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_w2 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 2 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 4 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 2 2 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_w0 endpoint_18_35_w2
private theorem endpoint_18_35_w4 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 4 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 6 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 4 2 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_p4 endpoint_18_35_w4
private theorem endpoint_18_35_w6 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 6 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 8 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 6 2 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_p6 endpoint_18_35_w6
private theorem endpoint_18_35_w8 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 8 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 10 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 8 2 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_p8 endpoint_18_35_w8
private theorem endpoint_18_35_w10 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 10 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 12 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 10 2 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_p10 endpoint_18_35_w10
private theorem endpoint_18_35_w12 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 12 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 14 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 12 2 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_p12 endpoint_18_35_w12
private theorem endpoint_18_35_w14 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 14 2 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 16 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 14 2 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_p14 endpoint_18_35_w14
private theorem endpoint_18_35_w16 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 16 1 197584434421494021 = some 197584434421494021 := by decide +kernel
private theorem endpoint_18_35_p17 : receiptWindow endpoint_18_35_flag endpoint_18_35_sources 0 17 197584434421494021 = some 197584434421494021 :=
  join_receipt_window endpoint_18_35_flag endpoint_18_35_sources 0 16 1 197584434421494021 197584434421494021 197584434421494021 endpoint_18_35_p16 endpoint_18_35_w16
def endpoint_18_35 : CertifiedEndpoint :=
  ⟨⟨18, 35, 2777⟩, 197584434421494021, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_35_flag endpoint_18_35_sources 17 197584434421494021 197584434421494021 rfl endpoint_18_35_base endpoint_18_35_p17) (by decide)⟩
private def endpoint_18_36_flag : Flag := ⟨18, 36, 2741⟩
private def endpoint_18_36_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_36_base : receiptBase endpoint_18_36_flag endpoint_18_36_sources = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_w0 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_w2 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 2 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 4 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 2 2 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_w0 endpoint_18_36_w2
private theorem endpoint_18_36_w4 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 4 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 6 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 4 2 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_p4 endpoint_18_36_w4
private theorem endpoint_18_36_w6 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 6 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 8 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 6 2 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_p6 endpoint_18_36_w6
private theorem endpoint_18_36_w8 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 8 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 10 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 8 2 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_p8 endpoint_18_36_w8
private theorem endpoint_18_36_w10 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 10 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 12 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 10 2 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_p10 endpoint_18_36_w10
private theorem endpoint_18_36_w12 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 12 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 14 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 12 2 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_p12 endpoint_18_36_w12
private theorem endpoint_18_36_w14 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 14 2 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 16 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 14 2 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_p14 endpoint_18_36_w14
private theorem endpoint_18_36_w16 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 16 1 199756920098668335 = some 199756920098668335 := by decide +kernel
private theorem endpoint_18_36_p17 : receiptWindow endpoint_18_36_flag endpoint_18_36_sources 0 17 199756920098668335 = some 199756920098668335 :=
  join_receipt_window endpoint_18_36_flag endpoint_18_36_sources 0 16 1 199756920098668335 199756920098668335 199756920098668335 endpoint_18_36_p16 endpoint_18_36_w16
def endpoint_18_36 : CertifiedEndpoint :=
  ⟨⟨18, 36, 2741⟩, 199756920098668335, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_36_flag endpoint_18_36_sources 17 199756920098668335 199756920098668335 rfl endpoint_18_36_base endpoint_18_36_p17) (by decide)⟩
private def endpoint_18_37_flag : Flag := ⟨18, 37, 2703⟩
private def endpoint_18_37_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_37_base : receiptBase endpoint_18_37_flag endpoint_18_37_sources = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_w0 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_w2 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 2 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 4 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 2 2 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_w0 endpoint_18_37_w2
private theorem endpoint_18_37_w4 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 4 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 6 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 4 2 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_p4 endpoint_18_37_w4
private theorem endpoint_18_37_w6 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 6 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 8 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 6 2 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_p6 endpoint_18_37_w6
private theorem endpoint_18_37_w8 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 8 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 10 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 8 2 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_p8 endpoint_18_37_w8
private theorem endpoint_18_37_w10 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 10 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 12 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 10 2 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_p10 endpoint_18_37_w10
private theorem endpoint_18_37_w12 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 12 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 14 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 12 2 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_p12 endpoint_18_37_w12
private theorem endpoint_18_37_w14 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 14 2 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 16 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 14 2 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_p14 endpoint_18_37_w14
private theorem endpoint_18_37_w16 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 16 1 201659363593093704 = some 201659363593093704 := by decide +kernel
private theorem endpoint_18_37_p17 : receiptWindow endpoint_18_37_flag endpoint_18_37_sources 0 17 201659363593093704 = some 201659363593093704 :=
  join_receipt_window endpoint_18_37_flag endpoint_18_37_sources 0 16 1 201659363593093704 201659363593093704 201659363593093704 endpoint_18_37_p16 endpoint_18_37_w16
def endpoint_18_37 : CertifiedEndpoint :=
  ⟨⟨18, 37, 2703⟩, 201659363593093704, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_37_flag endpoint_18_37_sources 17 201659363593093704 201659363593093704 rfl endpoint_18_37_base endpoint_18_37_p17) (by decide)⟩
private def endpoint_18_38_flag : Flag := ⟨18, 38, 2665⟩
private def endpoint_18_38_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_38_base : receiptBase endpoint_18_38_flag endpoint_18_38_sources = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_w0 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_w2 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 2 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 4 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 2 2 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_w0 endpoint_18_38_w2
private theorem endpoint_18_38_w4 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 4 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 6 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 4 2 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_p4 endpoint_18_38_w4
private theorem endpoint_18_38_w6 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 6 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 8 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 6 2 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_p6 endpoint_18_38_w6
private theorem endpoint_18_38_w8 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 8 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 10 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 8 2 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_p8 endpoint_18_38_w8
private theorem endpoint_18_38_w10 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 10 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 12 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 10 2 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_p10 endpoint_18_38_w10
private theorem endpoint_18_38_w12 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 12 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 14 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 12 2 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_p12 endpoint_18_38_w12
private theorem endpoint_18_38_w14 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 14 2 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 16 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 14 2 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_p14 endpoint_18_38_w14
private theorem endpoint_18_38_w16 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 16 1 203432217297430013 = some 203432217297430013 := by decide +kernel
private theorem endpoint_18_38_p17 : receiptWindow endpoint_18_38_flag endpoint_18_38_sources 0 17 203432217297430013 = some 203432217297430013 :=
  join_receipt_window endpoint_18_38_flag endpoint_18_38_sources 0 16 1 203432217297430013 203432217297430013 203432217297430013 endpoint_18_38_p16 endpoint_18_38_w16
def endpoint_18_38 : CertifiedEndpoint :=
  ⟨⟨18, 38, 2665⟩, 203432217297430013, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_38_flag endpoint_18_38_sources 17 203432217297430013 203432217297430013 rfl endpoint_18_38_base endpoint_18_38_p17) (by decide)⟩
private def endpoint_18_39_flag : Flag := ⟨18, 39, 2627⟩
private def endpoint_18_39_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_39_base : receiptBase endpoint_18_39_flag endpoint_18_39_sources = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_w0 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_w2 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 2 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 4 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 2 2 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_w0 endpoint_18_39_w2
private theorem endpoint_18_39_w4 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 4 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 6 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 4 2 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_p4 endpoint_18_39_w4
private theorem endpoint_18_39_w6 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 6 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 8 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 6 2 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_p6 endpoint_18_39_w6
private theorem endpoint_18_39_w8 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 8 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 10 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 8 2 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_p8 endpoint_18_39_w8
private theorem endpoint_18_39_w10 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 10 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 12 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 10 2 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_p10 endpoint_18_39_w10
private theorem endpoint_18_39_w12 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 12 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 14 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 12 2 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_p12 endpoint_18_39_w12
private theorem endpoint_18_39_w14 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 14 2 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 16 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 14 2 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_p14 endpoint_18_39_w14
private theorem endpoint_18_39_w16 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 16 1 205075481211677262 = some 205075481211677262 := by decide +kernel
private theorem endpoint_18_39_p17 : receiptWindow endpoint_18_39_flag endpoint_18_39_sources 0 17 205075481211677262 = some 205075481211677262 :=
  join_receipt_window endpoint_18_39_flag endpoint_18_39_sources 0 16 1 205075481211677262 205075481211677262 205075481211677262 endpoint_18_39_p16 endpoint_18_39_w16
def endpoint_18_39 : CertifiedEndpoint :=
  ⟨⟨18, 39, 2627⟩, 205075481211677262, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_39_flag endpoint_18_39_sources 17 205075481211677262 205075481211677262 rfl endpoint_18_39_base endpoint_18_39_p17) (by decide)⟩
private def endpoint_18_40_flag : Flag := ⟨18, 40, 2588⟩
private def endpoint_18_40_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_40_base : receiptBase endpoint_18_40_flag endpoint_18_40_sources = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_w0 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_w2 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 2 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 4 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 2 2 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_w0 endpoint_18_40_w2
private theorem endpoint_18_40_w4 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 4 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 6 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 4 2 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_p4 endpoint_18_40_w4
private theorem endpoint_18_40_w6 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 6 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 8 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 6 2 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_p6 endpoint_18_40_w6
private theorem endpoint_18_40_w8 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 8 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 10 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 8 2 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_p8 endpoint_18_40_w8
private theorem endpoint_18_40_w10 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 10 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 12 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 10 2 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_p10 endpoint_18_40_w10
private theorem endpoint_18_40_w12 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 12 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 14 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 12 2 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_p12 endpoint_18_40_w12
private theorem endpoint_18_40_w14 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 14 2 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 16 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 14 2 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_p14 endpoint_18_40_w14
private theorem endpoint_18_40_w16 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 16 1 206510514218071153 = some 206510514218071153 := by decide +kernel
private theorem endpoint_18_40_p17 : receiptWindow endpoint_18_40_flag endpoint_18_40_sources 0 17 206510514218071153 = some 206510514218071153 :=
  join_receipt_window endpoint_18_40_flag endpoint_18_40_sources 0 16 1 206510514218071153 206510514218071153 206510514218071153 endpoint_18_40_p16 endpoint_18_40_w16
def endpoint_18_40 : CertifiedEndpoint :=
  ⟨⟨18, 40, 2588⟩, 206510514218071153, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_40_flag endpoint_18_40_sources 17 206510514218071153 206510514218071153 rfl endpoint_18_40_base endpoint_18_40_p17) (by decide)⟩
private def endpoint_18_41_flag : Flag := ⟨18, 41, 2547⟩
private def endpoint_18_41_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_18_41_base : receiptBase endpoint_18_41_flag endpoint_18_41_sources = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_w0 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_w2 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 2 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 4 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 2 2 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_w0 endpoint_18_41_w2
private theorem endpoint_18_41_w4 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 4 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 6 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 4 2 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_p4 endpoint_18_41_w4
private theorem endpoint_18_41_w6 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 6 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 8 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 6 2 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_p6 endpoint_18_41_w6
private theorem endpoint_18_41_w8 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 8 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 10 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 8 2 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_p8 endpoint_18_41_w8
private theorem endpoint_18_41_w10 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 10 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 12 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 10 2 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_p10 endpoint_18_41_w10
private theorem endpoint_18_41_w12 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 12 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 14 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 12 2 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_p12 endpoint_18_41_w12
private theorem endpoint_18_41_w14 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 14 2 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 16 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 14 2 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_p14 endpoint_18_41_w14
private theorem endpoint_18_41_w16 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 16 1 207651943261699906 = some 207651943261699906 := by decide +kernel
private theorem endpoint_18_41_p17 : receiptWindow endpoint_18_41_flag endpoint_18_41_sources 0 17 207651943261699906 = some 207651943261699906 :=
  join_receipt_window endpoint_18_41_flag endpoint_18_41_sources 0 16 1 207651943261699906 207651943261699906 207651943261699906 endpoint_18_41_p16 endpoint_18_41_w16
def endpoint_18_41 : CertifiedEndpoint :=
  ⟨⟨18, 41, 2547⟩, 207651943261699906, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_18_41_flag endpoint_18_41_sources 17 207651943261699906 207651943261699906 rfl endpoint_18_41_base endpoint_18_41_p17) (by decide)⟩
private def endpoint_18_42_flag : Flag := ⟨18, 42, 2507⟩
private def endpoint_18_42_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_18_42_base : receiptBase endpoint_18_42_flag endpoint_18_42_sources = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_w0 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_w2 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 2 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 4 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 2 2 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_w0 endpoint_18_42_w2
private theorem endpoint_18_42_w4 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 4 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 6 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 4 2 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_p4 endpoint_18_42_w4
private theorem endpoint_18_42_w6 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 6 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 8 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 6 2 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_p6 endpoint_18_42_w6
private theorem endpoint_18_42_w8 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 8 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 10 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 8 2 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_p8 endpoint_18_42_w8
private theorem endpoint_18_42_w10 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 10 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 12 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 10 2 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_p10 endpoint_18_42_w10
private theorem endpoint_18_42_w12 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 12 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 14 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 12 2 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_p12 endpoint_18_42_w12
private theorem endpoint_18_42_w14 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 14 2 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 16 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 14 2 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_p14 endpoint_18_42_w14
private theorem endpoint_18_42_w16 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 16 1 213840020765325874 = some 213840020765325874 := by decide +kernel
private theorem endpoint_18_42_p17 : receiptWindow endpoint_18_42_flag endpoint_18_42_sources 0 17 213840020765325874 = some 213840020765325874 :=
  join_receipt_window endpoint_18_42_flag endpoint_18_42_sources 0 16 1 213840020765325874 213840020765325874 213840020765325874 endpoint_18_42_p16 endpoint_18_42_w16
def endpoint_18_42 : CertifiedEndpoint :=
  ⟨⟨18, 42, 2507⟩, 213840020765325874, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_18_42_flag endpoint_18_42_sources 17 213840020765325874 213840020765325874 rfl endpoint_18_42_base endpoint_18_42_p17) (by decide)⟩
private def endpoint_18_43_flag : Flag := ⟨18, 43, 2465⟩
private def endpoint_18_43_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_43_base : receiptBase endpoint_18_43_flag endpoint_18_43_sources = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_w0 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_w2 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 2 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 4 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 2 2 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_w0 endpoint_18_43_w2
private theorem endpoint_18_43_w4 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 4 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 6 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 4 2 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_p4 endpoint_18_43_w4
private theorem endpoint_18_43_w6 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 6 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 8 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 6 2 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_p6 endpoint_18_43_w6
private theorem endpoint_18_43_w8 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 8 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 10 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 8 2 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_p8 endpoint_18_43_w8
private theorem endpoint_18_43_w10 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 10 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 12 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 10 2 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_p10 endpoint_18_43_w10
private theorem endpoint_18_43_w12 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 12 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 14 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 12 2 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_p12 endpoint_18_43_w12
private theorem endpoint_18_43_w14 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 14 2 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 16 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 14 2 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_p14 endpoint_18_43_w14
private theorem endpoint_18_43_w16 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 16 1 215156484153803632 = some 215156484153803632 := by decide +kernel
private theorem endpoint_18_43_p17 : receiptWindow endpoint_18_43_flag endpoint_18_43_sources 0 17 215156484153803632 = some 215156484153803632 :=
  join_receipt_window endpoint_18_43_flag endpoint_18_43_sources 0 16 1 215156484153803632 215156484153803632 215156484153803632 endpoint_18_43_p16 endpoint_18_43_w16
def endpoint_18_43 : CertifiedEndpoint :=
  ⟨⟨18, 43, 2465⟩, 215156484153803632, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_43_flag endpoint_18_43_sources 17 215156484153803632 215156484153803632 rfl endpoint_18_43_base endpoint_18_43_p17) (by decide)⟩
private def endpoint_18_44_flag : Flag := ⟨18, 44, 2423⟩
private def endpoint_18_44_sources : Sources := ⟨contact33, contact11, contact29⟩
private theorem endpoint_18_44_base : receiptBase endpoint_18_44_flag endpoint_18_44_sources = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_w0 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_w2 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 2 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 4 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 2 2 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_w0 endpoint_18_44_w2
private theorem endpoint_18_44_w4 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 4 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 6 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 4 2 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_p4 endpoint_18_44_w4
private theorem endpoint_18_44_w6 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 6 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 8 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 6 2 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_p6 endpoint_18_44_w6
private theorem endpoint_18_44_w8 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 8 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 10 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 8 2 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_p8 endpoint_18_44_w8
private theorem endpoint_18_44_w10 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 10 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 12 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 10 2 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_p10 endpoint_18_44_w10
private theorem endpoint_18_44_w12 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 12 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 14 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 12 2 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_p12 endpoint_18_44_w12
private theorem endpoint_18_44_w14 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 14 2 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 16 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 14 2 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_p14 endpoint_18_44_w14
private theorem endpoint_18_44_w16 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 16 1 215862474548258573 = some 215862474548258573 := by decide +kernel
private theorem endpoint_18_44_p17 : receiptWindow endpoint_18_44_flag endpoint_18_44_sources 0 17 215862474548258573 = some 215862474548258573 :=
  join_receipt_window endpoint_18_44_flag endpoint_18_44_sources 0 16 1 215862474548258573 215862474548258573 215862474548258573 endpoint_18_44_p16 endpoint_18_44_w16
def endpoint_18_44 : CertifiedEndpoint :=
  ⟨⟨18, 44, 2423⟩, 215862474548258573, .terminal ⟨contact33, contact11, contact29⟩ (finish_receipt_window endpoint_18_44_flag endpoint_18_44_sources 17 215862474548258573 215862474548258573 rfl endpoint_18_44_base endpoint_18_44_p17) (by decide)⟩
private def endpoint_18_45_flag : Flag := ⟨18, 45, 2380⟩
private def endpoint_18_45_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_45_base : receiptBase endpoint_18_45_flag endpoint_18_45_sources = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_w0 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_w2 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 2 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 4 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 2 2 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_w0 endpoint_18_45_w2
private theorem endpoint_18_45_w4 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 4 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 6 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 4 2 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_p4 endpoint_18_45_w4
private theorem endpoint_18_45_w6 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 6 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 8 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 6 2 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_p6 endpoint_18_45_w6
private theorem endpoint_18_45_w8 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 8 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 10 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 8 2 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_p8 endpoint_18_45_w8
private theorem endpoint_18_45_w10 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 10 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 12 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 10 2 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_p10 endpoint_18_45_w10
private theorem endpoint_18_45_w12 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 12 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 14 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 12 2 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_p12 endpoint_18_45_w12
private theorem endpoint_18_45_w14 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 14 2 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 16 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 14 2 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_p14 endpoint_18_45_w14
private theorem endpoint_18_45_w16 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 16 1 216937007446985937 = some 216937007446985937 := by decide +kernel
private theorem endpoint_18_45_p17 : receiptWindow endpoint_18_45_flag endpoint_18_45_sources 0 17 216937007446985937 = some 216937007446985937 :=
  join_receipt_window endpoint_18_45_flag endpoint_18_45_sources 0 16 1 216937007446985937 216937007446985937 216937007446985937 endpoint_18_45_p16 endpoint_18_45_w16
def endpoint_18_45 : CertifiedEndpoint :=
  ⟨⟨18, 45, 2380⟩, 216937007446985937, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_45_flag endpoint_18_45_sources 17 216937007446985937 216937007446985937 rfl endpoint_18_45_base endpoint_18_45_p17) (by decide)⟩
private def endpoint_18_46_flag : Flag := ⟨18, 46, 2336⟩
private def endpoint_18_46_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_46_base : receiptBase endpoint_18_46_flag endpoint_18_46_sources = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_w0 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_w2 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 2 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 4 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 2 2 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_w0 endpoint_18_46_w2
private theorem endpoint_18_46_w4 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 4 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 6 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 4 2 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_p4 endpoint_18_46_w4
private theorem endpoint_18_46_w6 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 6 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 8 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 6 2 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_p6 endpoint_18_46_w6
private theorem endpoint_18_46_w8 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 8 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 10 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 8 2 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_p8 endpoint_18_46_w8
private theorem endpoint_18_46_w10 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 10 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 12 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 10 2 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_p10 endpoint_18_46_w10
private theorem endpoint_18_46_w12 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 12 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 14 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 12 2 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_p12 endpoint_18_46_w12
private theorem endpoint_18_46_w14 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 14 2 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 16 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 14 2 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_p14 endpoint_18_46_w14
private theorem endpoint_18_46_w16 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 16 1 217138892057386490 = some 217138892057386490 := by decide +kernel
private theorem endpoint_18_46_p17 : receiptWindow endpoint_18_46_flag endpoint_18_46_sources 0 17 217138892057386490 = some 217138892057386490 :=
  join_receipt_window endpoint_18_46_flag endpoint_18_46_sources 0 16 1 217138892057386490 217138892057386490 217138892057386490 endpoint_18_46_p16 endpoint_18_46_w16
def endpoint_18_46 : CertifiedEndpoint :=
  ⟨⟨18, 46, 2336⟩, 217138892057386490, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_46_flag endpoint_18_46_sources 17 217138892057386490 217138892057386490 rfl endpoint_18_46_base endpoint_18_46_p17) (by decide)⟩
private def endpoint_18_47_flag : Flag := ⟨18, 47, 2291⟩
private def endpoint_18_47_sources : Sources := ⟨contact14, contact14, contact29⟩
private theorem endpoint_18_47_base : receiptBase endpoint_18_47_flag endpoint_18_47_sources = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_w0 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_w2 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 2 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 4 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 2 2 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_w0 endpoint_18_47_w2
private theorem endpoint_18_47_w4 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 4 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 6 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 4 2 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_p4 endpoint_18_47_w4
private theorem endpoint_18_47_w6 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 6 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 8 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 6 2 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_p6 endpoint_18_47_w6
private theorem endpoint_18_47_w8 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 8 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 10 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 8 2 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_p8 endpoint_18_47_w8
private theorem endpoint_18_47_w10 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 10 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 12 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 10 2 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_p10 endpoint_18_47_w10
private theorem endpoint_18_47_w12 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 12 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 14 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 12 2 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_p12 endpoint_18_47_w12
private theorem endpoint_18_47_w14 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 14 2 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 16 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 14 2 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_p14 endpoint_18_47_w14
private theorem endpoint_18_47_w16 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 16 1 217097192472251089 = some 217097192472251089 := by decide +kernel
private theorem endpoint_18_47_p17 : receiptWindow endpoint_18_47_flag endpoint_18_47_sources 0 17 217097192472251089 = some 217097192472251089 :=
  join_receipt_window endpoint_18_47_flag endpoint_18_47_sources 0 16 1 217097192472251089 217097192472251089 217097192472251089 endpoint_18_47_p16 endpoint_18_47_w16
def endpoint_18_47 : CertifiedEndpoint :=
  ⟨⟨18, 47, 2291⟩, 217097192472251089, .terminal ⟨contact14, contact14, contact29⟩ (finish_receipt_window endpoint_18_47_flag endpoint_18_47_sources 17 217097192472251089 217097192472251089 rfl endpoint_18_47_base endpoint_18_47_p17) (by decide)⟩
private def endpoint_18_48_flag : Flag := ⟨18, 48, 2246⟩
private def endpoint_18_48_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_48_base : receiptBase endpoint_18_48_flag endpoint_18_48_sources = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_w0 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_w2 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 2 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 4 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 2 2 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_w0 endpoint_18_48_w2
private theorem endpoint_18_48_w4 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 4 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 6 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 4 2 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_p4 endpoint_18_48_w4
private theorem endpoint_18_48_w6 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 6 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 8 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 6 2 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_p6 endpoint_18_48_w6
private theorem endpoint_18_48_w8 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 8 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 10 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 8 2 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_p8 endpoint_18_48_w8
private theorem endpoint_18_48_w10 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 10 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 12 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 10 2 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_p10 endpoint_18_48_w10
private theorem endpoint_18_48_w12 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 12 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 14 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 12 2 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_p12 endpoint_18_48_w12
private theorem endpoint_18_48_w14 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 14 2 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 16 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 14 2 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_p14 endpoint_18_48_w14
private theorem endpoint_18_48_w16 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 16 1 217758445898914943 = some 217758445898914943 := by decide +kernel
private theorem endpoint_18_48_p17 : receiptWindow endpoint_18_48_flag endpoint_18_48_sources 0 17 217758445898914943 = some 217758445898914943 :=
  join_receipt_window endpoint_18_48_flag endpoint_18_48_sources 0 16 1 217758445898914943 217758445898914943 217758445898914943 endpoint_18_48_p16 endpoint_18_48_w16
def endpoint_18_48 : CertifiedEndpoint :=
  ⟨⟨18, 48, 2246⟩, 217758445898914943, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_48_flag endpoint_18_48_sources 17 217758445898914943 217758445898914943 rfl endpoint_18_48_base endpoint_18_48_p17) (by decide)⟩
private def endpoint_18_49_flag : Flag := ⟨18, 49, 2199⟩
private def endpoint_18_49_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_49_base : receiptBase endpoint_18_49_flag endpoint_18_49_sources = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_w0 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_w2 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 2 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 4 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 2 2 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_w0 endpoint_18_49_w2
private theorem endpoint_18_49_w4 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 4 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 6 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 4 2 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_p4 endpoint_18_49_w4
private theorem endpoint_18_49_w6 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 6 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 8 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 6 2 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_p6 endpoint_18_49_w6
private theorem endpoint_18_49_w8 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 8 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 10 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 8 2 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_p8 endpoint_18_49_w8
private theorem endpoint_18_49_w10 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 10 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 12 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 10 2 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_p10 endpoint_18_49_w10
private theorem endpoint_18_49_w12 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 12 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 14 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 12 2 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_p12 endpoint_18_49_w12
private theorem endpoint_18_49_w14 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 14 2 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 16 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 14 2 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_p14 endpoint_18_49_w14
private theorem endpoint_18_49_w16 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 16 1 217210710241702153 = some 217210710241702153 := by decide +kernel
private theorem endpoint_18_49_p17 : receiptWindow endpoint_18_49_flag endpoint_18_49_sources 0 17 217210710241702153 = some 217210710241702153 :=
  join_receipt_window endpoint_18_49_flag endpoint_18_49_sources 0 16 1 217210710241702153 217210710241702153 217210710241702153 endpoint_18_49_p16 endpoint_18_49_w16
def endpoint_18_49 : CertifiedEndpoint :=
  ⟨⟨18, 49, 2199⟩, 217210710241702153, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_49_flag endpoint_18_49_sources 17 217210710241702153 217210710241702153 rfl endpoint_18_49_base endpoint_18_49_p17) (by decide)⟩
private def endpoint_18_50_flag : Flag := ⟨18, 50, 2152⟩
private def endpoint_18_50_sources : Sources := ⟨contact15, contact16, contact29⟩
private theorem endpoint_18_50_base : receiptBase endpoint_18_50_flag endpoint_18_50_sources = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_w0 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_w2 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 2 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 4 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 2 2 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_w0 endpoint_18_50_w2
private theorem endpoint_18_50_w4 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 4 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 6 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 4 2 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_p4 endpoint_18_50_w4
private theorem endpoint_18_50_w6 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 6 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 8 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 6 2 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_p6 endpoint_18_50_w6
private theorem endpoint_18_50_w8 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 8 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 10 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 8 2 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_p8 endpoint_18_50_w8
private theorem endpoint_18_50_w10 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 10 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 12 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 10 2 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_p10 endpoint_18_50_w10
private theorem endpoint_18_50_w12 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 12 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 14 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 12 2 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_p12 endpoint_18_50_w12
private theorem endpoint_18_50_w14 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 14 2 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 16 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 14 2 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_p14 endpoint_18_50_w14
private theorem endpoint_18_50_w16 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 16 1 216499150407208706 = some 216499150407208706 := by decide +kernel
private theorem endpoint_18_50_p17 : receiptWindow endpoint_18_50_flag endpoint_18_50_sources 0 17 216499150407208706 = some 216499150407208706 :=
  join_receipt_window endpoint_18_50_flag endpoint_18_50_sources 0 16 1 216499150407208706 216499150407208706 216499150407208706 endpoint_18_50_p16 endpoint_18_50_w16
def endpoint_18_50 : CertifiedEndpoint :=
  ⟨⟨18, 50, 2152⟩, 216499150407208706, .terminal ⟨contact15, contact16, contact29⟩ (finish_receipt_window endpoint_18_50_flag endpoint_18_50_sources 17 216499150407208706 216499150407208706 rfl endpoint_18_50_base endpoint_18_50_p17) (by decide)⟩
private def endpoint_18_51_flag : Flag := ⟨18, 51, 2103⟩
private def endpoint_18_51_sources : Sources := ⟨contact15, contact16, contact12⟩
private theorem endpoint_18_51_base : receiptBase endpoint_18_51_flag endpoint_18_51_sources = some 215484678769129895 := by decide +kernel
private theorem endpoint_18_51_w0 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 2 215484678769129895 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_w2 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 2 2 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 4 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 2 2 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_w0 endpoint_18_51_w2
private theorem endpoint_18_51_w4 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 4 2 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 6 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 4 2 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_p4 endpoint_18_51_w4
private theorem endpoint_18_51_w6 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 6 2 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 8 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 6 2 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_p6 endpoint_18_51_w6
private theorem endpoint_18_51_w8 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 8 2 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 10 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 8 2 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_p8 endpoint_18_51_w8
private theorem endpoint_18_51_w10 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 10 2 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 12 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 10 2 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_p10 endpoint_18_51_w10
private theorem endpoint_18_51_w12 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 12 2 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 14 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 12 2 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_p12 endpoint_18_51_w12
private theorem endpoint_18_51_w14 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 14 2 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 16 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 14 2 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_p14 endpoint_18_51_w14
private theorem endpoint_18_51_w16 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 16 1 216907409683559232 = some 216907409683559232 := by decide +kernel
private theorem endpoint_18_51_p17 : receiptWindow endpoint_18_51_flag endpoint_18_51_sources 0 17 215484678769129895 = some 216907409683559232 :=
  join_receipt_window endpoint_18_51_flag endpoint_18_51_sources 0 16 1 215484678769129895 216907409683559232 216907409683559232 endpoint_18_51_p16 endpoint_18_51_w16
def endpoint_18_51 : CertifiedEndpoint :=
  ⟨⟨18, 51, 2103⟩, 216907409683559232, .terminal ⟨contact15, contact16, contact12⟩ (finish_receipt_window endpoint_18_51_flag endpoint_18_51_sources 17 215484678769129895 216907409683559232 rfl endpoint_18_51_base endpoint_18_51_p17) (by decide)⟩
private def endpoint_18_52_flag : Flag := ⟨18, 52, 2054⟩
private def endpoint_18_52_sources : Sources := ⟨contact29, contact16, contact12⟩
private theorem endpoint_18_52_base : receiptBase endpoint_18_52_flag endpoint_18_52_sources = some 214739421301693794 := by decide +kernel
private theorem endpoint_18_52_w0 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 2 214739421301693794 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_w2 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 2 2 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 4 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 2 2 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_w0 endpoint_18_52_w2
private theorem endpoint_18_52_w4 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 4 2 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 6 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 4 2 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_p4 endpoint_18_52_w4
private theorem endpoint_18_52_w6 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 6 2 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 8 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 6 2 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_p6 endpoint_18_52_w6
private theorem endpoint_18_52_w8 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 8 2 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 10 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 8 2 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_p8 endpoint_18_52_w8
private theorem endpoint_18_52_w10 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 10 2 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 12 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 10 2 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_p10 endpoint_18_52_w10
private theorem endpoint_18_52_w12 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 12 2 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 14 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 12 2 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_p12 endpoint_18_52_w12
private theorem endpoint_18_52_w14 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 14 2 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 16 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 14 2 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_p14 endpoint_18_52_w14
private theorem endpoint_18_52_w16 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 16 1 218036076283624504 = some 218036076283624504 := by decide +kernel
private theorem endpoint_18_52_p17 : receiptWindow endpoint_18_52_flag endpoint_18_52_sources 0 17 214739421301693794 = some 218036076283624504 :=
  join_receipt_window endpoint_18_52_flag endpoint_18_52_sources 0 16 1 214739421301693794 218036076283624504 218036076283624504 endpoint_18_52_p16 endpoint_18_52_w16
def endpoint_18_52 : CertifiedEndpoint :=
  ⟨⟨18, 52, 2054⟩, 218036076283624504, .terminal ⟨contact29, contact16, contact12⟩ (finish_receipt_window endpoint_18_52_flag endpoint_18_52_sources 17 214739421301693794 218036076283624504 rfl endpoint_18_52_base endpoint_18_52_p17) (by decide)⟩
private def endpoint_18_53_flag : Flag := ⟨18, 53, 2004⟩
private def endpoint_18_53_sources : Sources := ⟨contact12, contact19, contact12⟩
private theorem endpoint_18_53_base : receiptBase endpoint_18_53_flag endpoint_18_53_sources = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_w0 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_w2 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 2 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 4 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 2 2 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_w0 endpoint_18_53_w2
private theorem endpoint_18_53_w4 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 4 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 6 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 4 2 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_p4 endpoint_18_53_w4
private theorem endpoint_18_53_w6 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 6 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 8 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 6 2 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_p6 endpoint_18_53_w6
private theorem endpoint_18_53_w8 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 8 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 10 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 8 2 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_p8 endpoint_18_53_w8
private theorem endpoint_18_53_w10 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 10 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 12 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 10 2 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_p10 endpoint_18_53_w10
private theorem endpoint_18_53_w12 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 12 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 14 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 12 2 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_p12 endpoint_18_53_w12
private theorem endpoint_18_53_w14 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 14 2 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 16 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 14 2 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_p14 endpoint_18_53_w14
private theorem endpoint_18_53_w16 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 16 1 214973996344587049 = some 214973996344587049 := by decide +kernel
private theorem endpoint_18_53_p17 : receiptWindow endpoint_18_53_flag endpoint_18_53_sources 0 17 214973996344587049 = some 214973996344587049 :=
  join_receipt_window endpoint_18_53_flag endpoint_18_53_sources 0 16 1 214973996344587049 214973996344587049 214973996344587049 endpoint_18_53_p16 endpoint_18_53_w16
def endpoint_18_53 : CertifiedEndpoint :=
  ⟨⟨18, 53, 2004⟩, 214973996344587049, .terminal ⟨contact12, contact19, contact12⟩ (finish_receipt_window endpoint_18_53_flag endpoint_18_53_sources 17 214973996344587049 214973996344587049 rfl endpoint_18_53_base endpoint_18_53_p17) (by decide)⟩
private def endpoint_18_54_flag : Flag := ⟨18, 54, 1952⟩
private def endpoint_18_54_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_54_base : receiptBase endpoint_18_54_flag endpoint_18_54_sources = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_w0 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_w2 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 2 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 4 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 2 2 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_w0 endpoint_18_54_w2
private theorem endpoint_18_54_w4 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 4 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 6 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 4 2 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_p4 endpoint_18_54_w4
private theorem endpoint_18_54_w6 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 6 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 8 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 6 2 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_p6 endpoint_18_54_w6
private theorem endpoint_18_54_w8 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 8 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 10 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 8 2 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_p8 endpoint_18_54_w8
private theorem endpoint_18_54_w10 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 10 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 12 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 10 2 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_p10 endpoint_18_54_w10
private theorem endpoint_18_54_w12 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 12 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 14 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 12 2 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_p12 endpoint_18_54_w12
private theorem endpoint_18_54_w14 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 14 2 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 16 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 14 2 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_p14 endpoint_18_54_w14
private theorem endpoint_18_54_w16 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 16 1 215276646326186295 = some 215276646326186295 := by decide +kernel
private theorem endpoint_18_54_p17 : receiptWindow endpoint_18_54_flag endpoint_18_54_sources 0 17 215276646326186295 = some 215276646326186295 :=
  join_receipt_window endpoint_18_54_flag endpoint_18_54_sources 0 16 1 215276646326186295 215276646326186295 215276646326186295 endpoint_18_54_p16 endpoint_18_54_w16
def endpoint_18_54 : CertifiedEndpoint :=
  ⟨⟨18, 54, 1952⟩, 215276646326186295, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_54_flag endpoint_18_54_sources 17 215276646326186295 215276646326186295 rfl endpoint_18_54_base endpoint_18_54_p17) (by decide)⟩
private def endpoint_18_55_flag : Flag := ⟨18, 55, 1900⟩
private def endpoint_18_55_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_55_base : receiptBase endpoint_18_55_flag endpoint_18_55_sources = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_w0 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_w2 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 2 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 4 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 2 2 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_w0 endpoint_18_55_w2
private theorem endpoint_18_55_w4 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 4 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 6 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 4 2 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_p4 endpoint_18_55_w4
private theorem endpoint_18_55_w6 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 6 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 8 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 6 2 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_p6 endpoint_18_55_w6
private theorem endpoint_18_55_w8 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 8 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 10 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 8 2 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_p8 endpoint_18_55_w8
private theorem endpoint_18_55_w10 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 10 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 12 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 10 2 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_p10 endpoint_18_55_w10
private theorem endpoint_18_55_w12 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 12 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 14 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 12 2 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_p12 endpoint_18_55_w12
private theorem endpoint_18_55_w14 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 14 2 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 16 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 14 2 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_p14 endpoint_18_55_w14
private theorem endpoint_18_55_w16 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 16 1 212984213871947676 = some 212984213871947676 := by decide +kernel
private theorem endpoint_18_55_p17 : receiptWindow endpoint_18_55_flag endpoint_18_55_sources 0 17 212984213871947676 = some 212984213871947676 :=
  join_receipt_window endpoint_18_55_flag endpoint_18_55_sources 0 16 1 212984213871947676 212984213871947676 212984213871947676 endpoint_18_55_p16 endpoint_18_55_w16
def endpoint_18_55 : CertifiedEndpoint :=
  ⟨⟨18, 55, 1900⟩, 212984213871947676, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_55_flag endpoint_18_55_sources 17 212984213871947676 212984213871947676 rfl endpoint_18_55_base endpoint_18_55_p17) (by decide)⟩
private def endpoint_18_56_flag : Flag := ⟨18, 56, 1846⟩
private def endpoint_18_56_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_56_base : receiptBase endpoint_18_56_flag endpoint_18_56_sources = some 208477234486649635 := by decide +kernel
private theorem endpoint_18_56_w0 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 2 208477234486649635 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_w2 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 2 2 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 4 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 2 2 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_w0 endpoint_18_56_w2
private theorem endpoint_18_56_w4 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 4 2 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 6 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 4 2 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_p4 endpoint_18_56_w4
private theorem endpoint_18_56_w6 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 6 2 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 8 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 6 2 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_p6 endpoint_18_56_w6
private theorem endpoint_18_56_w8 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 8 2 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 10 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 8 2 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_p8 endpoint_18_56_w8
private theorem endpoint_18_56_w10 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 10 2 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 12 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 10 2 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_p10 endpoint_18_56_w10
private theorem endpoint_18_56_w12 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 12 2 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 14 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 12 2 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_p12 endpoint_18_56_w12
private theorem endpoint_18_56_w14 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 14 2 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 16 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 14 2 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_p14 endpoint_18_56_w14
private theorem endpoint_18_56_w16 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 16 1 210272567926245008 = some 210272567926245008 := by decide +kernel
private theorem endpoint_18_56_p17 : receiptWindow endpoint_18_56_flag endpoint_18_56_sources 0 17 208477234486649635 = some 210272567926245008 :=
  join_receipt_window endpoint_18_56_flag endpoint_18_56_sources 0 16 1 208477234486649635 210272567926245008 210272567926245008 endpoint_18_56_p16 endpoint_18_56_w16
def endpoint_18_56 : CertifiedEndpoint :=
  ⟨⟨18, 56, 1846⟩, 210272567926245008, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_56_flag endpoint_18_56_sources 17 208477234486649635 210272567926245008 rfl endpoint_18_56_base endpoint_18_56_p17) (by decide)⟩
private def endpoint_18_57_flag : Flag := ⟨18, 57, 1792⟩
private def endpoint_18_57_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_18_57_base : receiptBase endpoint_18_57_flag endpoint_18_57_sources = some 205624018918896014 := by decide +kernel
private theorem endpoint_18_57_w0 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 2 205624018918896014 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_w2 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 2 2 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 4 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 2 2 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_w0 endpoint_18_57_w2
private theorem endpoint_18_57_w4 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 4 2 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 6 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 4 2 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_p4 endpoint_18_57_w4
private theorem endpoint_18_57_w6 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 6 2 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 8 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 6 2 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_p6 endpoint_18_57_w6
private theorem endpoint_18_57_w8 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 8 2 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 10 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 8 2 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_p8 endpoint_18_57_w8
private theorem endpoint_18_57_w10 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 10 2 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 12 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 10 2 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_p10 endpoint_18_57_w10
private theorem endpoint_18_57_w12 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 12 2 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 14 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 12 2 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_p12 endpoint_18_57_w12
private theorem endpoint_18_57_w14 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 14 2 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 16 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 14 2 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_p14 endpoint_18_57_w14
private theorem endpoint_18_57_w16 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 16 1 211208754915678147 = some 211208754915678147 := by decide +kernel
private theorem endpoint_18_57_p17 : receiptWindow endpoint_18_57_flag endpoint_18_57_sources 0 17 205624018918896014 = some 211208754915678147 :=
  join_receipt_window endpoint_18_57_flag endpoint_18_57_sources 0 16 1 205624018918896014 211208754915678147 211208754915678147 endpoint_18_57_p16 endpoint_18_57_w16
def endpoint_18_57 : CertifiedEndpoint :=
  ⟨⟨18, 57, 1792⟩, 211208754915678147, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_18_57_flag endpoint_18_57_sources 17 205624018918896014 211208754915678147 rfl endpoint_18_57_base endpoint_18_57_p17) (by decide)⟩
private def endpoint_18_58_flag : Flag := ⟨18, 58, 1736⟩
private def endpoint_18_58_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_58_base : receiptBase endpoint_18_58_flag endpoint_18_58_sources = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_w0 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_w2 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 2 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 4 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 2 2 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_w0 endpoint_18_58_w2
private theorem endpoint_18_58_w4 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 4 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 6 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 4 2 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_p4 endpoint_18_58_w4
private theorem endpoint_18_58_w6 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 6 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 8 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 6 2 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_p6 endpoint_18_58_w6
private theorem endpoint_18_58_w8 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 8 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 10 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 8 2 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_p8 endpoint_18_58_w8
private theorem endpoint_18_58_w10 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 10 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 12 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 10 2 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_p10 endpoint_18_58_w10
private theorem endpoint_18_58_w12 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 12 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 14 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 12 2 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_p12 endpoint_18_58_w12
private theorem endpoint_18_58_w14 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 14 2 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 16 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 14 2 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_p14 endpoint_18_58_w14
private theorem endpoint_18_58_w16 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 16 1 204067095164929844 = some 204067095164929844 := by decide +kernel
private theorem endpoint_18_58_p17 : receiptWindow endpoint_18_58_flag endpoint_18_58_sources 0 17 204067095164929844 = some 204067095164929844 :=
  join_receipt_window endpoint_18_58_flag endpoint_18_58_sources 0 16 1 204067095164929844 204067095164929844 204067095164929844 endpoint_18_58_p16 endpoint_18_58_w16
def endpoint_18_58 : CertifiedEndpoint :=
  ⟨⟨18, 58, 1736⟩, 204067095164929844, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_58_flag endpoint_18_58_sources 17 204067095164929844 204067095164929844 rfl endpoint_18_58_base endpoint_18_58_p17) (by decide)⟩
private def endpoint_18_59_flag : Flag := ⟨18, 59, 1679⟩
private def endpoint_18_59_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_59_base : receiptBase endpoint_18_59_flag endpoint_18_59_sources = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_w0 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_w2 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 2 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 4 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 2 2 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_w0 endpoint_18_59_w2
private theorem endpoint_18_59_w4 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 4 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 6 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 4 2 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_p4 endpoint_18_59_w4
private theorem endpoint_18_59_w6 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 6 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 8 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 6 2 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_p6 endpoint_18_59_w6
private theorem endpoint_18_59_w8 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 8 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 10 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 8 2 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_p8 endpoint_18_59_w8
private theorem endpoint_18_59_w10 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 10 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 12 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 10 2 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_p10 endpoint_18_59_w10
private theorem endpoint_18_59_w12 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 12 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 14 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 12 2 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_p12 endpoint_18_59_w12
private theorem endpoint_18_59_w14 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 14 2 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 16 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 14 2 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_p14 endpoint_18_59_w14
private theorem endpoint_18_59_w16 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 16 1 200430539935673898 = some 200430539935673898 := by decide +kernel
private theorem endpoint_18_59_p17 : receiptWindow endpoint_18_59_flag endpoint_18_59_sources 0 17 200430539935673898 = some 200430539935673898 :=
  join_receipt_window endpoint_18_59_flag endpoint_18_59_sources 0 16 1 200430539935673898 200430539935673898 200430539935673898 endpoint_18_59_p16 endpoint_18_59_w16
def endpoint_18_59 : CertifiedEndpoint :=
  ⟨⟨18, 59, 1679⟩, 200430539935673898, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_59_flag endpoint_18_59_sources 17 200430539935673898 200430539935673898 rfl endpoint_18_59_base endpoint_18_59_p17) (by decide)⟩
private def endpoint_18_60_flag : Flag := ⟨18, 60, 1620⟩
private def endpoint_18_60_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_18_60_base : receiptBase endpoint_18_60_flag endpoint_18_60_sources = some 196351940854187066 := by decide +kernel
private theorem endpoint_18_60_w0 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 2 196351940854187066 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_w2 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 2 2 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 4 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 2 2 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_w0 endpoint_18_60_w2
private theorem endpoint_18_60_w4 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 4 2 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 6 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 4 2 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_p4 endpoint_18_60_w4
private theorem endpoint_18_60_w6 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 6 2 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 8 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 6 2 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_p6 endpoint_18_60_w6
private theorem endpoint_18_60_w8 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 8 2 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 10 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 8 2 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_p8 endpoint_18_60_w8
private theorem endpoint_18_60_w10 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 10 2 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 12 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 10 2 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_p10 endpoint_18_60_w10
private theorem endpoint_18_60_w12 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 12 2 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 14 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 12 2 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_p12 endpoint_18_60_w12
private theorem endpoint_18_60_w14 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 14 2 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 16 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 14 2 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_p14 endpoint_18_60_w14
private theorem endpoint_18_60_w16 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 16 1 197012120013520704 = some 197012120013520704 := by decide +kernel
private theorem endpoint_18_60_p17 : receiptWindow endpoint_18_60_flag endpoint_18_60_sources 0 17 196351940854187066 = some 197012120013520704 :=
  join_receipt_window endpoint_18_60_flag endpoint_18_60_sources 0 16 1 196351940854187066 197012120013520704 197012120013520704 endpoint_18_60_p16 endpoint_18_60_w16
def endpoint_18_60 : CertifiedEndpoint :=
  ⟨⟨18, 60, 1620⟩, 197012120013520704, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_18_60_flag endpoint_18_60_sources 17 196351940854187066 197012120013520704 rfl endpoint_18_60_base endpoint_18_60_p17) (by decide)⟩
private def endpoint_18_61_flag : Flag := ⟨18, 61, 1561⟩
private def endpoint_18_61_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_18_61_base : receiptBase endpoint_18_61_flag endpoint_18_61_sources = some 192282061039591175 := by decide +kernel
private theorem endpoint_18_61_w0 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 2 192282061039591175 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_w2 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 2 2 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 4 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 2 2 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_w0 endpoint_18_61_w2
private theorem endpoint_18_61_w4 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 4 2 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 6 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 4 2 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_p4 endpoint_18_61_w4
private theorem endpoint_18_61_w6 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 6 2 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 8 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 6 2 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_p6 endpoint_18_61_w6
private theorem endpoint_18_61_w8 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 8 2 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 10 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 8 2 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_p8 endpoint_18_61_w8
private theorem endpoint_18_61_w10 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 10 2 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 12 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 10 2 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_p10 endpoint_18_61_w10
private theorem endpoint_18_61_w12 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 12 2 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 14 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 12 2 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_p12 endpoint_18_61_w12
private theorem endpoint_18_61_w14 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 14 2 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 16 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 14 2 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_p14 endpoint_18_61_w14
private theorem endpoint_18_61_w16 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 16 1 193719754677396729 = some 193719754677396729 := by decide +kernel
private theorem endpoint_18_61_p17 : receiptWindow endpoint_18_61_flag endpoint_18_61_sources 0 17 192282061039591175 = some 193719754677396729 :=
  join_receipt_window endpoint_18_61_flag endpoint_18_61_sources 0 16 1 192282061039591175 193719754677396729 193719754677396729 endpoint_18_61_p16 endpoint_18_61_w16
def endpoint_18_61 : CertifiedEndpoint :=
  ⟨⟨18, 61, 1561⟩, 193719754677396729, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_18_61_flag endpoint_18_61_sources 17 192282061039591175 193719754677396729 rfl endpoint_18_61_base endpoint_18_61_p17) (by decide)⟩
private def endpoint_18_62_flag : Flag := ⟨18, 62, 1500⟩
private def endpoint_18_62_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_18_62_base : receiptBase endpoint_18_62_flag endpoint_18_62_sources = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_w0 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_w2 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 2 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 4 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 2 2 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_w0 endpoint_18_62_w2
private theorem endpoint_18_62_w4 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 4 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 6 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 4 2 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_p4 endpoint_18_62_w4
private theorem endpoint_18_62_w6 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 6 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 8 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 6 2 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_p6 endpoint_18_62_w6
private theorem endpoint_18_62_w8 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 8 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 10 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 8 2 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_p8 endpoint_18_62_w8
private theorem endpoint_18_62_w10 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 10 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 12 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 10 2 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_p10 endpoint_18_62_w10
private theorem endpoint_18_62_w12 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 12 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 14 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 12 2 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_p12 endpoint_18_62_w12
private theorem endpoint_18_62_w14 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 14 2 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 16 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 14 2 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_p14 endpoint_18_62_w14
private theorem endpoint_18_62_w16 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 16 1 189079638733937054 = some 189079638733937054 := by decide +kernel
private theorem endpoint_18_62_p17 : receiptWindow endpoint_18_62_flag endpoint_18_62_sources 0 17 189079638733937054 = some 189079638733937054 :=
  join_receipt_window endpoint_18_62_flag endpoint_18_62_sources 0 16 1 189079638733937054 189079638733937054 189079638733937054 endpoint_18_62_p16 endpoint_18_62_w16
def endpoint_18_62 : CertifiedEndpoint :=
  ⟨⟨18, 62, 1500⟩, 189079638733937054, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_18_62_flag endpoint_18_62_sources 17 189079638733937054 189079638733937054 rfl endpoint_18_62_base endpoint_18_62_p17) (by decide)⟩
private def endpoint_18_63_flag : Flag := ⟨18, 63, 1437⟩
private def endpoint_18_63_sources : Sources := ⟨contact20, contact22, contact22⟩
private theorem endpoint_18_63_base : receiptBase endpoint_18_63_flag endpoint_18_63_sources = some 183987096784548733 := by decide +kernel
private theorem endpoint_18_63_w0 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 2 183987096784548733 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_w2 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 2 2 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 4 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 2 2 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_w0 endpoint_18_63_w2
private theorem endpoint_18_63_w4 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 4 2 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 6 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 4 2 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_p4 endpoint_18_63_w4
private theorem endpoint_18_63_w6 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 6 2 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 8 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 6 2 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_p6 endpoint_18_63_w6
private theorem endpoint_18_63_w8 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 8 2 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 10 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 8 2 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_p8 endpoint_18_63_w8
private theorem endpoint_18_63_w10 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 10 2 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 12 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 10 2 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_p10 endpoint_18_63_w10
private theorem endpoint_18_63_w12 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 12 2 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 14 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 12 2 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_p12 endpoint_18_63_w12
private theorem endpoint_18_63_w14 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 14 2 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 16 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 14 2 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_p14 endpoint_18_63_w14
private theorem endpoint_18_63_w16 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 16 1 184469509322275848 = some 184469509322275848 := by decide +kernel
private theorem endpoint_18_63_p17 : receiptWindow endpoint_18_63_flag endpoint_18_63_sources 0 17 183987096784548733 = some 184469509322275848 :=
  join_receipt_window endpoint_18_63_flag endpoint_18_63_sources 0 16 1 183987096784548733 184469509322275848 184469509322275848 endpoint_18_63_p16 endpoint_18_63_w16
def endpoint_18_63 : CertifiedEndpoint :=
  ⟨⟨18, 63, 1437⟩, 184469509322275848, .terminal ⟨contact20, contact22, contact22⟩ (finish_receipt_window endpoint_18_63_flag endpoint_18_63_sources 17 183987096784548733 184469509322275848 rfl endpoint_18_63_base endpoint_18_63_p17) (by decide)⟩
private def endpoint_18_64_flag : Flag := ⟨18, 64, 1374⟩
private def endpoint_18_64_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_64_base : receiptBase endpoint_18_64_flag endpoint_18_64_sources = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_w0 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_w2 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 2 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 4 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 2 2 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_w0 endpoint_18_64_w2
private theorem endpoint_18_64_w4 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 4 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 6 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 4 2 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_p4 endpoint_18_64_w4
private theorem endpoint_18_64_w6 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 6 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 8 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 6 2 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_p6 endpoint_18_64_w6
private theorem endpoint_18_64_w8 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 8 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 10 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 8 2 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_p8 endpoint_18_64_w8
private theorem endpoint_18_64_w10 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 10 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 12 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 10 2 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_p10 endpoint_18_64_w10
private theorem endpoint_18_64_w12 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 12 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 14 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 12 2 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_p12 endpoint_18_64_w12
private theorem endpoint_18_64_w14 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 14 2 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 16 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 14 2 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_p14 endpoint_18_64_w14
private theorem endpoint_18_64_w16 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 16 1 180365045794723387 = some 180365045794723387 := by decide +kernel
private theorem endpoint_18_64_p17 : receiptWindow endpoint_18_64_flag endpoint_18_64_sources 0 17 180365045794723387 = some 180365045794723387 :=
  join_receipt_window endpoint_18_64_flag endpoint_18_64_sources 0 16 1 180365045794723387 180365045794723387 180365045794723387 endpoint_18_64_p16 endpoint_18_64_w16
def endpoint_18_64 : CertifiedEndpoint :=
  ⟨⟨18, 64, 1374⟩, 180365045794723387, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_64_flag endpoint_18_64_sources 17 180365045794723387 180365045794723387 rfl endpoint_18_64_base endpoint_18_64_p17) (by decide)⟩
private def endpoint_18_65_flag : Flag := ⟨18, 65, 1309⟩
private def endpoint_18_65_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_65_base : receiptBase endpoint_18_65_flag endpoint_18_65_sources = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_w0 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_w2 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 2 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p4 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 4 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 2 2 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_w0 endpoint_18_65_w2
private theorem endpoint_18_65_w4 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 4 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p6 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 6 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 4 2 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_p4 endpoint_18_65_w4
private theorem endpoint_18_65_w6 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 6 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p8 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 8 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 6 2 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_p6 endpoint_18_65_w6
private theorem endpoint_18_65_w8 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 8 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p10 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 10 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 8 2 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_p8 endpoint_18_65_w8
private theorem endpoint_18_65_w10 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 10 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p12 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 12 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 10 2 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_p10 endpoint_18_65_w10
private theorem endpoint_18_65_w12 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 12 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p14 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 14 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 12 2 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_p12 endpoint_18_65_w12
private theorem endpoint_18_65_w14 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 14 2 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p16 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 16 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 14 2 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_p14 endpoint_18_65_w14
private theorem endpoint_18_65_w16 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 16 1 174286702659906494 = some 174286702659906494 := by decide +kernel
private theorem endpoint_18_65_p17 : receiptWindow endpoint_18_65_flag endpoint_18_65_sources 0 17 174286702659906494 = some 174286702659906494 :=
  join_receipt_window endpoint_18_65_flag endpoint_18_65_sources 0 16 1 174286702659906494 174286702659906494 174286702659906494 endpoint_18_65_p16 endpoint_18_65_w16
def endpoint_18_65 : CertifiedEndpoint :=
  ⟨⟨18, 65, 1309⟩, 174286702659906494, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_65_flag endpoint_18_65_sources 17 174286702659906494 174286702659906494 rfl endpoint_18_65_base endpoint_18_65_p17) (by decide)⟩
private def endpoint_18_66_flag : Flag := ⟨18, 66, 1242⟩
private def endpoint_18_66_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_66_base : receiptBase endpoint_18_66_flag endpoint_18_66_sources = some 167711786939540008 := by decide +kernel
private theorem endpoint_18_66_w0 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 2 167711786939540008 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_w2 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 2 2 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p4 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 4 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 2 2 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_w0 endpoint_18_66_w2
private theorem endpoint_18_66_w4 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 4 2 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p6 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 6 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 4 2 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_p4 endpoint_18_66_w4
private theorem endpoint_18_66_w6 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 6 2 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p8 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 8 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 6 2 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_p6 endpoint_18_66_w6
private theorem endpoint_18_66_w8 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 8 2 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p10 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 10 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 8 2 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_p8 endpoint_18_66_w8
private theorem endpoint_18_66_w10 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 10 2 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p12 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 12 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 10 2 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_p10 endpoint_18_66_w10
private theorem endpoint_18_66_w12 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 12 2 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p14 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 14 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 12 2 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_p12 endpoint_18_66_w12
private theorem endpoint_18_66_w14 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 14 2 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p16 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 16 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 14 2 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_p14 endpoint_18_66_w14
private theorem endpoint_18_66_w16 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 16 1 169838461290675138 = some 169838461290675138 := by decide +kernel
private theorem endpoint_18_66_p17 : receiptWindow endpoint_18_66_flag endpoint_18_66_sources 0 17 167711786939540008 = some 169838461290675138 :=
  join_receipt_window endpoint_18_66_flag endpoint_18_66_sources 0 16 1 167711786939540008 169838461290675138 169838461290675138 endpoint_18_66_p16 endpoint_18_66_w16
def endpoint_18_66 : CertifiedEndpoint :=
  ⟨⟨18, 66, 1242⟩, 169838461290675138, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_66_flag endpoint_18_66_sources 17 167711786939540008 169838461290675138 rfl endpoint_18_66_base endpoint_18_66_p17) (by decide)⟩
private def endpoint_18_67_flag : Flag := ⟨18, 67, 1174⟩
private def endpoint_18_67_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_67_base : receiptBase endpoint_18_67_flag endpoint_18_67_sources = some 160764229086696656 := by decide +kernel
private theorem endpoint_18_67_w0 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 2 160764229086696656 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_w2 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 2 2 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p4 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 4 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 2 2 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_w0 endpoint_18_67_w2
private theorem endpoint_18_67_w4 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 4 2 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p6 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 6 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 4 2 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_p4 endpoint_18_67_w4
private theorem endpoint_18_67_w6 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 6 2 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p8 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 8 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 6 2 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_p6 endpoint_18_67_w6
private theorem endpoint_18_67_w8 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 8 2 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p10 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 10 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 8 2 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_p8 endpoint_18_67_w8
private theorem endpoint_18_67_w10 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 10 2 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p12 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 12 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 10 2 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_p10 endpoint_18_67_w10
private theorem endpoint_18_67_w12 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 12 2 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p14 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 14 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 12 2 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_p12 endpoint_18_67_w12
private theorem endpoint_18_67_w14 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 14 2 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p16 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 16 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 14 2 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_p14 endpoint_18_67_w14
private theorem endpoint_18_67_w16 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 16 1 167345211306021018 = some 167345211306021018 := by decide +kernel
private theorem endpoint_18_67_p17 : receiptWindow endpoint_18_67_flag endpoint_18_67_sources 0 17 160764229086696656 = some 167345211306021018 :=
  join_receipt_window endpoint_18_67_flag endpoint_18_67_sources 0 16 1 160764229086696656 167345211306021018 167345211306021018 endpoint_18_67_p16 endpoint_18_67_w16
def endpoint_18_67 : CertifiedEndpoint :=
  ⟨⟨18, 67, 1174⟩, 167345211306021018, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_67_flag endpoint_18_67_sources 17 160764229086696656 167345211306021018 rfl endpoint_18_67_base endpoint_18_67_p17) (by decide)⟩
private def endpoint_18_68_flag : Flag := ⟨18, 68, 1104⟩
private def endpoint_18_68_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_68_base : receiptBase endpoint_18_68_flag endpoint_18_68_sources = some 153302459522104835 := by decide +kernel
private theorem endpoint_18_68_w0 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 2 153302459522104835 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_w2 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 2 2 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p4 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 4 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 2 2 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_w0 endpoint_18_68_w2
private theorem endpoint_18_68_w4 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 4 2 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p6 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 6 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 4 2 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_p4 endpoint_18_68_w4
private theorem endpoint_18_68_w6 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 6 2 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p8 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 8 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 6 2 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_p6 endpoint_18_68_w6
private theorem endpoint_18_68_w8 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 8 2 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p10 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 10 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 8 2 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_p8 endpoint_18_68_w8
private theorem endpoint_18_68_w10 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 10 2 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p12 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 12 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 10 2 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_p10 endpoint_18_68_w10
private theorem endpoint_18_68_w12 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 12 2 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p14 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 14 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 12 2 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_p12 endpoint_18_68_w12
private theorem endpoint_18_68_w14 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 14 2 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p16 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 16 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 14 2 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_p14 endpoint_18_68_w14
private theorem endpoint_18_68_w16 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 16 1 164495504423998984 = some 164495504423998984 := by decide +kernel
private theorem endpoint_18_68_p17 : receiptWindow endpoint_18_68_flag endpoint_18_68_sources 0 17 153302459522104835 = some 164495504423998984 :=
  join_receipt_window endpoint_18_68_flag endpoint_18_68_sources 0 16 1 153302459522104835 164495504423998984 164495504423998984 endpoint_18_68_p16 endpoint_18_68_w16
def endpoint_18_68 : CertifiedEndpoint :=
  ⟨⟨18, 68, 1104⟩, 164495504423998984, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_68_flag endpoint_18_68_sources 17 153302459522104835 164495504423998984 rfl endpoint_18_68_base endpoint_18_68_p17) (by decide)⟩
private def endpoint_18_69_flag : Flag := ⟨18, 69, 1032⟩
private def endpoint_18_69_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_18_69_base : receiptBase endpoint_18_69_flag endpoint_18_69_sources = some 145315894770045220 := by decide +kernel
private theorem endpoint_18_69_w0 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 2 145315894770045220 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_w2 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 2 2 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p4 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 4 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 2 2 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_w0 endpoint_18_69_w2
private theorem endpoint_18_69_w4 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 4 2 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p6 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 6 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 4 2 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_p4 endpoint_18_69_w4
private theorem endpoint_18_69_w6 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 6 2 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p8 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 8 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 6 2 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_p6 endpoint_18_69_w6
private theorem endpoint_18_69_w8 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 8 2 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p10 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 10 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 8 2 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_p8 endpoint_18_69_w8
private theorem endpoint_18_69_w10 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 10 2 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p12 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 12 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 10 2 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_p10 endpoint_18_69_w10
private theorem endpoint_18_69_w12 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 12 2 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p14 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 14 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 12 2 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_p12 endpoint_18_69_w12
private theorem endpoint_18_69_w14 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 14 2 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p16 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 16 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 14 2 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_p14 endpoint_18_69_w14
private theorem endpoint_18_69_w16 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 16 1 161280939478206258 = some 161280939478206258 := by decide +kernel
private theorem endpoint_18_69_p17 : receiptWindow endpoint_18_69_flag endpoint_18_69_sources 0 17 145315894770045220 = some 161280939478206258 :=
  join_receipt_window endpoint_18_69_flag endpoint_18_69_sources 0 16 1 145315894770045220 161280939478206258 161280939478206258 endpoint_18_69_p16 endpoint_18_69_w16
def endpoint_18_69 : CertifiedEndpoint :=
  ⟨⟨18, 69, 1032⟩, 161280939478206258, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_18_69_flag endpoint_18_69_sources 17 145315894770045220 161280939478206258 rfl endpoint_18_69_base endpoint_18_69_p17) (by decide)⟩
def endpoint_18_70 : CertifiedEndpoint :=
  ⟨⟨18, 70, 959⟩, 251356117562072861, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_71 : CertifiedEndpoint :=
  ⟨⟨18, 71, 884⟩, 234528882156696117, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_18_72 : CertifiedEndpoint :=
  ⟨⟨18, 72, 807⟩, 216454546195644597, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock11 : List CertifiedEndpoint := [
  endpoint_16_79, endpoint_16_80, endpoint_16_81, endpoint_16_82, endpoint_16_83, endpoint_16_84, endpoint_16_85,
  endpoint_16_86, endpoint_17_17, endpoint_17_18, endpoint_17_19, endpoint_17_20, endpoint_17_21, endpoint_17_22,
  endpoint_17_23, endpoint_17_24, endpoint_17_25, endpoint_17_26, endpoint_17_27, endpoint_17_28, endpoint_17_29,
  endpoint_17_30, endpoint_17_31, endpoint_17_32, endpoint_17_33, endpoint_17_34, endpoint_17_35, endpoint_17_36,
  endpoint_17_37, endpoint_17_38, endpoint_17_39, endpoint_17_40, endpoint_17_41, endpoint_17_42, endpoint_17_43,
  endpoint_17_44, endpoint_17_45, endpoint_17_46, endpoint_17_47, endpoint_17_48, endpoint_17_49, endpoint_17_50,
  endpoint_17_51, endpoint_17_52, endpoint_17_53, endpoint_17_54, endpoint_17_55, endpoint_17_56, endpoint_17_57,
  endpoint_17_58, endpoint_17_59, endpoint_17_60, endpoint_17_61, endpoint_17_62, endpoint_17_63, endpoint_17_64,
  endpoint_17_65, endpoint_17_66, endpoint_17_67, endpoint_17_68, endpoint_17_69, endpoint_17_70, endpoint_17_71,
  endpoint_17_72, endpoint_17_73, endpoint_17_74, endpoint_17_75, endpoint_17_76, endpoint_17_77, endpoint_17_78,
  endpoint_17_79, endpoint_17_80, endpoint_17_81, endpoint_17_82, endpoint_17_83, endpoint_18_18, endpoint_18_19,
  endpoint_18_20, endpoint_18_21, endpoint_18_22, endpoint_18_23, endpoint_18_24, endpoint_18_25, endpoint_18_26,
  endpoint_18_27, endpoint_18_28, endpoint_18_29, endpoint_18_30, endpoint_18_31, endpoint_18_32, endpoint_18_33,
  endpoint_18_34, endpoint_18_35, endpoint_18_36, endpoint_18_37, endpoint_18_38, endpoint_18_39, endpoint_18_40,
  endpoint_18_41, endpoint_18_42, endpoint_18_43, endpoint_18_44, endpoint_18_45, endpoint_18_46, endpoint_18_47,
  endpoint_18_48, endpoint_18_49, endpoint_18_50, endpoint_18_51, endpoint_18_52, endpoint_18_53, endpoint_18_54,
  endpoint_18_55, endpoint_18_56, endpoint_18_57, endpoint_18_58, endpoint_18_59, endpoint_18_60, endpoint_18_61,
  endpoint_18_62, endpoint_18_63, endpoint_18_64, endpoint_18_65, endpoint_18_66, endpoint_18_67, endpoint_18_68,
  endpoint_18_69, endpoint_18_70, endpoint_18_71, endpoint_18_72
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
