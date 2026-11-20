import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_14_72_flag : Flag := ⟨14, 72, 1860⟩
private def endpoint_14_72_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_14_72_base : receiptBase endpoint_14_72_flag endpoint_14_72_sources = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_w0 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 2 222717373071396821 = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_w2 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 2 2 222717373071396821 = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_p4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 4 222717373071396821 = some 222717373071396821 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 2 2 222717373071396821 222717373071396821 222717373071396821 endpoint_14_72_w0 endpoint_14_72_w2
private theorem endpoint_14_72_w4 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 4 2 222717373071396821 = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_p6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 6 222717373071396821 = some 222717373071396821 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 4 2 222717373071396821 222717373071396821 222717373071396821 endpoint_14_72_p4 endpoint_14_72_w4
private theorem endpoint_14_72_w6 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 6 2 222717373071396821 = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_p8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 8 222717373071396821 = some 222717373071396821 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 6 2 222717373071396821 222717373071396821 222717373071396821 endpoint_14_72_p6 endpoint_14_72_w6
private theorem endpoint_14_72_w8 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 8 2 222717373071396821 = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_p10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 10 222717373071396821 = some 222717373071396821 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 8 2 222717373071396821 222717373071396821 222717373071396821 endpoint_14_72_p8 endpoint_14_72_w8
private theorem endpoint_14_72_w10 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 10 2 222717373071396821 = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_p12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 12 222717373071396821 = some 222717373071396821 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 10 2 222717373071396821 222717373071396821 222717373071396821 endpoint_14_72_p10 endpoint_14_72_w10
private theorem endpoint_14_72_w12 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 12 1 222717373071396821 = some 222717373071396821 := by decide +kernel
private theorem endpoint_14_72_p13 : receiptWindow endpoint_14_72_flag endpoint_14_72_sources 0 13 222717373071396821 = some 222717373071396821 :=
  join_receipt_window endpoint_14_72_flag endpoint_14_72_sources 0 12 1 222717373071396821 222717373071396821 222717373071396821 endpoint_14_72_p12 endpoint_14_72_w12
def endpoint_14_72 : CertifiedEndpoint :=
  ⟨⟨14, 72, 1860⟩, 222717373071396821, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_14_72_flag endpoint_14_72_sources 13 222717373071396821 222717373071396821 rfl endpoint_14_72_base endpoint_14_72_p13) (by decide)⟩
private def endpoint_14_73_flag : Flag := ⟨14, 73, 1767⟩
private def endpoint_14_73_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_73_base : receiptBase endpoint_14_73_flag endpoint_14_73_sources = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_w0 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 2 216011089198681070 = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_w2 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 2 2 216011089198681070 = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_p4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 4 216011089198681070 = some 216011089198681070 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 2 2 216011089198681070 216011089198681070 216011089198681070 endpoint_14_73_w0 endpoint_14_73_w2
private theorem endpoint_14_73_w4 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 4 2 216011089198681070 = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_p6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 6 216011089198681070 = some 216011089198681070 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 4 2 216011089198681070 216011089198681070 216011089198681070 endpoint_14_73_p4 endpoint_14_73_w4
private theorem endpoint_14_73_w6 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 6 2 216011089198681070 = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_p8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 8 216011089198681070 = some 216011089198681070 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 6 2 216011089198681070 216011089198681070 216011089198681070 endpoint_14_73_p6 endpoint_14_73_w6
private theorem endpoint_14_73_w8 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 8 2 216011089198681070 = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_p10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 10 216011089198681070 = some 216011089198681070 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 8 2 216011089198681070 216011089198681070 216011089198681070 endpoint_14_73_p8 endpoint_14_73_w8
private theorem endpoint_14_73_w10 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 10 2 216011089198681070 = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_p12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 12 216011089198681070 = some 216011089198681070 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 10 2 216011089198681070 216011089198681070 216011089198681070 endpoint_14_73_p10 endpoint_14_73_w10
private theorem endpoint_14_73_w12 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 12 1 216011089198681070 = some 216011089198681070 := by decide +kernel
private theorem endpoint_14_73_p13 : receiptWindow endpoint_14_73_flag endpoint_14_73_sources 0 13 216011089198681070 = some 216011089198681070 :=
  join_receipt_window endpoint_14_73_flag endpoint_14_73_sources 0 12 1 216011089198681070 216011089198681070 216011089198681070 endpoint_14_73_p12 endpoint_14_73_w12
def endpoint_14_73 : CertifiedEndpoint :=
  ⟨⟨14, 73, 1767⟩, 216011089198681070, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_73_flag endpoint_14_73_sources 13 216011089198681070 216011089198681070 rfl endpoint_14_73_base endpoint_14_73_p13) (by decide)⟩
private def endpoint_14_74_flag : Flag := ⟨14, 74, 1670⟩
private def endpoint_14_74_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_74_base : receiptBase endpoint_14_74_flag endpoint_14_74_sources = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_w0 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 2 206733677412476077 = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_w2 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 2 2 206733677412476077 = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_p4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 4 206733677412476077 = some 206733677412476077 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 2 2 206733677412476077 206733677412476077 206733677412476077 endpoint_14_74_w0 endpoint_14_74_w2
private theorem endpoint_14_74_w4 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 4 2 206733677412476077 = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_p6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 6 206733677412476077 = some 206733677412476077 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 4 2 206733677412476077 206733677412476077 206733677412476077 endpoint_14_74_p4 endpoint_14_74_w4
private theorem endpoint_14_74_w6 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 6 2 206733677412476077 = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_p8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 8 206733677412476077 = some 206733677412476077 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 6 2 206733677412476077 206733677412476077 206733677412476077 endpoint_14_74_p6 endpoint_14_74_w6
private theorem endpoint_14_74_w8 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 8 2 206733677412476077 = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_p10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 10 206733677412476077 = some 206733677412476077 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 8 2 206733677412476077 206733677412476077 206733677412476077 endpoint_14_74_p8 endpoint_14_74_w8
private theorem endpoint_14_74_w10 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 10 2 206733677412476077 = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_p12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 12 206733677412476077 = some 206733677412476077 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 10 2 206733677412476077 206733677412476077 206733677412476077 endpoint_14_74_p10 endpoint_14_74_w10
private theorem endpoint_14_74_w12 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 12 1 206733677412476077 = some 206733677412476077 := by decide +kernel
private theorem endpoint_14_74_p13 : receiptWindow endpoint_14_74_flag endpoint_14_74_sources 0 13 206733677412476077 = some 206733677412476077 :=
  join_receipt_window endpoint_14_74_flag endpoint_14_74_sources 0 12 1 206733677412476077 206733677412476077 206733677412476077 endpoint_14_74_p12 endpoint_14_74_w12
def endpoint_14_74 : CertifiedEndpoint :=
  ⟨⟨14, 74, 1670⟩, 206733677412476077, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_74_flag endpoint_14_74_sources 13 206733677412476077 206733677412476077 rfl endpoint_14_74_base endpoint_14_74_p13) (by decide)⟩
private def endpoint_14_75_flag : Flag := ⟨14, 75, 1571⟩
private def endpoint_14_75_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_14_75_base : receiptBase endpoint_14_75_flag endpoint_14_75_sources = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_w0 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 2 196917700675942816 = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_w2 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 2 2 196917700675942816 = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_p4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 4 196917700675942816 = some 196917700675942816 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 2 2 196917700675942816 196917700675942816 196917700675942816 endpoint_14_75_w0 endpoint_14_75_w2
private theorem endpoint_14_75_w4 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 4 2 196917700675942816 = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_p6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 6 196917700675942816 = some 196917700675942816 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 4 2 196917700675942816 196917700675942816 196917700675942816 endpoint_14_75_p4 endpoint_14_75_w4
private theorem endpoint_14_75_w6 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 6 2 196917700675942816 = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_p8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 8 196917700675942816 = some 196917700675942816 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 6 2 196917700675942816 196917700675942816 196917700675942816 endpoint_14_75_p6 endpoint_14_75_w6
private theorem endpoint_14_75_w8 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 8 2 196917700675942816 = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_p10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 10 196917700675942816 = some 196917700675942816 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 8 2 196917700675942816 196917700675942816 196917700675942816 endpoint_14_75_p8 endpoint_14_75_w8
private theorem endpoint_14_75_w10 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 10 2 196917700675942816 = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_p12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 12 196917700675942816 = some 196917700675942816 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 10 2 196917700675942816 196917700675942816 196917700675942816 endpoint_14_75_p10 endpoint_14_75_w10
private theorem endpoint_14_75_w12 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 12 1 196917700675942816 = some 196917700675942816 := by decide +kernel
private theorem endpoint_14_75_p13 : receiptWindow endpoint_14_75_flag endpoint_14_75_sources 0 13 196917700675942816 = some 196917700675942816 :=
  join_receipt_window endpoint_14_75_flag endpoint_14_75_sources 0 12 1 196917700675942816 196917700675942816 196917700675942816 endpoint_14_75_p12 endpoint_14_75_w12
def endpoint_14_75 : CertifiedEndpoint :=
  ⟨⟨14, 75, 1571⟩, 196917700675942816, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_14_75_flag endpoint_14_75_sources 13 196917700675942816 196917700675942816 rfl endpoint_14_75_base endpoint_14_75_p13) (by decide)⟩
private def endpoint_14_76_flag : Flag := ⟨14, 76, 1469⟩
private def endpoint_14_76_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_76_base : receiptBase endpoint_14_76_flag endpoint_14_76_sources = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_w0 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 2 187938330376512962 = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_w2 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 2 2 187938330376512962 = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_p4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 4 187938330376512962 = some 187938330376512962 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 2 2 187938330376512962 187938330376512962 187938330376512962 endpoint_14_76_w0 endpoint_14_76_w2
private theorem endpoint_14_76_w4 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 4 2 187938330376512962 = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_p6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 6 187938330376512962 = some 187938330376512962 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 4 2 187938330376512962 187938330376512962 187938330376512962 endpoint_14_76_p4 endpoint_14_76_w4
private theorem endpoint_14_76_w6 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 6 2 187938330376512962 = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_p8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 8 187938330376512962 = some 187938330376512962 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 6 2 187938330376512962 187938330376512962 187938330376512962 endpoint_14_76_p6 endpoint_14_76_w6
private theorem endpoint_14_76_w8 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 8 2 187938330376512962 = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_p10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 10 187938330376512962 = some 187938330376512962 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 8 2 187938330376512962 187938330376512962 187938330376512962 endpoint_14_76_p8 endpoint_14_76_w8
private theorem endpoint_14_76_w10 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 10 2 187938330376512962 = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_p12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 12 187938330376512962 = some 187938330376512962 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 10 2 187938330376512962 187938330376512962 187938330376512962 endpoint_14_76_p10 endpoint_14_76_w10
private theorem endpoint_14_76_w12 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 12 1 187938330376512962 = some 187938330376512962 := by decide +kernel
private theorem endpoint_14_76_p13 : receiptWindow endpoint_14_76_flag endpoint_14_76_sources 0 13 187938330376512962 = some 187938330376512962 :=
  join_receipt_window endpoint_14_76_flag endpoint_14_76_sources 0 12 1 187938330376512962 187938330376512962 187938330376512962 endpoint_14_76_p12 endpoint_14_76_w12
def endpoint_14_76 : CertifiedEndpoint :=
  ⟨⟨14, 76, 1469⟩, 187938330376512962, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_76_flag endpoint_14_76_sources 13 187938330376512962 187938330376512962 rfl endpoint_14_76_base endpoint_14_76_p13) (by decide)⟩
private def endpoint_14_77_flag : Flag := ⟨14, 77, 1363⟩
private def endpoint_14_77_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_14_77_base : receiptBase endpoint_14_77_flag endpoint_14_77_sources = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_w0 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 2 176583584010968664 = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_w2 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 2 2 176583584010968664 = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_p4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 4 176583584010968664 = some 176583584010968664 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 2 2 176583584010968664 176583584010968664 176583584010968664 endpoint_14_77_w0 endpoint_14_77_w2
private theorem endpoint_14_77_w4 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 4 2 176583584010968664 = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_p6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 6 176583584010968664 = some 176583584010968664 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 4 2 176583584010968664 176583584010968664 176583584010968664 endpoint_14_77_p4 endpoint_14_77_w4
private theorem endpoint_14_77_w6 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 6 2 176583584010968664 = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_p8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 8 176583584010968664 = some 176583584010968664 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 6 2 176583584010968664 176583584010968664 176583584010968664 endpoint_14_77_p6 endpoint_14_77_w6
private theorem endpoint_14_77_w8 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 8 2 176583584010968664 = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_p10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 10 176583584010968664 = some 176583584010968664 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 8 2 176583584010968664 176583584010968664 176583584010968664 endpoint_14_77_p8 endpoint_14_77_w8
private theorem endpoint_14_77_w10 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 10 2 176583584010968664 = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_p12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 12 176583584010968664 = some 176583584010968664 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 10 2 176583584010968664 176583584010968664 176583584010968664 endpoint_14_77_p10 endpoint_14_77_w10
private theorem endpoint_14_77_w12 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 12 1 176583584010968664 = some 176583584010968664 := by decide +kernel
private theorem endpoint_14_77_p13 : receiptWindow endpoint_14_77_flag endpoint_14_77_sources 0 13 176583584010968664 = some 176583584010968664 :=
  join_receipt_window endpoint_14_77_flag endpoint_14_77_sources 0 12 1 176583584010968664 176583584010968664 176583584010968664 endpoint_14_77_p12 endpoint_14_77_w12
def endpoint_14_77 : CertifiedEndpoint :=
  ⟨⟨14, 77, 1363⟩, 176583584010968664, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_14_77_flag endpoint_14_77_sources 13 176583584010968664 176583584010968664 rfl endpoint_14_77_base endpoint_14_77_p13) (by decide)⟩
private def endpoint_14_78_flag : Flag := ⟨14, 78, 1255⟩
private def endpoint_14_78_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_78_base : receiptBase endpoint_14_78_flag endpoint_14_78_sources = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_w0 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 2 165947940840867963 = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_w2 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 2 2 165947940840867963 = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_p4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 4 165947940840867963 = some 165947940840867963 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 2 2 165947940840867963 165947940840867963 165947940840867963 endpoint_14_78_w0 endpoint_14_78_w2
private theorem endpoint_14_78_w4 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 4 2 165947940840867963 = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_p6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 6 165947940840867963 = some 165947940840867963 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 4 2 165947940840867963 165947940840867963 165947940840867963 endpoint_14_78_p4 endpoint_14_78_w4
private theorem endpoint_14_78_w6 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 6 2 165947940840867963 = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_p8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 8 165947940840867963 = some 165947940840867963 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 6 2 165947940840867963 165947940840867963 165947940840867963 endpoint_14_78_p6 endpoint_14_78_w6
private theorem endpoint_14_78_w8 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 8 2 165947940840867963 = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_p10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 10 165947940840867963 = some 165947940840867963 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 8 2 165947940840867963 165947940840867963 165947940840867963 endpoint_14_78_p8 endpoint_14_78_w8
private theorem endpoint_14_78_w10 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 10 2 165947940840867963 = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_p12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 12 165947940840867963 = some 165947940840867963 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 10 2 165947940840867963 165947940840867963 165947940840867963 endpoint_14_78_p10 endpoint_14_78_w10
private theorem endpoint_14_78_w12 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 12 1 165947940840867963 = some 165947940840867963 := by decide +kernel
private theorem endpoint_14_78_p13 : receiptWindow endpoint_14_78_flag endpoint_14_78_sources 0 13 165947940840867963 = some 165947940840867963 :=
  join_receipt_window endpoint_14_78_flag endpoint_14_78_sources 0 12 1 165947940840867963 165947940840867963 165947940840867963 endpoint_14_78_p12 endpoint_14_78_w12
def endpoint_14_78 : CertifiedEndpoint :=
  ⟨⟨14, 78, 1255⟩, 165947940840867963, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_78_flag endpoint_14_78_sources 13 165947940840867963 165947940840867963 rfl endpoint_14_78_base endpoint_14_78_p13) (by decide)⟩
private def endpoint_14_79_flag : Flag := ⟨14, 79, 1144⟩
private def endpoint_14_79_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_14_79_base : receiptBase endpoint_14_79_flag endpoint_14_79_sources = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_w0 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 2 153140764226808798 = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_w2 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 2 2 153140764226808798 = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_p4 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 4 153140764226808798 = some 153140764226808798 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 2 2 153140764226808798 153140764226808798 153140764226808798 endpoint_14_79_w0 endpoint_14_79_w2
private theorem endpoint_14_79_w4 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 4 2 153140764226808798 = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_p6 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 6 153140764226808798 = some 153140764226808798 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 4 2 153140764226808798 153140764226808798 153140764226808798 endpoint_14_79_p4 endpoint_14_79_w4
private theorem endpoint_14_79_w6 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 6 2 153140764226808798 = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_p8 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 8 153140764226808798 = some 153140764226808798 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 6 2 153140764226808798 153140764226808798 153140764226808798 endpoint_14_79_p6 endpoint_14_79_w6
private theorem endpoint_14_79_w8 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 8 2 153140764226808798 = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_p10 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 10 153140764226808798 = some 153140764226808798 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 8 2 153140764226808798 153140764226808798 153140764226808798 endpoint_14_79_p8 endpoint_14_79_w8
private theorem endpoint_14_79_w10 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 10 2 153140764226808798 = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_p12 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 12 153140764226808798 = some 153140764226808798 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 10 2 153140764226808798 153140764226808798 153140764226808798 endpoint_14_79_p10 endpoint_14_79_w10
private theorem endpoint_14_79_w12 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 12 1 153140764226808798 = some 153140764226808798 := by decide +kernel
private theorem endpoint_14_79_p13 : receiptWindow endpoint_14_79_flag endpoint_14_79_sources 0 13 153140764226808798 = some 153140764226808798 :=
  join_receipt_window endpoint_14_79_flag endpoint_14_79_sources 0 12 1 153140764226808798 153140764226808798 153140764226808798 endpoint_14_79_p12 endpoint_14_79_w12
def endpoint_14_79 : CertifiedEndpoint :=
  ⟨⟨14, 79, 1144⟩, 153140764226808798, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_14_79_flag endpoint_14_79_sources 13 153140764226808798 153140764226808798 rfl endpoint_14_79_base endpoint_14_79_p13) (by decide)⟩
def endpoint_14_80 : CertifiedEndpoint :=
  ⟨⟨14, 80, 1029⟩, 249156854307773631, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_81 : CertifiedEndpoint :=
  ⟨⟨14, 81, 912⟩, 222472214455923577, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_82 : CertifiedEndpoint :=
  ⟨⟨14, 82, 792⟩, 194188483958240436, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_83 : CertifiedEndpoint :=
  ⟨⟨14, 83, 668⟩, 164010951956395709, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_84 : CertifiedEndpoint :=
  ⟨⟨14, 84, 542⟩, 132431387357369650, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_85 : CertifiedEndpoint :=
  ⟨⟨14, 85, 412⟩, 98888269247270045, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_86 : CertifiedEndpoint :=
  ⟨⟨14, 86, 279⟩, 63613531678204629, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_87 : CertifiedEndpoint :=
  ⟨⟨14, 87, 144⟩, 26853059103663529, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_15 : CertifiedEndpoint :=
  ⟨⟨15, 15, 4251⟩, 132537779673392376, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_16 : CertifiedEndpoint :=
  ⟨⟨15, 16, 4226⟩, 136926589782345006, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_17 : CertifiedEndpoint :=
  ⟨⟨15, 17, 4200⟩, 141220263941565695, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_18 : CertifiedEndpoint :=
  ⟨⟨15, 18, 4175⟩, 155948458776824795, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_19 : CertifiedEndpoint :=
  ⟨⟨15, 19, 4148⟩, 170403229106932763, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_20 : CertifiedEndpoint :=
  ⟨⟨15, 20, 4122⟩, 184696959967965722, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_21 : CertifiedEndpoint :=
  ⟨⟨15, 21, 4095⟩, 198743492088515040, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_22 : CertifiedEndpoint :=
  ⟨⟨15, 22, 4068⟩, 212584032451947608, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_23 : CertifiedEndpoint :=
  ⟨⟨15, 23, 4040⟩, 226162392856197135, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_24 : CertifiedEndpoint :=
  ⟨⟨15, 24, 4012⟩, 239527270893980212, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_25 : CertifiedEndpoint :=
  ⟨⟨15, 25, 3984⟩, 252678666565296839, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_15_26_flag : Flag := ⟨15, 26, 3955⟩
private def endpoint_15_26_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_26_base : receiptBase endpoint_15_26_flag endpoint_15_26_sources = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_w0 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 0 2 190167246379992402 = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_w2 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 2 2 190167246379992402 = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_p4 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 0 4 190167246379992402 = some 190167246379992402 :=
  join_receipt_window endpoint_15_26_flag endpoint_15_26_sources 0 2 2 190167246379992402 190167246379992402 190167246379992402 endpoint_15_26_w0 endpoint_15_26_w2
private theorem endpoint_15_26_w4 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 4 2 190167246379992402 = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_p6 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 0 6 190167246379992402 = some 190167246379992402 :=
  join_receipt_window endpoint_15_26_flag endpoint_15_26_sources 0 4 2 190167246379992402 190167246379992402 190167246379992402 endpoint_15_26_p4 endpoint_15_26_w4
private theorem endpoint_15_26_w6 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 6 2 190167246379992402 = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_p8 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 0 8 190167246379992402 = some 190167246379992402 :=
  join_receipt_window endpoint_15_26_flag endpoint_15_26_sources 0 6 2 190167246379992402 190167246379992402 190167246379992402 endpoint_15_26_p6 endpoint_15_26_w6
private theorem endpoint_15_26_w8 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 8 2 190167246379992402 = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_p10 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 0 10 190167246379992402 = some 190167246379992402 :=
  join_receipt_window endpoint_15_26_flag endpoint_15_26_sources 0 8 2 190167246379992402 190167246379992402 190167246379992402 endpoint_15_26_p8 endpoint_15_26_w8
private theorem endpoint_15_26_w10 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 10 2 190167246379992402 = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_p12 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 0 12 190167246379992402 = some 190167246379992402 :=
  join_receipt_window endpoint_15_26_flag endpoint_15_26_sources 0 10 2 190167246379992402 190167246379992402 190167246379992402 endpoint_15_26_p10 endpoint_15_26_w10
private theorem endpoint_15_26_w12 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 12 2 190167246379992402 = some 190167246379992402 := by decide +kernel
private theorem endpoint_15_26_p14 : receiptWindow endpoint_15_26_flag endpoint_15_26_sources 0 14 190167246379992402 = some 190167246379992402 :=
  join_receipt_window endpoint_15_26_flag endpoint_15_26_sources 0 12 2 190167246379992402 190167246379992402 190167246379992402 endpoint_15_26_p12 endpoint_15_26_w12
def endpoint_15_26 : CertifiedEndpoint :=
  ⟨⟨15, 26, 3955⟩, 190167246379992402, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_26_flag endpoint_15_26_sources 14 190167246379992402 190167246379992402 rfl endpoint_15_26_base endpoint_15_26_p14) (by decide)⟩
private def endpoint_15_27_flag : Flag := ⟨15, 27, 3926⟩
private def endpoint_15_27_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_27_base : receiptBase endpoint_15_27_flag endpoint_15_27_sources = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_w0 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 2 194618716537229469 = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_w2 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 2 2 194618716537229469 = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_p4 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 4 194618716537229469 = some 194618716537229469 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 2 2 194618716537229469 194618716537229469 194618716537229469 endpoint_15_27_w0 endpoint_15_27_w2
private theorem endpoint_15_27_w4 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 4 2 194618716537229469 = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_p6 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 6 194618716537229469 = some 194618716537229469 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 4 2 194618716537229469 194618716537229469 194618716537229469 endpoint_15_27_p4 endpoint_15_27_w4
private theorem endpoint_15_27_w6 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 6 2 194618716537229469 = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_p8 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 8 194618716537229469 = some 194618716537229469 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 6 2 194618716537229469 194618716537229469 194618716537229469 endpoint_15_27_p6 endpoint_15_27_w6
private theorem endpoint_15_27_w8 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 8 2 194618716537229469 = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_p10 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 10 194618716537229469 = some 194618716537229469 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 8 2 194618716537229469 194618716537229469 194618716537229469 endpoint_15_27_p8 endpoint_15_27_w8
private theorem endpoint_15_27_w10 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 10 2 194618716537229469 = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_p12 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 12 194618716537229469 = some 194618716537229469 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 10 2 194618716537229469 194618716537229469 194618716537229469 endpoint_15_27_p10 endpoint_15_27_w10
private theorem endpoint_15_27_w12 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 12 2 194618716537229469 = some 194618716537229469 := by decide +kernel
private theorem endpoint_15_27_p14 : receiptWindow endpoint_15_27_flag endpoint_15_27_sources 0 14 194618716537229469 = some 194618716537229469 :=
  join_receipt_window endpoint_15_27_flag endpoint_15_27_sources 0 12 2 194618716537229469 194618716537229469 194618716537229469 endpoint_15_27_p12 endpoint_15_27_w12
def endpoint_15_27 : CertifiedEndpoint :=
  ⟨⟨15, 27, 3926⟩, 194618716537229469, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_27_flag endpoint_15_27_sources 14 194618716537229469 194618716537229469 rfl endpoint_15_27_base endpoint_15_27_p14) (by decide)⟩
private def endpoint_15_28_flag : Flag := ⟨15, 28, 3896⟩
private def endpoint_15_28_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_28_base : receiptBase endpoint_15_28_flag endpoint_15_28_sources = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_w0 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 2 198933835791788847 = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_w2 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 2 2 198933835791788847 = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_p4 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 4 198933835791788847 = some 198933835791788847 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 2 2 198933835791788847 198933835791788847 198933835791788847 endpoint_15_28_w0 endpoint_15_28_w2
private theorem endpoint_15_28_w4 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 4 2 198933835791788847 = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_p6 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 6 198933835791788847 = some 198933835791788847 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 4 2 198933835791788847 198933835791788847 198933835791788847 endpoint_15_28_p4 endpoint_15_28_w4
private theorem endpoint_15_28_w6 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 6 2 198933835791788847 = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_p8 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 8 198933835791788847 = some 198933835791788847 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 6 2 198933835791788847 198933835791788847 198933835791788847 endpoint_15_28_p6 endpoint_15_28_w6
private theorem endpoint_15_28_w8 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 8 2 198933835791788847 = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_p10 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 10 198933835791788847 = some 198933835791788847 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 8 2 198933835791788847 198933835791788847 198933835791788847 endpoint_15_28_p8 endpoint_15_28_w8
private theorem endpoint_15_28_w10 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 10 2 198933835791788847 = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_p12 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 12 198933835791788847 = some 198933835791788847 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 10 2 198933835791788847 198933835791788847 198933835791788847 endpoint_15_28_p10 endpoint_15_28_w10
private theorem endpoint_15_28_w12 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 12 2 198933835791788847 = some 198933835791788847 := by decide +kernel
private theorem endpoint_15_28_p14 : receiptWindow endpoint_15_28_flag endpoint_15_28_sources 0 14 198933835791788847 = some 198933835791788847 :=
  join_receipt_window endpoint_15_28_flag endpoint_15_28_sources 0 12 2 198933835791788847 198933835791788847 198933835791788847 endpoint_15_28_p12 endpoint_15_28_w12
def endpoint_15_28 : CertifiedEndpoint :=
  ⟨⟨15, 28, 3896⟩, 198933835791788847, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_28_flag endpoint_15_28_sources 14 198933835791788847 198933835791788847 rfl endpoint_15_28_base endpoint_15_28_p14) (by decide)⟩
private def endpoint_15_29_flag : Flag := ⟨15, 29, 3866⟩
private def endpoint_15_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_29_base : receiptBase endpoint_15_29_flag endpoint_15_29_sources = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_w0 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 2 203160148488883256 = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_w2 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 2 2 203160148488883256 = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_p4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 4 203160148488883256 = some 203160148488883256 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 2 2 203160148488883256 203160148488883256 203160148488883256 endpoint_15_29_w0 endpoint_15_29_w2
private theorem endpoint_15_29_w4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 4 2 203160148488883256 = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_p6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 6 203160148488883256 = some 203160148488883256 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 4 2 203160148488883256 203160148488883256 203160148488883256 endpoint_15_29_p4 endpoint_15_29_w4
private theorem endpoint_15_29_w6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 6 2 203160148488883256 = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_p8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 8 203160148488883256 = some 203160148488883256 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 6 2 203160148488883256 203160148488883256 203160148488883256 endpoint_15_29_p6 endpoint_15_29_w6
private theorem endpoint_15_29_w8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 8 2 203160148488883256 = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_p10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 10 203160148488883256 = some 203160148488883256 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 8 2 203160148488883256 203160148488883256 203160148488883256 endpoint_15_29_p8 endpoint_15_29_w8
private theorem endpoint_15_29_w10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 10 2 203160148488883256 = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_p12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 12 203160148488883256 = some 203160148488883256 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 10 2 203160148488883256 203160148488883256 203160148488883256 endpoint_15_29_p10 endpoint_15_29_w10
private theorem endpoint_15_29_w12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 12 2 203160148488883256 = some 203160148488883256 := by decide +kernel
private theorem endpoint_15_29_p14 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 14 203160148488883256 = some 203160148488883256 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 12 2 203160148488883256 203160148488883256 203160148488883256 endpoint_15_29_p12 endpoint_15_29_w12
def endpoint_15_29 : CertifiedEndpoint :=
  ⟨⟨15, 29, 3866⟩, 203160148488883256, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_29_flag endpoint_15_29_sources 14 203160148488883256 203160148488883256 rfl endpoint_15_29_base endpoint_15_29_p14) (by decide)⟩
private def endpoint_15_30_flag : Flag := ⟨15, 30, 3835⟩
private def endpoint_15_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_30_base : receiptBase endpoint_15_30_flag endpoint_15_30_sources = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_w0 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 2 207244288451526952 = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_w2 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 2 2 207244288451526952 = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_p4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 4 207244288451526952 = some 207244288451526952 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 2 2 207244288451526952 207244288451526952 207244288451526952 endpoint_15_30_w0 endpoint_15_30_w2
private theorem endpoint_15_30_w4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 4 2 207244288451526952 = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_p6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 6 207244288451526952 = some 207244288451526952 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 4 2 207244288451526952 207244288451526952 207244288451526952 endpoint_15_30_p4 endpoint_15_30_w4
private theorem endpoint_15_30_w6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 6 2 207244288451526952 = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_p8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 8 207244288451526952 = some 207244288451526952 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 6 2 207244288451526952 207244288451526952 207244288451526952 endpoint_15_30_p6 endpoint_15_30_w6
private theorem endpoint_15_30_w8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 8 2 207244288451526952 = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_p10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 10 207244288451526952 = some 207244288451526952 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 8 2 207244288451526952 207244288451526952 207244288451526952 endpoint_15_30_p8 endpoint_15_30_w8
private theorem endpoint_15_30_w10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 10 2 207244288451526952 = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_p12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 12 207244288451526952 = some 207244288451526952 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 10 2 207244288451526952 207244288451526952 207244288451526952 endpoint_15_30_p10 endpoint_15_30_w10
private theorem endpoint_15_30_w12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 12 2 207244288451526952 = some 207244288451526952 := by decide +kernel
private theorem endpoint_15_30_p14 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 14 207244288451526952 = some 207244288451526952 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 12 2 207244288451526952 207244288451526952 207244288451526952 endpoint_15_30_p12 endpoint_15_30_w12
def endpoint_15_30 : CertifiedEndpoint :=
  ⟨⟨15, 30, 3835⟩, 207244288451526952, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_30_flag endpoint_15_30_sources 14 207244288451526952 207244288451526952 rfl endpoint_15_30_base endpoint_15_30_p14) (by decide)⟩
private def endpoint_15_31_flag : Flag := ⟨15, 31, 3804⟩
private def endpoint_15_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_31_base : receiptBase endpoint_15_31_flag endpoint_15_31_sources = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_w0 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 2 211236710940819168 = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_w2 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 2 2 211236710940819168 = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_p4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 4 211236710940819168 = some 211236710940819168 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 2 2 211236710940819168 211236710940819168 211236710940819168 endpoint_15_31_w0 endpoint_15_31_w2
private theorem endpoint_15_31_w4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 4 2 211236710940819168 = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_p6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 6 211236710940819168 = some 211236710940819168 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 4 2 211236710940819168 211236710940819168 211236710940819168 endpoint_15_31_p4 endpoint_15_31_w4
private theorem endpoint_15_31_w6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 6 2 211236710940819168 = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_p8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 8 211236710940819168 = some 211236710940819168 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 6 2 211236710940819168 211236710940819168 211236710940819168 endpoint_15_31_p6 endpoint_15_31_w6
private theorem endpoint_15_31_w8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 8 2 211236710940819168 = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_p10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 10 211236710940819168 = some 211236710940819168 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 8 2 211236710940819168 211236710940819168 211236710940819168 endpoint_15_31_p8 endpoint_15_31_w8
private theorem endpoint_15_31_w10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 10 2 211236710940819168 = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_p12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 12 211236710940819168 = some 211236710940819168 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 10 2 211236710940819168 211236710940819168 211236710940819168 endpoint_15_31_p10 endpoint_15_31_w10
private theorem endpoint_15_31_w12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 12 2 211236710940819168 = some 211236710940819168 := by decide +kernel
private theorem endpoint_15_31_p14 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 14 211236710940819168 = some 211236710940819168 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 12 2 211236710940819168 211236710940819168 211236710940819168 endpoint_15_31_p12 endpoint_15_31_w12
def endpoint_15_31 : CertifiedEndpoint :=
  ⟨⟨15, 31, 3804⟩, 211236710940819168, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_31_flag endpoint_15_31_sources 14 211236710940819168 211236710940819168 rfl endpoint_15_31_base endpoint_15_31_p14) (by decide)⟩
private def endpoint_15_32_flag : Flag := ⟨15, 32, 3773⟩
private def endpoint_15_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_32_base : receiptBase endpoint_15_32_flag endpoint_15_32_sources = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_w0 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 2 215137415956759903 = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_w2 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 2 2 215137415956759903 = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_p4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 4 215137415956759903 = some 215137415956759903 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 2 2 215137415956759903 215137415956759903 215137415956759903 endpoint_15_32_w0 endpoint_15_32_w2
private theorem endpoint_15_32_w4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 4 2 215137415956759903 = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_p6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 6 215137415956759903 = some 215137415956759903 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 4 2 215137415956759903 215137415956759903 215137415956759903 endpoint_15_32_p4 endpoint_15_32_w4
private theorem endpoint_15_32_w6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 6 2 215137415956759903 = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_p8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 8 215137415956759903 = some 215137415956759903 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 6 2 215137415956759903 215137415956759903 215137415956759903 endpoint_15_32_p6 endpoint_15_32_w6
private theorem endpoint_15_32_w8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 8 2 215137415956759903 = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_p10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 10 215137415956759903 = some 215137415956759903 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 8 2 215137415956759903 215137415956759903 215137415956759903 endpoint_15_32_p8 endpoint_15_32_w8
private theorem endpoint_15_32_w10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 10 2 215137415956759903 = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_p12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 12 215137415956759903 = some 215137415956759903 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 10 2 215137415956759903 215137415956759903 215137415956759903 endpoint_15_32_p10 endpoint_15_32_w10
private theorem endpoint_15_32_w12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 12 2 215137415956759903 = some 215137415956759903 := by decide +kernel
private theorem endpoint_15_32_p14 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 14 215137415956759903 = some 215137415956759903 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 12 2 215137415956759903 215137415956759903 215137415956759903 endpoint_15_32_p12 endpoint_15_32_w12
def endpoint_15_32 : CertifiedEndpoint :=
  ⟨⟨15, 32, 3773⟩, 215137415956759903, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_32_flag endpoint_15_32_sources 14 215137415956759903 215137415956759903 rfl endpoint_15_32_base endpoint_15_32_p14) (by decide)⟩
private def endpoint_15_33_flag : Flag := ⟨15, 33, 3740⟩
private def endpoint_15_33_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_33_base : receiptBase endpoint_15_33_flag endpoint_15_33_sources = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_w0 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 2 218830938397718128 = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_w2 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 2 2 218830938397718128 = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_p4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 4 218830938397718128 = some 218830938397718128 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 2 2 218830938397718128 218830938397718128 218830938397718128 endpoint_15_33_w0 endpoint_15_33_w2
private theorem endpoint_15_33_w4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 4 2 218830938397718128 = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_p6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 6 218830938397718128 = some 218830938397718128 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 4 2 218830938397718128 218830938397718128 218830938397718128 endpoint_15_33_p4 endpoint_15_33_w4
private theorem endpoint_15_33_w6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 6 2 218830938397718128 = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_p8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 8 218830938397718128 = some 218830938397718128 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 6 2 218830938397718128 218830938397718128 218830938397718128 endpoint_15_33_p6 endpoint_15_33_w6
private theorem endpoint_15_33_w8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 8 2 218830938397718128 = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_p10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 10 218830938397718128 = some 218830938397718128 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 8 2 218830938397718128 218830938397718128 218830938397718128 endpoint_15_33_p8 endpoint_15_33_w8
private theorem endpoint_15_33_w10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 10 2 218830938397718128 = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_p12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 12 218830938397718128 = some 218830938397718128 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 10 2 218830938397718128 218830938397718128 218830938397718128 endpoint_15_33_p10 endpoint_15_33_w10
private theorem endpoint_15_33_w12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 12 2 218830938397718128 = some 218830938397718128 := by decide +kernel
private theorem endpoint_15_33_p14 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 14 218830938397718128 = some 218830938397718128 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 12 2 218830938397718128 218830938397718128 218830938397718128 endpoint_15_33_p12 endpoint_15_33_w12
def endpoint_15_33 : CertifiedEndpoint :=
  ⟨⟨15, 33, 3740⟩, 218830938397718128, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_33_flag endpoint_15_33_sources 14 218830938397718128 218830938397718128 rfl endpoint_15_33_base endpoint_15_33_p14) (by decide)⟩
private def endpoint_15_34_flag : Flag := ⟨15, 34, 3708⟩
private def endpoint_15_34_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_34_base : receiptBase endpoint_15_34_flag endpoint_15_34_sources = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_w0 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 2 222451753295918317 = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_w2 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 2 2 222451753295918317 = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_p4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 4 222451753295918317 = some 222451753295918317 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 2 2 222451753295918317 222451753295918317 222451753295918317 endpoint_15_34_w0 endpoint_15_34_w2
private theorem endpoint_15_34_w4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 4 2 222451753295918317 = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_p6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 6 222451753295918317 = some 222451753295918317 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 4 2 222451753295918317 222451753295918317 222451753295918317 endpoint_15_34_p4 endpoint_15_34_w4
private theorem endpoint_15_34_w6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 6 2 222451753295918317 = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_p8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 8 222451753295918317 = some 222451753295918317 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 6 2 222451753295918317 222451753295918317 222451753295918317 endpoint_15_34_p6 endpoint_15_34_w6
private theorem endpoint_15_34_w8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 8 2 222451753295918317 = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_p10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 10 222451753295918317 = some 222451753295918317 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 8 2 222451753295918317 222451753295918317 222451753295918317 endpoint_15_34_p8 endpoint_15_34_w8
private theorem endpoint_15_34_w10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 10 2 222451753295918317 = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_p12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 12 222451753295918317 = some 222451753295918317 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 10 2 222451753295918317 222451753295918317 222451753295918317 endpoint_15_34_p10 endpoint_15_34_w10
private theorem endpoint_15_34_w12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 12 2 222451753295918317 = some 222451753295918317 := by decide +kernel
private theorem endpoint_15_34_p14 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 14 222451753295918317 = some 222451753295918317 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 12 2 222451753295918317 222451753295918317 222451753295918317 endpoint_15_34_p12 endpoint_15_34_w12
def endpoint_15_34 : CertifiedEndpoint :=
  ⟨⟨15, 34, 3708⟩, 222451753295918317, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_34_flag endpoint_15_34_sources 14 222451753295918317 222451753295918317 rfl endpoint_15_34_base endpoint_15_34_p14) (by decide)⟩
private def endpoint_15_35_flag : Flag := ⟨15, 35, 3674⟩
private def endpoint_15_35_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_35_base : receiptBase endpoint_15_35_flag endpoint_15_35_sources = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_w0 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 2 225821721360714533 = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_w2 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 2 2 225821721360714533 = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_p4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 4 225821721360714533 = some 225821721360714533 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 2 2 225821721360714533 225821721360714533 225821721360714533 endpoint_15_35_w0 endpoint_15_35_w2
private theorem endpoint_15_35_w4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 4 2 225821721360714533 = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_p6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 6 225821721360714533 = some 225821721360714533 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 4 2 225821721360714533 225821721360714533 225821721360714533 endpoint_15_35_p4 endpoint_15_35_w4
private theorem endpoint_15_35_w6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 6 2 225821721360714533 = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_p8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 8 225821721360714533 = some 225821721360714533 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 6 2 225821721360714533 225821721360714533 225821721360714533 endpoint_15_35_p6 endpoint_15_35_w6
private theorem endpoint_15_35_w8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 8 2 225821721360714533 = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_p10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 10 225821721360714533 = some 225821721360714533 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 8 2 225821721360714533 225821721360714533 225821721360714533 endpoint_15_35_p8 endpoint_15_35_w8
private theorem endpoint_15_35_w10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 10 2 225821721360714533 = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_p12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 12 225821721360714533 = some 225821721360714533 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 10 2 225821721360714533 225821721360714533 225821721360714533 endpoint_15_35_p10 endpoint_15_35_w10
private theorem endpoint_15_35_w12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 12 2 225821721360714533 = some 225821721360714533 := by decide +kernel
private theorem endpoint_15_35_p14 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 14 225821721360714533 = some 225821721360714533 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 12 2 225821721360714533 225821721360714533 225821721360714533 endpoint_15_35_p12 endpoint_15_35_w12
def endpoint_15_35 : CertifiedEndpoint :=
  ⟨⟨15, 35, 3674⟩, 225821721360714533, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_35_flag endpoint_15_35_sources 14 225821721360714533 225821721360714533 rfl endpoint_15_35_base endpoint_15_35_p14) (by decide)⟩
private def endpoint_15_36_flag : Flag := ⟨15, 36, 3640⟩
private def endpoint_15_36_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_36_base : receiptBase endpoint_15_36_flag endpoint_15_36_sources = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_w0 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 2 230545783346535941 = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_w2 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 2 2 230545783346535941 = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_p4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 4 230545783346535941 = some 230545783346535941 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 2 2 230545783346535941 230545783346535941 230545783346535941 endpoint_15_36_w0 endpoint_15_36_w2
private theorem endpoint_15_36_w4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 4 2 230545783346535941 = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_p6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 6 230545783346535941 = some 230545783346535941 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 4 2 230545783346535941 230545783346535941 230545783346535941 endpoint_15_36_p4 endpoint_15_36_w4
private theorem endpoint_15_36_w6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 6 2 230545783346535941 = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_p8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 8 230545783346535941 = some 230545783346535941 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 6 2 230545783346535941 230545783346535941 230545783346535941 endpoint_15_36_p6 endpoint_15_36_w6
private theorem endpoint_15_36_w8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 8 2 230545783346535941 = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_p10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 10 230545783346535941 = some 230545783346535941 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 8 2 230545783346535941 230545783346535941 230545783346535941 endpoint_15_36_p8 endpoint_15_36_w8
private theorem endpoint_15_36_w10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 10 2 230545783346535941 = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_p12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 12 230545783346535941 = some 230545783346535941 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 10 2 230545783346535941 230545783346535941 230545783346535941 endpoint_15_36_p10 endpoint_15_36_w10
private theorem endpoint_15_36_w12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 12 2 230545783346535941 = some 230545783346535941 := by decide +kernel
private theorem endpoint_15_36_p14 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 14 230545783346535941 = some 230545783346535941 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 12 2 230545783346535941 230545783346535941 230545783346535941 endpoint_15_36_p12 endpoint_15_36_w12
def endpoint_15_36 : CertifiedEndpoint :=
  ⟨⟨15, 36, 3640⟩, 230545783346535941, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_36_flag endpoint_15_36_sources 14 230545783346535941 230545783346535941 rfl endpoint_15_36_base endpoint_15_36_p14) (by decide)⟩
private def endpoint_15_37_flag : Flag := ⟨15, 37, 3606⟩
private def endpoint_15_37_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_37_base : receiptBase endpoint_15_37_flag endpoint_15_37_sources = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_w0 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 2 233712367013373923 = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_w2 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 2 2 233712367013373923 = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_p4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 4 233712367013373923 = some 233712367013373923 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 2 2 233712367013373923 233712367013373923 233712367013373923 endpoint_15_37_w0 endpoint_15_37_w2
private theorem endpoint_15_37_w4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 4 2 233712367013373923 = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_p6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 6 233712367013373923 = some 233712367013373923 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 4 2 233712367013373923 233712367013373923 233712367013373923 endpoint_15_37_p4 endpoint_15_37_w4
private theorem endpoint_15_37_w6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 6 2 233712367013373923 = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_p8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 8 233712367013373923 = some 233712367013373923 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 6 2 233712367013373923 233712367013373923 233712367013373923 endpoint_15_37_p6 endpoint_15_37_w6
private theorem endpoint_15_37_w8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 8 2 233712367013373923 = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_p10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 10 233712367013373923 = some 233712367013373923 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 8 2 233712367013373923 233712367013373923 233712367013373923 endpoint_15_37_p8 endpoint_15_37_w8
private theorem endpoint_15_37_w10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 10 2 233712367013373923 = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_p12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 12 233712367013373923 = some 233712367013373923 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 10 2 233712367013373923 233712367013373923 233712367013373923 endpoint_15_37_p10 endpoint_15_37_w10
private theorem endpoint_15_37_w12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 12 2 233712367013373923 = some 233712367013373923 := by decide +kernel
private theorem endpoint_15_37_p14 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 14 233712367013373923 = some 233712367013373923 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 12 2 233712367013373923 233712367013373923 233712367013373923 endpoint_15_37_p12 endpoint_15_37_w12
def endpoint_15_37 : CertifiedEndpoint :=
  ⟨⟨15, 37, 3606⟩, 233712367013373923, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_37_flag endpoint_15_37_sources 14 233712367013373923 233712367013373923 rfl endpoint_15_37_base endpoint_15_37_p14) (by decide)⟩
private def endpoint_15_38_flag : Flag := ⟨15, 38, 3570⟩
private def endpoint_15_38_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_38_base : receiptBase endpoint_15_38_flag endpoint_15_38_sources = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_w0 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 2 238389600157808245 = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_w2 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 2 2 238389600157808245 = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_p4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 4 238389600157808245 = some 238389600157808245 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 2 2 238389600157808245 238389600157808245 238389600157808245 endpoint_15_38_w0 endpoint_15_38_w2
private theorem endpoint_15_38_w4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 4 2 238389600157808245 = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_p6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 6 238389600157808245 = some 238389600157808245 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 4 2 238389600157808245 238389600157808245 238389600157808245 endpoint_15_38_p4 endpoint_15_38_w4
private theorem endpoint_15_38_w6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 6 2 238389600157808245 = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_p8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 8 238389600157808245 = some 238389600157808245 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 6 2 238389600157808245 238389600157808245 238389600157808245 endpoint_15_38_p6 endpoint_15_38_w6
private theorem endpoint_15_38_w8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 8 2 238389600157808245 = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_p10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 10 238389600157808245 = some 238389600157808245 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 8 2 238389600157808245 238389600157808245 238389600157808245 endpoint_15_38_p8 endpoint_15_38_w8
private theorem endpoint_15_38_w10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 10 2 238389600157808245 = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_p12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 12 238389600157808245 = some 238389600157808245 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 10 2 238389600157808245 238389600157808245 238389600157808245 endpoint_15_38_p10 endpoint_15_38_w10
private theorem endpoint_15_38_w12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 12 2 238389600157808245 = some 238389600157808245 := by decide +kernel
private theorem endpoint_15_38_p14 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 14 238389600157808245 = some 238389600157808245 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 12 2 238389600157808245 238389600157808245 238389600157808245 endpoint_15_38_p12 endpoint_15_38_w12
def endpoint_15_38 : CertifiedEndpoint :=
  ⟨⟨15, 38, 3570⟩, 238389600157808245, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_38_flag endpoint_15_38_sources 14 238389600157808245 238389600157808245 rfl endpoint_15_38_base endpoint_15_38_p14) (by decide)⟩
private def endpoint_15_39_flag : Flag := ⟨15, 39, 3534⟩
private def endpoint_15_39_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_39_base : receiptBase endpoint_15_39_flag endpoint_15_39_sources = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_w0 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 2 241162500997200682 = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_w2 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 2 2 241162500997200682 = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_p4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 4 241162500997200682 = some 241162500997200682 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 2 2 241162500997200682 241162500997200682 241162500997200682 endpoint_15_39_w0 endpoint_15_39_w2
private theorem endpoint_15_39_w4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 4 2 241162500997200682 = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_p6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 6 241162500997200682 = some 241162500997200682 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 4 2 241162500997200682 241162500997200682 241162500997200682 endpoint_15_39_p4 endpoint_15_39_w4
private theorem endpoint_15_39_w6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 6 2 241162500997200682 = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_p8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 8 241162500997200682 = some 241162500997200682 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 6 2 241162500997200682 241162500997200682 241162500997200682 endpoint_15_39_p6 endpoint_15_39_w6
private theorem endpoint_15_39_w8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 8 2 241162500997200682 = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_p10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 10 241162500997200682 = some 241162500997200682 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 8 2 241162500997200682 241162500997200682 241162500997200682 endpoint_15_39_p8 endpoint_15_39_w8
private theorem endpoint_15_39_w10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 10 2 241162500997200682 = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_p12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 12 241162500997200682 = some 241162500997200682 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 10 2 241162500997200682 241162500997200682 241162500997200682 endpoint_15_39_p10 endpoint_15_39_w10
private theorem endpoint_15_39_w12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 12 2 241162500997200682 = some 241162500997200682 := by decide +kernel
private theorem endpoint_15_39_p14 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 14 241162500997200682 = some 241162500997200682 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 12 2 241162500997200682 241162500997200682 241162500997200682 endpoint_15_39_p12 endpoint_15_39_w12
def endpoint_15_39 : CertifiedEndpoint :=
  ⟨⟨15, 39, 3534⟩, 241162500997200682, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_39_flag endpoint_15_39_sources 14 241162500997200682 241162500997200682 rfl endpoint_15_39_base endpoint_15_39_p14) (by decide)⟩
private def endpoint_15_40_flag : Flag := ⟨15, 40, 3497⟩
private def endpoint_15_40_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_40_base : receiptBase endpoint_15_40_flag endpoint_15_40_sources = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_w0 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 2 243762067479786599 = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_w2 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 2 2 243762067479786599 = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_p4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 4 243762067479786599 = some 243762067479786599 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 2 2 243762067479786599 243762067479786599 243762067479786599 endpoint_15_40_w0 endpoint_15_40_w2
private theorem endpoint_15_40_w4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 4 2 243762067479786599 = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_p6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 6 243762067479786599 = some 243762067479786599 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 4 2 243762067479786599 243762067479786599 243762067479786599 endpoint_15_40_p4 endpoint_15_40_w4
private theorem endpoint_15_40_w6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 6 2 243762067479786599 = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_p8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 8 243762067479786599 = some 243762067479786599 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 6 2 243762067479786599 243762067479786599 243762067479786599 endpoint_15_40_p6 endpoint_15_40_w6
private theorem endpoint_15_40_w8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 8 2 243762067479786599 = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_p10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 10 243762067479786599 = some 243762067479786599 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 8 2 243762067479786599 243762067479786599 243762067479786599 endpoint_15_40_p8 endpoint_15_40_w8
private theorem endpoint_15_40_w10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 10 2 243762067479786599 = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_p12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 12 243762067479786599 = some 243762067479786599 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 10 2 243762067479786599 243762067479786599 243762067479786599 endpoint_15_40_p10 endpoint_15_40_w10
private theorem endpoint_15_40_w12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 12 2 243762067479786599 = some 243762067479786599 := by decide +kernel
private theorem endpoint_15_40_p14 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 14 243762067479786599 = some 243762067479786599 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 12 2 243762067479786599 243762067479786599 243762067479786599 endpoint_15_40_p12 endpoint_15_40_w12
def endpoint_15_40 : CertifiedEndpoint :=
  ⟨⟨15, 40, 3497⟩, 243762067479786599, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_40_flag endpoint_15_40_sources 14 243762067479786599 243762067479786599 rfl endpoint_15_40_base endpoint_15_40_p14) (by decide)⟩
private def endpoint_15_41_flag : Flag := ⟨15, 41, 3460⟩
private def endpoint_15_41_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_15_41_base : receiptBase endpoint_15_41_flag endpoint_15_41_sources = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_w0 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 2 245091936144106000 = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_w2 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 2 2 245091936144106000 = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_p4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 4 245091936144106000 = some 245091936144106000 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 2 2 245091936144106000 245091936144106000 245091936144106000 endpoint_15_41_w0 endpoint_15_41_w2
private theorem endpoint_15_41_w4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 4 2 245091936144106000 = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_p6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 6 245091936144106000 = some 245091936144106000 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 4 2 245091936144106000 245091936144106000 245091936144106000 endpoint_15_41_p4 endpoint_15_41_w4
private theorem endpoint_15_41_w6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 6 2 245091936144106000 = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_p8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 8 245091936144106000 = some 245091936144106000 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 6 2 245091936144106000 245091936144106000 245091936144106000 endpoint_15_41_p6 endpoint_15_41_w6
private theorem endpoint_15_41_w8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 8 2 245091936144106000 = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_p10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 10 245091936144106000 = some 245091936144106000 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 8 2 245091936144106000 245091936144106000 245091936144106000 endpoint_15_41_p8 endpoint_15_41_w8
private theorem endpoint_15_41_w10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 10 2 245091936144106000 = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_p12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 12 245091936144106000 = some 245091936144106000 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 10 2 245091936144106000 245091936144106000 245091936144106000 endpoint_15_41_p10 endpoint_15_41_w10
private theorem endpoint_15_41_w12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 12 2 245091936144106000 = some 245091936144106000 := by decide +kernel
private theorem endpoint_15_41_p14 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 14 245091936144106000 = some 245091936144106000 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 12 2 245091936144106000 245091936144106000 245091936144106000 endpoint_15_41_p12 endpoint_15_41_w12
def endpoint_15_41 : CertifiedEndpoint :=
  ⟨⟨15, 41, 3460⟩, 245091936144106000, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_15_41_flag endpoint_15_41_sources 14 245091936144106000 245091936144106000 rfl endpoint_15_41_base endpoint_15_41_p14) (by decide)⟩
private def endpoint_15_42_flag : Flag := ⟨15, 42, 3421⟩
private def endpoint_15_42_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_42_base : receiptBase endpoint_15_42_flag endpoint_15_42_sources = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_w0 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 2 249159972389105649 = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_w2 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 2 2 249159972389105649 = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_p4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 4 249159972389105649 = some 249159972389105649 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 2 2 249159972389105649 249159972389105649 249159972389105649 endpoint_15_42_w0 endpoint_15_42_w2
private theorem endpoint_15_42_w4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 4 2 249159972389105649 = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_p6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 6 249159972389105649 = some 249159972389105649 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 4 2 249159972389105649 249159972389105649 249159972389105649 endpoint_15_42_p4 endpoint_15_42_w4
private theorem endpoint_15_42_w6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 6 2 249159972389105649 = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_p8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 8 249159972389105649 = some 249159972389105649 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 6 2 249159972389105649 249159972389105649 249159972389105649 endpoint_15_42_p6 endpoint_15_42_w6
private theorem endpoint_15_42_w8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 8 2 249159972389105649 = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_p10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 10 249159972389105649 = some 249159972389105649 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 8 2 249159972389105649 249159972389105649 249159972389105649 endpoint_15_42_p8 endpoint_15_42_w8
private theorem endpoint_15_42_w10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 10 2 249159972389105649 = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_p12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 12 249159972389105649 = some 249159972389105649 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 10 2 249159972389105649 249159972389105649 249159972389105649 endpoint_15_42_p10 endpoint_15_42_w10
private theorem endpoint_15_42_w12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 12 2 249159972389105649 = some 249159972389105649 := by decide +kernel
private theorem endpoint_15_42_p14 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 14 249159972389105649 = some 249159972389105649 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 12 2 249159972389105649 249159972389105649 249159972389105649 endpoint_15_42_p12 endpoint_15_42_w12
def endpoint_15_42 : CertifiedEndpoint :=
  ⟨⟨15, 42, 3421⟩, 249159972389105649, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_42_flag endpoint_15_42_sources 14 249159972389105649 249159972389105649 rfl endpoint_15_42_base endpoint_15_42_p14) (by decide)⟩
private def endpoint_15_43_flag : Flag := ⟨15, 43, 3381⟩
private def endpoint_15_43_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_43_base : receiptBase endpoint_15_43_flag endpoint_15_43_sources = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_w0 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 2 251229982513956646 = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_w2 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 2 2 251229982513956646 = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_p4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 4 251229982513956646 = some 251229982513956646 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 2 2 251229982513956646 251229982513956646 251229982513956646 endpoint_15_43_w0 endpoint_15_43_w2
private theorem endpoint_15_43_w4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 4 2 251229982513956646 = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_p6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 6 251229982513956646 = some 251229982513956646 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 4 2 251229982513956646 251229982513956646 251229982513956646 endpoint_15_43_p4 endpoint_15_43_w4
private theorem endpoint_15_43_w6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 6 2 251229982513956646 = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_p8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 8 251229982513956646 = some 251229982513956646 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 6 2 251229982513956646 251229982513956646 251229982513956646 endpoint_15_43_p6 endpoint_15_43_w6
private theorem endpoint_15_43_w8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 8 2 251229982513956646 = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_p10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 10 251229982513956646 = some 251229982513956646 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 8 2 251229982513956646 251229982513956646 251229982513956646 endpoint_15_43_p8 endpoint_15_43_w8
private theorem endpoint_15_43_w10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 10 2 251229982513956646 = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_p12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 12 251229982513956646 = some 251229982513956646 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 10 2 251229982513956646 251229982513956646 251229982513956646 endpoint_15_43_p10 endpoint_15_43_w10
private theorem endpoint_15_43_w12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 12 2 251229982513956646 = some 251229982513956646 := by decide +kernel
private theorem endpoint_15_43_p14 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 14 251229982513956646 = some 251229982513956646 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 12 2 251229982513956646 251229982513956646 251229982513956646 endpoint_15_43_p12 endpoint_15_43_w12
def endpoint_15_43 : CertifiedEndpoint :=
  ⟨⟨15, 43, 3381⟩, 251229982513956646, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_43_flag endpoint_15_43_sources 14 251229982513956646 251229982513956646 rfl endpoint_15_43_base endpoint_15_43_p14) (by decide)⟩
private def endpoint_15_44_flag : Flag := ⟨15, 44, 3341⟩
private def endpoint_15_44_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_44_base : receiptBase endpoint_15_44_flag endpoint_15_44_sources = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_w0 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 2 253183285989224204 = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_w2 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 2 2 253183285989224204 = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_p4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 4 253183285989224204 = some 253183285989224204 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 2 2 253183285989224204 253183285989224204 253183285989224204 endpoint_15_44_w0 endpoint_15_44_w2
private theorem endpoint_15_44_w4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 4 2 253183285989224204 = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_p6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 6 253183285989224204 = some 253183285989224204 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 4 2 253183285989224204 253183285989224204 253183285989224204 endpoint_15_44_p4 endpoint_15_44_w4
private theorem endpoint_15_44_w6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 6 2 253183285989224204 = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_p8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 8 253183285989224204 = some 253183285989224204 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 6 2 253183285989224204 253183285989224204 253183285989224204 endpoint_15_44_p6 endpoint_15_44_w6
private theorem endpoint_15_44_w8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 8 2 253183285989224204 = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_p10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 10 253183285989224204 = some 253183285989224204 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 8 2 253183285989224204 253183285989224204 253183285989224204 endpoint_15_44_p8 endpoint_15_44_w8
private theorem endpoint_15_44_w10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 10 2 253183285989224204 = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_p12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 12 253183285989224204 = some 253183285989224204 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 10 2 253183285989224204 253183285989224204 253183285989224204 endpoint_15_44_p10 endpoint_15_44_w10
private theorem endpoint_15_44_w12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 12 2 253183285989224204 = some 253183285989224204 := by decide +kernel
private theorem endpoint_15_44_p14 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 14 253183285989224204 = some 253183285989224204 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 12 2 253183285989224204 253183285989224204 253183285989224204 endpoint_15_44_p12 endpoint_15_44_w12
def endpoint_15_44 : CertifiedEndpoint :=
  ⟨⟨15, 44, 3341⟩, 253183285989224204, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_44_flag endpoint_15_44_sources 14 253183285989224204 253183285989224204 rfl endpoint_15_44_base endpoint_15_44_p14) (by decide)⟩
private def endpoint_15_45_flag : Flag := ⟨15, 45, 3299⟩
private def endpoint_15_45_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_45_base : receiptBase endpoint_15_45_flag endpoint_15_45_sources = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_w0 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 2 254867408408587879 = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_w2 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 2 2 254867408408587879 = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_p4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 4 254867408408587879 = some 254867408408587879 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 2 2 254867408408587879 254867408408587879 254867408408587879 endpoint_15_45_w0 endpoint_15_45_w2
private theorem endpoint_15_45_w4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 4 2 254867408408587879 = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_p6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 6 254867408408587879 = some 254867408408587879 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 4 2 254867408408587879 254867408408587879 254867408408587879 endpoint_15_45_p4 endpoint_15_45_w4
private theorem endpoint_15_45_w6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 6 2 254867408408587879 = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_p8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 8 254867408408587879 = some 254867408408587879 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 6 2 254867408408587879 254867408408587879 254867408408587879 endpoint_15_45_p6 endpoint_15_45_w6
private theorem endpoint_15_45_w8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 8 2 254867408408587879 = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_p10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 10 254867408408587879 = some 254867408408587879 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 8 2 254867408408587879 254867408408587879 254867408408587879 endpoint_15_45_p8 endpoint_15_45_w8
private theorem endpoint_15_45_w10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 10 2 254867408408587879 = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_p12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 12 254867408408587879 = some 254867408408587879 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 10 2 254867408408587879 254867408408587879 254867408408587879 endpoint_15_45_p10 endpoint_15_45_w10
private theorem endpoint_15_45_w12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 12 2 254867408408587879 = some 254867408408587879 := by decide +kernel
private theorem endpoint_15_45_p14 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 14 254867408408587879 = some 254867408408587879 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 12 2 254867408408587879 254867408408587879 254867408408587879 endpoint_15_45_p12 endpoint_15_45_w12
def endpoint_15_45 : CertifiedEndpoint :=
  ⟨⟨15, 45, 3299⟩, 254867408408587879, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_45_flag endpoint_15_45_sources 14 254867408408587879 254867408408587879 rfl endpoint_15_45_base endpoint_15_45_p14) (by decide)⟩
private def endpoint_15_46_flag : Flag := ⟨15, 46, 3257⟩
private def endpoint_15_46_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_46_base : receiptBase endpoint_15_46_flag endpoint_15_46_sources = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_w0 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 2 256429060887030662 = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_w2 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 2 2 256429060887030662 = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_p4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 4 256429060887030662 = some 256429060887030662 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 2 2 256429060887030662 256429060887030662 256429060887030662 endpoint_15_46_w0 endpoint_15_46_w2
private theorem endpoint_15_46_w4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 4 2 256429060887030662 = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_p6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 6 256429060887030662 = some 256429060887030662 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 4 2 256429060887030662 256429060887030662 256429060887030662 endpoint_15_46_p4 endpoint_15_46_w4
private theorem endpoint_15_46_w6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 6 2 256429060887030662 = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_p8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 8 256429060887030662 = some 256429060887030662 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 6 2 256429060887030662 256429060887030662 256429060887030662 endpoint_15_46_p6 endpoint_15_46_w6
private theorem endpoint_15_46_w8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 8 2 256429060887030662 = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_p10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 10 256429060887030662 = some 256429060887030662 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 8 2 256429060887030662 256429060887030662 256429060887030662 endpoint_15_46_p8 endpoint_15_46_w8
private theorem endpoint_15_46_w10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 10 2 256429060887030662 = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_p12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 12 256429060887030662 = some 256429060887030662 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 10 2 256429060887030662 256429060887030662 256429060887030662 endpoint_15_46_p10 endpoint_15_46_w10
private theorem endpoint_15_46_w12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 12 2 256429060887030662 = some 256429060887030662 := by decide +kernel
private theorem endpoint_15_46_p14 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 14 256429060887030662 = some 256429060887030662 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 12 2 256429060887030662 256429060887030662 256429060887030662 endpoint_15_46_p12 endpoint_15_46_w12
def endpoint_15_46 : CertifiedEndpoint :=
  ⟨⟨15, 46, 3257⟩, 256429060887030662, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_46_flag endpoint_15_46_sources 14 256429060887030662 256429060887030662 rfl endpoint_15_46_base endpoint_15_46_p14) (by decide)⟩
private def endpoint_15_47_flag : Flag := ⟨15, 47, 3213⟩
private def endpoint_15_47_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_47_base : receiptBase endpoint_15_47_flag endpoint_15_47_sources = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_w0 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 2 258487224019319517 = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_w2 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 2 2 258487224019319517 = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_p4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 4 258487224019319517 = some 258487224019319517 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 2 2 258487224019319517 258487224019319517 258487224019319517 endpoint_15_47_w0 endpoint_15_47_w2
private theorem endpoint_15_47_w4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 4 2 258487224019319517 = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_p6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 6 258487224019319517 = some 258487224019319517 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 4 2 258487224019319517 258487224019319517 258487224019319517 endpoint_15_47_p4 endpoint_15_47_w4
private theorem endpoint_15_47_w6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 6 2 258487224019319517 = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_p8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 8 258487224019319517 = some 258487224019319517 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 6 2 258487224019319517 258487224019319517 258487224019319517 endpoint_15_47_p6 endpoint_15_47_w6
private theorem endpoint_15_47_w8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 8 2 258487224019319517 = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_p10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 10 258487224019319517 = some 258487224019319517 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 8 2 258487224019319517 258487224019319517 258487224019319517 endpoint_15_47_p8 endpoint_15_47_w8
private theorem endpoint_15_47_w10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 10 2 258487224019319517 = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_p12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 12 258487224019319517 = some 258487224019319517 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 10 2 258487224019319517 258487224019319517 258487224019319517 endpoint_15_47_p10 endpoint_15_47_w10
private theorem endpoint_15_47_w12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 12 2 258487224019319517 = some 258487224019319517 := by decide +kernel
private theorem endpoint_15_47_p14 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 14 258487224019319517 = some 258487224019319517 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 12 2 258487224019319517 258487224019319517 258487224019319517 endpoint_15_47_p12 endpoint_15_47_w12
def endpoint_15_47 : CertifiedEndpoint :=
  ⟨⟨15, 47, 3213⟩, 258487224019319517, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_47_flag endpoint_15_47_sources 14 258487224019319517 258487224019319517 rfl endpoint_15_47_base endpoint_15_47_p14) (by decide)⟩
private def endpoint_15_48_flag : Flag := ⟨15, 48, 3168⟩
private def endpoint_15_48_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_48_base : receiptBase endpoint_15_48_flag endpoint_15_48_sources = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_w0 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 2 259570530454450038 = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_w2 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 2 2 259570530454450038 = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_p4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 4 259570530454450038 = some 259570530454450038 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 2 2 259570530454450038 259570530454450038 259570530454450038 endpoint_15_48_w0 endpoint_15_48_w2
private theorem endpoint_15_48_w4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 4 2 259570530454450038 = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_p6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 6 259570530454450038 = some 259570530454450038 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 4 2 259570530454450038 259570530454450038 259570530454450038 endpoint_15_48_p4 endpoint_15_48_w4
private theorem endpoint_15_48_w6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 6 2 259570530454450038 = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_p8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 8 259570530454450038 = some 259570530454450038 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 6 2 259570530454450038 259570530454450038 259570530454450038 endpoint_15_48_p6 endpoint_15_48_w6
private theorem endpoint_15_48_w8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 8 2 259570530454450038 = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_p10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 10 259570530454450038 = some 259570530454450038 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 8 2 259570530454450038 259570530454450038 259570530454450038 endpoint_15_48_p8 endpoint_15_48_w8
private theorem endpoint_15_48_w10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 10 2 259570530454450038 = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_p12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 12 259570530454450038 = some 259570530454450038 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 10 2 259570530454450038 259570530454450038 259570530454450038 endpoint_15_48_p10 endpoint_15_48_w10
private theorem endpoint_15_48_w12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 12 2 259570530454450038 = some 259570530454450038 := by decide +kernel
private theorem endpoint_15_48_p14 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 14 259570530454450038 = some 259570530454450038 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 12 2 259570530454450038 259570530454450038 259570530454450038 endpoint_15_48_p12 endpoint_15_48_w12
def endpoint_15_48 : CertifiedEndpoint :=
  ⟨⟨15, 48, 3168⟩, 259570530454450038, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_48_flag endpoint_15_48_sources 14 259570530454450038 259570530454450038 rfl endpoint_15_48_base endpoint_15_48_p14) (by decide)⟩
private def endpoint_15_49_flag : Flag := ⟨15, 49, 3123⟩
private def endpoint_15_49_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_49_base : receiptBase endpoint_15_49_flag endpoint_15_49_sources = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_w0 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 2 260521902945310358 = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_w2 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 2 2 260521902945310358 = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_p4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 4 260521902945310358 = some 260521902945310358 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 2 2 260521902945310358 260521902945310358 260521902945310358 endpoint_15_49_w0 endpoint_15_49_w2
private theorem endpoint_15_49_w4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 4 2 260521902945310358 = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_p6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 6 260521902945310358 = some 260521902945310358 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 4 2 260521902945310358 260521902945310358 260521902945310358 endpoint_15_49_p4 endpoint_15_49_w4
private theorem endpoint_15_49_w6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 6 2 260521902945310358 = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_p8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 8 260521902945310358 = some 260521902945310358 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 6 2 260521902945310358 260521902945310358 260521902945310358 endpoint_15_49_p6 endpoint_15_49_w6
private theorem endpoint_15_49_w8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 8 2 260521902945310358 = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_p10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 10 260521902945310358 = some 260521902945310358 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 8 2 260521902945310358 260521902945310358 260521902945310358 endpoint_15_49_p8 endpoint_15_49_w8
private theorem endpoint_15_49_w10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 10 2 260521902945310358 = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_p12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 12 260521902945310358 = some 260521902945310358 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 10 2 260521902945310358 260521902945310358 260521902945310358 endpoint_15_49_p10 endpoint_15_49_w10
private theorem endpoint_15_49_w12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 12 2 260521902945310358 = some 260521902945310358 := by decide +kernel
private theorem endpoint_15_49_p14 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 14 260521902945310358 = some 260521902945310358 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 12 2 260521902945310358 260521902945310358 260521902945310358 endpoint_15_49_p12 endpoint_15_49_w12
def endpoint_15_49 : CertifiedEndpoint :=
  ⟨⟨15, 49, 3123⟩, 260521902945310358, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_49_flag endpoint_15_49_sources 14 260521902945310358 260521902945310358 rfl endpoint_15_49_base endpoint_15_49_p14) (by decide)⟩
private def endpoint_15_50_flag : Flag := ⟨15, 50, 3075⟩
private def endpoint_15_50_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_50_base : receiptBase endpoint_15_50_flag endpoint_15_50_sources = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_w0 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 2 261090082280422683 = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_w2 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 2 2 261090082280422683 = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_p4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 4 261090082280422683 = some 261090082280422683 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 2 2 261090082280422683 261090082280422683 261090082280422683 endpoint_15_50_w0 endpoint_15_50_w2
private theorem endpoint_15_50_w4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 4 2 261090082280422683 = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_p6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 6 261090082280422683 = some 261090082280422683 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 4 2 261090082280422683 261090082280422683 261090082280422683 endpoint_15_50_p4 endpoint_15_50_w4
private theorem endpoint_15_50_w6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 6 2 261090082280422683 = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_p8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 8 261090082280422683 = some 261090082280422683 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 6 2 261090082280422683 261090082280422683 261090082280422683 endpoint_15_50_p6 endpoint_15_50_w6
private theorem endpoint_15_50_w8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 8 2 261090082280422683 = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_p10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 10 261090082280422683 = some 261090082280422683 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 8 2 261090082280422683 261090082280422683 261090082280422683 endpoint_15_50_p8 endpoint_15_50_w8
private theorem endpoint_15_50_w10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 10 2 261090082280422683 = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_p12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 12 261090082280422683 = some 261090082280422683 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 10 2 261090082280422683 261090082280422683 261090082280422683 endpoint_15_50_p10 endpoint_15_50_w10
private theorem endpoint_15_50_w12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 12 2 261090082280422683 = some 261090082280422683 := by decide +kernel
private theorem endpoint_15_50_p14 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 14 261090082280422683 = some 261090082280422683 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 12 2 261090082280422683 261090082280422683 261090082280422683 endpoint_15_50_p12 endpoint_15_50_w12
def endpoint_15_50 : CertifiedEndpoint :=
  ⟨⟨15, 50, 3075⟩, 261090082280422683, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_50_flag endpoint_15_50_sources 14 261090082280422683 261090082280422683 rfl endpoint_15_50_base endpoint_15_50_p14) (by decide)⟩
private def endpoint_15_51_flag : Flag := ⟨15, 51, 3027⟩
private def endpoint_15_51_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_51_base : receiptBase endpoint_15_51_flag endpoint_15_51_sources = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_w0 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 2 262382640827234560 = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_w2 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 2 2 262382640827234560 = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_p4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 4 262382640827234560 = some 262382640827234560 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 2 2 262382640827234560 262382640827234560 262382640827234560 endpoint_15_51_w0 endpoint_15_51_w2
private theorem endpoint_15_51_w4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 4 2 262382640827234560 = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_p6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 6 262382640827234560 = some 262382640827234560 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 4 2 262382640827234560 262382640827234560 262382640827234560 endpoint_15_51_p4 endpoint_15_51_w4
private theorem endpoint_15_51_w6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 6 2 262382640827234560 = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_p8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 8 262382640827234560 = some 262382640827234560 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 6 2 262382640827234560 262382640827234560 262382640827234560 endpoint_15_51_p6 endpoint_15_51_w6
private theorem endpoint_15_51_w8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 8 2 262382640827234560 = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_p10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 10 262382640827234560 = some 262382640827234560 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 8 2 262382640827234560 262382640827234560 262382640827234560 endpoint_15_51_p8 endpoint_15_51_w8
private theorem endpoint_15_51_w10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 10 2 262382640827234560 = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_p12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 12 262382640827234560 = some 262382640827234560 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 10 2 262382640827234560 262382640827234560 262382640827234560 endpoint_15_51_p10 endpoint_15_51_w10
private theorem endpoint_15_51_w12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 12 2 262382640827234560 = some 262382640827234560 := by decide +kernel
private theorem endpoint_15_51_p14 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 14 262382640827234560 = some 262382640827234560 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 12 2 262382640827234560 262382640827234560 262382640827234560 endpoint_15_51_p12 endpoint_15_51_w12
def endpoint_15_51 : CertifiedEndpoint :=
  ⟨⟨15, 51, 3027⟩, 262382640827234560, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_51_flag endpoint_15_51_sources 14 262382640827234560 262382640827234560 rfl endpoint_15_51_base endpoint_15_51_p14) (by decide)⟩
private def endpoint_15_52_flag : Flag := ⟨15, 52, 2977⟩
private def endpoint_15_52_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_52_base : receiptBase endpoint_15_52_flag endpoint_15_52_sources = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_w0 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 2 262503842250274275 = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_w2 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 2 2 262503842250274275 = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_p4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 4 262503842250274275 = some 262503842250274275 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 2 2 262503842250274275 262503842250274275 262503842250274275 endpoint_15_52_w0 endpoint_15_52_w2
private theorem endpoint_15_52_w4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 4 2 262503842250274275 = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_p6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 6 262503842250274275 = some 262503842250274275 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 4 2 262503842250274275 262503842250274275 262503842250274275 endpoint_15_52_p4 endpoint_15_52_w4
private theorem endpoint_15_52_w6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 6 2 262503842250274275 = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_p8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 8 262503842250274275 = some 262503842250274275 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 6 2 262503842250274275 262503842250274275 262503842250274275 endpoint_15_52_p6 endpoint_15_52_w6
private theorem endpoint_15_52_w8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 8 2 262503842250274275 = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_p10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 10 262503842250274275 = some 262503842250274275 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 8 2 262503842250274275 262503842250274275 262503842250274275 endpoint_15_52_p8 endpoint_15_52_w8
private theorem endpoint_15_52_w10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 10 2 262503842250274275 = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_p12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 12 262503842250274275 = some 262503842250274275 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 10 2 262503842250274275 262503842250274275 262503842250274275 endpoint_15_52_p10 endpoint_15_52_w10
private theorem endpoint_15_52_w12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 12 2 262503842250274275 = some 262503842250274275 := by decide +kernel
private theorem endpoint_15_52_p14 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 14 262503842250274275 = some 262503842250274275 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 12 2 262503842250274275 262503842250274275 262503842250274275 endpoint_15_52_p12 endpoint_15_52_w12
def endpoint_15_52 : CertifiedEndpoint :=
  ⟨⟨15, 52, 2977⟩, 262503842250274275, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_52_flag endpoint_15_52_sources 14 262503842250274275 262503842250274275 rfl endpoint_15_52_base endpoint_15_52_p14) (by decide)⟩
private def endpoint_15_53_flag : Flag := ⟨15, 53, 2926⟩
private def endpoint_15_53_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_53_base : receiptBase endpoint_15_53_flag endpoint_15_53_sources = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_w0 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 2 263305962270412255 = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_w2 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 2 2 263305962270412255 = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_p4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 4 263305962270412255 = some 263305962270412255 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 2 2 263305962270412255 263305962270412255 263305962270412255 endpoint_15_53_w0 endpoint_15_53_w2
private theorem endpoint_15_53_w4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 4 2 263305962270412255 = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_p6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 6 263305962270412255 = some 263305962270412255 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 4 2 263305962270412255 263305962270412255 263305962270412255 endpoint_15_53_p4 endpoint_15_53_w4
private theorem endpoint_15_53_w6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 6 2 263305962270412255 = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_p8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 8 263305962270412255 = some 263305962270412255 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 6 2 263305962270412255 263305962270412255 263305962270412255 endpoint_15_53_p6 endpoint_15_53_w6
private theorem endpoint_15_53_w8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 8 2 263305962270412255 = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_p10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 10 263305962270412255 = some 263305962270412255 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 8 2 263305962270412255 263305962270412255 263305962270412255 endpoint_15_53_p8 endpoint_15_53_w8
private theorem endpoint_15_53_w10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 10 2 263305962270412255 = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_p12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 12 263305962270412255 = some 263305962270412255 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 10 2 263305962270412255 263305962270412255 263305962270412255 endpoint_15_53_p10 endpoint_15_53_w10
private theorem endpoint_15_53_w12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 12 2 263305962270412255 = some 263305962270412255 := by decide +kernel
private theorem endpoint_15_53_p14 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 14 263305962270412255 = some 263305962270412255 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 12 2 263305962270412255 263305962270412255 263305962270412255 endpoint_15_53_p12 endpoint_15_53_w12
def endpoint_15_53 : CertifiedEndpoint :=
  ⟨⟨15, 53, 2926⟩, 263305962270412255, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_53_flag endpoint_15_53_sources 14 263305962270412255 263305962270412255 rfl endpoint_15_53_base endpoint_15_53_p14) (by decide)⟩
private def endpoint_15_54_flag : Flag := ⟨15, 54, 2874⟩
private def endpoint_15_54_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_54_base : receiptBase endpoint_15_54_flag endpoint_15_54_sources = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_w0 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 2 262957305496269502 = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_w2 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 2 2 262957305496269502 = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_p4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 4 262957305496269502 = some 262957305496269502 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 2 2 262957305496269502 262957305496269502 262957305496269502 endpoint_15_54_w0 endpoint_15_54_w2
private theorem endpoint_15_54_w4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 4 2 262957305496269502 = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_p6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 6 262957305496269502 = some 262957305496269502 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 4 2 262957305496269502 262957305496269502 262957305496269502 endpoint_15_54_p4 endpoint_15_54_w4
private theorem endpoint_15_54_w6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 6 2 262957305496269502 = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_p8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 8 262957305496269502 = some 262957305496269502 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 6 2 262957305496269502 262957305496269502 262957305496269502 endpoint_15_54_p6 endpoint_15_54_w6
private theorem endpoint_15_54_w8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 8 2 262957305496269502 = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_p10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 10 262957305496269502 = some 262957305496269502 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 8 2 262957305496269502 262957305496269502 262957305496269502 endpoint_15_54_p8 endpoint_15_54_w8
private theorem endpoint_15_54_w10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 10 2 262957305496269502 = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_p12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 12 262957305496269502 = some 262957305496269502 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 10 2 262957305496269502 262957305496269502 262957305496269502 endpoint_15_54_p10 endpoint_15_54_w10
private theorem endpoint_15_54_w12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 12 2 262957305496269502 = some 262957305496269502 := by decide +kernel
private theorem endpoint_15_54_p14 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 14 262957305496269502 = some 262957305496269502 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 12 2 262957305496269502 262957305496269502 262957305496269502 endpoint_15_54_p12 endpoint_15_54_w12
def endpoint_15_54 : CertifiedEndpoint :=
  ⟨⟨15, 54, 2874⟩, 262957305496269502, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_54_flag endpoint_15_54_sources 14 262957305496269502 262957305496269502 rfl endpoint_15_54_base endpoint_15_54_p14) (by decide)⟩
private def endpoint_15_55_flag : Flag := ⟨15, 55, 2820⟩
private def endpoint_15_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_55_base : receiptBase endpoint_15_55_flag endpoint_15_55_sources = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_w0 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 2 263078577288248906 = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_w2 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 2 2 263078577288248906 = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_p4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 4 263078577288248906 = some 263078577288248906 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 2 2 263078577288248906 263078577288248906 263078577288248906 endpoint_15_55_w0 endpoint_15_55_w2
private theorem endpoint_15_55_w4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 4 2 263078577288248906 = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_p6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 6 263078577288248906 = some 263078577288248906 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 4 2 263078577288248906 263078577288248906 263078577288248906 endpoint_15_55_p4 endpoint_15_55_w4
private theorem endpoint_15_55_w6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 6 2 263078577288248906 = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_p8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 8 263078577288248906 = some 263078577288248906 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 6 2 263078577288248906 263078577288248906 263078577288248906 endpoint_15_55_p6 endpoint_15_55_w6
private theorem endpoint_15_55_w8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 8 2 263078577288248906 = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_p10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 10 263078577288248906 = some 263078577288248906 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 8 2 263078577288248906 263078577288248906 263078577288248906 endpoint_15_55_p8 endpoint_15_55_w8
private theorem endpoint_15_55_w10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 10 2 263078577288248906 = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_p12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 12 263078577288248906 = some 263078577288248906 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 10 2 263078577288248906 263078577288248906 263078577288248906 endpoint_15_55_p10 endpoint_15_55_w10
private theorem endpoint_15_55_w12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 12 2 263078577288248906 = some 263078577288248906 := by decide +kernel
private theorem endpoint_15_55_p14 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 14 263078577288248906 = some 263078577288248906 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 12 2 263078577288248906 263078577288248906 263078577288248906 endpoint_15_55_p12 endpoint_15_55_w12
def endpoint_15_55 : CertifiedEndpoint :=
  ⟨⟨15, 55, 2820⟩, 263078577288248906, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_55_flag endpoint_15_55_sources 14 263078577288248906 263078577288248906 rfl endpoint_15_55_base endpoint_15_55_p14) (by decide)⟩
private def endpoint_15_56_flag : Flag := ⟨15, 56, 2764⟩
private def endpoint_15_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_56_base : receiptBase endpoint_15_56_flag endpoint_15_56_sources = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_w0 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 2 262045681278169991 = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_w2 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 2 2 262045681278169991 = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_p4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 4 262045681278169991 = some 262045681278169991 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 2 2 262045681278169991 262045681278169991 262045681278169991 endpoint_15_56_w0 endpoint_15_56_w2
private theorem endpoint_15_56_w4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 4 2 262045681278169991 = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_p6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 6 262045681278169991 = some 262045681278169991 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 4 2 262045681278169991 262045681278169991 262045681278169991 endpoint_15_56_p4 endpoint_15_56_w4
private theorem endpoint_15_56_w6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 6 2 262045681278169991 = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_p8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 8 262045681278169991 = some 262045681278169991 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 6 2 262045681278169991 262045681278169991 262045681278169991 endpoint_15_56_p6 endpoint_15_56_w6
private theorem endpoint_15_56_w8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 8 2 262045681278169991 = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_p10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 10 262045681278169991 = some 262045681278169991 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 8 2 262045681278169991 262045681278169991 262045681278169991 endpoint_15_56_p8 endpoint_15_56_w8
private theorem endpoint_15_56_w10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 10 2 262045681278169991 = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_p12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 12 262045681278169991 = some 262045681278169991 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 10 2 262045681278169991 262045681278169991 262045681278169991 endpoint_15_56_p10 endpoint_15_56_w10
private theorem endpoint_15_56_w12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 12 2 262045681278169991 = some 262045681278169991 := by decide +kernel
private theorem endpoint_15_56_p14 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 14 262045681278169991 = some 262045681278169991 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 12 2 262045681278169991 262045681278169991 262045681278169991 endpoint_15_56_p12 endpoint_15_56_w12
def endpoint_15_56 : CertifiedEndpoint :=
  ⟨⟨15, 56, 2764⟩, 262045681278169991, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_56_flag endpoint_15_56_sources 14 262045681278169991 262045681278169991 rfl endpoint_15_56_base endpoint_15_56_p14) (by decide)⟩
private def endpoint_15_57_flag : Flag := ⟨15, 57, 2707⟩
private def endpoint_15_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_57_base : receiptBase endpoint_15_57_flag endpoint_15_57_sources = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_w0 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 2 260750878340970736 = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_w2 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 2 2 260750878340970736 = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_p4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 4 260750878340970736 = some 260750878340970736 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 2 2 260750878340970736 260750878340970736 260750878340970736 endpoint_15_57_w0 endpoint_15_57_w2
private theorem endpoint_15_57_w4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 4 2 260750878340970736 = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_p6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 6 260750878340970736 = some 260750878340970736 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 4 2 260750878340970736 260750878340970736 260750878340970736 endpoint_15_57_p4 endpoint_15_57_w4
private theorem endpoint_15_57_w6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 6 2 260750878340970736 = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_p8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 8 260750878340970736 = some 260750878340970736 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 6 2 260750878340970736 260750878340970736 260750878340970736 endpoint_15_57_p6 endpoint_15_57_w6
private theorem endpoint_15_57_w8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 8 2 260750878340970736 = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_p10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 10 260750878340970736 = some 260750878340970736 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 8 2 260750878340970736 260750878340970736 260750878340970736 endpoint_15_57_p8 endpoint_15_57_w8
private theorem endpoint_15_57_w10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 10 2 260750878340970736 = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_p12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 12 260750878340970736 = some 260750878340970736 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 10 2 260750878340970736 260750878340970736 260750878340970736 endpoint_15_57_p10 endpoint_15_57_w10
private theorem endpoint_15_57_w12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 12 2 260750878340970736 = some 260750878340970736 := by decide +kernel
private theorem endpoint_15_57_p14 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 14 260750878340970736 = some 260750878340970736 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 12 2 260750878340970736 260750878340970736 260750878340970736 endpoint_15_57_p12 endpoint_15_57_w12
def endpoint_15_57 : CertifiedEndpoint :=
  ⟨⟨15, 57, 2707⟩, 260750878340970736, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_57_flag endpoint_15_57_sources 14 260750878340970736 260750878340970736 rfl endpoint_15_57_base endpoint_15_57_p14) (by decide)⟩
private def endpoint_15_58_flag : Flag := ⟨15, 58, 2648⟩
private def endpoint_15_58_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_58_base : receiptBase endpoint_15_58_flag endpoint_15_58_sources = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_w0 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 2 259220154808901717 = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_w2 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 2 2 259220154808901717 = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_p4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 4 259220154808901717 = some 259220154808901717 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 2 2 259220154808901717 259220154808901717 259220154808901717 endpoint_15_58_w0 endpoint_15_58_w2
private theorem endpoint_15_58_w4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 4 2 259220154808901717 = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_p6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 6 259220154808901717 = some 259220154808901717 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 4 2 259220154808901717 259220154808901717 259220154808901717 endpoint_15_58_p4 endpoint_15_58_w4
private theorem endpoint_15_58_w6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 6 2 259220154808901717 = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_p8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 8 259220154808901717 = some 259220154808901717 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 6 2 259220154808901717 259220154808901717 259220154808901717 endpoint_15_58_p6 endpoint_15_58_w6
private theorem endpoint_15_58_w8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 8 2 259220154808901717 = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_p10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 10 259220154808901717 = some 259220154808901717 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 8 2 259220154808901717 259220154808901717 259220154808901717 endpoint_15_58_p8 endpoint_15_58_w8
private theorem endpoint_15_58_w10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 10 2 259220154808901717 = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_p12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 12 259220154808901717 = some 259220154808901717 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 10 2 259220154808901717 259220154808901717 259220154808901717 endpoint_15_58_p10 endpoint_15_58_w10
private theorem endpoint_15_58_w12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 12 2 259220154808901717 = some 259220154808901717 := by decide +kernel
private theorem endpoint_15_58_p14 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 14 259220154808901717 = some 259220154808901717 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 12 2 259220154808901717 259220154808901717 259220154808901717 endpoint_15_58_p12 endpoint_15_58_w12
def endpoint_15_58 : CertifiedEndpoint :=
  ⟨⟨15, 58, 2648⟩, 259220154808901717, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_58_flag endpoint_15_58_sources 14 259220154808901717 259220154808901717 rfl endpoint_15_58_base endpoint_15_58_p14) (by decide)⟩
private def endpoint_15_59_flag : Flag := ⟨15, 59, 2587⟩
private def endpoint_15_59_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_15_59_base : receiptBase endpoint_15_59_flag endpoint_15_59_sources = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_w0 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 2 263308801483871196 = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_w2 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 2 2 263308801483871196 = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_p4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 4 263308801483871196 = some 263308801483871196 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 2 2 263308801483871196 263308801483871196 263308801483871196 endpoint_15_59_w0 endpoint_15_59_w2
private theorem endpoint_15_59_w4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 4 2 263308801483871196 = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_p6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 6 263308801483871196 = some 263308801483871196 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 4 2 263308801483871196 263308801483871196 263308801483871196 endpoint_15_59_p4 endpoint_15_59_w4
private theorem endpoint_15_59_w6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 6 2 263308801483871196 = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_p8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 8 263308801483871196 = some 263308801483871196 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 6 2 263308801483871196 263308801483871196 263308801483871196 endpoint_15_59_p6 endpoint_15_59_w6
private theorem endpoint_15_59_w8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 8 2 263308801483871196 = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_p10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 10 263308801483871196 = some 263308801483871196 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 8 2 263308801483871196 263308801483871196 263308801483871196 endpoint_15_59_p8 endpoint_15_59_w8
private theorem endpoint_15_59_w10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 10 2 263308801483871196 = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_p12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 12 263308801483871196 = some 263308801483871196 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 10 2 263308801483871196 263308801483871196 263308801483871196 endpoint_15_59_p10 endpoint_15_59_w10
private theorem endpoint_15_59_w12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 12 2 263308801483871196 = some 263308801483871196 := by decide +kernel
private theorem endpoint_15_59_p14 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 14 263308801483871196 = some 263308801483871196 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 12 2 263308801483871196 263308801483871196 263308801483871196 endpoint_15_59_p12 endpoint_15_59_w12
def endpoint_15_59 : CertifiedEndpoint :=
  ⟨⟨15, 59, 2587⟩, 263308801483871196, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_15_59_flag endpoint_15_59_sources 14 263308801483871196 263308801483871196 rfl endpoint_15_59_base endpoint_15_59_p14) (by decide)⟩
private def endpoint_15_60_flag : Flag := ⟨15, 60, 2525⟩
private def endpoint_15_60_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_60_base : receiptBase endpoint_15_60_flag endpoint_15_60_sources = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_w0 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 2 261089749424229969 = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_w2 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 2 2 261089749424229969 = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_p4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 4 261089749424229969 = some 261089749424229969 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 2 2 261089749424229969 261089749424229969 261089749424229969 endpoint_15_60_w0 endpoint_15_60_w2
private theorem endpoint_15_60_w4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 4 2 261089749424229969 = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_p6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 6 261089749424229969 = some 261089749424229969 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 4 2 261089749424229969 261089749424229969 261089749424229969 endpoint_15_60_p4 endpoint_15_60_w4
private theorem endpoint_15_60_w6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 6 2 261089749424229969 = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_p8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 8 261089749424229969 = some 261089749424229969 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 6 2 261089749424229969 261089749424229969 261089749424229969 endpoint_15_60_p6 endpoint_15_60_w6
private theorem endpoint_15_60_w8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 8 2 261089749424229969 = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_p10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 10 261089749424229969 = some 261089749424229969 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 8 2 261089749424229969 261089749424229969 261089749424229969 endpoint_15_60_p8 endpoint_15_60_w8
private theorem endpoint_15_60_w10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 10 2 261089749424229969 = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_p12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 12 261089749424229969 = some 261089749424229969 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 10 2 261089749424229969 261089749424229969 261089749424229969 endpoint_15_60_p10 endpoint_15_60_w10
private theorem endpoint_15_60_w12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 12 2 261089749424229969 = some 261089749424229969 := by decide +kernel
private theorem endpoint_15_60_p14 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 14 261089749424229969 = some 261089749424229969 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 12 2 261089749424229969 261089749424229969 261089749424229969 endpoint_15_60_p12 endpoint_15_60_w12
def endpoint_15_60 : CertifiedEndpoint :=
  ⟨⟨15, 60, 2525⟩, 261089749424229969, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_60_flag endpoint_15_60_sources 14 261089749424229969 261089749424229969 rfl endpoint_15_60_base endpoint_15_60_p14) (by decide)⟩
private def endpoint_15_61_flag : Flag := ⟨15, 61, 2461⟩
private def endpoint_15_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_61_base : receiptBase endpoint_15_61_flag endpoint_15_61_sources = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_w0 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 2 258357933861571948 = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_w2 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 2 2 258357933861571948 = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_p4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 4 258357933861571948 = some 258357933861571948 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 2 2 258357933861571948 258357933861571948 258357933861571948 endpoint_15_61_w0 endpoint_15_61_w2
private theorem endpoint_15_61_w4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 4 2 258357933861571948 = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_p6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 6 258357933861571948 = some 258357933861571948 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 4 2 258357933861571948 258357933861571948 258357933861571948 endpoint_15_61_p4 endpoint_15_61_w4
private theorem endpoint_15_61_w6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 6 2 258357933861571948 = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_p8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 8 258357933861571948 = some 258357933861571948 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 6 2 258357933861571948 258357933861571948 258357933861571948 endpoint_15_61_p6 endpoint_15_61_w6
private theorem endpoint_15_61_w8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 8 2 258357933861571948 = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_p10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 10 258357933861571948 = some 258357933861571948 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 8 2 258357933861571948 258357933861571948 258357933861571948 endpoint_15_61_p8 endpoint_15_61_w8
private theorem endpoint_15_61_w10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 10 2 258357933861571948 = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_p12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 12 258357933861571948 = some 258357933861571948 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 10 2 258357933861571948 258357933861571948 258357933861571948 endpoint_15_61_p10 endpoint_15_61_w10
private theorem endpoint_15_61_w12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 12 2 258357933861571948 = some 258357933861571948 := by decide +kernel
private theorem endpoint_15_61_p14 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 14 258357933861571948 = some 258357933861571948 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 12 2 258357933861571948 258357933861571948 258357933861571948 endpoint_15_61_p12 endpoint_15_61_w12
def endpoint_15_61 : CertifiedEndpoint :=
  ⟨⟨15, 61, 2461⟩, 258357933861571948, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_61_flag endpoint_15_61_sources 14 258357933861571948 258357933861571948 rfl endpoint_15_61_base endpoint_15_61_p14) (by decide)⟩
private def endpoint_15_62_flag : Flag := ⟨15, 62, 2394⟩
private def endpoint_15_62_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_62_base : receiptBase endpoint_15_62_flag endpoint_15_62_sources = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_w0 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 2 255123624818096332 = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_w2 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 2 2 255123624818096332 = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_p4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 4 255123624818096332 = some 255123624818096332 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 2 2 255123624818096332 255123624818096332 255123624818096332 endpoint_15_62_w0 endpoint_15_62_w2
private theorem endpoint_15_62_w4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 4 2 255123624818096332 = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_p6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 6 255123624818096332 = some 255123624818096332 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 4 2 255123624818096332 255123624818096332 255123624818096332 endpoint_15_62_p4 endpoint_15_62_w4
private theorem endpoint_15_62_w6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 6 2 255123624818096332 = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_p8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 8 255123624818096332 = some 255123624818096332 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 6 2 255123624818096332 255123624818096332 255123624818096332 endpoint_15_62_p6 endpoint_15_62_w6
private theorem endpoint_15_62_w8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 8 2 255123624818096332 = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_p10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 10 255123624818096332 = some 255123624818096332 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 8 2 255123624818096332 255123624818096332 255123624818096332 endpoint_15_62_p8 endpoint_15_62_w8
private theorem endpoint_15_62_w10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 10 2 255123624818096332 = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_p12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 12 255123624818096332 = some 255123624818096332 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 10 2 255123624818096332 255123624818096332 255123624818096332 endpoint_15_62_p10 endpoint_15_62_w10
private theorem endpoint_15_62_w12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 12 2 255123624818096332 = some 255123624818096332 := by decide +kernel
private theorem endpoint_15_62_p14 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 14 255123624818096332 = some 255123624818096332 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 12 2 255123624818096332 255123624818096332 255123624818096332 endpoint_15_62_p12 endpoint_15_62_w12
def endpoint_15_62 : CertifiedEndpoint :=
  ⟨⟨15, 62, 2394⟩, 255123624818096332, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_62_flag endpoint_15_62_sources 14 255123624818096332 255123624818096332 rfl endpoint_15_62_base endpoint_15_62_p14) (by decide)⟩
private def endpoint_15_63_flag : Flag := ⟨15, 63, 2326⟩
private def endpoint_15_63_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_63_base : receiptBase endpoint_15_63_flag endpoint_15_63_sources = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_w0 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 2 252708031739993787 = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_w2 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 2 2 252708031739993787 = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_p4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 4 252708031739993787 = some 252708031739993787 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 2 2 252708031739993787 252708031739993787 252708031739993787 endpoint_15_63_w0 endpoint_15_63_w2
private theorem endpoint_15_63_w4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 4 2 252708031739993787 = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_p6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 6 252708031739993787 = some 252708031739993787 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 4 2 252708031739993787 252708031739993787 252708031739993787 endpoint_15_63_p4 endpoint_15_63_w4
private theorem endpoint_15_63_w6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 6 2 252708031739993787 = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_p8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 8 252708031739993787 = some 252708031739993787 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 6 2 252708031739993787 252708031739993787 252708031739993787 endpoint_15_63_p6 endpoint_15_63_w6
private theorem endpoint_15_63_w8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 8 2 252708031739993787 = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_p10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 10 252708031739993787 = some 252708031739993787 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 8 2 252708031739993787 252708031739993787 252708031739993787 endpoint_15_63_p8 endpoint_15_63_w8
private theorem endpoint_15_63_w10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 10 2 252708031739993787 = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_p12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 12 252708031739993787 = some 252708031739993787 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 10 2 252708031739993787 252708031739993787 252708031739993787 endpoint_15_63_p10 endpoint_15_63_w10
private theorem endpoint_15_63_w12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 12 2 252708031739993787 = some 252708031739993787 := by decide +kernel
private theorem endpoint_15_63_p14 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 14 252708031739993787 = some 252708031739993787 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 12 2 252708031739993787 252708031739993787 252708031739993787 endpoint_15_63_p12 endpoint_15_63_w12
def endpoint_15_63 : CertifiedEndpoint :=
  ⟨⟨15, 63, 2326⟩, 252708031739993787, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_63_flag endpoint_15_63_sources 14 252708031739993787 252708031739993787 rfl endpoint_15_63_base endpoint_15_63_p14) (by decide)⟩
private def endpoint_15_64_flag : Flag := ⟨15, 64, 2255⟩
private def endpoint_15_64_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_64_base : receiptBase endpoint_15_64_flag endpoint_15_64_sources = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_w0 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 2 248614201194604393 = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_w2 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 2 2 248614201194604393 = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_p4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 4 248614201194604393 = some 248614201194604393 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 2 2 248614201194604393 248614201194604393 248614201194604393 endpoint_15_64_w0 endpoint_15_64_w2
private theorem endpoint_15_64_w4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 4 2 248614201194604393 = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_p6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 6 248614201194604393 = some 248614201194604393 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 4 2 248614201194604393 248614201194604393 248614201194604393 endpoint_15_64_p4 endpoint_15_64_w4
private theorem endpoint_15_64_w6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 6 2 248614201194604393 = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_p8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 8 248614201194604393 = some 248614201194604393 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 6 2 248614201194604393 248614201194604393 248614201194604393 endpoint_15_64_p6 endpoint_15_64_w6
private theorem endpoint_15_64_w8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 8 2 248614201194604393 = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_p10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 10 248614201194604393 = some 248614201194604393 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 8 2 248614201194604393 248614201194604393 248614201194604393 endpoint_15_64_p8 endpoint_15_64_w8
private theorem endpoint_15_64_w10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 10 2 248614201194604393 = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_p12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 12 248614201194604393 = some 248614201194604393 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 10 2 248614201194604393 248614201194604393 248614201194604393 endpoint_15_64_p10 endpoint_15_64_w10
private theorem endpoint_15_64_w12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 12 2 248614201194604393 = some 248614201194604393 := by decide +kernel
private theorem endpoint_15_64_p14 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 14 248614201194604393 = some 248614201194604393 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 12 2 248614201194604393 248614201194604393 248614201194604393 endpoint_15_64_p12 endpoint_15_64_w12
def endpoint_15_64 : CertifiedEndpoint :=
  ⟨⟨15, 64, 2255⟩, 248614201194604393, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_64_flag endpoint_15_64_sources 14 248614201194604393 248614201194604393 rfl endpoint_15_64_base endpoint_15_64_p14) (by decide)⟩
private def endpoint_15_65_flag : Flag := ⟨15, 65, 2182⟩
private def endpoint_15_65_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_65_base : receiptBase endpoint_15_65_flag endpoint_15_65_sources = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_w0 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 2 244088381424858800 = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_w2 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 2 2 244088381424858800 = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_p4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 4 244088381424858800 = some 244088381424858800 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 2 2 244088381424858800 244088381424858800 244088381424858800 endpoint_15_65_w0 endpoint_15_65_w2
private theorem endpoint_15_65_w4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 4 2 244088381424858800 = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_p6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 6 244088381424858800 = some 244088381424858800 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 4 2 244088381424858800 244088381424858800 244088381424858800 endpoint_15_65_p4 endpoint_15_65_w4
private theorem endpoint_15_65_w6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 6 2 244088381424858800 = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_p8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 8 244088381424858800 = some 244088381424858800 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 6 2 244088381424858800 244088381424858800 244088381424858800 endpoint_15_65_p6 endpoint_15_65_w6
private theorem endpoint_15_65_w8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 8 2 244088381424858800 = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_p10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 10 244088381424858800 = some 244088381424858800 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 8 2 244088381424858800 244088381424858800 244088381424858800 endpoint_15_65_p8 endpoint_15_65_w8
private theorem endpoint_15_65_w10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 10 2 244088381424858800 = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_p12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 12 244088381424858800 = some 244088381424858800 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 10 2 244088381424858800 244088381424858800 244088381424858800 endpoint_15_65_p10 endpoint_15_65_w10
private theorem endpoint_15_65_w12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 12 2 244088381424858800 = some 244088381424858800 := by decide +kernel
private theorem endpoint_15_65_p14 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 14 244088381424858800 = some 244088381424858800 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 12 2 244088381424858800 244088381424858800 244088381424858800 endpoint_15_65_p12 endpoint_15_65_w12
def endpoint_15_65 : CertifiedEndpoint :=
  ⟨⟨15, 65, 2182⟩, 244088381424858800, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_65_flag endpoint_15_65_sources 14 244088381424858800 244088381424858800 rfl endpoint_15_65_base endpoint_15_65_p14) (by decide)⟩
private def endpoint_15_66_flag : Flag := ⟨15, 66, 2106⟩
private def endpoint_15_66_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_15_66_base : receiptBase endpoint_15_66_flag endpoint_15_66_sources = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_w0 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 2 240467397369912531 = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_w2 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 2 2 240467397369912531 = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_p4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 4 240467397369912531 = some 240467397369912531 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 2 2 240467397369912531 240467397369912531 240467397369912531 endpoint_15_66_w0 endpoint_15_66_w2
private theorem endpoint_15_66_w4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 4 2 240467397369912531 = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_p6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 6 240467397369912531 = some 240467397369912531 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 4 2 240467397369912531 240467397369912531 240467397369912531 endpoint_15_66_p4 endpoint_15_66_w4
private theorem endpoint_15_66_w6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 6 2 240467397369912531 = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_p8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 8 240467397369912531 = some 240467397369912531 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 6 2 240467397369912531 240467397369912531 240467397369912531 endpoint_15_66_p6 endpoint_15_66_w6
private theorem endpoint_15_66_w8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 8 2 240467397369912531 = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_p10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 10 240467397369912531 = some 240467397369912531 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 8 2 240467397369912531 240467397369912531 240467397369912531 endpoint_15_66_p8 endpoint_15_66_w8
private theorem endpoint_15_66_w10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 10 2 240467397369912531 = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_p12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 12 240467397369912531 = some 240467397369912531 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 10 2 240467397369912531 240467397369912531 240467397369912531 endpoint_15_66_p10 endpoint_15_66_w10
private theorem endpoint_15_66_w12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 12 2 240467397369912531 = some 240467397369912531 := by decide +kernel
private theorem endpoint_15_66_p14 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 14 240467397369912531 = some 240467397369912531 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 12 2 240467397369912531 240467397369912531 240467397369912531 endpoint_15_66_p12 endpoint_15_66_w12
def endpoint_15_66 : CertifiedEndpoint :=
  ⟨⟨15, 66, 2106⟩, 240467397369912531, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_15_66_flag endpoint_15_66_sources 14 240467397369912531 240467397369912531 rfl endpoint_15_66_base endpoint_15_66_p14) (by decide)⟩
private def endpoint_15_67_flag : Flag := ⟨15, 67, 2028⟩
private def endpoint_15_67_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_67_base : receiptBase endpoint_15_67_flag endpoint_15_67_sources = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_w0 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 2 238007229815574412 = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_w2 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 2 2 238007229815574412 = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_p4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 4 238007229815574412 = some 238007229815574412 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 2 2 238007229815574412 238007229815574412 238007229815574412 endpoint_15_67_w0 endpoint_15_67_w2
private theorem endpoint_15_67_w4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 4 2 238007229815574412 = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_p6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 6 238007229815574412 = some 238007229815574412 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 4 2 238007229815574412 238007229815574412 238007229815574412 endpoint_15_67_p4 endpoint_15_67_w4
private theorem endpoint_15_67_w6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 6 2 238007229815574412 = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_p8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 8 238007229815574412 = some 238007229815574412 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 6 2 238007229815574412 238007229815574412 238007229815574412 endpoint_15_67_p6 endpoint_15_67_w6
private theorem endpoint_15_67_w8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 8 2 238007229815574412 = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_p10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 10 238007229815574412 = some 238007229815574412 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 8 2 238007229815574412 238007229815574412 238007229815574412 endpoint_15_67_p8 endpoint_15_67_w8
private theorem endpoint_15_67_w10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 10 2 238007229815574412 = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_p12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 12 238007229815574412 = some 238007229815574412 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 10 2 238007229815574412 238007229815574412 238007229815574412 endpoint_15_67_p10 endpoint_15_67_w10
private theorem endpoint_15_67_w12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 12 2 238007229815574412 = some 238007229815574412 := by decide +kernel
private theorem endpoint_15_67_p14 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 14 238007229815574412 = some 238007229815574412 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 12 2 238007229815574412 238007229815574412 238007229815574412 endpoint_15_67_p12 endpoint_15_67_w12
def endpoint_15_67 : CertifiedEndpoint :=
  ⟨⟨15, 67, 2028⟩, 238007229815574412, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_67_flag endpoint_15_67_sources 14 238007229815574412 238007229815574412 rfl endpoint_15_67_base endpoint_15_67_p14) (by decide)⟩
private def endpoint_15_68_flag : Flag := ⟨15, 68, 1947⟩
private def endpoint_15_68_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_68_base : receiptBase endpoint_15_68_flag endpoint_15_68_sources = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_w0 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 2 231607696540253428 = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_w2 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 2 2 231607696540253428 = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_p4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 4 231607696540253428 = some 231607696540253428 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 2 2 231607696540253428 231607696540253428 231607696540253428 endpoint_15_68_w0 endpoint_15_68_w2
private theorem endpoint_15_68_w4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 4 2 231607696540253428 = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_p6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 6 231607696540253428 = some 231607696540253428 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 4 2 231607696540253428 231607696540253428 231607696540253428 endpoint_15_68_p4 endpoint_15_68_w4
private theorem endpoint_15_68_w6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 6 2 231607696540253428 = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_p8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 8 231607696540253428 = some 231607696540253428 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 6 2 231607696540253428 231607696540253428 231607696540253428 endpoint_15_68_p6 endpoint_15_68_w6
private theorem endpoint_15_68_w8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 8 2 231607696540253428 = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_p10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 10 231607696540253428 = some 231607696540253428 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 8 2 231607696540253428 231607696540253428 231607696540253428 endpoint_15_68_p8 endpoint_15_68_w8
private theorem endpoint_15_68_w10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 10 2 231607696540253428 = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_p12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 12 231607696540253428 = some 231607696540253428 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 10 2 231607696540253428 231607696540253428 231607696540253428 endpoint_15_68_p10 endpoint_15_68_w10
private theorem endpoint_15_68_w12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 12 2 231607696540253428 = some 231607696540253428 := by decide +kernel
private theorem endpoint_15_68_p14 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 14 231607696540253428 = some 231607696540253428 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 12 2 231607696540253428 231607696540253428 231607696540253428 endpoint_15_68_p12 endpoint_15_68_w12
def endpoint_15_68 : CertifiedEndpoint :=
  ⟨⟨15, 68, 1947⟩, 231607696540253428, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_68_flag endpoint_15_68_sources 14 231607696540253428 231607696540253428 rfl endpoint_15_68_base endpoint_15_68_p14) (by decide)⟩
private def endpoint_15_69_flag : Flag := ⟨15, 69, 1864⟩
private def endpoint_15_69_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_69_base : receiptBase endpoint_15_69_flag endpoint_15_69_sources = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_w0 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 2 224716879514050484 = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_w2 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 2 2 224716879514050484 = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_p4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 4 224716879514050484 = some 224716879514050484 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 2 2 224716879514050484 224716879514050484 224716879514050484 endpoint_15_69_w0 endpoint_15_69_w2
private theorem endpoint_15_69_w4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 4 2 224716879514050484 = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_p6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 6 224716879514050484 = some 224716879514050484 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 4 2 224716879514050484 224716879514050484 224716879514050484 endpoint_15_69_p4 endpoint_15_69_w4
private theorem endpoint_15_69_w6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 6 2 224716879514050484 = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_p8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 8 224716879514050484 = some 224716879514050484 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 6 2 224716879514050484 224716879514050484 224716879514050484 endpoint_15_69_p6 endpoint_15_69_w6
private theorem endpoint_15_69_w8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 8 2 224716879514050484 = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_p10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 10 224716879514050484 = some 224716879514050484 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 8 2 224716879514050484 224716879514050484 224716879514050484 endpoint_15_69_p8 endpoint_15_69_w8
private theorem endpoint_15_69_w10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 10 2 224716879514050484 = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_p12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 12 224716879514050484 = some 224716879514050484 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 10 2 224716879514050484 224716879514050484 224716879514050484 endpoint_15_69_p10 endpoint_15_69_w10
private theorem endpoint_15_69_w12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 12 2 224716879514050484 = some 224716879514050484 := by decide +kernel
private theorem endpoint_15_69_p14 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 14 224716879514050484 = some 224716879514050484 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 12 2 224716879514050484 224716879514050484 224716879514050484 endpoint_15_69_p12 endpoint_15_69_w12
def endpoint_15_69 : CertifiedEndpoint :=
  ⟨⟨15, 69, 1864⟩, 224716879514050484, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_69_flag endpoint_15_69_sources 14 224716879514050484 224716879514050484 rfl endpoint_15_69_base endpoint_15_69_p14) (by decide)⟩
private def endpoint_15_70_flag : Flag := ⟨15, 70, 1778⟩
private def endpoint_15_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_15_70_base : receiptBase endpoint_15_70_flag endpoint_15_70_sources = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_w0 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 2 215823204948438115 = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_w2 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 2 2 215823204948438115 = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_p4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 4 215823204948438115 = some 215823204948438115 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 2 2 215823204948438115 215823204948438115 215823204948438115 endpoint_15_70_w0 endpoint_15_70_w2
private theorem endpoint_15_70_w4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 4 2 215823204948438115 = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_p6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 6 215823204948438115 = some 215823204948438115 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 4 2 215823204948438115 215823204948438115 215823204948438115 endpoint_15_70_p4 endpoint_15_70_w4
private theorem endpoint_15_70_w6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 6 2 215823204948438115 = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_p8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 8 215823204948438115 = some 215823204948438115 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 6 2 215823204948438115 215823204948438115 215823204948438115 endpoint_15_70_p6 endpoint_15_70_w6
private theorem endpoint_15_70_w8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 8 2 215823204948438115 = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_p10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 10 215823204948438115 = some 215823204948438115 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 8 2 215823204948438115 215823204948438115 215823204948438115 endpoint_15_70_p8 endpoint_15_70_w8
private theorem endpoint_15_70_w10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 10 2 215823204948438115 = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_p12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 12 215823204948438115 = some 215823204948438115 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 10 2 215823204948438115 215823204948438115 215823204948438115 endpoint_15_70_p10 endpoint_15_70_w10
private theorem endpoint_15_70_w12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 12 2 215823204948438115 = some 215823204948438115 := by decide +kernel
private theorem endpoint_15_70_p14 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 14 215823204948438115 = some 215823204948438115 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 12 2 215823204948438115 215823204948438115 215823204948438115 endpoint_15_70_p12 endpoint_15_70_w12
def endpoint_15_70 : CertifiedEndpoint :=
  ⟨⟨15, 70, 1778⟩, 215823204948438115, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_15_70_flag endpoint_15_70_sources 14 215823204948438115 215823204948438115 rfl endpoint_15_70_base endpoint_15_70_p14) (by decide)⟩
private def endpoint_15_71_flag : Flag := ⟨15, 71, 1689⟩
private def endpoint_15_71_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_71_base : receiptBase endpoint_15_71_flag endpoint_15_71_sources = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_w0 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 2 210726001901410981 = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_w2 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 2 2 210726001901410981 = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_p4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 4 210726001901410981 = some 210726001901410981 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 2 2 210726001901410981 210726001901410981 210726001901410981 endpoint_15_71_w0 endpoint_15_71_w2
private theorem endpoint_15_71_w4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 4 2 210726001901410981 = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_p6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 6 210726001901410981 = some 210726001901410981 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 4 2 210726001901410981 210726001901410981 210726001901410981 endpoint_15_71_p4 endpoint_15_71_w4
private theorem endpoint_15_71_w6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 6 2 210726001901410981 = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_p8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 8 210726001901410981 = some 210726001901410981 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 6 2 210726001901410981 210726001901410981 210726001901410981 endpoint_15_71_p6 endpoint_15_71_w6
private theorem endpoint_15_71_w8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 8 2 210726001901410981 = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_p10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 10 210726001901410981 = some 210726001901410981 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 8 2 210726001901410981 210726001901410981 210726001901410981 endpoint_15_71_p8 endpoint_15_71_w8
private theorem endpoint_15_71_w10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 10 2 210726001901410981 = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_p12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 12 210726001901410981 = some 210726001901410981 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 10 2 210726001901410981 210726001901410981 210726001901410981 endpoint_15_71_p10 endpoint_15_71_w10
private theorem endpoint_15_71_w12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 12 2 210726001901410981 = some 210726001901410981 := by decide +kernel
private theorem endpoint_15_71_p14 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 14 210726001901410981 = some 210726001901410981 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 12 2 210726001901410981 210726001901410981 210726001901410981 endpoint_15_71_p12 endpoint_15_71_w12
def endpoint_15_71 : CertifiedEndpoint :=
  ⟨⟨15, 71, 1689⟩, 210726001901410981, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_71_flag endpoint_15_71_sources 14 210726001901410981 210726001901410981 rfl endpoint_15_71_base endpoint_15_71_p14) (by decide)⟩
private def endpoint_15_72_flag : Flag := ⟨15, 72, 1597⟩
private def endpoint_15_72_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_72_base : receiptBase endpoint_15_72_flag endpoint_15_72_sources = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_w0 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 2 201845017463347988 = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_w2 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 2 2 201845017463347988 = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_p4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 4 201845017463347988 = some 201845017463347988 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 2 2 201845017463347988 201845017463347988 201845017463347988 endpoint_15_72_w0 endpoint_15_72_w2
private theorem endpoint_15_72_w4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 4 2 201845017463347988 = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_p6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 6 201845017463347988 = some 201845017463347988 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 4 2 201845017463347988 201845017463347988 201845017463347988 endpoint_15_72_p4 endpoint_15_72_w4
private theorem endpoint_15_72_w6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 6 2 201845017463347988 = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_p8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 8 201845017463347988 = some 201845017463347988 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 6 2 201845017463347988 201845017463347988 201845017463347988 endpoint_15_72_p6 endpoint_15_72_w6
private theorem endpoint_15_72_w8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 8 2 201845017463347988 = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_p10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 10 201845017463347988 = some 201845017463347988 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 8 2 201845017463347988 201845017463347988 201845017463347988 endpoint_15_72_p8 endpoint_15_72_w8
private theorem endpoint_15_72_w10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 10 2 201845017463347988 = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_p12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 12 201845017463347988 = some 201845017463347988 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 10 2 201845017463347988 201845017463347988 201845017463347988 endpoint_15_72_p10 endpoint_15_72_w10
private theorem endpoint_15_72_w12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 12 2 201845017463347988 = some 201845017463347988 := by decide +kernel
private theorem endpoint_15_72_p14 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 14 201845017463347988 = some 201845017463347988 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 12 2 201845017463347988 201845017463347988 201845017463347988 endpoint_15_72_p12 endpoint_15_72_w12
def endpoint_15_72 : CertifiedEndpoint :=
  ⟨⟨15, 72, 1597⟩, 201845017463347988, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_72_flag endpoint_15_72_sources 14 201845017463347988 201845017463347988 rfl endpoint_15_72_base endpoint_15_72_p14) (by decide)⟩
private def endpoint_15_73_flag : Flag := ⟨15, 73, 1502⟩
private def endpoint_15_73_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_15_73_base : receiptBase endpoint_15_73_flag endpoint_15_73_sources = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_w0 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 2 192655417039835927 = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_w2 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 2 2 192655417039835927 = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_p4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 4 192655417039835927 = some 192655417039835927 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 2 2 192655417039835927 192655417039835927 192655417039835927 endpoint_15_73_w0 endpoint_15_73_w2
private theorem endpoint_15_73_w4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 4 2 192655417039835927 = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_p6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 6 192655417039835927 = some 192655417039835927 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 4 2 192655417039835927 192655417039835927 192655417039835927 endpoint_15_73_p4 endpoint_15_73_w4
private theorem endpoint_15_73_w6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 6 2 192655417039835927 = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_p8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 8 192655417039835927 = some 192655417039835927 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 6 2 192655417039835927 192655417039835927 192655417039835927 endpoint_15_73_p6 endpoint_15_73_w6
private theorem endpoint_15_73_w8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 8 2 192655417039835927 = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_p10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 10 192655417039835927 = some 192655417039835927 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 8 2 192655417039835927 192655417039835927 192655417039835927 endpoint_15_73_p8 endpoint_15_73_w8
private theorem endpoint_15_73_w10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 10 2 192655417039835927 = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_p12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 12 192655417039835927 = some 192655417039835927 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 10 2 192655417039835927 192655417039835927 192655417039835927 endpoint_15_73_p10 endpoint_15_73_w10
private theorem endpoint_15_73_w12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 12 2 192655417039835927 = some 192655417039835927 := by decide +kernel
private theorem endpoint_15_73_p14 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 14 192655417039835927 = some 192655417039835927 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 12 2 192655417039835927 192655417039835927 192655417039835927 endpoint_15_73_p12 endpoint_15_73_w12
def endpoint_15_73 : CertifiedEndpoint :=
  ⟨⟨15, 73, 1502⟩, 192655417039835927, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_15_73_flag endpoint_15_73_sources 14 192655417039835927 192655417039835927 rfl endpoint_15_73_base endpoint_15_73_p14) (by decide)⟩
private def endpoint_15_74_flag : Flag := ⟨15, 74, 1404⟩
private def endpoint_15_74_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_15_74_base : receiptBase endpoint_15_74_flag endpoint_15_74_sources = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_w0 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 2 183616787188799770 = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_w2 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 2 2 183616787188799770 = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_p4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 4 183616787188799770 = some 183616787188799770 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 2 2 183616787188799770 183616787188799770 183616787188799770 endpoint_15_74_w0 endpoint_15_74_w2
private theorem endpoint_15_74_w4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 4 2 183616787188799770 = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_p6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 6 183616787188799770 = some 183616787188799770 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 4 2 183616787188799770 183616787188799770 183616787188799770 endpoint_15_74_p4 endpoint_15_74_w4
private theorem endpoint_15_74_w6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 6 2 183616787188799770 = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_p8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 8 183616787188799770 = some 183616787188799770 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 6 2 183616787188799770 183616787188799770 183616787188799770 endpoint_15_74_p6 endpoint_15_74_w6
private theorem endpoint_15_74_w8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 8 2 183616787188799770 = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_p10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 10 183616787188799770 = some 183616787188799770 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 8 2 183616787188799770 183616787188799770 183616787188799770 endpoint_15_74_p8 endpoint_15_74_w8
private theorem endpoint_15_74_w10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 10 2 183616787188799770 = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_p12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 12 183616787188799770 = some 183616787188799770 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 10 2 183616787188799770 183616787188799770 183616787188799770 endpoint_15_74_p10 endpoint_15_74_w10
private theorem endpoint_15_74_w12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 12 2 183616787188799770 = some 183616787188799770 := by decide +kernel
private theorem endpoint_15_74_p14 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 14 183616787188799770 = some 183616787188799770 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 12 2 183616787188799770 183616787188799770 183616787188799770 endpoint_15_74_p12 endpoint_15_74_w12
def endpoint_15_74 : CertifiedEndpoint :=
  ⟨⟨15, 74, 1404⟩, 183616787188799770, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_15_74_flag endpoint_15_74_sources 14 183616787188799770 183616787188799770 rfl endpoint_15_74_base endpoint_15_74_p14) (by decide)⟩
private def endpoint_15_75_flag : Flag := ⟨15, 75, 1303⟩
private def endpoint_15_75_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_75_base : receiptBase endpoint_15_75_flag endpoint_15_75_sources = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_w0 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 2 174116897494047386 = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_w2 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 2 2 174116897494047386 = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_p4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 4 174116897494047386 = some 174116897494047386 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 2 2 174116897494047386 174116897494047386 174116897494047386 endpoint_15_75_w0 endpoint_15_75_w2
private theorem endpoint_15_75_w4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 4 2 174116897494047386 = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_p6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 6 174116897494047386 = some 174116897494047386 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 4 2 174116897494047386 174116897494047386 174116897494047386 endpoint_15_75_p4 endpoint_15_75_w4
private theorem endpoint_15_75_w6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 6 2 174116897494047386 = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_p8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 8 174116897494047386 = some 174116897494047386 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 6 2 174116897494047386 174116897494047386 174116897494047386 endpoint_15_75_p6 endpoint_15_75_w6
private theorem endpoint_15_75_w8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 8 2 174116897494047386 = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_p10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 10 174116897494047386 = some 174116897494047386 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 8 2 174116897494047386 174116897494047386 174116897494047386 endpoint_15_75_p8 endpoint_15_75_w8
private theorem endpoint_15_75_w10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 10 2 174116897494047386 = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_p12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 12 174116897494047386 = some 174116897494047386 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 10 2 174116897494047386 174116897494047386 174116897494047386 endpoint_15_75_p10 endpoint_15_75_w10
private theorem endpoint_15_75_w12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 12 2 174116897494047386 = some 174116897494047386 := by decide +kernel
private theorem endpoint_15_75_p14 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 14 174116897494047386 = some 174116897494047386 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 12 2 174116897494047386 174116897494047386 174116897494047386 endpoint_15_75_p12 endpoint_15_75_w12
def endpoint_15_75 : CertifiedEndpoint :=
  ⟨⟨15, 75, 1303⟩, 174116897494047386, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_75_flag endpoint_15_75_sources 14 174116897494047386 174116897494047386 rfl endpoint_15_75_base endpoint_15_75_p14) (by decide)⟩
private def endpoint_15_76_flag : Flag := ⟨15, 76, 1200⟩
private def endpoint_15_76_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_76_base : receiptBase endpoint_15_76_flag endpoint_15_76_sources = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_w0 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 2 162395626150751610 = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_w2 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 2 2 162395626150751610 = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_p4 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 4 162395626150751610 = some 162395626150751610 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 2 2 162395626150751610 162395626150751610 162395626150751610 endpoint_15_76_w0 endpoint_15_76_w2
private theorem endpoint_15_76_w4 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 4 2 162395626150751610 = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_p6 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 6 162395626150751610 = some 162395626150751610 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 4 2 162395626150751610 162395626150751610 162395626150751610 endpoint_15_76_p4 endpoint_15_76_w4
private theorem endpoint_15_76_w6 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 6 2 162395626150751610 = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_p8 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 8 162395626150751610 = some 162395626150751610 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 6 2 162395626150751610 162395626150751610 162395626150751610 endpoint_15_76_p6 endpoint_15_76_w6
private theorem endpoint_15_76_w8 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 8 2 162395626150751610 = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_p10 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 10 162395626150751610 = some 162395626150751610 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 8 2 162395626150751610 162395626150751610 162395626150751610 endpoint_15_76_p8 endpoint_15_76_w8
private theorem endpoint_15_76_w10 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 10 2 162395626150751610 = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_p12 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 12 162395626150751610 = some 162395626150751610 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 10 2 162395626150751610 162395626150751610 162395626150751610 endpoint_15_76_p10 endpoint_15_76_w10
private theorem endpoint_15_76_w12 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 12 2 162395626150751610 = some 162395626150751610 := by decide +kernel
private theorem endpoint_15_76_p14 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 14 162395626150751610 = some 162395626150751610 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 12 2 162395626150751610 162395626150751610 162395626150751610 endpoint_15_76_p12 endpoint_15_76_w12
def endpoint_15_76 : CertifiedEndpoint :=
  ⟨⟨15, 76, 1200⟩, 162395626150751610, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_76_flag endpoint_15_76_sources 14 162395626150751610 162395626150751610 rfl endpoint_15_76_base endpoint_15_76_p14) (by decide)⟩
private def endpoint_15_77_flag : Flag := ⟨15, 77, 1093⟩
private def endpoint_15_77_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_77_base : receiptBase endpoint_15_77_flag endpoint_15_77_sources = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_w0 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 2 149812134191483893 = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_w2 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 2 2 149812134191483893 = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_p4 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 4 149812134191483893 = some 149812134191483893 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 2 2 149812134191483893 149812134191483893 149812134191483893 endpoint_15_77_w0 endpoint_15_77_w2
private theorem endpoint_15_77_w4 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 4 2 149812134191483893 = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_p6 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 6 149812134191483893 = some 149812134191483893 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 4 2 149812134191483893 149812134191483893 149812134191483893 endpoint_15_77_p4 endpoint_15_77_w4
private theorem endpoint_15_77_w6 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 6 2 149812134191483893 = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_p8 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 8 149812134191483893 = some 149812134191483893 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 6 2 149812134191483893 149812134191483893 149812134191483893 endpoint_15_77_p6 endpoint_15_77_w6
private theorem endpoint_15_77_w8 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 8 2 149812134191483893 = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_p10 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 10 149812134191483893 = some 149812134191483893 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 8 2 149812134191483893 149812134191483893 149812134191483893 endpoint_15_77_p8 endpoint_15_77_w8
private theorem endpoint_15_77_w10 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 10 2 149812134191483893 = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_p12 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 12 149812134191483893 = some 149812134191483893 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 10 2 149812134191483893 149812134191483893 149812134191483893 endpoint_15_77_p10 endpoint_15_77_w10
private theorem endpoint_15_77_w12 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 12 2 149812134191483893 = some 149812134191483893 := by decide +kernel
private theorem endpoint_15_77_p14 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 14 149812134191483893 = some 149812134191483893 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 12 2 149812134191483893 149812134191483893 149812134191483893 endpoint_15_77_p12 endpoint_15_77_w12
def endpoint_15_77 : CertifiedEndpoint :=
  ⟨⟨15, 77, 1093⟩, 149812134191483893, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_77_flag endpoint_15_77_sources 14 149812134191483893 149812134191483893 rfl endpoint_15_77_base endpoint_15_77_p14) (by decide)⟩
def endpoint_15_78 : CertifiedEndpoint :=
  ⟨⟨15, 78, 983⟩, 246482372650914923, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_79 : CertifiedEndpoint :=
  ⟨⟨15, 79, 871⟩, 220086371177232956, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_80 : CertifiedEndpoint :=
  ⟨⟨15, 80, 755⟩, 191768993877578775, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_81 : CertifiedEndpoint :=
  ⟨⟨15, 81, 636⟩, 161758712969061771, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_82 : CertifiedEndpoint :=
  ⟨⟨15, 82, 515⟩, 130298981887490735, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_83 : CertifiedEndpoint :=
  ⟨⟨15, 83, 390⟩, 96805515839701985, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_84 : CertifiedEndpoint :=
  ⟨⟨15, 84, 262⟩, 61518022956829462, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_85 : CertifiedEndpoint :=
  ⟨⟨15, 85, 131⟩, 24402795496799516, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_16 : CertifiedEndpoint :=
  ⟨⟨16, 16, 4068⟩, 143625873982143364, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_17 : CertifiedEndpoint :=
  ⟨⟨16, 17, 4041⟩, 147957241421261806, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_18 : CertifiedEndpoint :=
  ⟨⟨16, 18, 4014⟩, 152217637040681782, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_19 : CertifiedEndpoint :=
  ⟨⟨16, 19, 3986⟩, 167034533096040143, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_20 : CertifiedEndpoint :=
  ⟨⟨16, 20, 3958⟩, 181623257638164690, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_21 : CertifiedEndpoint :=
  ⟨⟨16, 21, 3929⟩, 195933764419742534, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_22 : CertifiedEndpoint :=
  ⟨⟨16, 22, 3900⟩, 210008093670078360, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_23 : CertifiedEndpoint :=
  ⟨⟨16, 23, 3871⟩, 223846245389172168, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_24 : CertifiedEndpoint :=
  ⟨⟨16, 24, 3841⟩, 237386164302698763, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_25 : CertifiedEndpoint :=
  ⟨⟨16, 25, 3811⟩, 250681899666975136, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_26 : CertifiedEndpoint :=
  ⟨⟨16, 26, 3780⟩, 263663390189667888, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_16_27_flag : Flag := ⟨16, 27, 3748⟩
private def endpoint_16_27_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_27_base : receiptBase endpoint_16_27_flag endpoint_16_27_sources = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_w0 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 2 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_w2 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 2 2 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_p4 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 4 193477001620355952 = some 193477001620355952 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 2 2 193477001620355952 193477001620355952 193477001620355952 endpoint_16_27_w0 endpoint_16_27_w2
private theorem endpoint_16_27_w4 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 4 2 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_p6 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 6 193477001620355952 = some 193477001620355952 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 4 2 193477001620355952 193477001620355952 193477001620355952 endpoint_16_27_p4 endpoint_16_27_w4
private theorem endpoint_16_27_w6 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 6 2 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_p8 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 8 193477001620355952 = some 193477001620355952 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 6 2 193477001620355952 193477001620355952 193477001620355952 endpoint_16_27_p6 endpoint_16_27_w6
private theorem endpoint_16_27_w8 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 8 2 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_p10 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 10 193477001620355952 = some 193477001620355952 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 8 2 193477001620355952 193477001620355952 193477001620355952 endpoint_16_27_p8 endpoint_16_27_w8
private theorem endpoint_16_27_w10 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 10 2 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_p12 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 12 193477001620355952 = some 193477001620355952 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 10 2 193477001620355952 193477001620355952 193477001620355952 endpoint_16_27_p10 endpoint_16_27_w10
private theorem endpoint_16_27_w12 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 12 2 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_p14 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 14 193477001620355952 = some 193477001620355952 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 12 2 193477001620355952 193477001620355952 193477001620355952 endpoint_16_27_p12 endpoint_16_27_w12
private theorem endpoint_16_27_w14 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 14 1 193477001620355952 = some 193477001620355952 := by decide +kernel
private theorem endpoint_16_27_p15 : receiptWindow endpoint_16_27_flag endpoint_16_27_sources 0 15 193477001620355952 = some 193477001620355952 :=
  join_receipt_window endpoint_16_27_flag endpoint_16_27_sources 0 14 1 193477001620355952 193477001620355952 193477001620355952 endpoint_16_27_p14 endpoint_16_27_w14
def endpoint_16_27 : CertifiedEndpoint :=
  ⟨⟨16, 27, 3748⟩, 193477001620355952, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_27_flag endpoint_16_27_sources 15 193477001620355952 193477001620355952 rfl endpoint_16_27_base endpoint_16_27_p15) (by decide)⟩
private def endpoint_16_28_flag : Flag := ⟨16, 28, 3716⟩
private def endpoint_16_28_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_28_base : receiptBase endpoint_16_28_flag endpoint_16_28_sources = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_w0 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 2 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_w2 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 2 2 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_p4 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 4 197632132683238480 = some 197632132683238480 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 2 2 197632132683238480 197632132683238480 197632132683238480 endpoint_16_28_w0 endpoint_16_28_w2
private theorem endpoint_16_28_w4 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 4 2 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_p6 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 6 197632132683238480 = some 197632132683238480 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 4 2 197632132683238480 197632132683238480 197632132683238480 endpoint_16_28_p4 endpoint_16_28_w4
private theorem endpoint_16_28_w6 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 6 2 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_p8 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 8 197632132683238480 = some 197632132683238480 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 6 2 197632132683238480 197632132683238480 197632132683238480 endpoint_16_28_p6 endpoint_16_28_w6
private theorem endpoint_16_28_w8 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 8 2 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_p10 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 10 197632132683238480 = some 197632132683238480 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 8 2 197632132683238480 197632132683238480 197632132683238480 endpoint_16_28_p8 endpoint_16_28_w8
private theorem endpoint_16_28_w10 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 10 2 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_p12 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 12 197632132683238480 = some 197632132683238480 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 10 2 197632132683238480 197632132683238480 197632132683238480 endpoint_16_28_p10 endpoint_16_28_w10
private theorem endpoint_16_28_w12 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 12 2 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_p14 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 14 197632132683238480 = some 197632132683238480 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 12 2 197632132683238480 197632132683238480 197632132683238480 endpoint_16_28_p12 endpoint_16_28_w12
private theorem endpoint_16_28_w14 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 14 1 197632132683238480 = some 197632132683238480 := by decide +kernel
private theorem endpoint_16_28_p15 : receiptWindow endpoint_16_28_flag endpoint_16_28_sources 0 15 197632132683238480 = some 197632132683238480 :=
  join_receipt_window endpoint_16_28_flag endpoint_16_28_sources 0 14 1 197632132683238480 197632132683238480 197632132683238480 endpoint_16_28_p14 endpoint_16_28_w14
def endpoint_16_28 : CertifiedEndpoint :=
  ⟨⟨16, 28, 3716⟩, 197632132683238480, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_28_flag endpoint_16_28_sources 15 197632132683238480 197632132683238480 rfl endpoint_16_28_base endpoint_16_28_p15) (by decide)⟩
private def endpoint_16_29_flag : Flag := ⟨16, 29, 3684⟩
private def endpoint_16_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_29_base : receiptBase endpoint_16_29_flag endpoint_16_29_sources = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_w0 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 2 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_w2 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 2 2 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_p4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 4 201688168522737736 = some 201688168522737736 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 2 2 201688168522737736 201688168522737736 201688168522737736 endpoint_16_29_w0 endpoint_16_29_w2
private theorem endpoint_16_29_w4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 4 2 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_p6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 6 201688168522737736 = some 201688168522737736 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 4 2 201688168522737736 201688168522737736 201688168522737736 endpoint_16_29_p4 endpoint_16_29_w4
private theorem endpoint_16_29_w6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 6 2 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_p8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 8 201688168522737736 = some 201688168522737736 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 6 2 201688168522737736 201688168522737736 201688168522737736 endpoint_16_29_p6 endpoint_16_29_w6
private theorem endpoint_16_29_w8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 8 2 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_p10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 10 201688168522737736 = some 201688168522737736 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 8 2 201688168522737736 201688168522737736 201688168522737736 endpoint_16_29_p8 endpoint_16_29_w8
private theorem endpoint_16_29_w10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 10 2 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_p12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 12 201688168522737736 = some 201688168522737736 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 10 2 201688168522737736 201688168522737736 201688168522737736 endpoint_16_29_p10 endpoint_16_29_w10
private theorem endpoint_16_29_w12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 12 2 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_p14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 14 201688168522737736 = some 201688168522737736 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 12 2 201688168522737736 201688168522737736 201688168522737736 endpoint_16_29_p12 endpoint_16_29_w12
private theorem endpoint_16_29_w14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 14 1 201688168522737736 = some 201688168522737736 := by decide +kernel
private theorem endpoint_16_29_p15 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 15 201688168522737736 = some 201688168522737736 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 14 1 201688168522737736 201688168522737736 201688168522737736 endpoint_16_29_p14 endpoint_16_29_w14
def endpoint_16_29 : CertifiedEndpoint :=
  ⟨⟨16, 29, 3684⟩, 201688168522737736, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_29_flag endpoint_16_29_sources 15 201688168522737736 201688168522737736 rfl endpoint_16_29_base endpoint_16_29_p15) (by decide)⟩
private def endpoint_16_30_flag : Flag := ⟨16, 30, 3651⟩
private def endpoint_16_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_30_base : receiptBase endpoint_16_30_flag endpoint_16_30_sources = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_w0 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 2 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_w2 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 2 2 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_p4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 4 205589534251596010 = some 205589534251596010 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 2 2 205589534251596010 205589534251596010 205589534251596010 endpoint_16_30_w0 endpoint_16_30_w2
private theorem endpoint_16_30_w4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 4 2 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_p6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 6 205589534251596010 = some 205589534251596010 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 4 2 205589534251596010 205589534251596010 205589534251596010 endpoint_16_30_p4 endpoint_16_30_w4
private theorem endpoint_16_30_w6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 6 2 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_p8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 8 205589534251596010 = some 205589534251596010 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 6 2 205589534251596010 205589534251596010 205589534251596010 endpoint_16_30_p6 endpoint_16_30_w6
private theorem endpoint_16_30_w8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 8 2 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_p10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 10 205589534251596010 = some 205589534251596010 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 8 2 205589534251596010 205589534251596010 205589534251596010 endpoint_16_30_p8 endpoint_16_30_w8
private theorem endpoint_16_30_w10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 10 2 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_p12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 12 205589534251596010 = some 205589534251596010 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 10 2 205589534251596010 205589534251596010 205589534251596010 endpoint_16_30_p10 endpoint_16_30_w10
private theorem endpoint_16_30_w12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 12 2 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_p14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 14 205589534251596010 = some 205589534251596010 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 12 2 205589534251596010 205589534251596010 205589534251596010 endpoint_16_30_p12 endpoint_16_30_w12
private theorem endpoint_16_30_w14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 14 1 205589534251596010 = some 205589534251596010 := by decide +kernel
private theorem endpoint_16_30_p15 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 15 205589534251596010 = some 205589534251596010 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 14 1 205589534251596010 205589534251596010 205589534251596010 endpoint_16_30_p14 endpoint_16_30_w14
def endpoint_16_30 : CertifiedEndpoint :=
  ⟨⟨16, 30, 3651⟩, 205589534251596010, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_30_flag endpoint_16_30_sources 15 205589534251596010 205589534251596010 rfl endpoint_16_30_base endpoint_16_30_p15) (by decide)⟩
private def endpoint_16_31_flag : Flag := ⟨16, 31, 3617⟩
private def endpoint_16_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_31_base : receiptBase endpoint_16_31_flag endpoint_16_31_sources = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_w0 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 2 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_w2 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 2 2 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_p4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 4 209331657334407596 = some 209331657334407596 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 2 2 209331657334407596 209331657334407596 209331657334407596 endpoint_16_31_w0 endpoint_16_31_w2
private theorem endpoint_16_31_w4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 4 2 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_p6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 6 209331657334407596 = some 209331657334407596 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 4 2 209331657334407596 209331657334407596 209331657334407596 endpoint_16_31_p4 endpoint_16_31_w4
private theorem endpoint_16_31_w6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 6 2 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_p8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 8 209331657334407596 = some 209331657334407596 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 6 2 209331657334407596 209331657334407596 209331657334407596 endpoint_16_31_p6 endpoint_16_31_w6
private theorem endpoint_16_31_w8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 8 2 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_p10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 10 209331657334407596 = some 209331657334407596 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 8 2 209331657334407596 209331657334407596 209331657334407596 endpoint_16_31_p8 endpoint_16_31_w8
private theorem endpoint_16_31_w10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 10 2 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_p12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 12 209331657334407596 = some 209331657334407596 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 10 2 209331657334407596 209331657334407596 209331657334407596 endpoint_16_31_p10 endpoint_16_31_w10
private theorem endpoint_16_31_w12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 12 2 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_p14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 14 209331657334407596 = some 209331657334407596 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 12 2 209331657334407596 209331657334407596 209331657334407596 endpoint_16_31_p12 endpoint_16_31_w12
private theorem endpoint_16_31_w14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 14 1 209331657334407596 = some 209331657334407596 := by decide +kernel
private theorem endpoint_16_31_p15 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 15 209331657334407596 = some 209331657334407596 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 14 1 209331657334407596 209331657334407596 209331657334407596 endpoint_16_31_p14 endpoint_16_31_w14
def endpoint_16_31 : CertifiedEndpoint :=
  ⟨⟨16, 31, 3617⟩, 209331657334407596, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_31_flag endpoint_16_31_sources 15 209331657334407596 209331657334407596 rfl endpoint_16_31_base endpoint_16_31_p15) (by decide)⟩
private def endpoint_16_32_flag : Flag := ⟨16, 32, 3583⟩
private def endpoint_16_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_32_base : receiptBase endpoint_16_32_flag endpoint_16_32_sources = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_w0 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 2 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_w2 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 2 2 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_p4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 4 212968588479961637 = some 212968588479961637 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 2 2 212968588479961637 212968588479961637 212968588479961637 endpoint_16_32_w0 endpoint_16_32_w2
private theorem endpoint_16_32_w4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 4 2 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_p6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 6 212968588479961637 = some 212968588479961637 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 4 2 212968588479961637 212968588479961637 212968588479961637 endpoint_16_32_p4 endpoint_16_32_w4
private theorem endpoint_16_32_w6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 6 2 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_p8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 8 212968588479961637 = some 212968588479961637 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 6 2 212968588479961637 212968588479961637 212968588479961637 endpoint_16_32_p6 endpoint_16_32_w6
private theorem endpoint_16_32_w8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 8 2 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_p10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 10 212968588479961637 = some 212968588479961637 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 8 2 212968588479961637 212968588479961637 212968588479961637 endpoint_16_32_p8 endpoint_16_32_w8
private theorem endpoint_16_32_w10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 10 2 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_p12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 12 212968588479961637 = some 212968588479961637 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 10 2 212968588479961637 212968588479961637 212968588479961637 endpoint_16_32_p10 endpoint_16_32_w10
private theorem endpoint_16_32_w12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 12 2 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_p14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 14 212968588479961637 = some 212968588479961637 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 12 2 212968588479961637 212968588479961637 212968588479961637 endpoint_16_32_p12 endpoint_16_32_w12
private theorem endpoint_16_32_w14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 14 1 212968588479961637 = some 212968588479961637 := by decide +kernel
private theorem endpoint_16_32_p15 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 15 212968588479961637 = some 212968588479961637 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 14 1 212968588479961637 212968588479961637 212968588479961637 endpoint_16_32_p14 endpoint_16_32_w14
def endpoint_16_32 : CertifiedEndpoint :=
  ⟨⟨16, 32, 3583⟩, 212968588479961637, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_32_flag endpoint_16_32_sources 15 212968588479961637 212968588479961637 rfl endpoint_16_32_base endpoint_16_32_p15) (by decide)⟩
private def endpoint_16_33_flag : Flag := ⟨16, 33, 3548⟩
private def endpoint_16_33_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_16_33_base : receiptBase endpoint_16_33_flag endpoint_16_33_sources = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_w0 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 2 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_w2 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 2 2 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_p4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 4 218395396089819880 = some 218395396089819880 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 2 2 218395396089819880 218395396089819880 218395396089819880 endpoint_16_33_w0 endpoint_16_33_w2
private theorem endpoint_16_33_w4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 4 2 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_p6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 6 218395396089819880 = some 218395396089819880 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 4 2 218395396089819880 218395396089819880 218395396089819880 endpoint_16_33_p4 endpoint_16_33_w4
private theorem endpoint_16_33_w6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 6 2 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_p8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 8 218395396089819880 = some 218395396089819880 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 6 2 218395396089819880 218395396089819880 218395396089819880 endpoint_16_33_p6 endpoint_16_33_w6
private theorem endpoint_16_33_w8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 8 2 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_p10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 10 218395396089819880 = some 218395396089819880 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 8 2 218395396089819880 218395396089819880 218395396089819880 endpoint_16_33_p8 endpoint_16_33_w8
private theorem endpoint_16_33_w10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 10 2 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_p12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 12 218395396089819880 = some 218395396089819880 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 10 2 218395396089819880 218395396089819880 218395396089819880 endpoint_16_33_p10 endpoint_16_33_w10
private theorem endpoint_16_33_w12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 12 2 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_p14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 14 218395396089819880 = some 218395396089819880 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 12 2 218395396089819880 218395396089819880 218395396089819880 endpoint_16_33_p12 endpoint_16_33_w12
private theorem endpoint_16_33_w14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 14 1 218395396089819880 = some 218395396089819880 := by decide +kernel
private theorem endpoint_16_33_p15 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 15 218395396089819880 = some 218395396089819880 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 14 1 218395396089819880 218395396089819880 218395396089819880 endpoint_16_33_p14 endpoint_16_33_w14
def endpoint_16_33 : CertifiedEndpoint :=
  ⟨⟨16, 33, 3548⟩, 218395396089819880, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_16_33_flag endpoint_16_33_sources 15 218395396089819880 218395396089819880 rfl endpoint_16_33_base endpoint_16_33_p15) (by decide)⟩
private def endpoint_16_34_flag : Flag := ⟨16, 34, 3512⟩
private def endpoint_16_34_sources : Sources := ⟨contact25, contact03, contact25⟩
private theorem endpoint_16_34_base : receiptBase endpoint_16_34_flag endpoint_16_34_sources = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_w0 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 2 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_w2 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 2 2 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_p4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 4 221916910030467876 = some 221916910030467876 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 2 2 221916910030467876 221916910030467876 221916910030467876 endpoint_16_34_w0 endpoint_16_34_w2
private theorem endpoint_16_34_w4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 4 2 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_p6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 6 221916910030467876 = some 221916910030467876 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 4 2 221916910030467876 221916910030467876 221916910030467876 endpoint_16_34_p4 endpoint_16_34_w4
private theorem endpoint_16_34_w6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 6 2 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_p8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 8 221916910030467876 = some 221916910030467876 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 6 2 221916910030467876 221916910030467876 221916910030467876 endpoint_16_34_p6 endpoint_16_34_w6
private theorem endpoint_16_34_w8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 8 2 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_p10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 10 221916910030467876 = some 221916910030467876 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 8 2 221916910030467876 221916910030467876 221916910030467876 endpoint_16_34_p8 endpoint_16_34_w8
private theorem endpoint_16_34_w10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 10 2 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_p12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 12 221916910030467876 = some 221916910030467876 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 10 2 221916910030467876 221916910030467876 221916910030467876 endpoint_16_34_p10 endpoint_16_34_w10
private theorem endpoint_16_34_w12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 12 2 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_p14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 14 221916910030467876 = some 221916910030467876 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 12 2 221916910030467876 221916910030467876 221916910030467876 endpoint_16_34_p12 endpoint_16_34_w12
private theorem endpoint_16_34_w14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 14 1 221916910030467876 = some 221916910030467876 := by decide +kernel
private theorem endpoint_16_34_p15 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 15 221916910030467876 = some 221916910030467876 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 14 1 221916910030467876 221916910030467876 221916910030467876 endpoint_16_34_p14 endpoint_16_34_w14
def endpoint_16_34 : CertifiedEndpoint :=
  ⟨⟨16, 34, 3512⟩, 221916910030467876, .terminal ⟨contact25, contact03, contact25⟩ (finish_receipt_window endpoint_16_34_flag endpoint_16_34_sources 15 221916910030467876 221916910030467876 rfl endpoint_16_34_base endpoint_16_34_p15) (by decide)⟩
private def endpoint_16_35_flag : Flag := ⟨16, 35, 3476⟩
private def endpoint_16_35_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_35_base : receiptBase endpoint_16_35_flag endpoint_16_35_sources = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_w0 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 2 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_w2 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 2 2 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_p4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 4 226874170834536133 = some 226874170834536133 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 2 2 226874170834536133 226874170834536133 226874170834536133 endpoint_16_35_w0 endpoint_16_35_w2
private theorem endpoint_16_35_w4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 4 2 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_p6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 6 226874170834536133 = some 226874170834536133 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 4 2 226874170834536133 226874170834536133 226874170834536133 endpoint_16_35_p4 endpoint_16_35_w4
private theorem endpoint_16_35_w6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 6 2 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_p8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 8 226874170834536133 = some 226874170834536133 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 6 2 226874170834536133 226874170834536133 226874170834536133 endpoint_16_35_p6 endpoint_16_35_w6
private theorem endpoint_16_35_w8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 8 2 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_p10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 10 226874170834536133 = some 226874170834536133 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 8 2 226874170834536133 226874170834536133 226874170834536133 endpoint_16_35_p8 endpoint_16_35_w8
private theorem endpoint_16_35_w10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 10 2 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_p12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 12 226874170834536133 = some 226874170834536133 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 10 2 226874170834536133 226874170834536133 226874170834536133 endpoint_16_35_p10 endpoint_16_35_w10
private theorem endpoint_16_35_w12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 12 2 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_p14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 14 226874170834536133 = some 226874170834536133 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 12 2 226874170834536133 226874170834536133 226874170834536133 endpoint_16_35_p12 endpoint_16_35_w12
private theorem endpoint_16_35_w14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 14 1 226874170834536133 = some 226874170834536133 := by decide +kernel
private theorem endpoint_16_35_p15 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 15 226874170834536133 = some 226874170834536133 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 14 1 226874170834536133 226874170834536133 226874170834536133 endpoint_16_35_p14 endpoint_16_35_w14
def endpoint_16_35 : CertifiedEndpoint :=
  ⟨⟨16, 35, 3476⟩, 226874170834536133, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_35_flag endpoint_16_35_sources 15 226874170834536133 226874170834536133 rfl endpoint_16_35_base endpoint_16_35_p15) (by decide)⟩
private def endpoint_16_36_flag : Flag := ⟨16, 36, 3438⟩
private def endpoint_16_36_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_36_base : receiptBase endpoint_16_36_flag endpoint_16_36_sources = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_w0 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 2 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_w2 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 2 2 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_p4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 4 229705210991078932 = some 229705210991078932 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 2 2 229705210991078932 229705210991078932 229705210991078932 endpoint_16_36_w0 endpoint_16_36_w2
private theorem endpoint_16_36_w4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 4 2 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_p6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 6 229705210991078932 = some 229705210991078932 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 4 2 229705210991078932 229705210991078932 229705210991078932 endpoint_16_36_p4 endpoint_16_36_w4
private theorem endpoint_16_36_w6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 6 2 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_p8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 8 229705210991078932 = some 229705210991078932 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 6 2 229705210991078932 229705210991078932 229705210991078932 endpoint_16_36_p6 endpoint_16_36_w6
private theorem endpoint_16_36_w8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 8 2 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_p10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 10 229705210991078932 = some 229705210991078932 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 8 2 229705210991078932 229705210991078932 229705210991078932 endpoint_16_36_p8 endpoint_16_36_w8
private theorem endpoint_16_36_w10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 10 2 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_p12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 12 229705210991078932 = some 229705210991078932 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 10 2 229705210991078932 229705210991078932 229705210991078932 endpoint_16_36_p10 endpoint_16_36_w10
private theorem endpoint_16_36_w12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 12 2 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_p14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 14 229705210991078932 = some 229705210991078932 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 12 2 229705210991078932 229705210991078932 229705210991078932 endpoint_16_36_p12 endpoint_16_36_w12
private theorem endpoint_16_36_w14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 14 1 229705210991078932 = some 229705210991078932 := by decide +kernel
private theorem endpoint_16_36_p15 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 15 229705210991078932 = some 229705210991078932 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 14 1 229705210991078932 229705210991078932 229705210991078932 endpoint_16_36_p14 endpoint_16_36_w14
def endpoint_16_36 : CertifiedEndpoint :=
  ⟨⟨16, 36, 3438⟩, 229705210991078932, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_36_flag endpoint_16_36_sources 15 229705210991078932 229705210991078932 rfl endpoint_16_36_base endpoint_16_36_p15) (by decide)⟩
private def endpoint_16_37_flag : Flag := ⟨16, 37, 3400⟩
private def endpoint_16_37_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_37_base : receiptBase endpoint_16_37_flag endpoint_16_37_sources = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_w0 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 2 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_w2 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 2 2 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_p4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 4 232420016308926723 = some 232420016308926723 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 2 2 232420016308926723 232420016308926723 232420016308926723 endpoint_16_37_w0 endpoint_16_37_w2
private theorem endpoint_16_37_w4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 4 2 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_p6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 6 232420016308926723 = some 232420016308926723 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 4 2 232420016308926723 232420016308926723 232420016308926723 endpoint_16_37_p4 endpoint_16_37_w4
private theorem endpoint_16_37_w6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 6 2 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_p8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 8 232420016308926723 = some 232420016308926723 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 6 2 232420016308926723 232420016308926723 232420016308926723 endpoint_16_37_p6 endpoint_16_37_w6
private theorem endpoint_16_37_w8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 8 2 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_p10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 10 232420016308926723 = some 232420016308926723 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 8 2 232420016308926723 232420016308926723 232420016308926723 endpoint_16_37_p8 endpoint_16_37_w8
private theorem endpoint_16_37_w10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 10 2 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_p12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 12 232420016308926723 = some 232420016308926723 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 10 2 232420016308926723 232420016308926723 232420016308926723 endpoint_16_37_p10 endpoint_16_37_w10
private theorem endpoint_16_37_w12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 12 2 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_p14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 14 232420016308926723 = some 232420016308926723 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 12 2 232420016308926723 232420016308926723 232420016308926723 endpoint_16_37_p12 endpoint_16_37_w12
private theorem endpoint_16_37_w14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 14 1 232420016308926723 = some 232420016308926723 := by decide +kernel
private theorem endpoint_16_37_p15 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 15 232420016308926723 = some 232420016308926723 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 14 1 232420016308926723 232420016308926723 232420016308926723 endpoint_16_37_p14 endpoint_16_37_w14
def endpoint_16_37 : CertifiedEndpoint :=
  ⟨⟨16, 37, 3400⟩, 232420016308926723, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_37_flag endpoint_16_37_sources 15 232420016308926723 232420016308926723 rfl endpoint_16_37_base endpoint_16_37_p15) (by decide)⟩
private def endpoint_16_38_flag : Flag := ⟨16, 38, 3362⟩
private def endpoint_16_38_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_38_base : receiptBase endpoint_16_38_flag endpoint_16_38_sources = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_w0 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 2 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_w2 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 2 2 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_p4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 4 235018586788079504 = some 235018586788079504 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 2 2 235018586788079504 235018586788079504 235018586788079504 endpoint_16_38_w0 endpoint_16_38_w2
private theorem endpoint_16_38_w4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 4 2 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_p6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 6 235018586788079504 = some 235018586788079504 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 4 2 235018586788079504 235018586788079504 235018586788079504 endpoint_16_38_p4 endpoint_16_38_w4
private theorem endpoint_16_38_w6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 6 2 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_p8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 8 235018586788079504 = some 235018586788079504 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 6 2 235018586788079504 235018586788079504 235018586788079504 endpoint_16_38_p6 endpoint_16_38_w6
private theorem endpoint_16_38_w8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 8 2 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_p10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 10 235018586788079504 = some 235018586788079504 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 8 2 235018586788079504 235018586788079504 235018586788079504 endpoint_16_38_p8 endpoint_16_38_w8
private theorem endpoint_16_38_w10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 10 2 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_p12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 12 235018586788079504 = some 235018586788079504 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 10 2 235018586788079504 235018586788079504 235018586788079504 endpoint_16_38_p10 endpoint_16_38_w10
private theorem endpoint_16_38_w12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 12 2 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_p14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 14 235018586788079504 = some 235018586788079504 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 12 2 235018586788079504 235018586788079504 235018586788079504 endpoint_16_38_p12 endpoint_16_38_w12
private theorem endpoint_16_38_w14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 14 1 235018586788079504 = some 235018586788079504 := by decide +kernel
private theorem endpoint_16_38_p15 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 15 235018586788079504 = some 235018586788079504 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 14 1 235018586788079504 235018586788079504 235018586788079504 endpoint_16_38_p14 endpoint_16_38_w14
def endpoint_16_38 : CertifiedEndpoint :=
  ⟨⟨16, 38, 3362⟩, 235018586788079504, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_38_flag endpoint_16_38_sources 15 235018586788079504 235018586788079504 rfl endpoint_16_38_base endpoint_16_38_p15) (by decide)⟩
private def endpoint_16_39_flag : Flag := ⟨16, 39, 3322⟩
private def endpoint_16_39_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_39_base : receiptBase endpoint_16_39_flag endpoint_16_39_sources = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_w0 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 2 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_w2 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 2 2 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_p4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 4 237933192668569722 = some 237933192668569722 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 2 2 237933192668569722 237933192668569722 237933192668569722 endpoint_16_39_w0 endpoint_16_39_w2
private theorem endpoint_16_39_w4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 4 2 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_p6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 6 237933192668569722 = some 237933192668569722 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 4 2 237933192668569722 237933192668569722 237933192668569722 endpoint_16_39_p4 endpoint_16_39_w4
private theorem endpoint_16_39_w6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 6 2 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_p8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 8 237933192668569722 = some 237933192668569722 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 6 2 237933192668569722 237933192668569722 237933192668569722 endpoint_16_39_p6 endpoint_16_39_w6
private theorem endpoint_16_39_w8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 8 2 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_p10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 10 237933192668569722 = some 237933192668569722 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 8 2 237933192668569722 237933192668569722 237933192668569722 endpoint_16_39_p8 endpoint_16_39_w8
private theorem endpoint_16_39_w10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 10 2 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_p12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 12 237933192668569722 = some 237933192668569722 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 10 2 237933192668569722 237933192668569722 237933192668569722 endpoint_16_39_p10 endpoint_16_39_w10
private theorem endpoint_16_39_w12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 12 2 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_p14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 14 237933192668569722 = some 237933192668569722 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 12 2 237933192668569722 237933192668569722 237933192668569722 endpoint_16_39_p12 endpoint_16_39_w12
private theorem endpoint_16_39_w14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 14 1 237933192668569722 = some 237933192668569722 := by decide +kernel
private theorem endpoint_16_39_p15 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 15 237933192668569722 = some 237933192668569722 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 14 1 237933192668569722 237933192668569722 237933192668569722 endpoint_16_39_p14 endpoint_16_39_w14
def endpoint_16_39 : CertifiedEndpoint :=
  ⟨⟨16, 39, 3322⟩, 237933192668569722, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_39_flag endpoint_16_39_sources 15 237933192668569722 237933192668569722 rfl endpoint_16_39_base endpoint_16_39_p15) (by decide)⟩
private def endpoint_16_40_flag : Flag := ⟨16, 40, 3282⟩
private def endpoint_16_40_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_40_base : receiptBase endpoint_16_40_flag endpoint_16_40_sources = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_w0 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 2 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_w2 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 2 2 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_p4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 4 240168826703083382 = some 240168826703083382 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 2 2 240168826703083382 240168826703083382 240168826703083382 endpoint_16_40_w0 endpoint_16_40_w2
private theorem endpoint_16_40_w4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 4 2 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_p6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 6 240168826703083382 = some 240168826703083382 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 4 2 240168826703083382 240168826703083382 240168826703083382 endpoint_16_40_p4 endpoint_16_40_w4
private theorem endpoint_16_40_w6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 6 2 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_p8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 8 240168826703083382 = some 240168826703083382 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 6 2 240168826703083382 240168826703083382 240168826703083382 endpoint_16_40_p6 endpoint_16_40_w6
private theorem endpoint_16_40_w8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 8 2 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_p10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 10 240168826703083382 = some 240168826703083382 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 8 2 240168826703083382 240168826703083382 240168826703083382 endpoint_16_40_p8 endpoint_16_40_w8
private theorem endpoint_16_40_w10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 10 2 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_p12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 12 240168826703083382 = some 240168826703083382 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 10 2 240168826703083382 240168826703083382 240168826703083382 endpoint_16_40_p10 endpoint_16_40_w10
private theorem endpoint_16_40_w12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 12 2 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_p14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 14 240168826703083382 = some 240168826703083382 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 12 2 240168826703083382 240168826703083382 240168826703083382 endpoint_16_40_p12 endpoint_16_40_w12
private theorem endpoint_16_40_w14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 14 1 240168826703083382 = some 240168826703083382 := by decide +kernel
private theorem endpoint_16_40_p15 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 15 240168826703083382 = some 240168826703083382 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 14 1 240168826703083382 240168826703083382 240168826703083382 endpoint_16_40_p14 endpoint_16_40_w14
def endpoint_16_40 : CertifiedEndpoint :=
  ⟨⟨16, 40, 3282⟩, 240168826703083382, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_40_flag endpoint_16_40_sources 15 240168826703083382 240168826703083382 rfl endpoint_16_40_base endpoint_16_40_p15) (by decide)⟩
private def endpoint_16_41_flag : Flag := ⟨16, 41, 3240⟩
private def endpoint_16_41_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_41_base : receiptBase endpoint_16_41_flag endpoint_16_41_sources = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_w0 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 2 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_w2 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 2 2 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_p4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 4 242133906370531918 = some 242133906370531918 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 2 2 242133906370531918 242133906370531918 242133906370531918 endpoint_16_41_w0 endpoint_16_41_w2
private theorem endpoint_16_41_w4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 4 2 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_p6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 6 242133906370531918 = some 242133906370531918 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 4 2 242133906370531918 242133906370531918 242133906370531918 endpoint_16_41_p4 endpoint_16_41_w4
private theorem endpoint_16_41_w6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 6 2 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_p8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 8 242133906370531918 = some 242133906370531918 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 6 2 242133906370531918 242133906370531918 242133906370531918 endpoint_16_41_p6 endpoint_16_41_w6
private theorem endpoint_16_41_w8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 8 2 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_p10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 10 242133906370531918 = some 242133906370531918 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 8 2 242133906370531918 242133906370531918 242133906370531918 endpoint_16_41_p8 endpoint_16_41_w8
private theorem endpoint_16_41_w10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 10 2 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_p12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 12 242133906370531918 = some 242133906370531918 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 10 2 242133906370531918 242133906370531918 242133906370531918 endpoint_16_41_p10 endpoint_16_41_w10
private theorem endpoint_16_41_w12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 12 2 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_p14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 14 242133906370531918 = some 242133906370531918 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 12 2 242133906370531918 242133906370531918 242133906370531918 endpoint_16_41_p12 endpoint_16_41_w12
private theorem endpoint_16_41_w14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 14 1 242133906370531918 = some 242133906370531918 := by decide +kernel
private theorem endpoint_16_41_p15 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 15 242133906370531918 = some 242133906370531918 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 14 1 242133906370531918 242133906370531918 242133906370531918 endpoint_16_41_p14 endpoint_16_41_w14
def endpoint_16_41 : CertifiedEndpoint :=
  ⟨⟨16, 41, 3240⟩, 242133906370531918, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_41_flag endpoint_16_41_sources 15 242133906370531918 242133906370531918 rfl endpoint_16_41_base endpoint_16_41_p15) (by decide)⟩
private def endpoint_16_42_flag : Flag := ⟨16, 42, 3198⟩
private def endpoint_16_42_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_42_base : receiptBase endpoint_16_42_flag endpoint_16_42_sources = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_w0 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 2 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_w2 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 2 2 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_p4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 4 243969909790439185 = some 243969909790439185 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 2 2 243969909790439185 243969909790439185 243969909790439185 endpoint_16_42_w0 endpoint_16_42_w2
private theorem endpoint_16_42_w4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 4 2 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_p6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 6 243969909790439185 = some 243969909790439185 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 4 2 243969909790439185 243969909790439185 243969909790439185 endpoint_16_42_p4 endpoint_16_42_w4
private theorem endpoint_16_42_w6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 6 2 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_p8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 8 243969909790439185 = some 243969909790439185 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 6 2 243969909790439185 243969909790439185 243969909790439185 endpoint_16_42_p6 endpoint_16_42_w6
private theorem endpoint_16_42_w8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 8 2 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_p10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 10 243969909790439185 = some 243969909790439185 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 8 2 243969909790439185 243969909790439185 243969909790439185 endpoint_16_42_p8 endpoint_16_42_w8
private theorem endpoint_16_42_w10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 10 2 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_p12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 12 243969909790439185 = some 243969909790439185 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 10 2 243969909790439185 243969909790439185 243969909790439185 endpoint_16_42_p10 endpoint_16_42_w10
private theorem endpoint_16_42_w12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 12 2 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_p14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 14 243969909790439185 = some 243969909790439185 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 12 2 243969909790439185 243969909790439185 243969909790439185 endpoint_16_42_p12 endpoint_16_42_w12
private theorem endpoint_16_42_w14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 14 1 243969909790439185 = some 243969909790439185 := by decide +kernel
private theorem endpoint_16_42_p15 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 15 243969909790439185 = some 243969909790439185 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 14 1 243969909790439185 243969909790439185 243969909790439185 endpoint_16_42_p14 endpoint_16_42_w14
def endpoint_16_42 : CertifiedEndpoint :=
  ⟨⟨16, 42, 3198⟩, 243969909790439185, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_42_flag endpoint_16_42_sources 15 243969909790439185 243969909790439185 rfl endpoint_16_42_base endpoint_16_42_p15) (by decide)⟩
private def endpoint_16_43_flag : Flag := ⟨16, 43, 3155⟩
private def endpoint_16_43_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_43_base : receiptBase endpoint_16_43_flag endpoint_16_43_sources = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_w0 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 2 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_w2 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 2 2 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_p4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 4 246273618242195825 = some 246273618242195825 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 2 2 246273618242195825 246273618242195825 246273618242195825 endpoint_16_43_w0 endpoint_16_43_w2
private theorem endpoint_16_43_w4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 4 2 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_p6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 6 246273618242195825 = some 246273618242195825 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 4 2 246273618242195825 246273618242195825 246273618242195825 endpoint_16_43_p4 endpoint_16_43_w4
private theorem endpoint_16_43_w6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 6 2 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_p8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 8 246273618242195825 = some 246273618242195825 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 6 2 246273618242195825 246273618242195825 246273618242195825 endpoint_16_43_p6 endpoint_16_43_w6
private theorem endpoint_16_43_w8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 8 2 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_p10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 10 246273618242195825 = some 246273618242195825 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 8 2 246273618242195825 246273618242195825 246273618242195825 endpoint_16_43_p8 endpoint_16_43_w8
private theorem endpoint_16_43_w10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 10 2 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_p12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 12 246273618242195825 = some 246273618242195825 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 10 2 246273618242195825 246273618242195825 246273618242195825 endpoint_16_43_p10 endpoint_16_43_w10
private theorem endpoint_16_43_w12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 12 2 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_p14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 14 246273618242195825 = some 246273618242195825 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 12 2 246273618242195825 246273618242195825 246273618242195825 endpoint_16_43_p12 endpoint_16_43_w12
private theorem endpoint_16_43_w14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 14 1 246273618242195825 = some 246273618242195825 := by decide +kernel
private theorem endpoint_16_43_p15 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 15 246273618242195825 = some 246273618242195825 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 14 1 246273618242195825 246273618242195825 246273618242195825 endpoint_16_43_p14 endpoint_16_43_w14
def endpoint_16_43 : CertifiedEndpoint :=
  ⟨⟨16, 43, 3155⟩, 246273618242195825, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_43_flag endpoint_16_43_sources 15 246273618242195825 246273618242195825 rfl endpoint_16_43_base endpoint_16_43_p15) (by decide)⟩
private def endpoint_16_44_flag : Flag := ⟨16, 44, 3111⟩
private def endpoint_16_44_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_44_base : receiptBase endpoint_16_44_flag endpoint_16_44_sources = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_w0 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 2 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_w2 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 2 2 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_p4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 4 247707467227591189 = some 247707467227591189 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 2 2 247707467227591189 247707467227591189 247707467227591189 endpoint_16_44_w0 endpoint_16_44_w2
private theorem endpoint_16_44_w4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 4 2 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_p6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 6 247707467227591189 = some 247707467227591189 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 4 2 247707467227591189 247707467227591189 247707467227591189 endpoint_16_44_p4 endpoint_16_44_w4
private theorem endpoint_16_44_w6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 6 2 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_p8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 8 247707467227591189 = some 247707467227591189 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 6 2 247707467227591189 247707467227591189 247707467227591189 endpoint_16_44_p6 endpoint_16_44_w6
private theorem endpoint_16_44_w8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 8 2 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_p10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 10 247707467227591189 = some 247707467227591189 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 8 2 247707467227591189 247707467227591189 247707467227591189 endpoint_16_44_p8 endpoint_16_44_w8
private theorem endpoint_16_44_w10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 10 2 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_p12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 12 247707467227591189 = some 247707467227591189 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 10 2 247707467227591189 247707467227591189 247707467227591189 endpoint_16_44_p10 endpoint_16_44_w10
private theorem endpoint_16_44_w12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 12 2 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_p14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 14 247707467227591189 = some 247707467227591189 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 12 2 247707467227591189 247707467227591189 247707467227591189 endpoint_16_44_p12 endpoint_16_44_w12
private theorem endpoint_16_44_w14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 14 1 247707467227591189 = some 247707467227591189 := by decide +kernel
private theorem endpoint_16_44_p15 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 15 247707467227591189 = some 247707467227591189 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 14 1 247707467227591189 247707467227591189 247707467227591189 endpoint_16_44_p14 endpoint_16_44_w14
def endpoint_16_44 : CertifiedEndpoint :=
  ⟨⟨16, 44, 3111⟩, 247707467227591189, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_44_flag endpoint_16_44_sources 15 247707467227591189 247707467227591189 rfl endpoint_16_44_base endpoint_16_44_p15) (by decide)⟩
private def endpoint_16_45_flag : Flag := ⟨16, 45, 3066⟩
private def endpoint_16_45_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_45_base : receiptBase endpoint_16_45_flag endpoint_16_45_sources = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_w0 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 2 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_w2 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 2 2 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_p4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 4 248925256651124824 = some 248925256651124824 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 2 2 248925256651124824 248925256651124824 248925256651124824 endpoint_16_45_w0 endpoint_16_45_w2
private theorem endpoint_16_45_w4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 4 2 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_p6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 6 248925256651124824 = some 248925256651124824 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 4 2 248925256651124824 248925256651124824 248925256651124824 endpoint_16_45_p4 endpoint_16_45_w4
private theorem endpoint_16_45_w6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 6 2 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_p8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 8 248925256651124824 = some 248925256651124824 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 6 2 248925256651124824 248925256651124824 248925256651124824 endpoint_16_45_p6 endpoint_16_45_w6
private theorem endpoint_16_45_w8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 8 2 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_p10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 10 248925256651124824 = some 248925256651124824 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 8 2 248925256651124824 248925256651124824 248925256651124824 endpoint_16_45_p8 endpoint_16_45_w8
private theorem endpoint_16_45_w10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 10 2 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_p12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 12 248925256651124824 = some 248925256651124824 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 10 2 248925256651124824 248925256651124824 248925256651124824 endpoint_16_45_p10 endpoint_16_45_w10
private theorem endpoint_16_45_w12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 12 2 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_p14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 14 248925256651124824 = some 248925256651124824 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 12 2 248925256651124824 248925256651124824 248925256651124824 endpoint_16_45_p12 endpoint_16_45_w12
private theorem endpoint_16_45_w14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 14 1 248925256651124824 = some 248925256651124824 := by decide +kernel
private theorem endpoint_16_45_p15 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 15 248925256651124824 = some 248925256651124824 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 14 1 248925256651124824 248925256651124824 248925256651124824 endpoint_16_45_p14 endpoint_16_45_w14
def endpoint_16_45 : CertifiedEndpoint :=
  ⟨⟨16, 45, 3066⟩, 248925256651124824, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_45_flag endpoint_16_45_sources 15 248925256651124824 248925256651124824 rfl endpoint_16_45_base endpoint_16_45_p15) (by decide)⟩
private def endpoint_16_46_flag : Flag := ⟨16, 46, 3019⟩
private def endpoint_16_46_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_46_base : receiptBase endpoint_16_46_flag endpoint_16_46_sources = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_w0 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 2 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_w2 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 2 2 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_p4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 4 250538728366604545 = some 250538728366604545 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 2 2 250538728366604545 250538728366604545 250538728366604545 endpoint_16_46_w0 endpoint_16_46_w2
private theorem endpoint_16_46_w4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 4 2 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_p6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 6 250538728366604545 = some 250538728366604545 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 4 2 250538728366604545 250538728366604545 250538728366604545 endpoint_16_46_p4 endpoint_16_46_w4
private theorem endpoint_16_46_w6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 6 2 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_p8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 8 250538728366604545 = some 250538728366604545 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 6 2 250538728366604545 250538728366604545 250538728366604545 endpoint_16_46_p6 endpoint_16_46_w6
private theorem endpoint_16_46_w8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 8 2 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_p10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 10 250538728366604545 = some 250538728366604545 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 8 2 250538728366604545 250538728366604545 250538728366604545 endpoint_16_46_p8 endpoint_16_46_w8
private theorem endpoint_16_46_w10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 10 2 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_p12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 12 250538728366604545 = some 250538728366604545 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 10 2 250538728366604545 250538728366604545 250538728366604545 endpoint_16_46_p10 endpoint_16_46_w10
private theorem endpoint_16_46_w12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 12 2 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_p14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 14 250538728366604545 = some 250538728366604545 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 12 2 250538728366604545 250538728366604545 250538728366604545 endpoint_16_46_p12 endpoint_16_46_w12
private theorem endpoint_16_46_w14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 14 1 250538728366604545 = some 250538728366604545 := by decide +kernel
private theorem endpoint_16_46_p15 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 15 250538728366604545 = some 250538728366604545 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 14 1 250538728366604545 250538728366604545 250538728366604545 endpoint_16_46_p14 endpoint_16_46_w14
def endpoint_16_46 : CertifiedEndpoint :=
  ⟨⟨16, 46, 3019⟩, 250538728366604545, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_46_flag endpoint_16_46_sources 15 250538728366604545 250538728366604545 rfl endpoint_16_46_base endpoint_16_46_p15) (by decide)⟩
private def endpoint_16_47_flag : Flag := ⟨16, 47, 2972⟩
private def endpoint_16_47_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_47_base : receiptBase endpoint_16_47_flag endpoint_16_47_sources = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_w0 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 2 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_w2 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 2 2 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_p4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 4 251342878743648398 = some 251342878743648398 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 2 2 251342878743648398 251342878743648398 251342878743648398 endpoint_16_47_w0 endpoint_16_47_w2
private theorem endpoint_16_47_w4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 4 2 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_p6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 6 251342878743648398 = some 251342878743648398 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 4 2 251342878743648398 251342878743648398 251342878743648398 endpoint_16_47_p4 endpoint_16_47_w4
private theorem endpoint_16_47_w6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 6 2 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_p8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 8 251342878743648398 = some 251342878743648398 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 6 2 251342878743648398 251342878743648398 251342878743648398 endpoint_16_47_p6 endpoint_16_47_w6
private theorem endpoint_16_47_w8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 8 2 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_p10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 10 251342878743648398 = some 251342878743648398 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 8 2 251342878743648398 251342878743648398 251342878743648398 endpoint_16_47_p8 endpoint_16_47_w8
private theorem endpoint_16_47_w10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 10 2 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_p12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 12 251342878743648398 = some 251342878743648398 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 10 2 251342878743648398 251342878743648398 251342878743648398 endpoint_16_47_p10 endpoint_16_47_w10
private theorem endpoint_16_47_w12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 12 2 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_p14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 14 251342878743648398 = some 251342878743648398 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 12 2 251342878743648398 251342878743648398 251342878743648398 endpoint_16_47_p12 endpoint_16_47_w12
private theorem endpoint_16_47_w14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 14 1 251342878743648398 = some 251342878743648398 := by decide +kernel
private theorem endpoint_16_47_p15 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 15 251342878743648398 = some 251342878743648398 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 14 1 251342878743648398 251342878743648398 251342878743648398 endpoint_16_47_p14 endpoint_16_47_w14
def endpoint_16_47 : CertifiedEndpoint :=
  ⟨⟨16, 47, 2972⟩, 251342878743648398, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_47_flag endpoint_16_47_sources 15 251342878743648398 251342878743648398 rfl endpoint_16_47_base endpoint_16_47_p15) (by decide)⟩
private def endpoint_16_48_flag : Flag := ⟨16, 48, 2924⟩
private def endpoint_16_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_48_base : receiptBase endpoint_16_48_flag endpoint_16_48_sources = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_w0 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 2 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_w2 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 2 2 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_p4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 4 252584319910255796 = some 252584319910255796 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 2 2 252584319910255796 252584319910255796 252584319910255796 endpoint_16_48_w0 endpoint_16_48_w2
private theorem endpoint_16_48_w4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 4 2 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_p6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 6 252584319910255796 = some 252584319910255796 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 4 2 252584319910255796 252584319910255796 252584319910255796 endpoint_16_48_p4 endpoint_16_48_w4
private theorem endpoint_16_48_w6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 6 2 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_p8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 8 252584319910255796 = some 252584319910255796 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 6 2 252584319910255796 252584319910255796 252584319910255796 endpoint_16_48_p6 endpoint_16_48_w6
private theorem endpoint_16_48_w8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 8 2 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_p10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 10 252584319910255796 = some 252584319910255796 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 8 2 252584319910255796 252584319910255796 252584319910255796 endpoint_16_48_p8 endpoint_16_48_w8
private theorem endpoint_16_48_w10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 10 2 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_p12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 12 252584319910255796 = some 252584319910255796 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 10 2 252584319910255796 252584319910255796 252584319910255796 endpoint_16_48_p10 endpoint_16_48_w10
private theorem endpoint_16_48_w12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 12 2 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_p14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 14 252584319910255796 = some 252584319910255796 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 12 2 252584319910255796 252584319910255796 252584319910255796 endpoint_16_48_p12 endpoint_16_48_w12
private theorem endpoint_16_48_w14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 14 1 252584319910255796 = some 252584319910255796 := by decide +kernel
private theorem endpoint_16_48_p15 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 15 252584319910255796 = some 252584319910255796 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 14 1 252584319910255796 252584319910255796 252584319910255796 endpoint_16_48_p14 endpoint_16_48_w14
def endpoint_16_48 : CertifiedEndpoint :=
  ⟨⟨16, 48, 2924⟩, 252584319910255796, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_48_flag endpoint_16_48_sources 15 252584319910255796 252584319910255796 rfl endpoint_16_48_base endpoint_16_48_p15) (by decide)⟩
private def endpoint_16_49_flag : Flag := ⟨16, 49, 2874⟩
private def endpoint_16_49_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_49_base : receiptBase endpoint_16_49_flag endpoint_16_49_sources = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_w0 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 2 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_w2 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 2 2 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_p4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 4 252819842784899818 = some 252819842784899818 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 2 2 252819842784899818 252819842784899818 252819842784899818 endpoint_16_49_w0 endpoint_16_49_w2
private theorem endpoint_16_49_w4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 4 2 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_p6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 6 252819842784899818 = some 252819842784899818 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 4 2 252819842784899818 252819842784899818 252819842784899818 endpoint_16_49_p4 endpoint_16_49_w4
private theorem endpoint_16_49_w6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 6 2 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_p8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 8 252819842784899818 = some 252819842784899818 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 6 2 252819842784899818 252819842784899818 252819842784899818 endpoint_16_49_p6 endpoint_16_49_w6
private theorem endpoint_16_49_w8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 8 2 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_p10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 10 252819842784899818 = some 252819842784899818 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 8 2 252819842784899818 252819842784899818 252819842784899818 endpoint_16_49_p8 endpoint_16_49_w8
private theorem endpoint_16_49_w10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 10 2 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_p12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 12 252819842784899818 = some 252819842784899818 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 10 2 252819842784899818 252819842784899818 252819842784899818 endpoint_16_49_p10 endpoint_16_49_w10
private theorem endpoint_16_49_w12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 12 2 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_p14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 14 252819842784899818 = some 252819842784899818 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 12 2 252819842784899818 252819842784899818 252819842784899818 endpoint_16_49_p12 endpoint_16_49_w12
private theorem endpoint_16_49_w14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 14 1 252819842784899818 = some 252819842784899818 := by decide +kernel
private theorem endpoint_16_49_p15 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 15 252819842784899818 = some 252819842784899818 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 14 1 252819842784899818 252819842784899818 252819842784899818 endpoint_16_49_p14 endpoint_16_49_w14
def endpoint_16_49 : CertifiedEndpoint :=
  ⟨⟨16, 49, 2874⟩, 252819842784899818, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_49_flag endpoint_16_49_sources 15 252819842784899818 252819842784899818 rfl endpoint_16_49_base endpoint_16_49_p15) (by decide)⟩
private def endpoint_16_50_flag : Flag := ⟨16, 50, 2824⟩
private def endpoint_16_50_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_50_base : receiptBase endpoint_16_50_flag endpoint_16_50_sources = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_w0 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 2 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_w2 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 2 2 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_p4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 4 252899265792522664 = some 252899265792522664 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 2 2 252899265792522664 252899265792522664 252899265792522664 endpoint_16_50_w0 endpoint_16_50_w2
private theorem endpoint_16_50_w4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 4 2 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_p6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 6 252899265792522664 = some 252899265792522664 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 4 2 252899265792522664 252899265792522664 252899265792522664 endpoint_16_50_p4 endpoint_16_50_w4
private theorem endpoint_16_50_w6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 6 2 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_p8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 8 252899265792522664 = some 252899265792522664 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 6 2 252899265792522664 252899265792522664 252899265792522664 endpoint_16_50_p6 endpoint_16_50_w6
private theorem endpoint_16_50_w8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 8 2 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_p10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 10 252899265792522664 = some 252899265792522664 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 8 2 252899265792522664 252899265792522664 252899265792522664 endpoint_16_50_p8 endpoint_16_50_w8
private theorem endpoint_16_50_w10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 10 2 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_p12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 12 252899265792522664 = some 252899265792522664 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 10 2 252899265792522664 252899265792522664 252899265792522664 endpoint_16_50_p10 endpoint_16_50_w10
private theorem endpoint_16_50_w12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 12 2 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_p14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 14 252899265792522664 = some 252899265792522664 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 12 2 252899265792522664 252899265792522664 252899265792522664 endpoint_16_50_p12 endpoint_16_50_w12
private theorem endpoint_16_50_w14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 14 1 252899265792522664 = some 252899265792522664 := by decide +kernel
private theorem endpoint_16_50_p15 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 15 252899265792522664 = some 252899265792522664 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 14 1 252899265792522664 252899265792522664 252899265792522664 endpoint_16_50_p14 endpoint_16_50_w14
def endpoint_16_50 : CertifiedEndpoint :=
  ⟨⟨16, 50, 2824⟩, 252899265792522664, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_50_flag endpoint_16_50_sources 15 252899265792522664 252899265792522664 rfl endpoint_16_50_base endpoint_16_50_p15) (by decide)⟩
private def endpoint_16_51_flag : Flag := ⟨16, 51, 2772⟩
private def endpoint_16_51_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_51_base : receiptBase endpoint_16_51_flag endpoint_16_51_sources = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_w0 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 2 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_w2 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 2 2 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_p4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 4 252642795496258861 = some 252642795496258861 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 2 2 252642795496258861 252642795496258861 252642795496258861 endpoint_16_51_w0 endpoint_16_51_w2
private theorem endpoint_16_51_w4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 4 2 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_p6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 6 252642795496258861 = some 252642795496258861 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 4 2 252642795496258861 252642795496258861 252642795496258861 endpoint_16_51_p4 endpoint_16_51_w4
private theorem endpoint_16_51_w6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 6 2 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_p8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 8 252642795496258861 = some 252642795496258861 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 6 2 252642795496258861 252642795496258861 252642795496258861 endpoint_16_51_p6 endpoint_16_51_w6
private theorem endpoint_16_51_w8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 8 2 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_p10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 10 252642795496258861 = some 252642795496258861 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 8 2 252642795496258861 252642795496258861 252642795496258861 endpoint_16_51_p8 endpoint_16_51_w8
private theorem endpoint_16_51_w10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 10 2 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_p12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 12 252642795496258861 = some 252642795496258861 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 10 2 252642795496258861 252642795496258861 252642795496258861 endpoint_16_51_p10 endpoint_16_51_w10
private theorem endpoint_16_51_w12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 12 2 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_p14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 14 252642795496258861 = some 252642795496258861 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 12 2 252642795496258861 252642795496258861 252642795496258861 endpoint_16_51_p12 endpoint_16_51_w12
private theorem endpoint_16_51_w14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 14 1 252642795496258861 = some 252642795496258861 := by decide +kernel
private theorem endpoint_16_51_p15 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 15 252642795496258861 = some 252642795496258861 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 14 1 252642795496258861 252642795496258861 252642795496258861 endpoint_16_51_p14 endpoint_16_51_w14
def endpoint_16_51 : CertifiedEndpoint :=
  ⟨⟨16, 51, 2772⟩, 252642795496258861, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_51_flag endpoint_16_51_sources 15 252642795496258861 252642795496258861 rfl endpoint_16_51_base endpoint_16_51_p15) (by decide)⟩
private def endpoint_16_52_flag : Flag := ⟨16, 52, 2719⟩
private def endpoint_16_52_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_52_base : receiptBase endpoint_16_52_flag endpoint_16_52_sources = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_w0 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 2 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_w2 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 2 2 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_p4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 4 252132600898351979 = some 252132600898351979 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 2 2 252132600898351979 252132600898351979 252132600898351979 endpoint_16_52_w0 endpoint_16_52_w2
private theorem endpoint_16_52_w4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 4 2 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_p6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 6 252132600898351979 = some 252132600898351979 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 4 2 252132600898351979 252132600898351979 252132600898351979 endpoint_16_52_p4 endpoint_16_52_w4
private theorem endpoint_16_52_w6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 6 2 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_p8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 8 252132600898351979 = some 252132600898351979 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 6 2 252132600898351979 252132600898351979 252132600898351979 endpoint_16_52_p6 endpoint_16_52_w6
private theorem endpoint_16_52_w8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 8 2 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_p10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 10 252132600898351979 = some 252132600898351979 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 8 2 252132600898351979 252132600898351979 252132600898351979 endpoint_16_52_p8 endpoint_16_52_w8
private theorem endpoint_16_52_w10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 10 2 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_p12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 12 252132600898351979 = some 252132600898351979 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 10 2 252132600898351979 252132600898351979 252132600898351979 endpoint_16_52_p10 endpoint_16_52_w10
private theorem endpoint_16_52_w12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 12 2 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_p14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 14 252132600898351979 = some 252132600898351979 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 12 2 252132600898351979 252132600898351979 252132600898351979 endpoint_16_52_p12 endpoint_16_52_w12
private theorem endpoint_16_52_w14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 14 1 252132600898351979 = some 252132600898351979 := by decide +kernel
private theorem endpoint_16_52_p15 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 15 252132600898351979 = some 252132600898351979 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 14 1 252132600898351979 252132600898351979 252132600898351979 endpoint_16_52_p14 endpoint_16_52_w14
def endpoint_16_52 : CertifiedEndpoint :=
  ⟨⟨16, 52, 2719⟩, 252132600898351979, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_52_flag endpoint_16_52_sources 15 252132600898351979 252132600898351979 rfl endpoint_16_52_base endpoint_16_52_p15) (by decide)⟩

def endpointBlock10 : List CertifiedEndpoint := [
  endpoint_14_72, endpoint_14_73, endpoint_14_74, endpoint_14_75, endpoint_14_76, endpoint_14_77, endpoint_14_78,
  endpoint_14_79, endpoint_14_80, endpoint_14_81, endpoint_14_82, endpoint_14_83, endpoint_14_84, endpoint_14_85,
  endpoint_14_86, endpoint_14_87, endpoint_15_15, endpoint_15_16, endpoint_15_17, endpoint_15_18, endpoint_15_19,
  endpoint_15_20, endpoint_15_21, endpoint_15_22, endpoint_15_23, endpoint_15_24, endpoint_15_25, endpoint_15_26,
  endpoint_15_27, endpoint_15_28, endpoint_15_29, endpoint_15_30, endpoint_15_31, endpoint_15_32, endpoint_15_33,
  endpoint_15_34, endpoint_15_35, endpoint_15_36, endpoint_15_37, endpoint_15_38, endpoint_15_39, endpoint_15_40,
  endpoint_15_41, endpoint_15_42, endpoint_15_43, endpoint_15_44, endpoint_15_45, endpoint_15_46, endpoint_15_47,
  endpoint_15_48, endpoint_15_49, endpoint_15_50, endpoint_15_51, endpoint_15_52, endpoint_15_53, endpoint_15_54,
  endpoint_15_55, endpoint_15_56, endpoint_15_57, endpoint_15_58, endpoint_15_59, endpoint_15_60, endpoint_15_61,
  endpoint_15_62, endpoint_15_63, endpoint_15_64, endpoint_15_65, endpoint_15_66, endpoint_15_67, endpoint_15_68,
  endpoint_15_69, endpoint_15_70, endpoint_15_71, endpoint_15_72, endpoint_15_73, endpoint_15_74, endpoint_15_75,
  endpoint_15_76, endpoint_15_77, endpoint_15_78, endpoint_15_79, endpoint_15_80, endpoint_15_81, endpoint_15_82,
  endpoint_15_83, endpoint_15_84, endpoint_15_85, endpoint_16_16, endpoint_16_17, endpoint_16_18, endpoint_16_19,
  endpoint_16_20, endpoint_16_21, endpoint_16_22, endpoint_16_23, endpoint_16_24, endpoint_16_25, endpoint_16_26,
  endpoint_16_27, endpoint_16_28, endpoint_16_29, endpoint_16_30, endpoint_16_31, endpoint_16_32, endpoint_16_33,
  endpoint_16_34, endpoint_16_35, endpoint_16_36, endpoint_16_37, endpoint_16_38, endpoint_16_39, endpoint_16_40,
  endpoint_16_41, endpoint_16_42, endpoint_16_43, endpoint_16_44, endpoint_16_45, endpoint_16_46, endpoint_16_47,
  endpoint_16_48, endpoint_16_49, endpoint_16_50, endpoint_16_51, endpoint_16_52
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
