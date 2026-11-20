import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def endpoint_14_81 : CertifiedEndpoint :=
  ⟨⟨14, 81, 953⟩, 232982451891527338, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_82 : CertifiedEndpoint :=
  ⟨⟨14, 82, 852⟩, 209778575250591576, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_83 : CertifiedEndpoint :=
  ⟨⟨14, 83, 747⟩, 184813425918626952, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_84 : CertifiedEndpoint :=
  ⟨⟨14, 84, 640⟩, 158578772802613720, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_85 : CertifiedEndpoint :=
  ⟨⟨14, 85, 531⟩, 131053690300478292, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_86 : CertifiedEndpoint :=
  ⟨⟨14, 86, 418⟩, 101669682297637258, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_87 : CertifiedEndpoint :=
  ⟨⟨14, 87, 304⟩, 71216716159744969, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_14_88 : CertifiedEndpoint :=
  ⟨⟨14, 88, 186⟩, 38842047714926310, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_15 : CertifiedEndpoint :=
  ⟨⟨15, 15, 3779⟩, 117783252726772704, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_16 : CertifiedEndpoint :=
  ⟨⟨15, 16, 3757⟩, 121689725988486782, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_17 : CertifiedEndpoint :=
  ⟨⟨15, 17, 3735⟩, 125542150023571880, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_18 : CertifiedEndpoint :=
  ⟨⟨15, 18, 3713⟩, 138641163221101853, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_19 : CertifiedEndpoint :=
  ⟨⟨15, 19, 3690⟩, 151530430724896685, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_20 : CertifiedEndpoint :=
  ⟨⟨15, 20, 3667⟩, 164243668908973567, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_21 : CertifiedEndpoint :=
  ⟨⟨15, 21, 3644⟩, 176780877773332499, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_22 : CertifiedEndpoint :=
  ⟨⟨15, 22, 3621⟩, 189142057317973481, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_23 : CertifiedEndpoint :=
  ⟨⟨15, 23, 3597⟩, 201271019340830222, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_24 : CertifiedEndpoint :=
  ⟨⟨15, 24, 3573⟩, 213216461434619313, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_25 : CertifiedEndpoint :=
  ⟨⟨15, 25, 3549⟩, 224978383599340754, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_26 : CertifiedEndpoint :=
  ⟨⟨15, 26, 3524⟩, 236489361718903704, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_27 : CertifiedEndpoint :=
  ⟨⟨15, 27, 3499⟩, 247809329300049304, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_28 : CertifiedEndpoint :=
  ⟨⟨15, 28, 3473⟩, 258863371617337013, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_15_29_flag : Flag := ⟨15, 29, 3447⟩
private def endpoint_15_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_29_base : receiptBase endpoint_15_29_flag endpoint_15_29_sources = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_w0 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 2 181364085826881274 = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_w2 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 2 2 181364085826881274 = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_p4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 4 181364085826881274 = some 181364085826881274 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 2 2 181364085826881274 181364085826881274 181364085826881274 endpoint_15_29_w0 endpoint_15_29_w2
private theorem endpoint_15_29_w4 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 4 2 181364085826881274 = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_p6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 6 181364085826881274 = some 181364085826881274 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 4 2 181364085826881274 181364085826881274 181364085826881274 endpoint_15_29_p4 endpoint_15_29_w4
private theorem endpoint_15_29_w6 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 6 2 181364085826881274 = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_p8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 8 181364085826881274 = some 181364085826881274 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 6 2 181364085826881274 181364085826881274 181364085826881274 endpoint_15_29_p6 endpoint_15_29_w6
private theorem endpoint_15_29_w8 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 8 2 181364085826881274 = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_p10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 10 181364085826881274 = some 181364085826881274 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 8 2 181364085826881274 181364085826881274 181364085826881274 endpoint_15_29_p8 endpoint_15_29_w8
private theorem endpoint_15_29_w10 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 10 2 181364085826881274 = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_p12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 12 181364085826881274 = some 181364085826881274 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 10 2 181364085826881274 181364085826881274 181364085826881274 endpoint_15_29_p10 endpoint_15_29_w10
private theorem endpoint_15_29_w12 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 12 2 181364085826881274 = some 181364085826881274 := by decide +kernel
private theorem endpoint_15_29_p14 : receiptWindow endpoint_15_29_flag endpoint_15_29_sources 0 14 181364085826881274 = some 181364085826881274 :=
  join_receipt_window endpoint_15_29_flag endpoint_15_29_sources 0 12 2 181364085826881274 181364085826881274 181364085826881274 endpoint_15_29_p12 endpoint_15_29_w12
def endpoint_15_29 : CertifiedEndpoint :=
  ⟨⟨15, 29, 3447⟩, 181364085826881274, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_29_flag endpoint_15_29_sources 14 181364085826881274 181364085826881274 rfl endpoint_15_29_base endpoint_15_29_p14) (by decide)⟩
private def endpoint_15_30_flag : Flag := ⟨15, 30, 3421⟩
private def endpoint_15_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_30_base : receiptBase endpoint_15_30_flag endpoint_15_30_sources = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_w0 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 2 185102992811771616 = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_w2 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 2 2 185102992811771616 = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_p4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 4 185102992811771616 = some 185102992811771616 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 2 2 185102992811771616 185102992811771616 185102992811771616 endpoint_15_30_w0 endpoint_15_30_w2
private theorem endpoint_15_30_w4 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 4 2 185102992811771616 = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_p6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 6 185102992811771616 = some 185102992811771616 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 4 2 185102992811771616 185102992811771616 185102992811771616 endpoint_15_30_p4 endpoint_15_30_w4
private theorem endpoint_15_30_w6 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 6 2 185102992811771616 = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_p8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 8 185102992811771616 = some 185102992811771616 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 6 2 185102992811771616 185102992811771616 185102992811771616 endpoint_15_30_p6 endpoint_15_30_w6
private theorem endpoint_15_30_w8 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 8 2 185102992811771616 = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_p10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 10 185102992811771616 = some 185102992811771616 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 8 2 185102992811771616 185102992811771616 185102992811771616 endpoint_15_30_p8 endpoint_15_30_w8
private theorem endpoint_15_30_w10 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 10 2 185102992811771616 = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_p12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 12 185102992811771616 = some 185102992811771616 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 10 2 185102992811771616 185102992811771616 185102992811771616 endpoint_15_30_p10 endpoint_15_30_w10
private theorem endpoint_15_30_w12 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 12 2 185102992811771616 = some 185102992811771616 := by decide +kernel
private theorem endpoint_15_30_p14 : receiptWindow endpoint_15_30_flag endpoint_15_30_sources 0 14 185102992811771616 = some 185102992811771616 :=
  join_receipt_window endpoint_15_30_flag endpoint_15_30_sources 0 12 2 185102992811771616 185102992811771616 185102992811771616 endpoint_15_30_p12 endpoint_15_30_w12
def endpoint_15_30 : CertifiedEndpoint :=
  ⟨⟨15, 30, 3421⟩, 185102992811771616, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_30_flag endpoint_15_30_sources 14 185102992811771616 185102992811771616 rfl endpoint_15_30_base endpoint_15_30_p14) (by decide)⟩
private def endpoint_15_31_flag : Flag := ⟨15, 31, 3395⟩
private def endpoint_15_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_31_base : receiptBase endpoint_15_31_flag endpoint_15_31_sources = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_w0 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 2 188764736902876509 = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_w2 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 2 2 188764736902876509 = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_p4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 4 188764736902876509 = some 188764736902876509 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 2 2 188764736902876509 188764736902876509 188764736902876509 endpoint_15_31_w0 endpoint_15_31_w2
private theorem endpoint_15_31_w4 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 4 2 188764736902876509 = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_p6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 6 188764736902876509 = some 188764736902876509 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 4 2 188764736902876509 188764736902876509 188764736902876509 endpoint_15_31_p4 endpoint_15_31_w4
private theorem endpoint_15_31_w6 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 6 2 188764736902876509 = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_p8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 8 188764736902876509 = some 188764736902876509 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 6 2 188764736902876509 188764736902876509 188764736902876509 endpoint_15_31_p6 endpoint_15_31_w6
private theorem endpoint_15_31_w8 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 8 2 188764736902876509 = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_p10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 10 188764736902876509 = some 188764736902876509 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 8 2 188764736902876509 188764736902876509 188764736902876509 endpoint_15_31_p8 endpoint_15_31_w8
private theorem endpoint_15_31_w10 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 10 2 188764736902876509 = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_p12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 12 188764736902876509 = some 188764736902876509 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 10 2 188764736902876509 188764736902876509 188764736902876509 endpoint_15_31_p10 endpoint_15_31_w10
private theorem endpoint_15_31_w12 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 12 2 188764736902876509 = some 188764736902876509 := by decide +kernel
private theorem endpoint_15_31_p14 : receiptWindow endpoint_15_31_flag endpoint_15_31_sources 0 14 188764736902876509 = some 188764736902876509 :=
  join_receipt_window endpoint_15_31_flag endpoint_15_31_sources 0 12 2 188764736902876509 188764736902876509 188764736902876509 endpoint_15_31_p12 endpoint_15_31_w12
def endpoint_15_31 : CertifiedEndpoint :=
  ⟨⟨15, 31, 3395⟩, 188764736902876509, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_31_flag endpoint_15_31_sources 14 188764736902876509 188764736902876509 rfl endpoint_15_31_base endpoint_15_31_p14) (by decide)⟩
private def endpoint_15_32_flag : Flag := ⟨15, 32, 3368⟩
private def endpoint_15_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_32_base : receiptBase endpoint_15_32_flag endpoint_15_32_sources = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_w0 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 2 192293041007483349 = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_w2 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 2 2 192293041007483349 = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_p4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 4 192293041007483349 = some 192293041007483349 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 2 2 192293041007483349 192293041007483349 192293041007483349 endpoint_15_32_w0 endpoint_15_32_w2
private theorem endpoint_15_32_w4 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 4 2 192293041007483349 = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_p6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 6 192293041007483349 = some 192293041007483349 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 4 2 192293041007483349 192293041007483349 192293041007483349 endpoint_15_32_p4 endpoint_15_32_w4
private theorem endpoint_15_32_w6 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 6 2 192293041007483349 = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_p8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 8 192293041007483349 = some 192293041007483349 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 6 2 192293041007483349 192293041007483349 192293041007483349 endpoint_15_32_p6 endpoint_15_32_w6
private theorem endpoint_15_32_w8 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 8 2 192293041007483349 = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_p10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 10 192293041007483349 = some 192293041007483349 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 8 2 192293041007483349 192293041007483349 192293041007483349 endpoint_15_32_p8 endpoint_15_32_w8
private theorem endpoint_15_32_w10 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 10 2 192293041007483349 = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_p12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 12 192293041007483349 = some 192293041007483349 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 10 2 192293041007483349 192293041007483349 192293041007483349 endpoint_15_32_p10 endpoint_15_32_w10
private theorem endpoint_15_32_w12 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 12 2 192293041007483349 = some 192293041007483349 := by decide +kernel
private theorem endpoint_15_32_p14 : receiptWindow endpoint_15_32_flag endpoint_15_32_sources 0 14 192293041007483349 = some 192293041007483349 :=
  join_receipt_window endpoint_15_32_flag endpoint_15_32_sources 0 12 2 192293041007483349 192293041007483349 192293041007483349 endpoint_15_32_p12 endpoint_15_32_w12
def endpoint_15_32 : CertifiedEndpoint :=
  ⟨⟨15, 32, 3368⟩, 192293041007483349, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_32_flag endpoint_15_32_sources 14 192293041007483349 192293041007483349 rfl endpoint_15_32_base endpoint_15_32_p14) (by decide)⟩
private def endpoint_15_33_flag : Flag := ⟨15, 33, 3340⟩
private def endpoint_15_33_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_15_33_base : receiptBase endpoint_15_33_flag endpoint_15_33_sources = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_w0 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 2 195683538751769924 = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_w2 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 2 2 195683538751769924 = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_p4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 4 195683538751769924 = some 195683538751769924 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 2 2 195683538751769924 195683538751769924 195683538751769924 endpoint_15_33_w0 endpoint_15_33_w2
private theorem endpoint_15_33_w4 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 4 2 195683538751769924 = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_p6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 6 195683538751769924 = some 195683538751769924 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 4 2 195683538751769924 195683538751769924 195683538751769924 endpoint_15_33_p4 endpoint_15_33_w4
private theorem endpoint_15_33_w6 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 6 2 195683538751769924 = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_p8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 8 195683538751769924 = some 195683538751769924 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 6 2 195683538751769924 195683538751769924 195683538751769924 endpoint_15_33_p6 endpoint_15_33_w6
private theorem endpoint_15_33_w8 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 8 2 195683538751769924 = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_p10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 10 195683538751769924 = some 195683538751769924 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 8 2 195683538751769924 195683538751769924 195683538751769924 endpoint_15_33_p8 endpoint_15_33_w8
private theorem endpoint_15_33_w10 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 10 2 195683538751769924 = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_p12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 12 195683538751769924 = some 195683538751769924 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 10 2 195683538751769924 195683538751769924 195683538751769924 endpoint_15_33_p10 endpoint_15_33_w10
private theorem endpoint_15_33_w12 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 12 2 195683538751769924 = some 195683538751769924 := by decide +kernel
private theorem endpoint_15_33_p14 : receiptWindow endpoint_15_33_flag endpoint_15_33_sources 0 14 195683538751769924 = some 195683538751769924 :=
  join_receipt_window endpoint_15_33_flag endpoint_15_33_sources 0 12 2 195683538751769924 195683538751769924 195683538751769924 endpoint_15_33_p12 endpoint_15_33_w12
def endpoint_15_33 : CertifiedEndpoint :=
  ⟨⟨15, 33, 3340⟩, 195683538751769924, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_15_33_flag endpoint_15_33_sources 14 195683538751769924 195683538751769924 rfl endpoint_15_33_base endpoint_15_33_p14) (by decide)⟩
private def endpoint_15_34_flag : Flag := ⟨15, 34, 3312⟩
private def endpoint_15_34_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_34_base : receiptBase endpoint_15_34_flag endpoint_15_34_sources = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_w0 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 2 198960397304819105 = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_w2 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 2 2 198960397304819105 = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_p4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 4 198960397304819105 = some 198960397304819105 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 2 2 198960397304819105 198960397304819105 198960397304819105 endpoint_15_34_w0 endpoint_15_34_w2
private theorem endpoint_15_34_w4 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 4 2 198960397304819105 = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_p6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 6 198960397304819105 = some 198960397304819105 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 4 2 198960397304819105 198960397304819105 198960397304819105 endpoint_15_34_p4 endpoint_15_34_w4
private theorem endpoint_15_34_w6 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 6 2 198960397304819105 = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_p8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 8 198960397304819105 = some 198960397304819105 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 6 2 198960397304819105 198960397304819105 198960397304819105 endpoint_15_34_p6 endpoint_15_34_w6
private theorem endpoint_15_34_w8 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 8 2 198960397304819105 = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_p10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 10 198960397304819105 = some 198960397304819105 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 8 2 198960397304819105 198960397304819105 198960397304819105 endpoint_15_34_p8 endpoint_15_34_w8
private theorem endpoint_15_34_w10 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 10 2 198960397304819105 = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_p12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 12 198960397304819105 = some 198960397304819105 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 10 2 198960397304819105 198960397304819105 198960397304819105 endpoint_15_34_p10 endpoint_15_34_w10
private theorem endpoint_15_34_w12 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 12 2 198960397304819105 = some 198960397304819105 := by decide +kernel
private theorem endpoint_15_34_p14 : receiptWindow endpoint_15_34_flag endpoint_15_34_sources 0 14 198960397304819105 = some 198960397304819105 :=
  join_receipt_window endpoint_15_34_flag endpoint_15_34_sources 0 12 2 198960397304819105 198960397304819105 198960397304819105 endpoint_15_34_p12 endpoint_15_34_w12
def endpoint_15_34 : CertifiedEndpoint :=
  ⟨⟨15, 34, 3312⟩, 198960397304819105, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_34_flag endpoint_15_34_sources 14 198960397304819105 198960397304819105 rfl endpoint_15_34_base endpoint_15_34_p14) (by decide)⟩
private def endpoint_15_35_flag : Flag := ⟨15, 35, 3283⟩
private def endpoint_15_35_sources : Sources := ⟨contact23, contact03, contact02⟩
private theorem endpoint_15_35_base : receiptBase endpoint_15_35_flag endpoint_15_35_sources = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_w0 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 2 202062427497120695 = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_w2 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 2 2 202062427497120695 = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_p4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 4 202062427497120695 = some 202062427497120695 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 2 2 202062427497120695 202062427497120695 202062427497120695 endpoint_15_35_w0 endpoint_15_35_w2
private theorem endpoint_15_35_w4 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 4 2 202062427497120695 = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_p6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 6 202062427497120695 = some 202062427497120695 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 4 2 202062427497120695 202062427497120695 202062427497120695 endpoint_15_35_p4 endpoint_15_35_w4
private theorem endpoint_15_35_w6 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 6 2 202062427497120695 = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_p8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 8 202062427497120695 = some 202062427497120695 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 6 2 202062427497120695 202062427497120695 202062427497120695 endpoint_15_35_p6 endpoint_15_35_w6
private theorem endpoint_15_35_w8 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 8 2 202062427497120695 = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_p10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 10 202062427497120695 = some 202062427497120695 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 8 2 202062427497120695 202062427497120695 202062427497120695 endpoint_15_35_p8 endpoint_15_35_w8
private theorem endpoint_15_35_w10 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 10 2 202062427497120695 = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_p12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 12 202062427497120695 = some 202062427497120695 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 10 2 202062427497120695 202062427497120695 202062427497120695 endpoint_15_35_p10 endpoint_15_35_w10
private theorem endpoint_15_35_w12 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 12 2 202062427497120695 = some 202062427497120695 := by decide +kernel
private theorem endpoint_15_35_p14 : receiptWindow endpoint_15_35_flag endpoint_15_35_sources 0 14 202062427497120695 = some 202062427497120695 :=
  join_receipt_window endpoint_15_35_flag endpoint_15_35_sources 0 12 2 202062427497120695 202062427497120695 202062427497120695 endpoint_15_35_p12 endpoint_15_35_w12
def endpoint_15_35 : CertifiedEndpoint :=
  ⟨⟨15, 35, 3283⟩, 202062427497120695, .terminal ⟨contact23, contact03, contact02⟩ (finish_receipt_window endpoint_15_35_flag endpoint_15_35_sources 14 202062427497120695 202062427497120695 rfl endpoint_15_35_base endpoint_15_35_p14) (by decide)⟩
private def endpoint_15_36_flag : Flag := ⟨15, 36, 3254⟩
private def endpoint_15_36_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_36_base : receiptBase endpoint_15_36_flag endpoint_15_36_sources = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_w0 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 2 206397695873294799 = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_w2 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 2 2 206397695873294799 = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_p4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 4 206397695873294799 = some 206397695873294799 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 2 2 206397695873294799 206397695873294799 206397695873294799 endpoint_15_36_w0 endpoint_15_36_w2
private theorem endpoint_15_36_w4 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 4 2 206397695873294799 = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_p6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 6 206397695873294799 = some 206397695873294799 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 4 2 206397695873294799 206397695873294799 206397695873294799 endpoint_15_36_p4 endpoint_15_36_w4
private theorem endpoint_15_36_w6 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 6 2 206397695873294799 = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_p8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 8 206397695873294799 = some 206397695873294799 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 6 2 206397695873294799 206397695873294799 206397695873294799 endpoint_15_36_p6 endpoint_15_36_w6
private theorem endpoint_15_36_w8 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 8 2 206397695873294799 = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_p10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 10 206397695873294799 = some 206397695873294799 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 8 2 206397695873294799 206397695873294799 206397695873294799 endpoint_15_36_p8 endpoint_15_36_w8
private theorem endpoint_15_36_w10 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 10 2 206397695873294799 = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_p12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 12 206397695873294799 = some 206397695873294799 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 10 2 206397695873294799 206397695873294799 206397695873294799 endpoint_15_36_p10 endpoint_15_36_w10
private theorem endpoint_15_36_w12 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 12 2 206397695873294799 = some 206397695873294799 := by decide +kernel
private theorem endpoint_15_36_p14 : receiptWindow endpoint_15_36_flag endpoint_15_36_sources 0 14 206397695873294799 = some 206397695873294799 :=
  join_receipt_window endpoint_15_36_flag endpoint_15_36_sources 0 12 2 206397695873294799 206397695873294799 206397695873294799 endpoint_15_36_p12 endpoint_15_36_w12
def endpoint_15_36 : CertifiedEndpoint :=
  ⟨⟨15, 36, 3254⟩, 206397695873294799, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_36_flag endpoint_15_36_sources 14 206397695873294799 206397695873294799 rfl endpoint_15_36_base endpoint_15_36_p14) (by decide)⟩
private def endpoint_15_37_flag : Flag := ⟨15, 37, 3225⟩
private def endpoint_15_37_sources : Sources := ⟨contact23, contact03, contact25⟩
private theorem endpoint_15_37_base : receiptBase endpoint_15_37_flag endpoint_15_37_sources = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_w0 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 2 209326609909702250 = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_w2 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 2 2 209326609909702250 = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_p4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 4 209326609909702250 = some 209326609909702250 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 2 2 209326609909702250 209326609909702250 209326609909702250 endpoint_15_37_w0 endpoint_15_37_w2
private theorem endpoint_15_37_w4 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 4 2 209326609909702250 = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_p6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 6 209326609909702250 = some 209326609909702250 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 4 2 209326609909702250 209326609909702250 209326609909702250 endpoint_15_37_p4 endpoint_15_37_w4
private theorem endpoint_15_37_w6 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 6 2 209326609909702250 = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_p8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 8 209326609909702250 = some 209326609909702250 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 6 2 209326609909702250 209326609909702250 209326609909702250 endpoint_15_37_p6 endpoint_15_37_w6
private theorem endpoint_15_37_w8 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 8 2 209326609909702250 = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_p10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 10 209326609909702250 = some 209326609909702250 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 8 2 209326609909702250 209326609909702250 209326609909702250 endpoint_15_37_p8 endpoint_15_37_w8
private theorem endpoint_15_37_w10 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 10 2 209326609909702250 = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_p12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 12 209326609909702250 = some 209326609909702250 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 10 2 209326609909702250 209326609909702250 209326609909702250 endpoint_15_37_p10 endpoint_15_37_w10
private theorem endpoint_15_37_w12 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 12 2 209326609909702250 = some 209326609909702250 := by decide +kernel
private theorem endpoint_15_37_p14 : receiptWindow endpoint_15_37_flag endpoint_15_37_sources 0 14 209326609909702250 = some 209326609909702250 :=
  join_receipt_window endpoint_15_37_flag endpoint_15_37_sources 0 12 2 209326609909702250 209326609909702250 209326609909702250 endpoint_15_37_p12 endpoint_15_37_w12
def endpoint_15_37 : CertifiedEndpoint :=
  ⟨⟨15, 37, 3225⟩, 209326609909702250, .terminal ⟨contact23, contact03, contact25⟩ (finish_receipt_window endpoint_15_37_flag endpoint_15_37_sources 14 209326609909702250 209326609909702250 rfl endpoint_15_37_base endpoint_15_37_p14) (by decide)⟩
private def endpoint_15_38_flag : Flag := ⟨15, 38, 3195⟩
private def endpoint_15_38_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_38_base : receiptBase endpoint_15_38_flag endpoint_15_38_sources = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_w0 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 2 213605293207732297 = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_w2 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 2 2 213605293207732297 = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_p4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 4 213605293207732297 = some 213605293207732297 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 2 2 213605293207732297 213605293207732297 213605293207732297 endpoint_15_38_w0 endpoint_15_38_w2
private theorem endpoint_15_38_w4 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 4 2 213605293207732297 = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_p6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 6 213605293207732297 = some 213605293207732297 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 4 2 213605293207732297 213605293207732297 213605293207732297 endpoint_15_38_p4 endpoint_15_38_w4
private theorem endpoint_15_38_w6 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 6 2 213605293207732297 = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_p8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 8 213605293207732297 = some 213605293207732297 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 6 2 213605293207732297 213605293207732297 213605293207732297 endpoint_15_38_p6 endpoint_15_38_w6
private theorem endpoint_15_38_w8 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 8 2 213605293207732297 = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_p10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 10 213605293207732297 = some 213605293207732297 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 8 2 213605293207732297 213605293207732297 213605293207732297 endpoint_15_38_p8 endpoint_15_38_w8
private theorem endpoint_15_38_w10 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 10 2 213605293207732297 = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_p12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 12 213605293207732297 = some 213605293207732297 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 10 2 213605293207732297 213605293207732297 213605293207732297 endpoint_15_38_p10 endpoint_15_38_w10
private theorem endpoint_15_38_w12 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 12 2 213605293207732297 = some 213605293207732297 := by decide +kernel
private theorem endpoint_15_38_p14 : receiptWindow endpoint_15_38_flag endpoint_15_38_sources 0 14 213605293207732297 = some 213605293207732297 :=
  join_receipt_window endpoint_15_38_flag endpoint_15_38_sources 0 12 2 213605293207732297 213605293207732297 213605293207732297 endpoint_15_38_p12 endpoint_15_38_w12
def endpoint_15_38 : CertifiedEndpoint :=
  ⟨⟨15, 38, 3195⟩, 213605293207732297, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_38_flag endpoint_15_38_sources 14 213605293207732297 213605293207732297 rfl endpoint_15_38_base endpoint_15_38_p14) (by decide)⟩
private def endpoint_15_39_flag : Flag := ⟨15, 39, 3164⟩
private def endpoint_15_39_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_39_base : receiptBase endpoint_15_39_flag endpoint_15_39_sources = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_w0 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 2 216176236510772435 = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_w2 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 2 2 216176236510772435 = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_p4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 4 216176236510772435 = some 216176236510772435 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 2 2 216176236510772435 216176236510772435 216176236510772435 endpoint_15_39_w0 endpoint_15_39_w2
private theorem endpoint_15_39_w4 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 4 2 216176236510772435 = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_p6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 6 216176236510772435 = some 216176236510772435 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 4 2 216176236510772435 216176236510772435 216176236510772435 endpoint_15_39_p4 endpoint_15_39_w4
private theorem endpoint_15_39_w6 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 6 2 216176236510772435 = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_p8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 8 216176236510772435 = some 216176236510772435 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 6 2 216176236510772435 216176236510772435 216176236510772435 endpoint_15_39_p6 endpoint_15_39_w6
private theorem endpoint_15_39_w8 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 8 2 216176236510772435 = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_p10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 10 216176236510772435 = some 216176236510772435 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 8 2 216176236510772435 216176236510772435 216176236510772435 endpoint_15_39_p8 endpoint_15_39_w8
private theorem endpoint_15_39_w10 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 10 2 216176236510772435 = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_p12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 12 216176236510772435 = some 216176236510772435 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 10 2 216176236510772435 216176236510772435 216176236510772435 endpoint_15_39_p10 endpoint_15_39_w10
private theorem endpoint_15_39_w12 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 12 2 216176236510772435 = some 216176236510772435 := by decide +kernel
private theorem endpoint_15_39_p14 : receiptWindow endpoint_15_39_flag endpoint_15_39_sources 0 14 216176236510772435 = some 216176236510772435 :=
  join_receipt_window endpoint_15_39_flag endpoint_15_39_sources 0 12 2 216176236510772435 216176236510772435 216176236510772435 endpoint_15_39_p12 endpoint_15_39_w12
def endpoint_15_39 : CertifiedEndpoint :=
  ⟨⟨15, 39, 3164⟩, 216176236510772435, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_39_flag endpoint_15_39_sources 14 216176236510772435 216176236510772435 rfl endpoint_15_39_base endpoint_15_39_p14) (by decide)⟩
private def endpoint_15_40_flag : Flag := ⟨15, 40, 3133⟩
private def endpoint_15_40_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_15_40_base : receiptBase endpoint_15_40_flag endpoint_15_40_sources = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_w0 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 2 218656975021322699 = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_w2 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 2 2 218656975021322699 = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_p4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 4 218656975021322699 = some 218656975021322699 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 2 2 218656975021322699 218656975021322699 218656975021322699 endpoint_15_40_w0 endpoint_15_40_w2
private theorem endpoint_15_40_w4 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 4 2 218656975021322699 = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_p6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 6 218656975021322699 = some 218656975021322699 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 4 2 218656975021322699 218656975021322699 218656975021322699 endpoint_15_40_p4 endpoint_15_40_w4
private theorem endpoint_15_40_w6 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 6 2 218656975021322699 = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_p8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 8 218656975021322699 = some 218656975021322699 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 6 2 218656975021322699 218656975021322699 218656975021322699 endpoint_15_40_p6 endpoint_15_40_w6
private theorem endpoint_15_40_w8 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 8 2 218656975021322699 = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_p10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 10 218656975021322699 = some 218656975021322699 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 8 2 218656975021322699 218656975021322699 218656975021322699 endpoint_15_40_p8 endpoint_15_40_w8
private theorem endpoint_15_40_w10 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 10 2 218656975021322699 = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_p12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 12 218656975021322699 = some 218656975021322699 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 10 2 218656975021322699 218656975021322699 218656975021322699 endpoint_15_40_p10 endpoint_15_40_w10
private theorem endpoint_15_40_w12 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 12 2 218656975021322699 = some 218656975021322699 := by decide +kernel
private theorem endpoint_15_40_p14 : receiptWindow endpoint_15_40_flag endpoint_15_40_sources 0 14 218656975021322699 = some 218656975021322699 :=
  join_receipt_window endpoint_15_40_flag endpoint_15_40_sources 0 12 2 218656975021322699 218656975021322699 218656975021322699 endpoint_15_40_p12 endpoint_15_40_w12
def endpoint_15_40 : CertifiedEndpoint :=
  ⟨⟨15, 40, 3133⟩, 218656975021322699, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_15_40_flag endpoint_15_40_sources 14 218656975021322699 218656975021322699 rfl endpoint_15_40_base endpoint_15_40_p14) (by decide)⟩
private def endpoint_15_41_flag : Flag := ⟨15, 41, 3100⟩
private def endpoint_15_41_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_15_41_base : receiptBase endpoint_15_41_flag endpoint_15_41_sources = some 219926579481143974 := by decide +kernel
private theorem endpoint_15_41_w0 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 2 219926579481143974 = some 220523558194869548 := by decide +kernel
private theorem endpoint_15_41_w2 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 2 2 220523558194869548 = some 220523558194869548 := by decide +kernel
private theorem endpoint_15_41_p4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 4 219926579481143974 = some 220523558194869548 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 2 2 219926579481143974 220523558194869548 220523558194869548 endpoint_15_41_w0 endpoint_15_41_w2
private theorem endpoint_15_41_w4 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 4 2 220523558194869548 = some 220523558194869548 := by decide +kernel
private theorem endpoint_15_41_p6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 6 219926579481143974 = some 220523558194869548 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 4 2 219926579481143974 220523558194869548 220523558194869548 endpoint_15_41_p4 endpoint_15_41_w4
private theorem endpoint_15_41_w6 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 6 2 220523558194869548 = some 220523558194869548 := by decide +kernel
private theorem endpoint_15_41_p8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 8 219926579481143974 = some 220523558194869548 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 6 2 219926579481143974 220523558194869548 220523558194869548 endpoint_15_41_p6 endpoint_15_41_w6
private theorem endpoint_15_41_w8 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 8 2 220523558194869548 = some 220523558194869548 := by decide +kernel
private theorem endpoint_15_41_p10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 10 219926579481143974 = some 220523558194869548 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 8 2 219926579481143974 220523558194869548 220523558194869548 endpoint_15_41_p8 endpoint_15_41_w8
private theorem endpoint_15_41_w10 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 10 2 220523558194869548 = some 220523558194869548 := by decide +kernel
private theorem endpoint_15_41_p12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 12 219926579481143974 = some 220523558194869548 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 10 2 219926579481143974 220523558194869548 220523558194869548 endpoint_15_41_p10 endpoint_15_41_w10
private theorem endpoint_15_41_w12 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 12 2 220523558194869548 = some 220523558194869548 := by decide +kernel
private theorem endpoint_15_41_p14 : receiptWindow endpoint_15_41_flag endpoint_15_41_sources 0 14 219926579481143974 = some 220523558194869548 :=
  join_receipt_window endpoint_15_41_flag endpoint_15_41_sources 0 12 2 219926579481143974 220523558194869548 220523558194869548 endpoint_15_41_p12 endpoint_15_41_w12
def endpoint_15_41 : CertifiedEndpoint :=
  ⟨⟨15, 41, 3100⟩, 220523558194869548, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_15_41_flag endpoint_15_41_sources 14 219926579481143974 220523558194869548 rfl endpoint_15_41_base endpoint_15_41_p14) (by decide)⟩
private def endpoint_15_42_flag : Flag := ⟨15, 42, 3068⟩
private def endpoint_15_42_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_42_base : receiptBase endpoint_15_42_flag endpoint_15_42_sources = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_w0 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 2 223716011805856667 = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_w2 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 2 2 223716011805856667 = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_p4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 4 223716011805856667 = some 223716011805856667 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 2 2 223716011805856667 223716011805856667 223716011805856667 endpoint_15_42_w0 endpoint_15_42_w2
private theorem endpoint_15_42_w4 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 4 2 223716011805856667 = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_p6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 6 223716011805856667 = some 223716011805856667 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 4 2 223716011805856667 223716011805856667 223716011805856667 endpoint_15_42_p4 endpoint_15_42_w4
private theorem endpoint_15_42_w6 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 6 2 223716011805856667 = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_p8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 8 223716011805856667 = some 223716011805856667 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 6 2 223716011805856667 223716011805856667 223716011805856667 endpoint_15_42_p6 endpoint_15_42_w6
private theorem endpoint_15_42_w8 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 8 2 223716011805856667 = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_p10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 10 223716011805856667 = some 223716011805856667 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 8 2 223716011805856667 223716011805856667 223716011805856667 endpoint_15_42_p8 endpoint_15_42_w8
private theorem endpoint_15_42_w10 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 10 2 223716011805856667 = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_p12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 12 223716011805856667 = some 223716011805856667 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 10 2 223716011805856667 223716011805856667 223716011805856667 endpoint_15_42_p10 endpoint_15_42_w10
private theorem endpoint_15_42_w12 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 12 2 223716011805856667 = some 223716011805856667 := by decide +kernel
private theorem endpoint_15_42_p14 : receiptWindow endpoint_15_42_flag endpoint_15_42_sources 0 14 223716011805856667 = some 223716011805856667 :=
  join_receipt_window endpoint_15_42_flag endpoint_15_42_sources 0 12 2 223716011805856667 223716011805856667 223716011805856667 endpoint_15_42_p12 endpoint_15_42_w12
def endpoint_15_42 : CertifiedEndpoint :=
  ⟨⟨15, 42, 3068⟩, 223716011805856667, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_42_flag endpoint_15_42_sources 14 223716011805856667 223716011805856667 rfl endpoint_15_42_base endpoint_15_42_p14) (by decide)⟩
private def endpoint_15_43_flag : Flag := ⟨15, 43, 3034⟩
private def endpoint_15_43_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_43_base : receiptBase endpoint_15_43_flag endpoint_15_43_sources = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_w0 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 2 225715757996498753 = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_w2 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 2 2 225715757996498753 = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_p4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 4 225715757996498753 = some 225715757996498753 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 2 2 225715757996498753 225715757996498753 225715757996498753 endpoint_15_43_w0 endpoint_15_43_w2
private theorem endpoint_15_43_w4 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 4 2 225715757996498753 = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_p6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 6 225715757996498753 = some 225715757996498753 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 4 2 225715757996498753 225715757996498753 225715757996498753 endpoint_15_43_p4 endpoint_15_43_w4
private theorem endpoint_15_43_w6 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 6 2 225715757996498753 = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_p8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 8 225715757996498753 = some 225715757996498753 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 6 2 225715757996498753 225715757996498753 225715757996498753 endpoint_15_43_p6 endpoint_15_43_w6
private theorem endpoint_15_43_w8 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 8 2 225715757996498753 = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_p10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 10 225715757996498753 = some 225715757996498753 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 8 2 225715757996498753 225715757996498753 225715757996498753 endpoint_15_43_p8 endpoint_15_43_w8
private theorem endpoint_15_43_w10 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 10 2 225715757996498753 = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_p12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 12 225715757996498753 = some 225715757996498753 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 10 2 225715757996498753 225715757996498753 225715757996498753 endpoint_15_43_p10 endpoint_15_43_w10
private theorem endpoint_15_43_w12 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 12 2 225715757996498753 = some 225715757996498753 := by decide +kernel
private theorem endpoint_15_43_p14 : receiptWindow endpoint_15_43_flag endpoint_15_43_sources 0 14 225715757996498753 = some 225715757996498753 :=
  join_receipt_window endpoint_15_43_flag endpoint_15_43_sources 0 12 2 225715757996498753 225715757996498753 225715757996498753 endpoint_15_43_p12 endpoint_15_43_w12
def endpoint_15_43 : CertifiedEndpoint :=
  ⟨⟨15, 43, 3034⟩, 225715757996498753, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_43_flag endpoint_15_43_sources 14 225715757996498753 225715757996498753 rfl endpoint_15_43_base endpoint_15_43_p14) (by decide)⟩
private def endpoint_15_44_flag : Flag := ⟨15, 44, 3000⟩
private def endpoint_15_44_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_44_base : receiptBase endpoint_15_44_flag endpoint_15_44_sources = some 227616087411730490 := by decide +kernel
private theorem endpoint_15_44_w0 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 2 227616087411730490 = some 228187978322169540 := by decide +kernel
private theorem endpoint_15_44_w2 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 2 2 228187978322169540 = some 228187978322169540 := by decide +kernel
private theorem endpoint_15_44_p4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 4 227616087411730490 = some 228187978322169540 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 2 2 227616087411730490 228187978322169540 228187978322169540 endpoint_15_44_w0 endpoint_15_44_w2
private theorem endpoint_15_44_w4 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 4 2 228187978322169540 = some 228187978322169540 := by decide +kernel
private theorem endpoint_15_44_p6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 6 227616087411730490 = some 228187978322169540 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 4 2 227616087411730490 228187978322169540 228187978322169540 endpoint_15_44_p4 endpoint_15_44_w4
private theorem endpoint_15_44_w6 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 6 2 228187978322169540 = some 228187978322169540 := by decide +kernel
private theorem endpoint_15_44_p8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 8 227616087411730490 = some 228187978322169540 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 6 2 227616087411730490 228187978322169540 228187978322169540 endpoint_15_44_p6 endpoint_15_44_w6
private theorem endpoint_15_44_w8 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 8 2 228187978322169540 = some 228187978322169540 := by decide +kernel
private theorem endpoint_15_44_p10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 10 227616087411730490 = some 228187978322169540 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 8 2 227616087411730490 228187978322169540 228187978322169540 endpoint_15_44_p8 endpoint_15_44_w8
private theorem endpoint_15_44_w10 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 10 2 228187978322169540 = some 228187978322169540 := by decide +kernel
private theorem endpoint_15_44_p12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 12 227616087411730490 = some 228187978322169540 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 10 2 227616087411730490 228187978322169540 228187978322169540 endpoint_15_44_p10 endpoint_15_44_w10
private theorem endpoint_15_44_w12 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 12 2 228187978322169540 = some 228187978322169540 := by decide +kernel
private theorem endpoint_15_44_p14 : receiptWindow endpoint_15_44_flag endpoint_15_44_sources 0 14 227616087411730490 = some 228187978322169540 :=
  join_receipt_window endpoint_15_44_flag endpoint_15_44_sources 0 12 2 227616087411730490 228187978322169540 228187978322169540 endpoint_15_44_p12 endpoint_15_44_w12
def endpoint_15_44 : CertifiedEndpoint :=
  ⟨⟨15, 44, 3000⟩, 228187978322169540, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_44_flag endpoint_15_44_sources 14 227616087411730490 228187978322169540 rfl endpoint_15_44_base endpoint_15_44_p14) (by decide)⟩
private def endpoint_15_45_flag : Flag := ⟨15, 45, 2965⟩
private def endpoint_15_45_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_45_base : receiptBase endpoint_15_45_flag endpoint_15_45_sources = some 229340762848573089 := by decide +kernel
private theorem endpoint_15_45_w0 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 2 229340762848573089 = some 233100743916598350 := by decide +kernel
private theorem endpoint_15_45_w2 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 2 2 233100743916598350 = some 233100743916598350 := by decide +kernel
private theorem endpoint_15_45_p4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 4 229340762848573089 = some 233100743916598350 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 2 2 229340762848573089 233100743916598350 233100743916598350 endpoint_15_45_w0 endpoint_15_45_w2
private theorem endpoint_15_45_w4 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 4 2 233100743916598350 = some 233100743916598350 := by decide +kernel
private theorem endpoint_15_45_p6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 6 229340762848573089 = some 233100743916598350 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 4 2 229340762848573089 233100743916598350 233100743916598350 endpoint_15_45_p4 endpoint_15_45_w4
private theorem endpoint_15_45_w6 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 6 2 233100743916598350 = some 233100743916598350 := by decide +kernel
private theorem endpoint_15_45_p8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 8 229340762848573089 = some 233100743916598350 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 6 2 229340762848573089 233100743916598350 233100743916598350 endpoint_15_45_p6 endpoint_15_45_w6
private theorem endpoint_15_45_w8 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 8 2 233100743916598350 = some 233100743916598350 := by decide +kernel
private theorem endpoint_15_45_p10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 10 229340762848573089 = some 233100743916598350 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 8 2 229340762848573089 233100743916598350 233100743916598350 endpoint_15_45_p8 endpoint_15_45_w8
private theorem endpoint_15_45_w10 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 10 2 233100743916598350 = some 233100743916598350 := by decide +kernel
private theorem endpoint_15_45_p12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 12 229340762848573089 = some 233100743916598350 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 10 2 229340762848573089 233100743916598350 233100743916598350 endpoint_15_45_p10 endpoint_15_45_w10
private theorem endpoint_15_45_w12 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 12 2 233100743916598350 = some 233100743916598350 := by decide +kernel
private theorem endpoint_15_45_p14 : receiptWindow endpoint_15_45_flag endpoint_15_45_sources 0 14 229340762848573089 = some 233100743916598350 :=
  join_receipt_window endpoint_15_45_flag endpoint_15_45_sources 0 12 2 229340762848573089 233100743916598350 233100743916598350 endpoint_15_45_p12 endpoint_15_45_w12
def endpoint_15_45 : CertifiedEndpoint :=
  ⟨⟨15, 45, 2965⟩, 233100743916598350, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_45_flag endpoint_15_45_sources 14 229340762848573089 233100743916598350 rfl endpoint_15_45_base endpoint_15_45_p14) (by decide)⟩
private def endpoint_15_46_flag : Flag := ⟨15, 46, 2929⟩
private def endpoint_15_46_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_15_46_base : receiptBase endpoint_15_46_flag endpoint_15_46_sources = some 230885461838530447 := by decide +kernel
private theorem endpoint_15_46_w0 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 2 230885461838530447 = some 237887466208612234 := by decide +kernel
private theorem endpoint_15_46_w2 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 2 2 237887466208612234 = some 237887466208612234 := by decide +kernel
private theorem endpoint_15_46_p4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 4 230885461838530447 = some 237887466208612234 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 2 2 230885461838530447 237887466208612234 237887466208612234 endpoint_15_46_w0 endpoint_15_46_w2
private theorem endpoint_15_46_w4 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 4 2 237887466208612234 = some 237887466208612234 := by decide +kernel
private theorem endpoint_15_46_p6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 6 230885461838530447 = some 237887466208612234 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 4 2 230885461838530447 237887466208612234 237887466208612234 endpoint_15_46_p4 endpoint_15_46_w4
private theorem endpoint_15_46_w6 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 6 2 237887466208612234 = some 237887466208612234 := by decide +kernel
private theorem endpoint_15_46_p8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 8 230885461838530447 = some 237887466208612234 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 6 2 230885461838530447 237887466208612234 237887466208612234 endpoint_15_46_p6 endpoint_15_46_w6
private theorem endpoint_15_46_w8 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 8 2 237887466208612234 = some 237887466208612234 := by decide +kernel
private theorem endpoint_15_46_p10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 10 230885461838530447 = some 237887466208612234 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 8 2 230885461838530447 237887466208612234 237887466208612234 endpoint_15_46_p8 endpoint_15_46_w8
private theorem endpoint_15_46_w10 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 10 2 237887466208612234 = some 237887466208612234 := by decide +kernel
private theorem endpoint_15_46_p12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 12 230885461838530447 = some 237887466208612234 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 10 2 230885461838530447 237887466208612234 237887466208612234 endpoint_15_46_p10 endpoint_15_46_w10
private theorem endpoint_15_46_w12 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 12 2 237887466208612234 = some 237887466208612234 := by decide +kernel
private theorem endpoint_15_46_p14 : receiptWindow endpoint_15_46_flag endpoint_15_46_sources 0 14 230885461838530447 = some 237887466208612234 :=
  join_receipt_window endpoint_15_46_flag endpoint_15_46_sources 0 12 2 230885461838530447 237887466208612234 237887466208612234 endpoint_15_46_p12 endpoint_15_46_w12
def endpoint_15_46 : CertifiedEndpoint :=
  ⟨⟨15, 46, 2929⟩, 237887466208612234, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_15_46_flag endpoint_15_46_sources 14 230885461838530447 237887466208612234 rfl endpoint_15_46_base endpoint_15_46_p14) (by decide)⟩
private def endpoint_15_47_flag : Flag := ⟨15, 47, 2892⟩
private def endpoint_15_47_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_47_base : receiptBase endpoint_15_47_flag endpoint_15_47_sources = some 232935898320373144 := by decide +kernel
private theorem endpoint_15_47_w0 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 2 232935898320373144 = some 237182067735665962 := by decide +kernel
private theorem endpoint_15_47_w2 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 2 2 237182067735665962 = some 237182067735665962 := by decide +kernel
private theorem endpoint_15_47_p4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 4 232935898320373144 = some 237182067735665962 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 2 2 232935898320373144 237182067735665962 237182067735665962 endpoint_15_47_w0 endpoint_15_47_w2
private theorem endpoint_15_47_w4 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 4 2 237182067735665962 = some 237182067735665962 := by decide +kernel
private theorem endpoint_15_47_p6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 6 232935898320373144 = some 237182067735665962 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 4 2 232935898320373144 237182067735665962 237182067735665962 endpoint_15_47_p4 endpoint_15_47_w4
private theorem endpoint_15_47_w6 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 6 2 237182067735665962 = some 237182067735665962 := by decide +kernel
private theorem endpoint_15_47_p8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 8 232935898320373144 = some 237182067735665962 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 6 2 232935898320373144 237182067735665962 237182067735665962 endpoint_15_47_p6 endpoint_15_47_w6
private theorem endpoint_15_47_w8 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 8 2 237182067735665962 = some 237182067735665962 := by decide +kernel
private theorem endpoint_15_47_p10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 10 232935898320373144 = some 237182067735665962 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 8 2 232935898320373144 237182067735665962 237182067735665962 endpoint_15_47_p8 endpoint_15_47_w8
private theorem endpoint_15_47_w10 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 10 2 237182067735665962 = some 237182067735665962 := by decide +kernel
private theorem endpoint_15_47_p12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 12 232935898320373144 = some 237182067735665962 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 10 2 232935898320373144 237182067735665962 237182067735665962 endpoint_15_47_p10 endpoint_15_47_w10
private theorem endpoint_15_47_w12 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 12 2 237182067735665962 = some 237182067735665962 := by decide +kernel
private theorem endpoint_15_47_p14 : receiptWindow endpoint_15_47_flag endpoint_15_47_sources 0 14 232935898320373144 = some 237182067735665962 :=
  join_receipt_window endpoint_15_47_flag endpoint_15_47_sources 0 12 2 232935898320373144 237182067735665962 237182067735665962 endpoint_15_47_p12 endpoint_15_47_w12
def endpoint_15_47 : CertifiedEndpoint :=
  ⟨⟨15, 47, 2892⟩, 237182067735665962, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_47_flag endpoint_15_47_sources 14 232935898320373144 237182067735665962 rfl endpoint_15_47_base endpoint_15_47_p14) (by decide)⟩
private def endpoint_15_48_flag : Flag := ⟨15, 48, 2854⟩
private def endpoint_15_48_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_48_base : receiptBase endpoint_15_48_flag endpoint_15_48_sources = some 234118133570336942 := by decide +kernel
private theorem endpoint_15_48_w0 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 2 234118133570336942 = some 241568059506020262 := by decide +kernel
private theorem endpoint_15_48_w2 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 2 2 241568059506020262 = some 241568059506020262 := by decide +kernel
private theorem endpoint_15_48_p4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 4 234118133570336942 = some 241568059506020262 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 2 2 234118133570336942 241568059506020262 241568059506020262 endpoint_15_48_w0 endpoint_15_48_w2
private theorem endpoint_15_48_w4 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 4 2 241568059506020262 = some 241568059506020262 := by decide +kernel
private theorem endpoint_15_48_p6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 6 234118133570336942 = some 241568059506020262 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 4 2 234118133570336942 241568059506020262 241568059506020262 endpoint_15_48_p4 endpoint_15_48_w4
private theorem endpoint_15_48_w6 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 6 2 241568059506020262 = some 241568059506020262 := by decide +kernel
private theorem endpoint_15_48_p8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 8 234118133570336942 = some 241568059506020262 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 6 2 234118133570336942 241568059506020262 241568059506020262 endpoint_15_48_p6 endpoint_15_48_w6
private theorem endpoint_15_48_w8 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 8 2 241568059506020262 = some 241568059506020262 := by decide +kernel
private theorem endpoint_15_48_p10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 10 234118133570336942 = some 241568059506020262 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 8 2 234118133570336942 241568059506020262 241568059506020262 endpoint_15_48_p8 endpoint_15_48_w8
private theorem endpoint_15_48_w10 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 10 2 241568059506020262 = some 241568059506020262 := by decide +kernel
private theorem endpoint_15_48_p12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 12 234118133570336942 = some 241568059506020262 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 10 2 234118133570336942 241568059506020262 241568059506020262 endpoint_15_48_p10 endpoint_15_48_w10
private theorem endpoint_15_48_w12 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 12 2 241568059506020262 = some 241568059506020262 := by decide +kernel
private theorem endpoint_15_48_p14 : receiptWindow endpoint_15_48_flag endpoint_15_48_sources 0 14 234118133570336942 = some 241568059506020262 :=
  join_receipt_window endpoint_15_48_flag endpoint_15_48_sources 0 12 2 234118133570336942 241568059506020262 241568059506020262 endpoint_15_48_p12 endpoint_15_48_w12
def endpoint_15_48 : CertifiedEndpoint :=
  ⟨⟨15, 48, 2854⟩, 241568059506020262, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_48_flag endpoint_15_48_sources 14 234118133570336942 241568059506020262 rfl endpoint_15_48_base endpoint_15_48_p14) (by decide)⟩
private def endpoint_15_49_flag : Flag := ⟨15, 49, 2815⟩
private def endpoint_15_49_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_49_base : receiptBase endpoint_15_49_flag endpoint_15_49_sources = some 235106429159361982 := by decide +kernel
private theorem endpoint_15_49_w0 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 2 235106429159361982 = some 245817725563318737 := by decide +kernel
private theorem endpoint_15_49_w2 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 2 2 245817725563318737 = some 245817725563318737 := by decide +kernel
private theorem endpoint_15_49_p4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 4 235106429159361982 = some 245817725563318737 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 2 2 235106429159361982 245817725563318737 245817725563318737 endpoint_15_49_w0 endpoint_15_49_w2
private theorem endpoint_15_49_w4 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 4 2 245817725563318737 = some 245817725563318737 := by decide +kernel
private theorem endpoint_15_49_p6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 6 235106429159361982 = some 245817725563318737 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 4 2 235106429159361982 245817725563318737 245817725563318737 endpoint_15_49_p4 endpoint_15_49_w4
private theorem endpoint_15_49_w6 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 6 2 245817725563318737 = some 245817725563318737 := by decide +kernel
private theorem endpoint_15_49_p8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 8 235106429159361982 = some 245817725563318737 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 6 2 235106429159361982 245817725563318737 245817725563318737 endpoint_15_49_p6 endpoint_15_49_w6
private theorem endpoint_15_49_w8 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 8 2 245817725563318737 = some 245817725563318737 := by decide +kernel
private theorem endpoint_15_49_p10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 10 235106429159361982 = some 245817725563318737 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 8 2 235106429159361982 245817725563318737 245817725563318737 endpoint_15_49_p8 endpoint_15_49_w8
private theorem endpoint_15_49_w10 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 10 2 245817725563318737 = some 245817725563318737 := by decide +kernel
private theorem endpoint_15_49_p12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 12 235106429159361982 = some 245817725563318737 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 10 2 235106429159361982 245817725563318737 245817725563318737 endpoint_15_49_p10 endpoint_15_49_w10
private theorem endpoint_15_49_w12 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 12 2 245817725563318737 = some 245817725563318737 := by decide +kernel
private theorem endpoint_15_49_p14 : receiptWindow endpoint_15_49_flag endpoint_15_49_sources 0 14 235106429159361982 = some 245817725563318737 :=
  join_receipt_window endpoint_15_49_flag endpoint_15_49_sources 0 12 2 235106429159361982 245817725563318737 245817725563318737 endpoint_15_49_p12 endpoint_15_49_w12
def endpoint_15_49 : CertifiedEndpoint :=
  ⟨⟨15, 49, 2815⟩, 245817725563318737, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_49_flag endpoint_15_49_sources 14 235106429159361982 245817725563318737 rfl endpoint_15_49_base endpoint_15_49_p14) (by decide)⟩
private def endpoint_15_50_flag : Flag := ⟨15, 50, 2775⟩
private def endpoint_15_50_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_15_50_base : receiptBase endpoint_15_50_flag endpoint_15_50_sources = some 235896435616765102 := by decide +kernel
private theorem endpoint_15_50_w0 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 2 235896435616765102 = some 249927638437347754 := by decide +kernel
private theorem endpoint_15_50_w2 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 2 2 249927638437347754 = some 249927638437347754 := by decide +kernel
private theorem endpoint_15_50_p4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 4 235896435616765102 = some 249927638437347754 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 2 2 235896435616765102 249927638437347754 249927638437347754 endpoint_15_50_w0 endpoint_15_50_w2
private theorem endpoint_15_50_w4 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 4 2 249927638437347754 = some 249927638437347754 := by decide +kernel
private theorem endpoint_15_50_p6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 6 235896435616765102 = some 249927638437347754 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 4 2 235896435616765102 249927638437347754 249927638437347754 endpoint_15_50_p4 endpoint_15_50_w4
private theorem endpoint_15_50_w6 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 6 2 249927638437347754 = some 249927638437347754 := by decide +kernel
private theorem endpoint_15_50_p8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 8 235896435616765102 = some 249927638437347754 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 6 2 235896435616765102 249927638437347754 249927638437347754 endpoint_15_50_p6 endpoint_15_50_w6
private theorem endpoint_15_50_w8 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 8 2 249927638437347754 = some 249927638437347754 := by decide +kernel
private theorem endpoint_15_50_p10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 10 235896435616765102 = some 249927638437347754 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 8 2 235896435616765102 249927638437347754 249927638437347754 endpoint_15_50_p8 endpoint_15_50_w8
private theorem endpoint_15_50_w10 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 10 2 249927638437347754 = some 249927638437347754 := by decide +kernel
private theorem endpoint_15_50_p12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 12 235896435616765102 = some 249927638437347754 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 10 2 235896435616765102 249927638437347754 249927638437347754 endpoint_15_50_p10 endpoint_15_50_w10
private theorem endpoint_15_50_w12 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 12 2 249927638437347754 = some 249927638437347754 := by decide +kernel
private theorem endpoint_15_50_p14 : receiptWindow endpoint_15_50_flag endpoint_15_50_sources 0 14 235896435616765102 = some 249927638437347754 :=
  join_receipt_window endpoint_15_50_flag endpoint_15_50_sources 0 12 2 235896435616765102 249927638437347754 249927638437347754 endpoint_15_50_p12 endpoint_15_50_w12
def endpoint_15_50 : CertifiedEndpoint :=
  ⟨⟨15, 50, 2775⟩, 249927638437347754, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_15_50_flag endpoint_15_50_sources 14 235896435616765102 249927638437347754 rfl endpoint_15_50_base endpoint_15_50_p14) (by decide)⟩
private def endpoint_15_51_flag : Flag := ⟨15, 51, 2734⟩
private def endpoint_15_51_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_51_base : receiptBase endpoint_15_51_flag endpoint_15_51_sources = some 237257216331515412 := by decide +kernel
private theorem endpoint_15_51_w0 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 2 237257216331515412 = some 249983730917785371 := by decide +kernel
private theorem endpoint_15_51_w2 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 2 2 249983730917785371 = some 249983730917785371 := by decide +kernel
private theorem endpoint_15_51_p4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 4 237257216331515412 = some 249983730917785371 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 2 2 237257216331515412 249983730917785371 249983730917785371 endpoint_15_51_w0 endpoint_15_51_w2
private theorem endpoint_15_51_w4 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 4 2 249983730917785371 = some 249983730917785371 := by decide +kernel
private theorem endpoint_15_51_p6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 6 237257216331515412 = some 249983730917785371 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 4 2 237257216331515412 249983730917785371 249983730917785371 endpoint_15_51_p4 endpoint_15_51_w4
private theorem endpoint_15_51_w6 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 6 2 249983730917785371 = some 249983730917785371 := by decide +kernel
private theorem endpoint_15_51_p8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 8 237257216331515412 = some 249983730917785371 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 6 2 237257216331515412 249983730917785371 249983730917785371 endpoint_15_51_p6 endpoint_15_51_w6
private theorem endpoint_15_51_w8 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 8 2 249983730917785371 = some 249983730917785371 := by decide +kernel
private theorem endpoint_15_51_p10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 10 237257216331515412 = some 249983730917785371 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 8 2 237257216331515412 249983730917785371 249983730917785371 endpoint_15_51_p8 endpoint_15_51_w8
private theorem endpoint_15_51_w10 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 10 2 249983730917785371 = some 249983730917785371 := by decide +kernel
private theorem endpoint_15_51_p12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 12 237257216331515412 = some 249983730917785371 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 10 2 237257216331515412 249983730917785371 249983730917785371 endpoint_15_51_p10 endpoint_15_51_w10
private theorem endpoint_15_51_w12 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 12 2 249983730917785371 = some 249983730917785371 := by decide +kernel
private theorem endpoint_15_51_p14 : receiptWindow endpoint_15_51_flag endpoint_15_51_sources 0 14 237257216331515412 = some 249983730917785371 :=
  join_receipt_window endpoint_15_51_flag endpoint_15_51_sources 0 12 2 237257216331515412 249983730917785371 249983730917785371 endpoint_15_51_p12 endpoint_15_51_w12
def endpoint_15_51 : CertifiedEndpoint :=
  ⟨⟨15, 51, 2734⟩, 249983730917785371, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_51_flag endpoint_15_51_sources 14 237257216331515412 249983730917785371 rfl endpoint_15_51_base endpoint_15_51_p14) (by decide)⟩
private def endpoint_15_52_flag : Flag := ⟨15, 52, 2692⟩
private def endpoint_15_52_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_15_52_base : receiptBase endpoint_15_52_flag endpoint_15_52_sources = some 237645257747518369 := by decide +kernel
private theorem endpoint_15_52_w0 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 2 237645257747518369 = some 253712395713933480 := by decide +kernel
private theorem endpoint_15_52_w2 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 2 2 253712395713933480 = some 253712395713933480 := by decide +kernel
private theorem endpoint_15_52_p4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 4 237645257747518369 = some 253712395713933480 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 2 2 237645257747518369 253712395713933480 253712395713933480 endpoint_15_52_w0 endpoint_15_52_w2
private theorem endpoint_15_52_w4 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 4 2 253712395713933480 = some 253712395713933480 := by decide +kernel
private theorem endpoint_15_52_p6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 6 237645257747518369 = some 253712395713933480 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 4 2 237645257747518369 253712395713933480 253712395713933480 endpoint_15_52_p4 endpoint_15_52_w4
private theorem endpoint_15_52_w6 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 6 2 253712395713933480 = some 253712395713933480 := by decide +kernel
private theorem endpoint_15_52_p8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 8 237645257747518369 = some 253712395713933480 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 6 2 237645257747518369 253712395713933480 253712395713933480 endpoint_15_52_p6 endpoint_15_52_w6
private theorem endpoint_15_52_w8 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 8 2 253712395713933480 = some 253712395713933480 := by decide +kernel
private theorem endpoint_15_52_p10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 10 237645257747518369 = some 253712395713933480 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 8 2 237645257747518369 253712395713933480 253712395713933480 endpoint_15_52_p8 endpoint_15_52_w8
private theorem endpoint_15_52_w10 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 10 2 253712395713933480 = some 253712395713933480 := by decide +kernel
private theorem endpoint_15_52_p12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 12 237645257747518369 = some 253712395713933480 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 10 2 237645257747518369 253712395713933480 253712395713933480 endpoint_15_52_p10 endpoint_15_52_w10
private theorem endpoint_15_52_w12 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 12 2 253712395713933480 = some 253712395713933480 := by decide +kernel
private theorem endpoint_15_52_p14 : receiptWindow endpoint_15_52_flag endpoint_15_52_sources 0 14 237645257747518369 = some 253712395713933480 :=
  join_receipt_window endpoint_15_52_flag endpoint_15_52_sources 0 12 2 237645257747518369 253712395713933480 253712395713933480 endpoint_15_52_p12 endpoint_15_52_w12
def endpoint_15_52 : CertifiedEndpoint :=
  ⟨⟨15, 52, 2692⟩, 253712395713933480, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_15_52_flag endpoint_15_52_sources 14 237645257747518369 253712395713933480 rfl endpoint_15_52_base endpoint_15_52_p14) (by decide)⟩
private def endpoint_15_53_flag : Flag := ⟨15, 53, 2649⟩
private def endpoint_15_53_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_53_base : receiptBase endpoint_15_53_flag endpoint_15_53_sources = some 238643723716302162 := by decide +kernel
private theorem endpoint_15_53_w0 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 2 238643723716302162 = some 254666949056228607 := by decide +kernel
private theorem endpoint_15_53_w2 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 2 2 254666949056228607 = some 254666949056228607 := by decide +kernel
private theorem endpoint_15_53_p4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 4 238643723716302162 = some 254666949056228607 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 2 2 238643723716302162 254666949056228607 254666949056228607 endpoint_15_53_w0 endpoint_15_53_w2
private theorem endpoint_15_53_w4 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 4 2 254666949056228607 = some 254666949056228607 := by decide +kernel
private theorem endpoint_15_53_p6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 6 238643723716302162 = some 254666949056228607 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 4 2 238643723716302162 254666949056228607 254666949056228607 endpoint_15_53_p4 endpoint_15_53_w4
private theorem endpoint_15_53_w6 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 6 2 254666949056228607 = some 254666949056228607 := by decide +kernel
private theorem endpoint_15_53_p8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 8 238643723716302162 = some 254666949056228607 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 6 2 238643723716302162 254666949056228607 254666949056228607 endpoint_15_53_p6 endpoint_15_53_w6
private theorem endpoint_15_53_w8 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 8 2 254666949056228607 = some 254666949056228607 := by decide +kernel
private theorem endpoint_15_53_p10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 10 238643723716302162 = some 254666949056228607 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 8 2 238643723716302162 254666949056228607 254666949056228607 endpoint_15_53_p8 endpoint_15_53_w8
private theorem endpoint_15_53_w10 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 10 2 254666949056228607 = some 254666949056228607 := by decide +kernel
private theorem endpoint_15_53_p12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 12 238643723716302162 = some 254666949056228607 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 10 2 238643723716302162 254666949056228607 254666949056228607 endpoint_15_53_p10 endpoint_15_53_w10
private theorem endpoint_15_53_w12 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 12 2 254666949056228607 = some 254666949056228607 := by decide +kernel
private theorem endpoint_15_53_p14 : receiptWindow endpoint_15_53_flag endpoint_15_53_sources 0 14 238643723716302162 = some 254666949056228607 :=
  join_receipt_window endpoint_15_53_flag endpoint_15_53_sources 0 12 2 238643723716302162 254666949056228607 254666949056228607 endpoint_15_53_p12 endpoint_15_53_w12
def endpoint_15_53 : CertifiedEndpoint :=
  ⟨⟨15, 53, 2649⟩, 254666949056228607, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_53_flag endpoint_15_53_sources 14 238643723716302162 254666949056228607 rfl endpoint_15_53_base endpoint_15_53_p14) (by decide)⟩
private def endpoint_15_54_flag : Flag := ⟨15, 54, 2604⟩
private def endpoint_15_54_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_15_54_base : receiptBase endpoint_15_54_flag endpoint_15_54_sources = some 238518630283257805 := by decide +kernel
private theorem endpoint_15_54_w0 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 2 238518630283257805 = some 257981766119828448 := by decide +kernel
private theorem endpoint_15_54_w2 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 2 2 257981766119828448 = some 257981766119828448 := by decide +kernel
private theorem endpoint_15_54_p4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 4 238518630283257805 = some 257981766119828448 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 2 2 238518630283257805 257981766119828448 257981766119828448 endpoint_15_54_w0 endpoint_15_54_w2
private theorem endpoint_15_54_w4 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 4 2 257981766119828448 = some 257981766119828448 := by decide +kernel
private theorem endpoint_15_54_p6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 6 238518630283257805 = some 257981766119828448 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 4 2 238518630283257805 257981766119828448 257981766119828448 endpoint_15_54_p4 endpoint_15_54_w4
private theorem endpoint_15_54_w6 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 6 2 257981766119828448 = some 257981766119828448 := by decide +kernel
private theorem endpoint_15_54_p8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 8 238518630283257805 = some 257981766119828448 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 6 2 238518630283257805 257981766119828448 257981766119828448 endpoint_15_54_p6 endpoint_15_54_w6
private theorem endpoint_15_54_w8 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 8 2 257981766119828448 = some 257981766119828448 := by decide +kernel
private theorem endpoint_15_54_p10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 10 238518630283257805 = some 257981766119828448 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 8 2 238518630283257805 257981766119828448 257981766119828448 endpoint_15_54_p8 endpoint_15_54_w8
private theorem endpoint_15_54_w10 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 10 2 257981766119828448 = some 257981766119828448 := by decide +kernel
private theorem endpoint_15_54_p12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 12 238518630283257805 = some 257981766119828448 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 10 2 238518630283257805 257981766119828448 257981766119828448 endpoint_15_54_p10 endpoint_15_54_w10
private theorem endpoint_15_54_w12 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 12 2 257981766119828448 = some 257981766119828448 := by decide +kernel
private theorem endpoint_15_54_p14 : receiptWindow endpoint_15_54_flag endpoint_15_54_sources 0 14 238518630283257805 = some 257981766119828448 :=
  join_receipt_window endpoint_15_54_flag endpoint_15_54_sources 0 12 2 238518630283257805 257981766119828448 257981766119828448 endpoint_15_54_p12 endpoint_15_54_w12
def endpoint_15_54 : CertifiedEndpoint :=
  ⟨⟨15, 54, 2604⟩, 257981766119828448, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_15_54_flag endpoint_15_54_sources 14 238518630283257805 257981766119828448 rfl endpoint_15_54_base endpoint_15_54_p14) (by decide)⟩
private def endpoint_15_55_flag : Flag := ⟨15, 55, 2559⟩
private def endpoint_15_55_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_55_base : receiptBase endpoint_15_55_flag endpoint_15_55_sources = some 238979673751088812 := by decide +kernel
private theorem endpoint_15_55_w0 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 2 238979673751088812 = some 253624196885366650 := by decide +kernel
private theorem endpoint_15_55_w2 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 2 2 253624196885366650 = some 253624196885366650 := by decide +kernel
private theorem endpoint_15_55_p4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 4 238979673751088812 = some 253624196885366650 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 2 2 238979673751088812 253624196885366650 253624196885366650 endpoint_15_55_w0 endpoint_15_55_w2
private theorem endpoint_15_55_w4 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 4 2 253624196885366650 = some 253624196885366650 := by decide +kernel
private theorem endpoint_15_55_p6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 6 238979673751088812 = some 253624196885366650 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 4 2 238979673751088812 253624196885366650 253624196885366650 endpoint_15_55_p4 endpoint_15_55_w4
private theorem endpoint_15_55_w6 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 6 2 253624196885366650 = some 253624196885366650 := by decide +kernel
private theorem endpoint_15_55_p8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 8 238979673751088812 = some 253624196885366650 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 6 2 238979673751088812 253624196885366650 253624196885366650 endpoint_15_55_p6 endpoint_15_55_w6
private theorem endpoint_15_55_w8 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 8 2 253624196885366650 = some 253624196885366650 := by decide +kernel
private theorem endpoint_15_55_p10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 10 238979673751088812 = some 253624196885366650 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 8 2 238979673751088812 253624196885366650 253624196885366650 endpoint_15_55_p8 endpoint_15_55_w8
private theorem endpoint_15_55_w10 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 10 2 253624196885366650 = some 253624196885366650 := by decide +kernel
private theorem endpoint_15_55_p12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 12 238979673751088812 = some 253624196885366650 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 10 2 238979673751088812 253624196885366650 253624196885366650 endpoint_15_55_p10 endpoint_15_55_w10
private theorem endpoint_15_55_w12 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 12 2 253624196885366650 = some 253624196885366650 := by decide +kernel
private theorem endpoint_15_55_p14 : receiptWindow endpoint_15_55_flag endpoint_15_55_sources 0 14 238979673751088812 = some 253624196885366650 :=
  join_receipt_window endpoint_15_55_flag endpoint_15_55_sources 0 12 2 238979673751088812 253624196885366650 253624196885366650 endpoint_15_55_p12 endpoint_15_55_w12
def endpoint_15_55 : CertifiedEndpoint :=
  ⟨⟨15, 55, 2559⟩, 253624196885366650, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_55_flag endpoint_15_55_sources 14 238979673751088812 253624196885366650 rfl endpoint_15_55_base endpoint_15_55_p14) (by decide)⟩
private def endpoint_15_56_flag : Flag := ⟨15, 56, 2512⟩
private def endpoint_15_56_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_56_base : receiptBase endpoint_15_56_flag endpoint_15_56_sources = some 238401820020915712 := by decide +kernel
private theorem endpoint_15_56_w0 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 2 238401820020915712 = some 256456565330931276 := by decide +kernel
private theorem endpoint_15_56_w2 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 2 2 256456565330931276 = some 256456565330931276 := by decide +kernel
private theorem endpoint_15_56_p4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 4 238401820020915712 = some 256456565330931276 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 2 2 238401820020915712 256456565330931276 256456565330931276 endpoint_15_56_w0 endpoint_15_56_w2
private theorem endpoint_15_56_w4 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 4 2 256456565330931276 = some 256456565330931276 := by decide +kernel
private theorem endpoint_15_56_p6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 6 238401820020915712 = some 256456565330931276 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 4 2 238401820020915712 256456565330931276 256456565330931276 endpoint_15_56_p4 endpoint_15_56_w4
private theorem endpoint_15_56_w6 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 6 2 256456565330931276 = some 256456565330931276 := by decide +kernel
private theorem endpoint_15_56_p8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 8 238401820020915712 = some 256456565330931276 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 6 2 238401820020915712 256456565330931276 256456565330931276 endpoint_15_56_p6 endpoint_15_56_w6
private theorem endpoint_15_56_w8 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 8 2 256456565330931276 = some 256456565330931276 := by decide +kernel
private theorem endpoint_15_56_p10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 10 238401820020915712 = some 256456565330931276 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 8 2 238401820020915712 256456565330931276 256456565330931276 endpoint_15_56_p8 endpoint_15_56_w8
private theorem endpoint_15_56_w10 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 10 2 256456565330931276 = some 256456565330931276 := by decide +kernel
private theorem endpoint_15_56_p12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 12 238401820020915712 = some 256456565330931276 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 10 2 238401820020915712 256456565330931276 256456565330931276 endpoint_15_56_p10 endpoint_15_56_w10
private theorem endpoint_15_56_w12 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 12 2 256456565330931276 = some 256456565330931276 := by decide +kernel
private theorem endpoint_15_56_p14 : receiptWindow endpoint_15_56_flag endpoint_15_56_sources 0 14 238401820020915712 = some 256456565330931276 :=
  join_receipt_window endpoint_15_56_flag endpoint_15_56_sources 0 12 2 238401820020915712 256456565330931276 256456565330931276 endpoint_15_56_p12 endpoint_15_56_w12
def endpoint_15_56 : CertifiedEndpoint :=
  ⟨⟨15, 56, 2512⟩, 256456565330931276, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_56_flag endpoint_15_56_sources 14 238401820020915712 256456565330931276 rfl endpoint_15_56_base endpoint_15_56_p14) (by decide)⟩
private def endpoint_15_57_flag : Flag := ⟨15, 57, 2463⟩
private def endpoint_15_57_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_15_57_base : receiptBase endpoint_15_57_flag endpoint_15_57_sources = some 237493616212490590 := by decide +kernel
private theorem endpoint_15_57_w0 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 2 237493616212490590 = some 259067754533720712 := by decide +kernel
private theorem endpoint_15_57_w2 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 2 2 259067754533720712 = some 259067754533720712 := by decide +kernel
private theorem endpoint_15_57_p4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 4 237493616212490590 = some 259067754533720712 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 2 2 237493616212490590 259067754533720712 259067754533720712 endpoint_15_57_w0 endpoint_15_57_w2
private theorem endpoint_15_57_w4 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 4 2 259067754533720712 = some 259067754533720712 := by decide +kernel
private theorem endpoint_15_57_p6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 6 237493616212490590 = some 259067754533720712 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 4 2 237493616212490590 259067754533720712 259067754533720712 endpoint_15_57_p4 endpoint_15_57_w4
private theorem endpoint_15_57_w6 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 6 2 259067754533720712 = some 259067754533720712 := by decide +kernel
private theorem endpoint_15_57_p8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 8 237493616212490590 = some 259067754533720712 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 6 2 237493616212490590 259067754533720712 259067754533720712 endpoint_15_57_p6 endpoint_15_57_w6
private theorem endpoint_15_57_w8 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 8 2 259067754533720712 = some 259067754533720712 := by decide +kernel
private theorem endpoint_15_57_p10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 10 237493616212490590 = some 259067754533720712 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 8 2 237493616212490590 259067754533720712 259067754533720712 endpoint_15_57_p8 endpoint_15_57_w8
private theorem endpoint_15_57_w10 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 10 2 259067754533720712 = some 259067754533720712 := by decide +kernel
private theorem endpoint_15_57_p12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 12 237493616212490590 = some 259067754533720712 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 10 2 237493616212490590 259067754533720712 259067754533720712 endpoint_15_57_p10 endpoint_15_57_w10
private theorem endpoint_15_57_w12 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 12 2 259067754533720712 = some 259067754533720712 := by decide +kernel
private theorem endpoint_15_57_p14 : receiptWindow endpoint_15_57_flag endpoint_15_57_sources 0 14 237493616212490590 = some 259067754533720712 :=
  join_receipt_window endpoint_15_57_flag endpoint_15_57_sources 0 12 2 237493616212490590 259067754533720712 259067754533720712 endpoint_15_57_p12 endpoint_15_57_w12
def endpoint_15_57 : CertifiedEndpoint :=
  ⟨⟨15, 57, 2463⟩, 259067754533720712, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_15_57_flag endpoint_15_57_sources 14 237493616212490590 259067754533720712 rfl endpoint_15_57_base endpoint_15_57_p14) (by decide)⟩
private def endpoint_15_58_flag : Flag := ⟨15, 58, 2414⟩
private def endpoint_15_58_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_58_base : receiptBase endpoint_15_58_flag endpoint_15_58_sources = some 242425708345824439 := by decide +kernel
private theorem endpoint_15_58_w0 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 2 242425708345824439 = some 248494370502986192 := by decide +kernel
private theorem endpoint_15_58_w2 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 2 2 248494370502986192 = some 248494370502986192 := by decide +kernel
private theorem endpoint_15_58_p4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 4 242425708345824439 = some 248494370502986192 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 2 2 242425708345824439 248494370502986192 248494370502986192 endpoint_15_58_w0 endpoint_15_58_w2
private theorem endpoint_15_58_w4 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 4 2 248494370502986192 = some 248494370502986192 := by decide +kernel
private theorem endpoint_15_58_p6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 6 242425708345824439 = some 248494370502986192 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 4 2 242425708345824439 248494370502986192 248494370502986192 endpoint_15_58_p4 endpoint_15_58_w4
private theorem endpoint_15_58_w6 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 6 2 248494370502986192 = some 248494370502986192 := by decide +kernel
private theorem endpoint_15_58_p8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 8 242425708345824439 = some 248494370502986192 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 6 2 242425708345824439 248494370502986192 248494370502986192 endpoint_15_58_p6 endpoint_15_58_w6
private theorem endpoint_15_58_w8 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 8 2 248494370502986192 = some 248494370502986192 := by decide +kernel
private theorem endpoint_15_58_p10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 10 242425708345824439 = some 248494370502986192 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 8 2 242425708345824439 248494370502986192 248494370502986192 endpoint_15_58_p8 endpoint_15_58_w8
private theorem endpoint_15_58_w10 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 10 2 248494370502986192 = some 248494370502986192 := by decide +kernel
private theorem endpoint_15_58_p12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 12 242425708345824439 = some 248494370502986192 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 10 2 242425708345824439 248494370502986192 248494370502986192 endpoint_15_58_p10 endpoint_15_58_w10
private theorem endpoint_15_58_w12 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 12 2 248494370502986192 = some 248494370502986192 := by decide +kernel
private theorem endpoint_15_58_p14 : receiptWindow endpoint_15_58_flag endpoint_15_58_sources 0 14 242425708345824439 = some 248494370502986192 :=
  join_receipt_window endpoint_15_58_flag endpoint_15_58_sources 0 12 2 242425708345824439 248494370502986192 248494370502986192 endpoint_15_58_p12 endpoint_15_58_w12
def endpoint_15_58 : CertifiedEndpoint :=
  ⟨⟨15, 58, 2414⟩, 248494370502986192, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_58_flag endpoint_15_58_sources 14 242425708345824439 248494370502986192 rfl endpoint_15_58_base endpoint_15_58_p14) (by decide)⟩
private def endpoint_15_59_flag : Flag := ⟨15, 59, 2362⟩
private def endpoint_15_59_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_15_59_base : receiptBase endpoint_15_59_flag endpoint_15_59_sources = some 240847354458396052 := by decide +kernel
private theorem endpoint_15_59_w0 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 2 240847354458396052 = some 255439118030213963 := by decide +kernel
private theorem endpoint_15_59_w2 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 2 2 255439118030213963 = some 255439118030213963 := by decide +kernel
private theorem endpoint_15_59_p4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 4 240847354458396052 = some 255439118030213963 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 2 2 240847354458396052 255439118030213963 255439118030213963 endpoint_15_59_w0 endpoint_15_59_w2
private theorem endpoint_15_59_w4 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 4 2 255439118030213963 = some 255439118030213963 := by decide +kernel
private theorem endpoint_15_59_p6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 6 240847354458396052 = some 255439118030213963 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 4 2 240847354458396052 255439118030213963 255439118030213963 endpoint_15_59_p4 endpoint_15_59_w4
private theorem endpoint_15_59_w6 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 6 2 255439118030213963 = some 255439118030213963 := by decide +kernel
private theorem endpoint_15_59_p8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 8 240847354458396052 = some 255439118030213963 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 6 2 240847354458396052 255439118030213963 255439118030213963 endpoint_15_59_p6 endpoint_15_59_w6
private theorem endpoint_15_59_w8 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 8 2 255439118030213963 = some 255439118030213963 := by decide +kernel
private theorem endpoint_15_59_p10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 10 240847354458396052 = some 255439118030213963 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 8 2 240847354458396052 255439118030213963 255439118030213963 endpoint_15_59_p8 endpoint_15_59_w8
private theorem endpoint_15_59_w10 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 10 2 255439118030213963 = some 255439118030213963 := by decide +kernel
private theorem endpoint_15_59_p12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 12 240847354458396052 = some 255439118030213963 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 10 2 240847354458396052 255439118030213963 255439118030213963 endpoint_15_59_p10 endpoint_15_59_w10
private theorem endpoint_15_59_w12 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 12 2 255439118030213963 = some 255439118030213963 := by decide +kernel
private theorem endpoint_15_59_p14 : receiptWindow endpoint_15_59_flag endpoint_15_59_sources 0 14 240847354458396052 = some 255439118030213963 :=
  join_receipt_window endpoint_15_59_flag endpoint_15_59_sources 0 12 2 240847354458396052 255439118030213963 255439118030213963 endpoint_15_59_p12 endpoint_15_59_w12
def endpoint_15_59 : CertifiedEndpoint :=
  ⟨⟨15, 59, 2362⟩, 255439118030213963, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_15_59_flag endpoint_15_59_sources 14 240847354458396052 255439118030213963 rfl endpoint_15_59_base endpoint_15_59_p14) (by decide)⟩
private def endpoint_15_60_flag : Flag := ⟨15, 60, 2310⟩
private def endpoint_15_60_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_60_base : receiptBase endpoint_15_60_flag endpoint_15_60_sources = some 239244287279399131 := by decide +kernel
private theorem endpoint_15_60_w0 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 2 239244287279399131 = some 252262728521991924 := by decide +kernel
private theorem endpoint_15_60_w2 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 2 2 252262728521991924 = some 252262728521991924 := by decide +kernel
private theorem endpoint_15_60_p4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 4 239244287279399131 = some 252262728521991924 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 2 2 239244287279399131 252262728521991924 252262728521991924 endpoint_15_60_w0 endpoint_15_60_w2
private theorem endpoint_15_60_w4 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 4 2 252262728521991924 = some 252262728521991924 := by decide +kernel
private theorem endpoint_15_60_p6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 6 239244287279399131 = some 252262728521991924 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 4 2 239244287279399131 252262728521991924 252262728521991924 endpoint_15_60_p4 endpoint_15_60_w4
private theorem endpoint_15_60_w6 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 6 2 252262728521991924 = some 252262728521991924 := by decide +kernel
private theorem endpoint_15_60_p8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 8 239244287279399131 = some 252262728521991924 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 6 2 239244287279399131 252262728521991924 252262728521991924 endpoint_15_60_p6 endpoint_15_60_w6
private theorem endpoint_15_60_w8 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 8 2 252262728521991924 = some 252262728521991924 := by decide +kernel
private theorem endpoint_15_60_p10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 10 239244287279399131 = some 252262728521991924 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 8 2 239244287279399131 252262728521991924 252262728521991924 endpoint_15_60_p8 endpoint_15_60_w8
private theorem endpoint_15_60_w10 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 10 2 252262728521991924 = some 252262728521991924 := by decide +kernel
private theorem endpoint_15_60_p12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 12 239244287279399131 = some 252262728521991924 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 10 2 239244287279399131 252262728521991924 252262728521991924 endpoint_15_60_p10 endpoint_15_60_w10
private theorem endpoint_15_60_w12 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 12 2 252262728521991924 = some 252262728521991924 := by decide +kernel
private theorem endpoint_15_60_p14 : receiptWindow endpoint_15_60_flag endpoint_15_60_sources 0 14 239244287279399131 = some 252262728521991924 :=
  join_receipt_window endpoint_15_60_flag endpoint_15_60_sources 0 12 2 239244287279399131 252262728521991924 252262728521991924 endpoint_15_60_p12 endpoint_15_60_w12
def endpoint_15_60 : CertifiedEndpoint :=
  ⟨⟨15, 60, 2310⟩, 252262728521991924, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_60_flag endpoint_15_60_sources 14 239244287279399131 252262728521991924 rfl endpoint_15_60_base endpoint_15_60_p14) (by decide)⟩
private def endpoint_15_61_flag : Flag := ⟨15, 61, 2255⟩
private def endpoint_15_61_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_61_base : receiptBase endpoint_15_61_flag endpoint_15_61_sources = some 237113368466231992 := by decide +kernel
private theorem endpoint_15_61_w0 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 2 237113368466231992 = some 253784291435409308 := by decide +kernel
private theorem endpoint_15_61_w2 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 2 2 253784291435409308 = some 253784291435409308 := by decide +kernel
private theorem endpoint_15_61_p4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 4 237113368466231992 = some 253784291435409308 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 2 2 237113368466231992 253784291435409308 253784291435409308 endpoint_15_61_w0 endpoint_15_61_w2
private theorem endpoint_15_61_w4 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 4 2 253784291435409308 = some 253784291435409308 := by decide +kernel
private theorem endpoint_15_61_p6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 6 237113368466231992 = some 253784291435409308 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 4 2 237113368466231992 253784291435409308 253784291435409308 endpoint_15_61_p4 endpoint_15_61_w4
private theorem endpoint_15_61_w6 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 6 2 253784291435409308 = some 253784291435409308 := by decide +kernel
private theorem endpoint_15_61_p8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 8 237113368466231992 = some 253784291435409308 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 6 2 237113368466231992 253784291435409308 253784291435409308 endpoint_15_61_p6 endpoint_15_61_w6
private theorem endpoint_15_61_w8 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 8 2 253784291435409308 = some 253784291435409308 := by decide +kernel
private theorem endpoint_15_61_p10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 10 237113368466231992 = some 253784291435409308 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 8 2 237113368466231992 253784291435409308 253784291435409308 endpoint_15_61_p8 endpoint_15_61_w8
private theorem endpoint_15_61_w10 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 10 2 253784291435409308 = some 253784291435409308 := by decide +kernel
private theorem endpoint_15_61_p12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 12 237113368466231992 = some 253784291435409308 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 10 2 237113368466231992 253784291435409308 253784291435409308 endpoint_15_61_p10 endpoint_15_61_w10
private theorem endpoint_15_61_w12 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 12 2 253784291435409308 = some 253784291435409308 := by decide +kernel
private theorem endpoint_15_61_p14 : receiptWindow endpoint_15_61_flag endpoint_15_61_sources 0 14 237113368466231992 = some 253784291435409308 :=
  join_receipt_window endpoint_15_61_flag endpoint_15_61_sources 0 12 2 237113368466231992 253784291435409308 253784291435409308 endpoint_15_61_p12 endpoint_15_61_w12
def endpoint_15_61 : CertifiedEndpoint :=
  ⟨⟨15, 61, 2255⟩, 253784291435409308, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_61_flag endpoint_15_61_sources 14 237113368466231992 253784291435409308 rfl endpoint_15_61_base endpoint_15_61_p14) (by decide)⟩
private def endpoint_15_62_flag : Flag := ⟨15, 62, 2199⟩
private def endpoint_15_62_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_15_62_base : receiptBase endpoint_15_62_flag endpoint_15_62_sources = some 234714379027098716 := by decide +kernel
private theorem endpoint_15_62_w0 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 2 234714379027098716 = some 255115831602423950 := by decide +kernel
private theorem endpoint_15_62_w2 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 2 2 255115831602423950 = some 255115831602423950 := by decide +kernel
private theorem endpoint_15_62_p4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 4 234714379027098716 = some 255115831602423950 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 2 2 234714379027098716 255115831602423950 255115831602423950 endpoint_15_62_w0 endpoint_15_62_w2
private theorem endpoint_15_62_w4 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 4 2 255115831602423950 = some 255115831602423950 := by decide +kernel
private theorem endpoint_15_62_p6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 6 234714379027098716 = some 255115831602423950 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 4 2 234714379027098716 255115831602423950 255115831602423950 endpoint_15_62_p4 endpoint_15_62_w4
private theorem endpoint_15_62_w6 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 6 2 255115831602423950 = some 255115831602423950 := by decide +kernel
private theorem endpoint_15_62_p8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 8 234714379027098716 = some 255115831602423950 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 6 2 234714379027098716 255115831602423950 255115831602423950 endpoint_15_62_p6 endpoint_15_62_w6
private theorem endpoint_15_62_w8 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 8 2 255115831602423950 = some 255115831602423950 := by decide +kernel
private theorem endpoint_15_62_p10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 10 234714379027098716 = some 255115831602423950 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 8 2 234714379027098716 255115831602423950 255115831602423950 endpoint_15_62_p8 endpoint_15_62_w8
private theorem endpoint_15_62_w10 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 10 2 255115831602423950 = some 255115831602423950 := by decide +kernel
private theorem endpoint_15_62_p12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 12 234714379027098716 = some 255115831602423950 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 10 2 234714379027098716 255115831602423950 255115831602423950 endpoint_15_62_p10 endpoint_15_62_w10
private theorem endpoint_15_62_w12 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 12 2 255115831602423950 = some 255115831602423950 := by decide +kernel
private theorem endpoint_15_62_p14 : receiptWindow endpoint_15_62_flag endpoint_15_62_sources 0 14 234714379027098716 = some 255115831602423950 :=
  join_receipt_window endpoint_15_62_flag endpoint_15_62_sources 0 12 2 234714379027098716 255115831602423950 255115831602423950 endpoint_15_62_p12 endpoint_15_62_w12
def endpoint_15_62 : CertifiedEndpoint :=
  ⟨⟨15, 62, 2199⟩, 255115831602423950, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_15_62_flag endpoint_15_62_sources 14 234714379027098716 255115831602423950 rfl endpoint_15_62_base endpoint_15_62_p14) (by decide)⟩
private def endpoint_15_63_flag : Flag := ⟨15, 63, 2141⟩
private def endpoint_15_63_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_63_base : receiptBase endpoint_15_63_flag endpoint_15_63_sources = some 232944801969960461 := by decide +kernel
private theorem endpoint_15_63_w0 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 2 232944801969960461 = some 243093675836086422 := by decide +kernel
private theorem endpoint_15_63_w2 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 2 2 243093675836086422 = some 243093675836086422 := by decide +kernel
private theorem endpoint_15_63_p4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 4 232944801969960461 = some 243093675836086422 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 2 2 232944801969960461 243093675836086422 243093675836086422 endpoint_15_63_w0 endpoint_15_63_w2
private theorem endpoint_15_63_w4 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 4 2 243093675836086422 = some 243093675836086422 := by decide +kernel
private theorem endpoint_15_63_p6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 6 232944801969960461 = some 243093675836086422 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 4 2 232944801969960461 243093675836086422 243093675836086422 endpoint_15_63_p4 endpoint_15_63_w4
private theorem endpoint_15_63_w6 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 6 2 243093675836086422 = some 243093675836086422 := by decide +kernel
private theorem endpoint_15_63_p8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 8 232944801969960461 = some 243093675836086422 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 6 2 232944801969960461 243093675836086422 243093675836086422 endpoint_15_63_p6 endpoint_15_63_w6
private theorem endpoint_15_63_w8 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 8 2 243093675836086422 = some 243093675836086422 := by decide +kernel
private theorem endpoint_15_63_p10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 10 232944801969960461 = some 243093675836086422 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 8 2 232944801969960461 243093675836086422 243093675836086422 endpoint_15_63_p8 endpoint_15_63_w8
private theorem endpoint_15_63_w10 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 10 2 243093675836086422 = some 243093675836086422 := by decide +kernel
private theorem endpoint_15_63_p12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 12 232944801969960461 = some 243093675836086422 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 10 2 232944801969960461 243093675836086422 243093675836086422 endpoint_15_63_p10 endpoint_15_63_w10
private theorem endpoint_15_63_w12 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 12 2 243093675836086422 = some 243093675836086422 := by decide +kernel
private theorem endpoint_15_63_p14 : receiptWindow endpoint_15_63_flag endpoint_15_63_sources 0 14 232944801969960461 = some 243093675836086422 :=
  join_receipt_window endpoint_15_63_flag endpoint_15_63_sources 0 12 2 232944801969960461 243093675836086422 243093675836086422 endpoint_15_63_p12 endpoint_15_63_w12
def endpoint_15_63 : CertifiedEndpoint :=
  ⟨⟨15, 63, 2141⟩, 243093675836086422, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_63_flag endpoint_15_63_sources 14 232944801969960461 243093675836086422 rfl endpoint_15_63_base endpoint_15_63_p14) (by decide)⟩
private def endpoint_15_64_flag : Flag := ⟨15, 64, 2082⟩
private def endpoint_15_64_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_64_base : receiptBase endpoint_15_64_flag endpoint_15_64_sources = some 229863498012323660 := by decide +kernel
private theorem endpoint_15_64_w0 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 2 229863498012323660 = some 243731398143229640 := by decide +kernel
private theorem endpoint_15_64_w2 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 2 2 243731398143229640 = some 243731398143229640 := by decide +kernel
private theorem endpoint_15_64_p4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 4 229863498012323660 = some 243731398143229640 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 2 2 229863498012323660 243731398143229640 243731398143229640 endpoint_15_64_w0 endpoint_15_64_w2
private theorem endpoint_15_64_w4 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 4 2 243731398143229640 = some 243731398143229640 := by decide +kernel
private theorem endpoint_15_64_p6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 6 229863498012323660 = some 243731398143229640 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 4 2 229863498012323660 243731398143229640 243731398143229640 endpoint_15_64_p4 endpoint_15_64_w4
private theorem endpoint_15_64_w6 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 6 2 243731398143229640 = some 243731398143229640 := by decide +kernel
private theorem endpoint_15_64_p8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 8 229863498012323660 = some 243731398143229640 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 6 2 229863498012323660 243731398143229640 243731398143229640 endpoint_15_64_p6 endpoint_15_64_w6
private theorem endpoint_15_64_w8 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 8 2 243731398143229640 = some 243731398143229640 := by decide +kernel
private theorem endpoint_15_64_p10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 10 229863498012323660 = some 243731398143229640 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 8 2 229863498012323660 243731398143229640 243731398143229640 endpoint_15_64_p8 endpoint_15_64_w8
private theorem endpoint_15_64_w10 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 10 2 243731398143229640 = some 243731398143229640 := by decide +kernel
private theorem endpoint_15_64_p12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 12 229863498012323660 = some 243731398143229640 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 10 2 229863498012323660 243731398143229640 243731398143229640 endpoint_15_64_p10 endpoint_15_64_w10
private theorem endpoint_15_64_w12 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 12 2 243731398143229640 = some 243731398143229640 := by decide +kernel
private theorem endpoint_15_64_p14 : receiptWindow endpoint_15_64_flag endpoint_15_64_sources 0 14 229863498012323660 = some 243731398143229640 :=
  join_receipt_window endpoint_15_64_flag endpoint_15_64_sources 0 12 2 229863498012323660 243731398143229640 243731398143229640 endpoint_15_64_p12 endpoint_15_64_w12
def endpoint_15_64 : CertifiedEndpoint :=
  ⟨⟨15, 64, 2082⟩, 243731398143229640, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_64_flag endpoint_15_64_sources 14 229863498012323660 243731398143229640 rfl endpoint_15_64_base endpoint_15_64_p14) (by decide)⟩
private def endpoint_15_65_flag : Flag := ⟨15, 65, 2020⟩
private def endpoint_15_65_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_15_65_base : receiptBase endpoint_15_65_flag endpoint_15_65_sources = some 226276959979330290 := by decide +kernel
private theorem endpoint_15_65_w0 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 2 226276959979330290 = some 244037952896311661 := by decide +kernel
private theorem endpoint_15_65_w2 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 2 2 244037952896311661 = some 244037952896311661 := by decide +kernel
private theorem endpoint_15_65_p4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 4 226276959979330290 = some 244037952896311661 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 2 2 226276959979330290 244037952896311661 244037952896311661 endpoint_15_65_w0 endpoint_15_65_w2
private theorem endpoint_15_65_w4 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 4 2 244037952896311661 = some 244037952896311661 := by decide +kernel
private theorem endpoint_15_65_p6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 6 226276959979330290 = some 244037952896311661 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 4 2 226276959979330290 244037952896311661 244037952896311661 endpoint_15_65_p4 endpoint_15_65_w4
private theorem endpoint_15_65_w6 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 6 2 244037952896311661 = some 244037952896311661 := by decide +kernel
private theorem endpoint_15_65_p8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 8 226276959979330290 = some 244037952896311661 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 6 2 226276959979330290 244037952896311661 244037952896311661 endpoint_15_65_p6 endpoint_15_65_w6
private theorem endpoint_15_65_w8 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 8 2 244037952896311661 = some 244037952896311661 := by decide +kernel
private theorem endpoint_15_65_p10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 10 226276959979330290 = some 244037952896311661 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 8 2 226276959979330290 244037952896311661 244037952896311661 endpoint_15_65_p8 endpoint_15_65_w8
private theorem endpoint_15_65_w10 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 10 2 244037952896311661 = some 244037952896311661 := by decide +kernel
private theorem endpoint_15_65_p12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 12 226276959979330290 = some 244037952896311661 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 10 2 226276959979330290 244037952896311661 244037952896311661 endpoint_15_65_p10 endpoint_15_65_w10
private theorem endpoint_15_65_w12 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 12 2 244037952896311661 = some 244037952896311661 := by decide +kernel
private theorem endpoint_15_65_p14 : receiptWindow endpoint_15_65_flag endpoint_15_65_sources 0 14 226276959979330290 = some 244037952896311661 :=
  join_receipt_window endpoint_15_65_flag endpoint_15_65_sources 0 12 2 226276959979330290 244037952896311661 244037952896311661 endpoint_15_65_p12 endpoint_15_65_w12
def endpoint_15_65 : CertifiedEndpoint :=
  ⟨⟨15, 65, 2020⟩, 244037952896311661, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_15_65_flag endpoint_15_65_sources 14 226276959979330290 244037952896311661 rfl endpoint_15_65_base endpoint_15_65_p14) (by decide)⟩
private def endpoint_15_66_flag : Flag := ⟨15, 66, 1956⟩
private def endpoint_15_66_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_15_66_base : receiptBase endpoint_15_66_flag endpoint_15_66_sources = some 223528221550418861 := by decide +kernel
private theorem endpoint_15_66_w0 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 2 223528221550418861 = some 237296015484963564 := by decide +kernel
private theorem endpoint_15_66_w2 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 2 2 237296015484963564 = some 237296015484963564 := by decide +kernel
private theorem endpoint_15_66_p4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 4 223528221550418861 = some 237296015484963564 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 2 2 223528221550418861 237296015484963564 237296015484963564 endpoint_15_66_w0 endpoint_15_66_w2
private theorem endpoint_15_66_w4 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 4 2 237296015484963564 = some 237296015484963564 := by decide +kernel
private theorem endpoint_15_66_p6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 6 223528221550418861 = some 237296015484963564 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 4 2 223528221550418861 237296015484963564 237296015484963564 endpoint_15_66_p4 endpoint_15_66_w4
private theorem endpoint_15_66_w6 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 6 2 237296015484963564 = some 237296015484963564 := by decide +kernel
private theorem endpoint_15_66_p8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 8 223528221550418861 = some 237296015484963564 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 6 2 223528221550418861 237296015484963564 237296015484963564 endpoint_15_66_p6 endpoint_15_66_w6
private theorem endpoint_15_66_w8 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 8 2 237296015484963564 = some 237296015484963564 := by decide +kernel
private theorem endpoint_15_66_p10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 10 223528221550418861 = some 237296015484963564 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 8 2 223528221550418861 237296015484963564 237296015484963564 endpoint_15_66_p8 endpoint_15_66_w8
private theorem endpoint_15_66_w10 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 10 2 237296015484963564 = some 237296015484963564 := by decide +kernel
private theorem endpoint_15_66_p12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 12 223528221550418861 = some 237296015484963564 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 10 2 223528221550418861 237296015484963564 237296015484963564 endpoint_15_66_p10 endpoint_15_66_w10
private theorem endpoint_15_66_w12 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 12 2 237296015484963564 = some 237296015484963564 := by decide +kernel
private theorem endpoint_15_66_p14 : receiptWindow endpoint_15_66_flag endpoint_15_66_sources 0 14 223528221550418861 = some 237296015484963564 :=
  join_receipt_window endpoint_15_66_flag endpoint_15_66_sources 0 12 2 223528221550418861 237296015484963564 237296015484963564 endpoint_15_66_p12 endpoint_15_66_w12
def endpoint_15_66 : CertifiedEndpoint :=
  ⟨⟨15, 66, 1956⟩, 237296015484963564, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_15_66_flag endpoint_15_66_sources 14 223528221550418861 237296015484963564 rfl endpoint_15_66_base endpoint_15_66_p14) (by decide)⟩
private def endpoint_15_67_flag : Flag := ⟨15, 67, 1891⟩
private def endpoint_15_67_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_67_base : receiptBase endpoint_15_67_flag endpoint_15_67_sources = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_w0 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 2 222035448645360357 = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_w2 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 2 2 222035448645360357 = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_p4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 4 222035448645360357 = some 222035448645360357 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 2 2 222035448645360357 222035448645360357 222035448645360357 endpoint_15_67_w0 endpoint_15_67_w2
private theorem endpoint_15_67_w4 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 4 2 222035448645360357 = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_p6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 6 222035448645360357 = some 222035448645360357 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 4 2 222035448645360357 222035448645360357 222035448645360357 endpoint_15_67_p4 endpoint_15_67_w4
private theorem endpoint_15_67_w6 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 6 2 222035448645360357 = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_p8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 8 222035448645360357 = some 222035448645360357 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 6 2 222035448645360357 222035448645360357 222035448645360357 endpoint_15_67_p6 endpoint_15_67_w6
private theorem endpoint_15_67_w8 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 8 2 222035448645360357 = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_p10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 10 222035448645360357 = some 222035448645360357 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 8 2 222035448645360357 222035448645360357 222035448645360357 endpoint_15_67_p8 endpoint_15_67_w8
private theorem endpoint_15_67_w10 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 10 2 222035448645360357 = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_p12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 12 222035448645360357 = some 222035448645360357 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 10 2 222035448645360357 222035448645360357 222035448645360357 endpoint_15_67_p10 endpoint_15_67_w10
private theorem endpoint_15_67_w12 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 12 2 222035448645360357 = some 222035448645360357 := by decide +kernel
private theorem endpoint_15_67_p14 : receiptWindow endpoint_15_67_flag endpoint_15_67_sources 0 14 222035448645360357 = some 222035448645360357 :=
  join_receipt_window endpoint_15_67_flag endpoint_15_67_sources 0 12 2 222035448645360357 222035448645360357 222035448645360357 endpoint_15_67_p12 endpoint_15_67_w12
def endpoint_15_67 : CertifiedEndpoint :=
  ⟨⟨15, 67, 1891⟩, 222035448645360357, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_67_flag endpoint_15_67_sources 14 222035448645360357 222035448645360357 rfl endpoint_15_67_base endpoint_15_67_p14) (by decide)⟩
private def endpoint_15_68_flag : Flag := ⟨15, 68, 1822⟩
private def endpoint_15_68_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_68_base : receiptBase endpoint_15_68_flag endpoint_15_68_sources = some 216836069600345305 := by decide +kernel
private theorem endpoint_15_68_w0 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 2 216836069600345305 = some 219450337749392052 := by decide +kernel
private theorem endpoint_15_68_w2 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 2 2 219450337749392052 = some 219450337749392052 := by decide +kernel
private theorem endpoint_15_68_p4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 4 216836069600345305 = some 219450337749392052 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 2 2 216836069600345305 219450337749392052 219450337749392052 endpoint_15_68_w0 endpoint_15_68_w2
private theorem endpoint_15_68_w4 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 4 2 219450337749392052 = some 219450337749392052 := by decide +kernel
private theorem endpoint_15_68_p6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 6 216836069600345305 = some 219450337749392052 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 4 2 216836069600345305 219450337749392052 219450337749392052 endpoint_15_68_p4 endpoint_15_68_w4
private theorem endpoint_15_68_w6 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 6 2 219450337749392052 = some 219450337749392052 := by decide +kernel
private theorem endpoint_15_68_p8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 8 216836069600345305 = some 219450337749392052 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 6 2 216836069600345305 219450337749392052 219450337749392052 endpoint_15_68_p6 endpoint_15_68_w6
private theorem endpoint_15_68_w8 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 8 2 219450337749392052 = some 219450337749392052 := by decide +kernel
private theorem endpoint_15_68_p10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 10 216836069600345305 = some 219450337749392052 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 8 2 216836069600345305 219450337749392052 219450337749392052 endpoint_15_68_p8 endpoint_15_68_w8
private theorem endpoint_15_68_w10 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 10 2 219450337749392052 = some 219450337749392052 := by decide +kernel
private theorem endpoint_15_68_p12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 12 216836069600345305 = some 219450337749392052 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 10 2 216836069600345305 219450337749392052 219450337749392052 endpoint_15_68_p10 endpoint_15_68_w10
private theorem endpoint_15_68_w12 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 12 2 219450337749392052 = some 219450337749392052 := by decide +kernel
private theorem endpoint_15_68_p14 : receiptWindow endpoint_15_68_flag endpoint_15_68_sources 0 14 216836069600345305 = some 219450337749392052 :=
  join_receipt_window endpoint_15_68_flag endpoint_15_68_sources 0 12 2 216836069600345305 219450337749392052 219450337749392052 endpoint_15_68_p12 endpoint_15_68_w12
def endpoint_15_68 : CertifiedEndpoint :=
  ⟨⟨15, 68, 1822⟩, 219450337749392052, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_68_flag endpoint_15_68_sources 14 216836069600345305 219450337749392052 rfl endpoint_15_68_base endpoint_15_68_p14) (by decide)⟩
private def endpoint_15_69_flag : Flag := ⟨15, 69, 1752⟩
private def endpoint_15_69_sources : Sources := ⟨contact12, contact19, contact13⟩
private theorem endpoint_15_69_base : receiptBase endpoint_15_69_flag endpoint_15_69_sources = some 211301933482313152 := by decide +kernel
private theorem endpoint_15_69_w0 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 2 211301933482313152 = some 218213019048491415 := by decide +kernel
private theorem endpoint_15_69_w2 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 2 2 218213019048491415 = some 218213019048491415 := by decide +kernel
private theorem endpoint_15_69_p4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 4 211301933482313152 = some 218213019048491415 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 2 2 211301933482313152 218213019048491415 218213019048491415 endpoint_15_69_w0 endpoint_15_69_w2
private theorem endpoint_15_69_w4 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 4 2 218213019048491415 = some 218213019048491415 := by decide +kernel
private theorem endpoint_15_69_p6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 6 211301933482313152 = some 218213019048491415 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 4 2 211301933482313152 218213019048491415 218213019048491415 endpoint_15_69_p4 endpoint_15_69_w4
private theorem endpoint_15_69_w6 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 6 2 218213019048491415 = some 218213019048491415 := by decide +kernel
private theorem endpoint_15_69_p8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 8 211301933482313152 = some 218213019048491415 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 6 2 211301933482313152 218213019048491415 218213019048491415 endpoint_15_69_p6 endpoint_15_69_w6
private theorem endpoint_15_69_w8 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 8 2 218213019048491415 = some 218213019048491415 := by decide +kernel
private theorem endpoint_15_69_p10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 10 211301933482313152 = some 218213019048491415 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 8 2 211301933482313152 218213019048491415 218213019048491415 endpoint_15_69_p8 endpoint_15_69_w8
private theorem endpoint_15_69_w10 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 10 2 218213019048491415 = some 218213019048491415 := by decide +kernel
private theorem endpoint_15_69_p12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 12 211301933482313152 = some 218213019048491415 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 10 2 211301933482313152 218213019048491415 218213019048491415 endpoint_15_69_p10 endpoint_15_69_w10
private theorem endpoint_15_69_w12 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 12 2 218213019048491415 = some 218213019048491415 := by decide +kernel
private theorem endpoint_15_69_p14 : receiptWindow endpoint_15_69_flag endpoint_15_69_sources 0 14 211301933482313152 = some 218213019048491415 :=
  join_receipt_window endpoint_15_69_flag endpoint_15_69_sources 0 12 2 211301933482313152 218213019048491415 218213019048491415 endpoint_15_69_p12 endpoint_15_69_w12
def endpoint_15_69 : CertifiedEndpoint :=
  ⟨⟨15, 69, 1752⟩, 218213019048491415, .terminal ⟨contact12, contact19, contact13⟩ (finish_receipt_window endpoint_15_69_flag endpoint_15_69_sources 14 211301933482313152 218213019048491415 rfl endpoint_15_69_base endpoint_15_69_p14) (by decide)⟩
private def endpoint_15_70_flag : Flag := ⟨15, 70, 1679⟩
private def endpoint_15_70_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_15_70_base : receiptBase endpoint_15_70_flag endpoint_15_70_sources = some 203913514724840941 := by decide +kernel
private theorem endpoint_15_70_w0 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 2 203913514724840941 = some 217471240115268478 := by decide +kernel
private theorem endpoint_15_70_w2 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 2 2 217471240115268478 = some 217471240115268478 := by decide +kernel
private theorem endpoint_15_70_p4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 4 203913514724840941 = some 217471240115268478 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 2 2 203913514724840941 217471240115268478 217471240115268478 endpoint_15_70_w0 endpoint_15_70_w2
private theorem endpoint_15_70_w4 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 4 2 217471240115268478 = some 217471240115268478 := by decide +kernel
private theorem endpoint_15_70_p6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 6 203913514724840941 = some 217471240115268478 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 4 2 203913514724840941 217471240115268478 217471240115268478 endpoint_15_70_p4 endpoint_15_70_w4
private theorem endpoint_15_70_w6 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 6 2 217471240115268478 = some 217471240115268478 := by decide +kernel
private theorem endpoint_15_70_p8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 8 203913514724840941 = some 217471240115268478 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 6 2 203913514724840941 217471240115268478 217471240115268478 endpoint_15_70_p6 endpoint_15_70_w6
private theorem endpoint_15_70_w8 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 8 2 217471240115268478 = some 217471240115268478 := by decide +kernel
private theorem endpoint_15_70_p10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 10 203913514724840941 = some 217471240115268478 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 8 2 203913514724840941 217471240115268478 217471240115268478 endpoint_15_70_p8 endpoint_15_70_w8
private theorem endpoint_15_70_w10 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 10 2 217471240115268478 = some 217471240115268478 := by decide +kernel
private theorem endpoint_15_70_p12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 12 203913514724840941 = some 217471240115268478 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 10 2 203913514724840941 217471240115268478 217471240115268478 endpoint_15_70_p10 endpoint_15_70_w10
private theorem endpoint_15_70_w12 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 12 2 217471240115268478 = some 217471240115268478 := by decide +kernel
private theorem endpoint_15_70_p14 : receiptWindow endpoint_15_70_flag endpoint_15_70_sources 0 14 203913514724840941 = some 217471240115268478 :=
  join_receipt_window endpoint_15_70_flag endpoint_15_70_sources 0 12 2 203913514724840941 217471240115268478 217471240115268478 endpoint_15_70_p12 endpoint_15_70_w12
def endpoint_15_70 : CertifiedEndpoint :=
  ⟨⟨15, 70, 1679⟩, 217471240115268478, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_15_70_flag endpoint_15_70_sources 14 203913514724840941 217471240115268478 rfl endpoint_15_70_base endpoint_15_70_p14) (by decide)⟩
private def endpoint_15_71_flag : Flag := ⟨15, 71, 1604⟩
private def endpoint_15_71_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_71_base : receiptBase endpoint_15_71_flag endpoint_15_71_sources = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_w0 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 2 200180052018054219 = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_w2 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 2 2 200180052018054219 = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_p4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 4 200180052018054219 = some 200180052018054219 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 2 2 200180052018054219 200180052018054219 200180052018054219 endpoint_15_71_w0 endpoint_15_71_w2
private theorem endpoint_15_71_w4 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 4 2 200180052018054219 = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_p6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 6 200180052018054219 = some 200180052018054219 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 4 2 200180052018054219 200180052018054219 200180052018054219 endpoint_15_71_p4 endpoint_15_71_w4
private theorem endpoint_15_71_w6 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 6 2 200180052018054219 = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_p8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 8 200180052018054219 = some 200180052018054219 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 6 2 200180052018054219 200180052018054219 200180052018054219 endpoint_15_71_p6 endpoint_15_71_w6
private theorem endpoint_15_71_w8 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 8 2 200180052018054219 = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_p10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 10 200180052018054219 = some 200180052018054219 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 8 2 200180052018054219 200180052018054219 200180052018054219 endpoint_15_71_p8 endpoint_15_71_w8
private theorem endpoint_15_71_w10 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 10 2 200180052018054219 = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_p12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 12 200180052018054219 = some 200180052018054219 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 10 2 200180052018054219 200180052018054219 200180052018054219 endpoint_15_71_p10 endpoint_15_71_w10
private theorem endpoint_15_71_w12 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 12 2 200180052018054219 = some 200180052018054219 := by decide +kernel
private theorem endpoint_15_71_p14 : receiptWindow endpoint_15_71_flag endpoint_15_71_sources 0 14 200180052018054219 = some 200180052018054219 :=
  join_receipt_window endpoint_15_71_flag endpoint_15_71_sources 0 12 2 200180052018054219 200180052018054219 200180052018054219 endpoint_15_71_p12 endpoint_15_71_w12
def endpoint_15_71 : CertifiedEndpoint :=
  ⟨⟨15, 71, 1604⟩, 200180052018054219, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_71_flag endpoint_15_71_sources 14 200180052018054219 200180052018054219 rfl endpoint_15_71_base endpoint_15_71_p14) (by decide)⟩
private def endpoint_15_72_flag : Flag := ⟨15, 72, 1527⟩
private def endpoint_15_72_sources : Sources := ⟨contact19, contact19, contact13⟩
private theorem endpoint_15_72_base : receiptBase endpoint_15_72_flag endpoint_15_72_sources = some 193041071330178160 := by decide +kernel
private theorem endpoint_15_72_w0 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 2 193041071330178160 = some 196587019861085868 := by decide +kernel
private theorem endpoint_15_72_w2 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 2 2 196587019861085868 = some 196587019861085868 := by decide +kernel
private theorem endpoint_15_72_p4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 4 193041071330178160 = some 196587019861085868 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 2 2 193041071330178160 196587019861085868 196587019861085868 endpoint_15_72_w0 endpoint_15_72_w2
private theorem endpoint_15_72_w4 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 4 2 196587019861085868 = some 196587019861085868 := by decide +kernel
private theorem endpoint_15_72_p6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 6 193041071330178160 = some 196587019861085868 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 4 2 193041071330178160 196587019861085868 196587019861085868 endpoint_15_72_p4 endpoint_15_72_w4
private theorem endpoint_15_72_w6 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 6 2 196587019861085868 = some 196587019861085868 := by decide +kernel
private theorem endpoint_15_72_p8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 8 193041071330178160 = some 196587019861085868 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 6 2 193041071330178160 196587019861085868 196587019861085868 endpoint_15_72_p6 endpoint_15_72_w6
private theorem endpoint_15_72_w8 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 8 2 196587019861085868 = some 196587019861085868 := by decide +kernel
private theorem endpoint_15_72_p10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 10 193041071330178160 = some 196587019861085868 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 8 2 193041071330178160 196587019861085868 196587019861085868 endpoint_15_72_p8 endpoint_15_72_w8
private theorem endpoint_15_72_w10 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 10 2 196587019861085868 = some 196587019861085868 := by decide +kernel
private theorem endpoint_15_72_p12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 12 193041071330178160 = some 196587019861085868 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 10 2 193041071330178160 196587019861085868 196587019861085868 endpoint_15_72_p10 endpoint_15_72_w10
private theorem endpoint_15_72_w12 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 12 2 196587019861085868 = some 196587019861085868 := by decide +kernel
private theorem endpoint_15_72_p14 : receiptWindow endpoint_15_72_flag endpoint_15_72_sources 0 14 193041071330178160 = some 196587019861085868 :=
  join_receipt_window endpoint_15_72_flag endpoint_15_72_sources 0 12 2 193041071330178160 196587019861085868 196587019861085868 endpoint_15_72_p12 endpoint_15_72_w12
def endpoint_15_72 : CertifiedEndpoint :=
  ⟨⟨15, 72, 1527⟩, 196587019861085868, .terminal ⟨contact19, contact19, contact13⟩ (finish_receipt_window endpoint_15_72_flag endpoint_15_72_sources 14 193041071330178160 196587019861085868 rfl endpoint_15_72_base endpoint_15_72_p14) (by decide)⟩
private def endpoint_15_73_flag : Flag := ⟨15, 73, 1447⟩
private def endpoint_15_73_sources : Sources := ⟨contact19, contact19, contact24⟩
private theorem endpoint_15_73_base : receiptBase endpoint_15_73_flag endpoint_15_73_sources = some 185638706360580684 := by decide +kernel
private theorem endpoint_15_73_w0 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 2 185638706360580684 = some 190658646190990042 := by decide +kernel
private theorem endpoint_15_73_w2 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 2 2 190658646190990042 = some 190658646190990042 := by decide +kernel
private theorem endpoint_15_73_p4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 4 185638706360580684 = some 190658646190990042 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 2 2 185638706360580684 190658646190990042 190658646190990042 endpoint_15_73_w0 endpoint_15_73_w2
private theorem endpoint_15_73_w4 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 4 2 190658646190990042 = some 190658646190990042 := by decide +kernel
private theorem endpoint_15_73_p6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 6 185638706360580684 = some 190658646190990042 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 4 2 185638706360580684 190658646190990042 190658646190990042 endpoint_15_73_p4 endpoint_15_73_w4
private theorem endpoint_15_73_w6 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 6 2 190658646190990042 = some 190658646190990042 := by decide +kernel
private theorem endpoint_15_73_p8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 8 185638706360580684 = some 190658646190990042 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 6 2 185638706360580684 190658646190990042 190658646190990042 endpoint_15_73_p6 endpoint_15_73_w6
private theorem endpoint_15_73_w8 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 8 2 190658646190990042 = some 190658646190990042 := by decide +kernel
private theorem endpoint_15_73_p10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 10 185638706360580684 = some 190658646190990042 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 8 2 185638706360580684 190658646190990042 190658646190990042 endpoint_15_73_p8 endpoint_15_73_w8
private theorem endpoint_15_73_w10 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 10 2 190658646190990042 = some 190658646190990042 := by decide +kernel
private theorem endpoint_15_73_p12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 12 185638706360580684 = some 190658646190990042 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 10 2 185638706360580684 190658646190990042 190658646190990042 endpoint_15_73_p10 endpoint_15_73_w10
private theorem endpoint_15_73_w12 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 12 2 190658646190990042 = some 190658646190990042 := by decide +kernel
private theorem endpoint_15_73_p14 : receiptWindow endpoint_15_73_flag endpoint_15_73_sources 0 14 185638706360580684 = some 190658646190990042 :=
  join_receipt_window endpoint_15_73_flag endpoint_15_73_sources 0 12 2 185638706360580684 190658646190990042 190658646190990042 endpoint_15_73_p12 endpoint_15_73_w12
def endpoint_15_73 : CertifiedEndpoint :=
  ⟨⟨15, 73, 1447⟩, 190658646190990042, .terminal ⟨contact19, contact19, contact24⟩ (finish_receipt_window endpoint_15_73_flag endpoint_15_73_sources 14 185638706360580684 190658646190990042 rfl endpoint_15_73_base endpoint_15_73_p14) (by decide)⟩
private def endpoint_15_74_flag : Flag := ⟨15, 74, 1364⟩
private def endpoint_15_74_sources : Sources := ⟨contact20, contact21, contact22⟩
private theorem endpoint_15_74_base : receiptBase endpoint_15_74_flag endpoint_15_74_sources = some 178396352671694032 := by decide +kernel
private theorem endpoint_15_74_w0 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 2 178396352671694032 = some 179600158236149020 := by decide +kernel
private theorem endpoint_15_74_w2 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 2 2 179600158236149020 = some 179600158236149020 := by decide +kernel
private theorem endpoint_15_74_p4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 4 178396352671694032 = some 179600158236149020 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 2 2 178396352671694032 179600158236149020 179600158236149020 endpoint_15_74_w0 endpoint_15_74_w2
private theorem endpoint_15_74_w4 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 4 2 179600158236149020 = some 179600158236149020 := by decide +kernel
private theorem endpoint_15_74_p6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 6 178396352671694032 = some 179600158236149020 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 4 2 178396352671694032 179600158236149020 179600158236149020 endpoint_15_74_p4 endpoint_15_74_w4
private theorem endpoint_15_74_w6 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 6 2 179600158236149020 = some 179600158236149020 := by decide +kernel
private theorem endpoint_15_74_p8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 8 178396352671694032 = some 179600158236149020 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 6 2 178396352671694032 179600158236149020 179600158236149020 endpoint_15_74_p6 endpoint_15_74_w6
private theorem endpoint_15_74_w8 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 8 2 179600158236149020 = some 179600158236149020 := by decide +kernel
private theorem endpoint_15_74_p10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 10 178396352671694032 = some 179600158236149020 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 8 2 178396352671694032 179600158236149020 179600158236149020 endpoint_15_74_p8 endpoint_15_74_w8
private theorem endpoint_15_74_w10 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 10 2 179600158236149020 = some 179600158236149020 := by decide +kernel
private theorem endpoint_15_74_p12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 12 178396352671694032 = some 179600158236149020 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 10 2 178396352671694032 179600158236149020 179600158236149020 endpoint_15_74_p10 endpoint_15_74_w10
private theorem endpoint_15_74_w12 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 12 2 179600158236149020 = some 179600158236149020 := by decide +kernel
private theorem endpoint_15_74_p14 : receiptWindow endpoint_15_74_flag endpoint_15_74_sources 0 14 178396352671694032 = some 179600158236149020 :=
  join_receipt_window endpoint_15_74_flag endpoint_15_74_sources 0 12 2 178396352671694032 179600158236149020 179600158236149020 endpoint_15_74_p12 endpoint_15_74_w12
def endpoint_15_74 : CertifiedEndpoint :=
  ⟨⟨15, 74, 1364⟩, 179600158236149020, .terminal ⟨contact20, contact21, contact22⟩ (finish_receipt_window endpoint_15_74_flag endpoint_15_74_sources 14 178396352671694032 179600158236149020 rfl endpoint_15_74_base endpoint_15_74_p14) (by decide)⟩
private def endpoint_15_75_flag : Flag := ⟨15, 75, 1279⟩
private def endpoint_15_75_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_75_base : receiptBase endpoint_15_75_flag endpoint_15_75_sources = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_w0 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 2 170890438477619415 = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_w2 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 2 2 170890438477619415 = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_p4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 4 170890438477619415 = some 170890438477619415 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 2 2 170890438477619415 170890438477619415 170890438477619415 endpoint_15_75_w0 endpoint_15_75_w2
private theorem endpoint_15_75_w4 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 4 2 170890438477619415 = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_p6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 6 170890438477619415 = some 170890438477619415 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 4 2 170890438477619415 170890438477619415 170890438477619415 endpoint_15_75_p4 endpoint_15_75_w4
private theorem endpoint_15_75_w6 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 6 2 170890438477619415 = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_p8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 8 170890438477619415 = some 170890438477619415 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 6 2 170890438477619415 170890438477619415 170890438477619415 endpoint_15_75_p6 endpoint_15_75_w6
private theorem endpoint_15_75_w8 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 8 2 170890438477619415 = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_p10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 10 170890438477619415 = some 170890438477619415 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 8 2 170890438477619415 170890438477619415 170890438477619415 endpoint_15_75_p8 endpoint_15_75_w8
private theorem endpoint_15_75_w10 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 10 2 170890438477619415 = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_p12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 12 170890438477619415 = some 170890438477619415 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 10 2 170890438477619415 170890438477619415 170890438477619415 endpoint_15_75_p10 endpoint_15_75_w10
private theorem endpoint_15_75_w12 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 12 2 170890438477619415 = some 170890438477619415 := by decide +kernel
private theorem endpoint_15_75_p14 : receiptWindow endpoint_15_75_flag endpoint_15_75_sources 0 14 170890438477619415 = some 170890438477619415 :=
  join_receipt_window endpoint_15_75_flag endpoint_15_75_sources 0 12 2 170890438477619415 170890438477619415 170890438477619415 endpoint_15_75_p12 endpoint_15_75_w12
def endpoint_15_75 : CertifiedEndpoint :=
  ⟨⟨15, 75, 1279⟩, 170890438477619415, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_75_flag endpoint_15_75_sources 14 170890438477619415 170890438477619415 rfl endpoint_15_75_base endpoint_15_75_p14) (by decide)⟩
private def endpoint_15_76_flag : Flag := ⟨15, 76, 1192⟩
private def endpoint_15_76_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_76_base : receiptBase endpoint_15_76_flag endpoint_15_76_sources = some 161264954472417820 := by decide +kernel
private theorem endpoint_15_76_w0 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 2 161264954472417820 = some 162254013191378522 := by decide +kernel
private theorem endpoint_15_76_w2 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 2 2 162254013191378522 = some 162254013191378522 := by decide +kernel
private theorem endpoint_15_76_p4 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 4 161264954472417820 = some 162254013191378522 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 2 2 161264954472417820 162254013191378522 162254013191378522 endpoint_15_76_w0 endpoint_15_76_w2
private theorem endpoint_15_76_w4 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 4 2 162254013191378522 = some 162254013191378522 := by decide +kernel
private theorem endpoint_15_76_p6 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 6 161264954472417820 = some 162254013191378522 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 4 2 161264954472417820 162254013191378522 162254013191378522 endpoint_15_76_p4 endpoint_15_76_w4
private theorem endpoint_15_76_w6 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 6 2 162254013191378522 = some 162254013191378522 := by decide +kernel
private theorem endpoint_15_76_p8 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 8 161264954472417820 = some 162254013191378522 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 6 2 161264954472417820 162254013191378522 162254013191378522 endpoint_15_76_p6 endpoint_15_76_w6
private theorem endpoint_15_76_w8 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 8 2 162254013191378522 = some 162254013191378522 := by decide +kernel
private theorem endpoint_15_76_p10 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 10 161264954472417820 = some 162254013191378522 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 8 2 161264954472417820 162254013191378522 162254013191378522 endpoint_15_76_p8 endpoint_15_76_w8
private theorem endpoint_15_76_w10 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 10 2 162254013191378522 = some 162254013191378522 := by decide +kernel
private theorem endpoint_15_76_p12 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 12 161264954472417820 = some 162254013191378522 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 10 2 161264954472417820 162254013191378522 162254013191378522 endpoint_15_76_p10 endpoint_15_76_w10
private theorem endpoint_15_76_w12 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 12 2 162254013191378522 = some 162254013191378522 := by decide +kernel
private theorem endpoint_15_76_p14 : receiptWindow endpoint_15_76_flag endpoint_15_76_sources 0 14 161264954472417820 = some 162254013191378522 :=
  join_receipt_window endpoint_15_76_flag endpoint_15_76_sources 0 12 2 161264954472417820 162254013191378522 162254013191378522 endpoint_15_76_p12 endpoint_15_76_w12
def endpoint_15_76 : CertifiedEndpoint :=
  ⟨⟨15, 76, 1192⟩, 162254013191378522, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_76_flag endpoint_15_76_sources 14 161264954472417820 162254013191378522 rfl endpoint_15_76_base endpoint_15_76_p14) (by decide)⟩
private def endpoint_15_77_flag : Flag := ⟨15, 77, 1102⟩
private def endpoint_15_77_sources : Sources := ⟨contact21, contact21, contact26⟩
private theorem endpoint_15_77_base : receiptBase endpoint_15_77_flag endpoint_15_77_sources = some 150962039422764772 := by decide +kernel
private theorem endpoint_15_77_w0 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 2 150962039422764772 = some 157518157802649086 := by decide +kernel
private theorem endpoint_15_77_w2 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 2 2 157518157802649086 = some 157518157802649086 := by decide +kernel
private theorem endpoint_15_77_p4 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 4 150962039422764772 = some 157518157802649086 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 2 2 150962039422764772 157518157802649086 157518157802649086 endpoint_15_77_w0 endpoint_15_77_w2
private theorem endpoint_15_77_w4 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 4 2 157518157802649086 = some 157518157802649086 := by decide +kernel
private theorem endpoint_15_77_p6 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 6 150962039422764772 = some 157518157802649086 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 4 2 150962039422764772 157518157802649086 157518157802649086 endpoint_15_77_p4 endpoint_15_77_w4
private theorem endpoint_15_77_w6 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 6 2 157518157802649086 = some 157518157802649086 := by decide +kernel
private theorem endpoint_15_77_p8 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 8 150962039422764772 = some 157518157802649086 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 6 2 150962039422764772 157518157802649086 157518157802649086 endpoint_15_77_p6 endpoint_15_77_w6
private theorem endpoint_15_77_w8 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 8 2 157518157802649086 = some 157518157802649086 := by decide +kernel
private theorem endpoint_15_77_p10 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 10 150962039422764772 = some 157518157802649086 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 8 2 150962039422764772 157518157802649086 157518157802649086 endpoint_15_77_p8 endpoint_15_77_w8
private theorem endpoint_15_77_w10 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 10 2 157518157802649086 = some 157518157802649086 := by decide +kernel
private theorem endpoint_15_77_p12 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 12 150962039422764772 = some 157518157802649086 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 10 2 150962039422764772 157518157802649086 157518157802649086 endpoint_15_77_p10 endpoint_15_77_w10
private theorem endpoint_15_77_w12 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 12 2 157518157802649086 = some 157518157802649086 := by decide +kernel
private theorem endpoint_15_77_p14 : receiptWindow endpoint_15_77_flag endpoint_15_77_sources 0 14 150962039422764772 = some 157518157802649086 :=
  join_receipt_window endpoint_15_77_flag endpoint_15_77_sources 0 12 2 150962039422764772 157518157802649086 157518157802649086 endpoint_15_77_p12 endpoint_15_77_w12
def endpoint_15_77 : CertifiedEndpoint :=
  ⟨⟨15, 77, 1102⟩, 157518157802649086, .terminal ⟨contact21, contact21, contact26⟩ (finish_receipt_window endpoint_15_77_flag endpoint_15_77_sources 14 150962039422764772 157518157802649086 rfl endpoint_15_77_base endpoint_15_77_p14) (by decide)⟩
def endpoint_15_78 : CertifiedEndpoint :=
  ⟨⟨15, 78, 1009⟩, 253299051589673989, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_79 : CertifiedEndpoint :=
  ⟨⟨15, 79, 914⟩, 231521157523122269, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_80 : CertifiedEndpoint :=
  ⟨⟨15, 80, 816⟩, 208218898558075976, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_81 : CertifiedEndpoint :=
  ⟨⟨15, 81, 716⟩, 183631982825669051, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_82 : CertifiedEndpoint :=
  ⟨⟨15, 82, 613⟩, 157460777319969953, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_83 : CertifiedEndpoint :=
  ⟨⟨15, 83, 507⟩, 129671574298905032, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_84 : CertifiedEndpoint :=
  ⟨⟨15, 84, 399⟩, 100515317807632779, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_85 : CertifiedEndpoint :=
  ⟨⟨15, 85, 288⟩, 69681138926197103, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_15_86 : CertifiedEndpoint :=
  ⟨⟨15, 86, 175⟩, 37427472309106195, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_16 : CertifiedEndpoint :=
  ⟨⟨16, 16, 3621⟩, 127798214411679589, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_17 : CertifiedEndpoint :=
  ⟨⟨16, 17, 3598⟩, 131688984608222434, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_18 : CertifiedEndpoint :=
  ⟨⟨16, 18, 3575⟩, 135519297328725845, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_19 : CertifiedEndpoint :=
  ⟨⟨16, 19, 3551⟩, 148747033348502168, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_20 : CertifiedEndpoint :=
  ⟨⟨16, 20, 3527⟩, 161778621927077493, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_21 : CertifiedEndpoint :=
  ⟨⟨16, 21, 3502⟩, 174564016817138931, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_22 : CertifiedEndpoint :=
  ⟨⟨16, 22, 3477⟩, 187145258247991167, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_23 : CertifiedEndpoint :=
  ⟨⟨16, 23, 3452⟩, 199522346219634201, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_24 : CertifiedEndpoint :=
  ⟨⟨16, 24, 3427⟩, 211695280732068033, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_25 : CertifiedEndpoint :=
  ⟨⟨16, 25, 3401⟩, 223598003501963366, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_26 : CertifiedEndpoint :=
  ⟨⟨16, 26, 3374⟩, 235218505502307894, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_27 : CertifiedEndpoint :=
  ⟨⟨16, 27, 3347⟩, 246618842007426812, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_16_28 : CertifiedEndpoint :=
  ⟨⟨16, 28, 3320⟩, 257799013017320120, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_16_29_flag : Flag := ⟨16, 29, 3292⟩
private def endpoint_16_29_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_29_base : receiptBase endpoint_16_29_flag endpoint_16_29_sources = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_w0 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 2 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_w2 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 2 2 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_p4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 4 180452984438902863 = some 180452984438902863 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 2 2 180452984438902863 180452984438902863 180452984438902863 endpoint_16_29_w0 endpoint_16_29_w2
private theorem endpoint_16_29_w4 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 4 2 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_p6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 6 180452984438902863 = some 180452984438902863 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 4 2 180452984438902863 180452984438902863 180452984438902863 endpoint_16_29_p4 endpoint_16_29_w4
private theorem endpoint_16_29_w6 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 6 2 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_p8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 8 180452984438902863 = some 180452984438902863 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 6 2 180452984438902863 180452984438902863 180452984438902863 endpoint_16_29_p6 endpoint_16_29_w6
private theorem endpoint_16_29_w8 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 8 2 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_p10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 10 180452984438902863 = some 180452984438902863 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 8 2 180452984438902863 180452984438902863 180452984438902863 endpoint_16_29_p8 endpoint_16_29_w8
private theorem endpoint_16_29_w10 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 10 2 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_p12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 12 180452984438902863 = some 180452984438902863 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 10 2 180452984438902863 180452984438902863 180452984438902863 endpoint_16_29_p10 endpoint_16_29_w10
private theorem endpoint_16_29_w12 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 12 2 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_p14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 14 180452984438902863 = some 180452984438902863 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 12 2 180452984438902863 180452984438902863 180452984438902863 endpoint_16_29_p12 endpoint_16_29_w12
private theorem endpoint_16_29_w14 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 14 1 180452984438902863 = some 180452984438902863 := by decide +kernel
private theorem endpoint_16_29_p15 : receiptWindow endpoint_16_29_flag endpoint_16_29_sources 0 15 180452984438902863 = some 180452984438902863 :=
  join_receipt_window endpoint_16_29_flag endpoint_16_29_sources 0 14 1 180452984438902863 180452984438902863 180452984438902863 endpoint_16_29_p14 endpoint_16_29_w14
def endpoint_16_29 : CertifiedEndpoint :=
  ⟨⟨16, 29, 3292⟩, 180452984438902863, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_29_flag endpoint_16_29_sources 15 180452984438902863 180452984438902863 rfl endpoint_16_29_base endpoint_16_29_p15) (by decide)⟩
private def endpoint_16_30_flag : Flag := ⟨16, 30, 3264⟩
private def endpoint_16_30_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_30_base : receiptBase endpoint_16_30_flag endpoint_16_30_sources = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_w0 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 2 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_w2 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 2 2 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_p4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 4 184032367758038399 = some 184032367758038399 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 2 2 184032367758038399 184032367758038399 184032367758038399 endpoint_16_30_w0 endpoint_16_30_w2
private theorem endpoint_16_30_w4 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 4 2 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_p6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 6 184032367758038399 = some 184032367758038399 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 4 2 184032367758038399 184032367758038399 184032367758038399 endpoint_16_30_p4 endpoint_16_30_w4
private theorem endpoint_16_30_w6 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 6 2 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_p8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 8 184032367758038399 = some 184032367758038399 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 6 2 184032367758038399 184032367758038399 184032367758038399 endpoint_16_30_p6 endpoint_16_30_w6
private theorem endpoint_16_30_w8 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 8 2 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_p10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 10 184032367758038399 = some 184032367758038399 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 8 2 184032367758038399 184032367758038399 184032367758038399 endpoint_16_30_p8 endpoint_16_30_w8
private theorem endpoint_16_30_w10 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 10 2 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_p12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 12 184032367758038399 = some 184032367758038399 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 10 2 184032367758038399 184032367758038399 184032367758038399 endpoint_16_30_p10 endpoint_16_30_w10
private theorem endpoint_16_30_w12 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 12 2 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_p14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 14 184032367758038399 = some 184032367758038399 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 12 2 184032367758038399 184032367758038399 184032367758038399 endpoint_16_30_p12 endpoint_16_30_w12
private theorem endpoint_16_30_w14 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 14 1 184032367758038399 = some 184032367758038399 := by decide +kernel
private theorem endpoint_16_30_p15 : receiptWindow endpoint_16_30_flag endpoint_16_30_sources 0 15 184032367758038399 = some 184032367758038399 :=
  join_receipt_window endpoint_16_30_flag endpoint_16_30_sources 0 14 1 184032367758038399 184032367758038399 184032367758038399 endpoint_16_30_p14 endpoint_16_30_w14
def endpoint_16_30 : CertifiedEndpoint :=
  ⟨⟨16, 30, 3264⟩, 184032367758038399, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_30_flag endpoint_16_30_sources 15 184032367758038399 184032367758038399 rfl endpoint_16_30_base endpoint_16_30_p15) (by decide)⟩
private def endpoint_16_31_flag : Flag := ⟨16, 31, 3236⟩
private def endpoint_16_31_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_31_base : receiptBase endpoint_16_31_flag endpoint_16_31_sources = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_w0 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 2 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_w2 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 2 2 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_p4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 4 187524849281682749 = some 187524849281682749 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 2 2 187524849281682749 187524849281682749 187524849281682749 endpoint_16_31_w0 endpoint_16_31_w2
private theorem endpoint_16_31_w4 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 4 2 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_p6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 6 187524849281682749 = some 187524849281682749 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 4 2 187524849281682749 187524849281682749 187524849281682749 endpoint_16_31_p4 endpoint_16_31_w4
private theorem endpoint_16_31_w6 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 6 2 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_p8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 8 187524849281682749 = some 187524849281682749 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 6 2 187524849281682749 187524849281682749 187524849281682749 endpoint_16_31_p6 endpoint_16_31_w6
private theorem endpoint_16_31_w8 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 8 2 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_p10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 10 187524849281682749 = some 187524849281682749 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 8 2 187524849281682749 187524849281682749 187524849281682749 endpoint_16_31_p8 endpoint_16_31_w8
private theorem endpoint_16_31_w10 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 10 2 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_p12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 12 187524849281682749 = some 187524849281682749 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 10 2 187524849281682749 187524849281682749 187524849281682749 endpoint_16_31_p10 endpoint_16_31_w10
private theorem endpoint_16_31_w12 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 12 2 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_p14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 14 187524849281682749 = some 187524849281682749 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 12 2 187524849281682749 187524849281682749 187524849281682749 endpoint_16_31_p12 endpoint_16_31_w12
private theorem endpoint_16_31_w14 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 14 1 187524849281682749 = some 187524849281682749 := by decide +kernel
private theorem endpoint_16_31_p15 : receiptWindow endpoint_16_31_flag endpoint_16_31_sources 0 15 187524849281682749 = some 187524849281682749 :=
  join_receipt_window endpoint_16_31_flag endpoint_16_31_sources 0 14 1 187524849281682749 187524849281682749 187524849281682749 endpoint_16_31_p14 endpoint_16_31_w14
def endpoint_16_31 : CertifiedEndpoint :=
  ⟨⟨16, 31, 3236⟩, 187524849281682749, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_31_flag endpoint_16_31_sources 15 187524849281682749 187524849281682749 rfl endpoint_16_31_base endpoint_16_31_p15) (by decide)⟩
private def endpoint_16_32_flag : Flag := ⟨16, 32, 3206⟩
private def endpoint_16_32_sources : Sources := ⟨contact02, contact03, contact02⟩
private theorem endpoint_16_32_base : receiptBase endpoint_16_32_flag endpoint_16_32_sources = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_w0 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 2 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_w2 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 2 2 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_p4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 4 190813182521776615 = some 190813182521776615 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 2 2 190813182521776615 190813182521776615 190813182521776615 endpoint_16_32_w0 endpoint_16_32_w2
private theorem endpoint_16_32_w4 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 4 2 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_p6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 6 190813182521776615 = some 190813182521776615 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 4 2 190813182521776615 190813182521776615 190813182521776615 endpoint_16_32_p4 endpoint_16_32_w4
private theorem endpoint_16_32_w6 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 6 2 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_p8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 8 190813182521776615 = some 190813182521776615 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 6 2 190813182521776615 190813182521776615 190813182521776615 endpoint_16_32_p6 endpoint_16_32_w6
private theorem endpoint_16_32_w8 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 8 2 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_p10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 10 190813182521776615 = some 190813182521776615 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 8 2 190813182521776615 190813182521776615 190813182521776615 endpoint_16_32_p8 endpoint_16_32_w8
private theorem endpoint_16_32_w10 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 10 2 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_p12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 12 190813182521776615 = some 190813182521776615 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 10 2 190813182521776615 190813182521776615 190813182521776615 endpoint_16_32_p10 endpoint_16_32_w10
private theorem endpoint_16_32_w12 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 12 2 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_p14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 14 190813182521776615 = some 190813182521776615 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 12 2 190813182521776615 190813182521776615 190813182521776615 endpoint_16_32_p12 endpoint_16_32_w12
private theorem endpoint_16_32_w14 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 14 1 190813182521776615 = some 190813182521776615 := by decide +kernel
private theorem endpoint_16_32_p15 : receiptWindow endpoint_16_32_flag endpoint_16_32_sources 0 15 190813182521776615 = some 190813182521776615 :=
  join_receipt_window endpoint_16_32_flag endpoint_16_32_sources 0 14 1 190813182521776615 190813182521776615 190813182521776615 endpoint_16_32_p14 endpoint_16_32_w14
def endpoint_16_32 : CertifiedEndpoint :=
  ⟨⟨16, 32, 3206⟩, 190813182521776615, .terminal ⟨contact02, contact03, contact02⟩ (finish_receipt_window endpoint_16_32_flag endpoint_16_32_sources 15 190813182521776615 190813182521776615 rfl endpoint_16_32_base endpoint_16_32_p15) (by decide)⟩
private def endpoint_16_33_flag : Flag := ⟨16, 33, 3176⟩
private def endpoint_16_33_sources : Sources := ⟨contact27, contact03, contact25⟩
private theorem endpoint_16_33_base : receiptBase endpoint_16_33_flag endpoint_16_33_sources = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_w0 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 2 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_w2 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 2 2 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_p4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 4 195776541580007382 = some 195776541580007382 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 2 2 195776541580007382 195776541580007382 195776541580007382 endpoint_16_33_w0 endpoint_16_33_w2
private theorem endpoint_16_33_w4 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 4 2 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_p6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 6 195776541580007382 = some 195776541580007382 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 4 2 195776541580007382 195776541580007382 195776541580007382 endpoint_16_33_p4 endpoint_16_33_w4
private theorem endpoint_16_33_w6 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 6 2 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_p8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 8 195776541580007382 = some 195776541580007382 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 6 2 195776541580007382 195776541580007382 195776541580007382 endpoint_16_33_p6 endpoint_16_33_w6
private theorem endpoint_16_33_w8 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 8 2 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_p10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 10 195776541580007382 = some 195776541580007382 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 8 2 195776541580007382 195776541580007382 195776541580007382 endpoint_16_33_p8 endpoint_16_33_w8
private theorem endpoint_16_33_w10 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 10 2 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_p12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 12 195776541580007382 = some 195776541580007382 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 10 2 195776541580007382 195776541580007382 195776541580007382 endpoint_16_33_p10 endpoint_16_33_w10
private theorem endpoint_16_33_w12 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 12 2 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_p14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 14 195776541580007382 = some 195776541580007382 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 12 2 195776541580007382 195776541580007382 195776541580007382 endpoint_16_33_p12 endpoint_16_33_w12
private theorem endpoint_16_33_w14 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 14 1 195776541580007382 = some 195776541580007382 := by decide +kernel
private theorem endpoint_16_33_p15 : receiptWindow endpoint_16_33_flag endpoint_16_33_sources 0 15 195776541580007382 = some 195776541580007382 :=
  join_receipt_window endpoint_16_33_flag endpoint_16_33_sources 0 14 1 195776541580007382 195776541580007382 195776541580007382 endpoint_16_33_p14 endpoint_16_33_w14
def endpoint_16_33 : CertifiedEndpoint :=
  ⟨⟨16, 33, 3176⟩, 195776541580007382, .terminal ⟨contact27, contact03, contact25⟩ (finish_receipt_window endpoint_16_33_flag endpoint_16_33_sources 15 195776541580007382 195776541580007382 rfl endpoint_16_33_base endpoint_16_33_p15) (by decide)⟩
private def endpoint_16_34_flag : Flag := ⟨16, 34, 3146⟩
private def endpoint_16_34_sources : Sources := ⟨contact25, contact03, contact25⟩
private theorem endpoint_16_34_base : receiptBase endpoint_16_34_flag endpoint_16_34_sources = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_w0 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 2 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_w2 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 2 2 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_p4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 4 199077202482500810 = some 199077202482500810 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 2 2 199077202482500810 199077202482500810 199077202482500810 endpoint_16_34_w0 endpoint_16_34_w2
private theorem endpoint_16_34_w4 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 4 2 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_p6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 6 199077202482500810 = some 199077202482500810 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 4 2 199077202482500810 199077202482500810 199077202482500810 endpoint_16_34_p4 endpoint_16_34_w4
private theorem endpoint_16_34_w6 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 6 2 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_p8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 8 199077202482500810 = some 199077202482500810 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 6 2 199077202482500810 199077202482500810 199077202482500810 endpoint_16_34_p6 endpoint_16_34_w6
private theorem endpoint_16_34_w8 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 8 2 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_p10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 10 199077202482500810 = some 199077202482500810 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 8 2 199077202482500810 199077202482500810 199077202482500810 endpoint_16_34_p8 endpoint_16_34_w8
private theorem endpoint_16_34_w10 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 10 2 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_p12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 12 199077202482500810 = some 199077202482500810 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 10 2 199077202482500810 199077202482500810 199077202482500810 endpoint_16_34_p10 endpoint_16_34_w10
private theorem endpoint_16_34_w12 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 12 2 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_p14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 14 199077202482500810 = some 199077202482500810 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 12 2 199077202482500810 199077202482500810 199077202482500810 endpoint_16_34_p12 endpoint_16_34_w12
private theorem endpoint_16_34_w14 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 14 1 199077202482500810 = some 199077202482500810 := by decide +kernel
private theorem endpoint_16_34_p15 : receiptWindow endpoint_16_34_flag endpoint_16_34_sources 0 15 199077202482500810 = some 199077202482500810 :=
  join_receipt_window endpoint_16_34_flag endpoint_16_34_sources 0 14 1 199077202482500810 199077202482500810 199077202482500810 endpoint_16_34_p14 endpoint_16_34_w14
def endpoint_16_34 : CertifiedEndpoint :=
  ⟨⟨16, 34, 3146⟩, 199077202482500810, .terminal ⟨contact25, contact03, contact25⟩ (finish_receipt_window endpoint_16_34_flag endpoint_16_34_sources 15 199077202482500810 199077202482500810 rfl endpoint_16_34_base endpoint_16_34_p15) (by decide)⟩
private def endpoint_16_35_flag : Flag := ⟨16, 35, 3115⟩
private def endpoint_16_35_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_35_base : receiptBase endpoint_16_35_flag endpoint_16_35_sources = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_w0 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 2 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_w2 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 2 2 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_p4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 4 203543182501204113 = some 203543182501204113 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 2 2 203543182501204113 203543182501204113 203543182501204113 endpoint_16_35_w0 endpoint_16_35_w2
private theorem endpoint_16_35_w4 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 4 2 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_p6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 6 203543182501204113 = some 203543182501204113 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 4 2 203543182501204113 203543182501204113 203543182501204113 endpoint_16_35_p4 endpoint_16_35_w4
private theorem endpoint_16_35_w6 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 6 2 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_p8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 8 203543182501204113 = some 203543182501204113 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 6 2 203543182501204113 203543182501204113 203543182501204113 endpoint_16_35_p6 endpoint_16_35_w6
private theorem endpoint_16_35_w8 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 8 2 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_p10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 10 203543182501204113 = some 203543182501204113 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 8 2 203543182501204113 203543182501204113 203543182501204113 endpoint_16_35_p8 endpoint_16_35_w8
private theorem endpoint_16_35_w10 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 10 2 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_p12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 12 203543182501204113 = some 203543182501204113 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 10 2 203543182501204113 203543182501204113 203543182501204113 endpoint_16_35_p10 endpoint_16_35_w10
private theorem endpoint_16_35_w12 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 12 2 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_p14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 14 203543182501204113 = some 203543182501204113 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 12 2 203543182501204113 203543182501204113 203543182501204113 endpoint_16_35_p12 endpoint_16_35_w12
private theorem endpoint_16_35_w14 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 14 1 203543182501204113 = some 203543182501204113 := by decide +kernel
private theorem endpoint_16_35_p15 : receiptWindow endpoint_16_35_flag endpoint_16_35_sources 0 15 203543182501204113 = some 203543182501204113 :=
  join_receipt_window endpoint_16_35_flag endpoint_16_35_sources 0 14 1 203543182501204113 203543182501204113 203543182501204113 endpoint_16_35_p14 endpoint_16_35_w14
def endpoint_16_35 : CertifiedEndpoint :=
  ⟨⟨16, 35, 3115⟩, 203543182501204113, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_35_flag endpoint_16_35_sources 15 203543182501204113 203543182501204113 rfl endpoint_16_35_base endpoint_16_35_p15) (by decide)⟩
private def endpoint_16_36_flag : Flag := ⟨16, 36, 3083⟩
private def endpoint_16_36_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_36_base : receiptBase endpoint_16_36_flag endpoint_16_36_sources = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_w0 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 2 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_w2 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 2 2 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_p4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 4 206223409275038495 = some 206223409275038495 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 2 2 206223409275038495 206223409275038495 206223409275038495 endpoint_16_36_w0 endpoint_16_36_w2
private theorem endpoint_16_36_w4 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 4 2 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_p6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 6 206223409275038495 = some 206223409275038495 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 4 2 206223409275038495 206223409275038495 206223409275038495 endpoint_16_36_p4 endpoint_16_36_w4
private theorem endpoint_16_36_w6 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 6 2 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_p8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 8 206223409275038495 = some 206223409275038495 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 6 2 206223409275038495 206223409275038495 206223409275038495 endpoint_16_36_p6 endpoint_16_36_w6
private theorem endpoint_16_36_w8 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 8 2 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_p10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 10 206223409275038495 = some 206223409275038495 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 8 2 206223409275038495 206223409275038495 206223409275038495 endpoint_16_36_p8 endpoint_16_36_w8
private theorem endpoint_16_36_w10 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 10 2 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_p12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 12 206223409275038495 = some 206223409275038495 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 10 2 206223409275038495 206223409275038495 206223409275038495 endpoint_16_36_p10 endpoint_16_36_w10
private theorem endpoint_16_36_w12 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 12 2 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_p14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 14 206223409275038495 = some 206223409275038495 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 12 2 206223409275038495 206223409275038495 206223409275038495 endpoint_16_36_p12 endpoint_16_36_w12
private theorem endpoint_16_36_w14 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 14 1 206223409275038495 = some 206223409275038495 := by decide +kernel
private theorem endpoint_16_36_p15 : receiptWindow endpoint_16_36_flag endpoint_16_36_sources 0 15 206223409275038495 = some 206223409275038495 :=
  join_receipt_window endpoint_16_36_flag endpoint_16_36_sources 0 14 1 206223409275038495 206223409275038495 206223409275038495 endpoint_16_36_p14 endpoint_16_36_w14
def endpoint_16_36 : CertifiedEndpoint :=
  ⟨⟨16, 36, 3083⟩, 206223409275038495, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_36_flag endpoint_16_36_sources 15 206223409275038495 206223409275038495 rfl endpoint_16_36_base endpoint_16_36_p15) (by decide)⟩
private def endpoint_16_37_flag : Flag := ⟨16, 37, 3051⟩
private def endpoint_16_37_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_37_base : receiptBase endpoint_16_37_flag endpoint_16_37_sources = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_w0 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 2 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_w2 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 2 2 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_p4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 4 208805515730645383 = some 208805515730645383 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 2 2 208805515730645383 208805515730645383 208805515730645383 endpoint_16_37_w0 endpoint_16_37_w2
private theorem endpoint_16_37_w4 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 4 2 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_p6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 6 208805515730645383 = some 208805515730645383 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 4 2 208805515730645383 208805515730645383 208805515730645383 endpoint_16_37_p4 endpoint_16_37_w4
private theorem endpoint_16_37_w6 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 6 2 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_p8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 8 208805515730645383 = some 208805515730645383 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 6 2 208805515730645383 208805515730645383 208805515730645383 endpoint_16_37_p6 endpoint_16_37_w6
private theorem endpoint_16_37_w8 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 8 2 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_p10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 10 208805515730645383 = some 208805515730645383 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 8 2 208805515730645383 208805515730645383 208805515730645383 endpoint_16_37_p8 endpoint_16_37_w8
private theorem endpoint_16_37_w10 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 10 2 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_p12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 12 208805515730645383 = some 208805515730645383 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 10 2 208805515730645383 208805515730645383 208805515730645383 endpoint_16_37_p10 endpoint_16_37_w10
private theorem endpoint_16_37_w12 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 12 2 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_p14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 14 208805515730645383 = some 208805515730645383 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 12 2 208805515730645383 208805515730645383 208805515730645383 endpoint_16_37_p12 endpoint_16_37_w12
private theorem endpoint_16_37_w14 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 14 1 208805515730645383 = some 208805515730645383 := by decide +kernel
private theorem endpoint_16_37_p15 : receiptWindow endpoint_16_37_flag endpoint_16_37_sources 0 15 208805515730645383 = some 208805515730645383 :=
  join_receipt_window endpoint_16_37_flag endpoint_16_37_sources 0 14 1 208805515730645383 208805515730645383 208805515730645383 endpoint_16_37_p14 endpoint_16_37_w14
def endpoint_16_37 : CertifiedEndpoint :=
  ⟨⟨16, 37, 3051⟩, 208805515730645383, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_37_flag endpoint_16_37_sources 15 208805515730645383 208805515730645383 rfl endpoint_16_37_base endpoint_16_37_p15) (by decide)⟩
private def endpoint_16_38_flag : Flag := ⟨16, 38, 3018⟩
private def endpoint_16_38_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_16_38_base : receiptBase endpoint_16_38_flag endpoint_16_38_sources = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_w0 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 2 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_w2 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 2 2 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_p4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 4 211220476096205032 = some 211220476096205032 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 2 2 211220476096205032 211220476096205032 211220476096205032 endpoint_16_38_w0 endpoint_16_38_w2
private theorem endpoint_16_38_w4 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 4 2 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_p6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 6 211220476096205032 = some 211220476096205032 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 4 2 211220476096205032 211220476096205032 211220476096205032 endpoint_16_38_p4 endpoint_16_38_w4
private theorem endpoint_16_38_w6 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 6 2 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_p8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 8 211220476096205032 = some 211220476096205032 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 6 2 211220476096205032 211220476096205032 211220476096205032 endpoint_16_38_p6 endpoint_16_38_w6
private theorem endpoint_16_38_w8 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 8 2 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_p10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 10 211220476096205032 = some 211220476096205032 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 8 2 211220476096205032 211220476096205032 211220476096205032 endpoint_16_38_p8 endpoint_16_38_w8
private theorem endpoint_16_38_w10 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 10 2 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_p12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 12 211220476096205032 = some 211220476096205032 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 10 2 211220476096205032 211220476096205032 211220476096205032 endpoint_16_38_p10 endpoint_16_38_w10
private theorem endpoint_16_38_w12 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 12 2 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_p14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 14 211220476096205032 = some 211220476096205032 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 12 2 211220476096205032 211220476096205032 211220476096205032 endpoint_16_38_p12 endpoint_16_38_w12
private theorem endpoint_16_38_w14 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 14 1 211220476096205032 = some 211220476096205032 := by decide +kernel
private theorem endpoint_16_38_p15 : receiptWindow endpoint_16_38_flag endpoint_16_38_sources 0 15 211220476096205032 = some 211220476096205032 :=
  join_receipt_window endpoint_16_38_flag endpoint_16_38_sources 0 14 1 211220476096205032 211220476096205032 211220476096205032 endpoint_16_38_p14 endpoint_16_38_w14
def endpoint_16_38 : CertifiedEndpoint :=
  ⟨⟨16, 38, 3018⟩, 211220476096205032, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_16_38_flag endpoint_16_38_sources 15 211220476096205032 211220476096205032 rfl endpoint_16_38_base endpoint_16_38_p15) (by decide)⟩
private def endpoint_16_39_flag : Flag := ⟨16, 39, 2985⟩
private def endpoint_16_39_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_39_base : receiptBase endpoint_16_39_flag endpoint_16_39_sources = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_w0 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 2 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_w2 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 2 2 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_p4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 4 214042184501218599 = some 214042184501218599 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 2 2 214042184501218599 214042184501218599 214042184501218599 endpoint_16_39_w0 endpoint_16_39_w2
private theorem endpoint_16_39_w4 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 4 2 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_p6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 6 214042184501218599 = some 214042184501218599 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 4 2 214042184501218599 214042184501218599 214042184501218599 endpoint_16_39_p4 endpoint_16_39_w4
private theorem endpoint_16_39_w6 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 6 2 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_p8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 8 214042184501218599 = some 214042184501218599 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 6 2 214042184501218599 214042184501218599 214042184501218599 endpoint_16_39_p6 endpoint_16_39_w6
private theorem endpoint_16_39_w8 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 8 2 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_p10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 10 214042184501218599 = some 214042184501218599 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 8 2 214042184501218599 214042184501218599 214042184501218599 endpoint_16_39_p8 endpoint_16_39_w8
private theorem endpoint_16_39_w10 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 10 2 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_p12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 12 214042184501218599 = some 214042184501218599 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 10 2 214042184501218599 214042184501218599 214042184501218599 endpoint_16_39_p10 endpoint_16_39_w10
private theorem endpoint_16_39_w12 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 12 2 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_p14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 14 214042184501218599 = some 214042184501218599 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 12 2 214042184501218599 214042184501218599 214042184501218599 endpoint_16_39_p12 endpoint_16_39_w12
private theorem endpoint_16_39_w14 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 14 1 214042184501218599 = some 214042184501218599 := by decide +kernel
private theorem endpoint_16_39_p15 : receiptWindow endpoint_16_39_flag endpoint_16_39_sources 0 15 214042184501218599 = some 214042184501218599 :=
  join_receipt_window endpoint_16_39_flag endpoint_16_39_sources 0 14 1 214042184501218599 214042184501218599 214042184501218599 endpoint_16_39_p14 endpoint_16_39_w14
def endpoint_16_39 : CertifiedEndpoint :=
  ⟨⟨16, 39, 2985⟩, 214042184501218599, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_39_flag endpoint_16_39_sources 15 214042184501218599 214042184501218599 rfl endpoint_16_39_base endpoint_16_39_p15) (by decide)⟩
private def endpoint_16_40_flag : Flag := ⟨16, 40, 2950⟩
private def endpoint_16_40_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_40_base : receiptBase endpoint_16_40_flag endpoint_16_40_sources = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_w0 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 2 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_w2 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 2 2 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_p4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 4 216125592891151335 = some 216125592891151335 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 2 2 216125592891151335 216125592891151335 216125592891151335 endpoint_16_40_w0 endpoint_16_40_w2
private theorem endpoint_16_40_w4 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 4 2 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_p6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 6 216125592891151335 = some 216125592891151335 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 4 2 216125592891151335 216125592891151335 216125592891151335 endpoint_16_40_p4 endpoint_16_40_w4
private theorem endpoint_16_40_w6 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 6 2 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_p8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 8 216125592891151335 = some 216125592891151335 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 6 2 216125592891151335 216125592891151335 216125592891151335 endpoint_16_40_p6 endpoint_16_40_w6
private theorem endpoint_16_40_w8 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 8 2 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_p10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 10 216125592891151335 = some 216125592891151335 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 8 2 216125592891151335 216125592891151335 216125592891151335 endpoint_16_40_p8 endpoint_16_40_w8
private theorem endpoint_16_40_w10 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 10 2 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_p12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 12 216125592891151335 = some 216125592891151335 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 10 2 216125592891151335 216125592891151335 216125592891151335 endpoint_16_40_p10 endpoint_16_40_w10
private theorem endpoint_16_40_w12 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 12 2 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_p14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 14 216125592891151335 = some 216125592891151335 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 12 2 216125592891151335 216125592891151335 216125592891151335 endpoint_16_40_p12 endpoint_16_40_w12
private theorem endpoint_16_40_w14 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 14 1 216125592891151335 = some 216125592891151335 := by decide +kernel
private theorem endpoint_16_40_p15 : receiptWindow endpoint_16_40_flag endpoint_16_40_sources 0 15 216125592891151335 = some 216125592891151335 :=
  join_receipt_window endpoint_16_40_flag endpoint_16_40_sources 0 14 1 216125592891151335 216125592891151335 216125592891151335 endpoint_16_40_p14 endpoint_16_40_w14
def endpoint_16_40 : CertifiedEndpoint :=
  ⟨⟨16, 40, 2950⟩, 216125592891151335, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_40_flag endpoint_16_40_sources 15 216125592891151335 216125592891151335 rfl endpoint_16_40_base endpoint_16_40_p15) (by decide)⟩
private def endpoint_16_41_flag : Flag := ⟨16, 41, 2915⟩
private def endpoint_16_41_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_41_base : receiptBase endpoint_16_41_flag endpoint_16_41_sources = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_w0 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 2 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_w2 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 2 2 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_p4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 4 218101184650952068 = some 218101184650952068 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 2 2 218101184650952068 218101184650952068 218101184650952068 endpoint_16_41_w0 endpoint_16_41_w2
private theorem endpoint_16_41_w4 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 4 2 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_p6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 6 218101184650952068 = some 218101184650952068 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 4 2 218101184650952068 218101184650952068 218101184650952068 endpoint_16_41_p4 endpoint_16_41_w4
private theorem endpoint_16_41_w6 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 6 2 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_p8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 8 218101184650952068 = some 218101184650952068 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 6 2 218101184650952068 218101184650952068 218101184650952068 endpoint_16_41_p6 endpoint_16_41_w6
private theorem endpoint_16_41_w8 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 8 2 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_p10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 10 218101184650952068 = some 218101184650952068 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 8 2 218101184650952068 218101184650952068 218101184650952068 endpoint_16_41_p8 endpoint_16_41_w8
private theorem endpoint_16_41_w10 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 10 2 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_p12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 12 218101184650952068 = some 218101184650952068 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 10 2 218101184650952068 218101184650952068 218101184650952068 endpoint_16_41_p10 endpoint_16_41_w10
private theorem endpoint_16_41_w12 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 12 2 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_p14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 14 218101184650952068 = some 218101184650952068 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 12 2 218101184650952068 218101184650952068 218101184650952068 endpoint_16_41_p12 endpoint_16_41_w12
private theorem endpoint_16_41_w14 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 14 1 218101184650952068 = some 218101184650952068 := by decide +kernel
private theorem endpoint_16_41_p15 : receiptWindow endpoint_16_41_flag endpoint_16_41_sources 0 15 218101184650952068 = some 218101184650952068 :=
  join_receipt_window endpoint_16_41_flag endpoint_16_41_sources 0 14 1 218101184650952068 218101184650952068 218101184650952068 endpoint_16_41_p14 endpoint_16_41_w14
def endpoint_16_41 : CertifiedEndpoint :=
  ⟨⟨16, 41, 2915⟩, 218101184650952068, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_41_flag endpoint_16_41_sources 15 218101184650952068 218101184650952068 rfl endpoint_16_41_base endpoint_16_41_p15) (by decide)⟩
private def endpoint_16_42_flag : Flag := ⟨16, 42, 2879⟩
private def endpoint_16_42_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_16_42_base : receiptBase endpoint_16_42_flag endpoint_16_42_sources = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_w0 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 2 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_w2 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 2 2 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_p4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 4 219893665088773172 = some 219893665088773172 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 2 2 219893665088773172 219893665088773172 219893665088773172 endpoint_16_42_w0 endpoint_16_42_w2
private theorem endpoint_16_42_w4 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 4 2 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_p6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 6 219893665088773172 = some 219893665088773172 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 4 2 219893665088773172 219893665088773172 219893665088773172 endpoint_16_42_p4 endpoint_16_42_w4
private theorem endpoint_16_42_w6 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 6 2 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_p8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 8 219893665088773172 = some 219893665088773172 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 6 2 219893665088773172 219893665088773172 219893665088773172 endpoint_16_42_p6 endpoint_16_42_w6
private theorem endpoint_16_42_w8 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 8 2 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_p10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 10 219893665088773172 = some 219893665088773172 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 8 2 219893665088773172 219893665088773172 219893665088773172 endpoint_16_42_p8 endpoint_16_42_w8
private theorem endpoint_16_42_w10 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 10 2 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_p12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 12 219893665088773172 = some 219893665088773172 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 10 2 219893665088773172 219893665088773172 219893665088773172 endpoint_16_42_p10 endpoint_16_42_w10
private theorem endpoint_16_42_w12 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 12 2 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_p14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 14 219893665088773172 = some 219893665088773172 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 12 2 219893665088773172 219893665088773172 219893665088773172 endpoint_16_42_p12 endpoint_16_42_w12
private theorem endpoint_16_42_w14 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 14 1 219893665088773172 = some 219893665088773172 := by decide +kernel
private theorem endpoint_16_42_p15 : receiptWindow endpoint_16_42_flag endpoint_16_42_sources 0 15 219893665088773172 = some 219893665088773172 :=
  join_receipt_window endpoint_16_42_flag endpoint_16_42_sources 0 14 1 219893665088773172 219893665088773172 219893665088773172 endpoint_16_42_p14 endpoint_16_42_w14
def endpoint_16_42 : CertifiedEndpoint :=
  ⟨⟨16, 42, 2879⟩, 219893665088773172, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_16_42_flag endpoint_16_42_sources 15 219893665088773172 219893665088773172 rfl endpoint_16_42_base endpoint_16_42_p15) (by decide)⟩
private def endpoint_16_43_flag : Flag := ⟨16, 43, 2842⟩
private def endpoint_16_43_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_43_base : receiptBase endpoint_16_43_flag endpoint_16_43_sources = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_w0 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 2 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_w2 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 2 2 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_p4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 4 222098924462412910 = some 222098924462412910 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 2 2 222098924462412910 222098924462412910 222098924462412910 endpoint_16_43_w0 endpoint_16_43_w2
private theorem endpoint_16_43_w4 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 4 2 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_p6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 6 222098924462412910 = some 222098924462412910 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 4 2 222098924462412910 222098924462412910 222098924462412910 endpoint_16_43_p4 endpoint_16_43_w4
private theorem endpoint_16_43_w6 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 6 2 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_p8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 8 222098924462412910 = some 222098924462412910 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 6 2 222098924462412910 222098924462412910 222098924462412910 endpoint_16_43_p6 endpoint_16_43_w6
private theorem endpoint_16_43_w8 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 8 2 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_p10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 10 222098924462412910 = some 222098924462412910 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 8 2 222098924462412910 222098924462412910 222098924462412910 endpoint_16_43_p8 endpoint_16_43_w8
private theorem endpoint_16_43_w10 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 10 2 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_p12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 12 222098924462412910 = some 222098924462412910 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 10 2 222098924462412910 222098924462412910 222098924462412910 endpoint_16_43_p10 endpoint_16_43_w10
private theorem endpoint_16_43_w12 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 12 2 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_p14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 14 222098924462412910 = some 222098924462412910 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 12 2 222098924462412910 222098924462412910 222098924462412910 endpoint_16_43_p12 endpoint_16_43_w12
private theorem endpoint_16_43_w14 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 14 1 222098924462412910 = some 222098924462412910 := by decide +kernel
private theorem endpoint_16_43_p15 : receiptWindow endpoint_16_43_flag endpoint_16_43_sources 0 15 222098924462412910 = some 222098924462412910 :=
  join_receipt_window endpoint_16_43_flag endpoint_16_43_sources 0 14 1 222098924462412910 222098924462412910 222098924462412910 endpoint_16_43_p14 endpoint_16_43_w14
def endpoint_16_43 : CertifiedEndpoint :=
  ⟨⟨16, 43, 2842⟩, 222098924462412910, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_43_flag endpoint_16_43_sources 15 222098924462412910 222098924462412910 rfl endpoint_16_43_base endpoint_16_43_p15) (by decide)⟩
private def endpoint_16_44_flag : Flag := ⟨16, 44, 2805⟩
private def endpoint_16_44_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_44_base : receiptBase endpoint_16_44_flag endpoint_16_44_sources = some 223603023329993504 := by decide +kernel
private theorem endpoint_16_44_w0 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 2 223603023329993504 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_w2 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 2 2 224597226783143832 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_p4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 4 223603023329993504 = some 224597226783143832 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 2 2 223603023329993504 224597226783143832 224597226783143832 endpoint_16_44_w0 endpoint_16_44_w2
private theorem endpoint_16_44_w4 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 4 2 224597226783143832 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_p6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 6 223603023329993504 = some 224597226783143832 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 4 2 223603023329993504 224597226783143832 224597226783143832 endpoint_16_44_p4 endpoint_16_44_w4
private theorem endpoint_16_44_w6 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 6 2 224597226783143832 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_p8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 8 223603023329993504 = some 224597226783143832 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 6 2 223603023329993504 224597226783143832 224597226783143832 endpoint_16_44_p6 endpoint_16_44_w6
private theorem endpoint_16_44_w8 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 8 2 224597226783143832 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_p10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 10 223603023329993504 = some 224597226783143832 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 8 2 223603023329993504 224597226783143832 224597226783143832 endpoint_16_44_p8 endpoint_16_44_w8
private theorem endpoint_16_44_w10 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 10 2 224597226783143832 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_p12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 12 223603023329993504 = some 224597226783143832 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 10 2 223603023329993504 224597226783143832 224597226783143832 endpoint_16_44_p10 endpoint_16_44_w10
private theorem endpoint_16_44_w12 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 12 2 224597226783143832 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_p14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 14 223603023329993504 = some 224597226783143832 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 12 2 223603023329993504 224597226783143832 224597226783143832 endpoint_16_44_p12 endpoint_16_44_w12
private theorem endpoint_16_44_w14 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 14 1 224597226783143832 = some 224597226783143832 := by decide +kernel
private theorem endpoint_16_44_p15 : receiptWindow endpoint_16_44_flag endpoint_16_44_sources 0 15 223603023329993504 = some 224597226783143832 :=
  join_receipt_window endpoint_16_44_flag endpoint_16_44_sources 0 14 1 223603023329993504 224597226783143832 224597226783143832 endpoint_16_44_p14 endpoint_16_44_w14
def endpoint_16_44 : CertifiedEndpoint :=
  ⟨⟨16, 44, 2805⟩, 224597226783143832, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_44_flag endpoint_16_44_sources 15 223603023329993504 224597226783143832 rfl endpoint_16_44_base endpoint_16_44_p15) (by decide)⟩
private def endpoint_16_45_flag : Flag := ⟨16, 45, 2767⟩
private def endpoint_16_45_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_16_45_base : receiptBase endpoint_16_45_flag endpoint_16_45_sources = some 224912448263527836 := by decide +kernel
private theorem endpoint_16_45_w0 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 2 224912448263527836 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_w2 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 2 2 229277164659460404 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_p4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 4 224912448263527836 = some 229277164659460404 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 2 2 224912448263527836 229277164659460404 229277164659460404 endpoint_16_45_w0 endpoint_16_45_w2
private theorem endpoint_16_45_w4 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 4 2 229277164659460404 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_p6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 6 224912448263527836 = some 229277164659460404 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 4 2 224912448263527836 229277164659460404 229277164659460404 endpoint_16_45_p4 endpoint_16_45_w4
private theorem endpoint_16_45_w6 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 6 2 229277164659460404 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_p8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 8 224912448263527836 = some 229277164659460404 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 6 2 224912448263527836 229277164659460404 229277164659460404 endpoint_16_45_p6 endpoint_16_45_w6
private theorem endpoint_16_45_w8 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 8 2 229277164659460404 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_p10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 10 224912448263527836 = some 229277164659460404 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 8 2 224912448263527836 229277164659460404 229277164659460404 endpoint_16_45_p8 endpoint_16_45_w8
private theorem endpoint_16_45_w10 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 10 2 229277164659460404 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_p12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 12 224912448263527836 = some 229277164659460404 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 10 2 224912448263527836 229277164659460404 229277164659460404 endpoint_16_45_p10 endpoint_16_45_w10
private theorem endpoint_16_45_w12 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 12 2 229277164659460404 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_p14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 14 224912448263527836 = some 229277164659460404 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 12 2 224912448263527836 229277164659460404 229277164659460404 endpoint_16_45_p12 endpoint_16_45_w12
private theorem endpoint_16_45_w14 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 14 1 229277164659460404 = some 229277164659460404 := by decide +kernel
private theorem endpoint_16_45_p15 : receiptWindow endpoint_16_45_flag endpoint_16_45_sources 0 15 224912448263527836 = some 229277164659460404 :=
  join_receipt_window endpoint_16_45_flag endpoint_16_45_sources 0 14 1 224912448263527836 229277164659460404 229277164659460404 endpoint_16_45_p14 endpoint_16_45_w14
def endpoint_16_45 : CertifiedEndpoint :=
  ⟨⟨16, 45, 2767⟩, 229277164659460404, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_16_45_flag endpoint_16_45_sources 15 224912448263527836 229277164659460404 rfl endpoint_16_45_base endpoint_16_45_p15) (by decide)⟩
private def endpoint_16_46_flag : Flag := ⟨16, 46, 2727⟩
private def endpoint_16_46_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_46_base : receiptBase endpoint_16_46_flag endpoint_16_46_sources = some 226565597377941248 := by decide +kernel
private theorem endpoint_16_46_w0 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 2 226565597377941248 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_w2 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 2 2 232644630722259142 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_p4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 4 226565597377941248 = some 232644630722259142 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 2 2 226565597377941248 232644630722259142 232644630722259142 endpoint_16_46_w0 endpoint_16_46_w2
private theorem endpoint_16_46_w4 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 4 2 232644630722259142 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_p6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 6 226565597377941248 = some 232644630722259142 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 4 2 226565597377941248 232644630722259142 232644630722259142 endpoint_16_46_p4 endpoint_16_46_w4
private theorem endpoint_16_46_w6 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 6 2 232644630722259142 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_p8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 8 226565597377941248 = some 232644630722259142 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 6 2 226565597377941248 232644630722259142 232644630722259142 endpoint_16_46_p6 endpoint_16_46_w6
private theorem endpoint_16_46_w8 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 8 2 232644630722259142 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_p10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 10 226565597377941248 = some 232644630722259142 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 8 2 226565597377941248 232644630722259142 232644630722259142 endpoint_16_46_p8 endpoint_16_46_w8
private theorem endpoint_16_46_w10 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 10 2 232644630722259142 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_p12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 12 226565597377941248 = some 232644630722259142 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 10 2 226565597377941248 232644630722259142 232644630722259142 endpoint_16_46_p10 endpoint_16_46_w10
private theorem endpoint_16_46_w12 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 12 2 232644630722259142 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_p14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 14 226565597377941248 = some 232644630722259142 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 12 2 226565597377941248 232644630722259142 232644630722259142 endpoint_16_46_p12 endpoint_16_46_w12
private theorem endpoint_16_46_w14 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 14 1 232644630722259142 = some 232644630722259142 := by decide +kernel
private theorem endpoint_16_46_p15 : receiptWindow endpoint_16_46_flag endpoint_16_46_sources 0 15 226565597377941248 = some 232644630722259142 :=
  join_receipt_window endpoint_16_46_flag endpoint_16_46_sources 0 14 1 226565597377941248 232644630722259142 232644630722259142 endpoint_16_46_p14 endpoint_16_46_w14
def endpoint_16_46 : CertifiedEndpoint :=
  ⟨⟨16, 46, 2727⟩, 232644630722259142, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_46_flag endpoint_16_46_sources 15 226565597377941248 232644630722259142 rfl endpoint_16_46_base endpoint_16_46_p15) (by decide)⟩
private def endpoint_16_47_flag : Flag := ⟨16, 47, 2687⟩
private def endpoint_16_47_sources : Sources := ⟨contact30, contact08, contact04⟩
private theorem endpoint_16_47_base : receiptBase endpoint_16_47_flag endpoint_16_47_sources = some 227501299884151207 := by decide +kernel
private theorem endpoint_16_47_w0 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 2 227501299884151207 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_w2 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 2 2 237004911892086682 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_p4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 4 227501299884151207 = some 237004911892086682 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 2 2 227501299884151207 237004911892086682 237004911892086682 endpoint_16_47_w0 endpoint_16_47_w2
private theorem endpoint_16_47_w4 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 4 2 237004911892086682 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_p6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 6 227501299884151207 = some 237004911892086682 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 4 2 227501299884151207 237004911892086682 237004911892086682 endpoint_16_47_p4 endpoint_16_47_w4
private theorem endpoint_16_47_w6 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 6 2 237004911892086682 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_p8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 8 227501299884151207 = some 237004911892086682 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 6 2 227501299884151207 237004911892086682 237004911892086682 endpoint_16_47_p6 endpoint_16_47_w6
private theorem endpoint_16_47_w8 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 8 2 237004911892086682 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_p10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 10 227501299884151207 = some 237004911892086682 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 8 2 227501299884151207 237004911892086682 237004911892086682 endpoint_16_47_p8 endpoint_16_47_w8
private theorem endpoint_16_47_w10 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 10 2 237004911892086682 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_p12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 12 227501299884151207 = some 237004911892086682 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 10 2 227501299884151207 237004911892086682 237004911892086682 endpoint_16_47_p10 endpoint_16_47_w10
private theorem endpoint_16_47_w12 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 12 2 237004911892086682 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_p14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 14 227501299884151207 = some 237004911892086682 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 12 2 227501299884151207 237004911892086682 237004911892086682 endpoint_16_47_p12 endpoint_16_47_w12
private theorem endpoint_16_47_w14 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 14 1 237004911892086682 = some 237004911892086682 := by decide +kernel
private theorem endpoint_16_47_p15 : receiptWindow endpoint_16_47_flag endpoint_16_47_sources 0 15 227501299884151207 = some 237004911892086682 :=
  join_receipt_window endpoint_16_47_flag endpoint_16_47_sources 0 14 1 227501299884151207 237004911892086682 237004911892086682 endpoint_16_47_p14 endpoint_16_47_w14
def endpoint_16_47 : CertifiedEndpoint :=
  ⟨⟨16, 47, 2687⟩, 237004911892086682, .terminal ⟨contact30, contact08, contact04⟩ (finish_receipt_window endpoint_16_47_flag endpoint_16_47_sources 15 227501299884151207 237004911892086682 rfl endpoint_16_47_base endpoint_16_47_p15) (by decide)⟩
private def endpoint_16_48_flag : Flag := ⟨16, 48, 2646⟩
private def endpoint_16_48_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_48_base : receiptBase endpoint_16_48_flag endpoint_16_48_sources = some 228820948604318549 := by decide +kernel
private theorem endpoint_16_48_w0 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 2 228820948604318549 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_w2 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 2 2 233115041809623104 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_p4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 4 228820948604318549 = some 233115041809623104 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 2 2 228820948604318549 233115041809623104 233115041809623104 endpoint_16_48_w0 endpoint_16_48_w2
private theorem endpoint_16_48_w4 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 4 2 233115041809623104 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_p6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 6 228820948604318549 = some 233115041809623104 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 4 2 228820948604318549 233115041809623104 233115041809623104 endpoint_16_48_p4 endpoint_16_48_w4
private theorem endpoint_16_48_w6 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 6 2 233115041809623104 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_p8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 8 228820948604318549 = some 233115041809623104 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 6 2 228820948604318549 233115041809623104 233115041809623104 endpoint_16_48_p6 endpoint_16_48_w6
private theorem endpoint_16_48_w8 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 8 2 233115041809623104 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_p10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 10 228820948604318549 = some 233115041809623104 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 8 2 228820948604318549 233115041809623104 233115041809623104 endpoint_16_48_p8 endpoint_16_48_w8
private theorem endpoint_16_48_w10 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 10 2 233115041809623104 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_p12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 12 228820948604318549 = some 233115041809623104 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 10 2 228820948604318549 233115041809623104 233115041809623104 endpoint_16_48_p10 endpoint_16_48_w10
private theorem endpoint_16_48_w12 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 12 2 233115041809623104 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_p14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 14 228820948604318549 = some 233115041809623104 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 12 2 228820948604318549 233115041809623104 233115041809623104 endpoint_16_48_p12 endpoint_16_48_w12
private theorem endpoint_16_48_w14 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 14 1 233115041809623104 = some 233115041809623104 := by decide +kernel
private theorem endpoint_16_48_p15 : receiptWindow endpoint_16_48_flag endpoint_16_48_sources 0 15 228820948604318549 = some 233115041809623104 :=
  join_receipt_window endpoint_16_48_flag endpoint_16_48_sources 0 14 1 228820948604318549 233115041809623104 233115041809623104 endpoint_16_48_p14 endpoint_16_48_w14
def endpoint_16_48 : CertifiedEndpoint :=
  ⟨⟨16, 48, 2646⟩, 233115041809623104, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_48_flag endpoint_16_48_sources 15 228820948604318549 233115041809623104 rfl endpoint_16_48_base endpoint_16_48_p15) (by decide)⟩
private def endpoint_16_49_flag : Flag := ⟨16, 49, 2604⟩
private def endpoint_16_49_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_49_base : receiptBase endpoint_16_49_flag endpoint_16_49_sources = some 229319707263185359 := by decide +kernel
private theorem endpoint_16_49_w0 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 2 229319707263185359 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_w2 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 2 2 236965970045065517 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_p4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 4 229319707263185359 = some 236965970045065517 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 2 2 229319707263185359 236965970045065517 236965970045065517 endpoint_16_49_w0 endpoint_16_49_w2
private theorem endpoint_16_49_w4 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 4 2 236965970045065517 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_p6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 6 229319707263185359 = some 236965970045065517 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 4 2 229319707263185359 236965970045065517 236965970045065517 endpoint_16_49_p4 endpoint_16_49_w4
private theorem endpoint_16_49_w6 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 6 2 236965970045065517 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_p8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 8 229319707263185359 = some 236965970045065517 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 6 2 229319707263185359 236965970045065517 236965970045065517 endpoint_16_49_p6 endpoint_16_49_w6
private theorem endpoint_16_49_w8 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 8 2 236965970045065517 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_p10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 10 229319707263185359 = some 236965970045065517 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 8 2 229319707263185359 236965970045065517 236965970045065517 endpoint_16_49_p8 endpoint_16_49_w8
private theorem endpoint_16_49_w10 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 10 2 236965970045065517 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_p12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 12 229319707263185359 = some 236965970045065517 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 10 2 229319707263185359 236965970045065517 236965970045065517 endpoint_16_49_p10 endpoint_16_49_w10
private theorem endpoint_16_49_w12 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 12 2 236965970045065517 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_p14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 14 229319707263185359 = some 236965970045065517 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 12 2 229319707263185359 236965970045065517 236965970045065517 endpoint_16_49_p12 endpoint_16_49_w12
private theorem endpoint_16_49_w14 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 14 1 236965970045065517 = some 236965970045065517 := by decide +kernel
private theorem endpoint_16_49_p15 : receiptWindow endpoint_16_49_flag endpoint_16_49_sources 0 15 229319707263185359 = some 236965970045065517 :=
  join_receipt_window endpoint_16_49_flag endpoint_16_49_sources 0 14 1 229319707263185359 236965970045065517 236965970045065517 endpoint_16_49_p14 endpoint_16_49_w14
def endpoint_16_49 : CertifiedEndpoint :=
  ⟨⟨16, 49, 2604⟩, 236965970045065517, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_49_flag endpoint_16_49_sources 15 229319707263185359 236965970045065517 rfl endpoint_16_49_base endpoint_16_49_p15) (by decide)⟩
private def endpoint_16_50_flag : Flag := ⟨16, 50, 2561⟩
private def endpoint_16_50_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_50_base : receiptBase endpoint_16_50_flag endpoint_16_50_sources = some 229598743572043470 := by decide +kernel
private theorem endpoint_16_50_w0 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 2 229598743572043470 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_w2 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 2 2 240659887491083794 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_p4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 4 229598743572043470 = some 240659887491083794 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 2 2 229598743572043470 240659887491083794 240659887491083794 endpoint_16_50_w0 endpoint_16_50_w2
private theorem endpoint_16_50_w4 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 4 2 240659887491083794 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_p6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 6 229598743572043470 = some 240659887491083794 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 4 2 229598743572043470 240659887491083794 240659887491083794 endpoint_16_50_p4 endpoint_16_50_w4
private theorem endpoint_16_50_w6 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 6 2 240659887491083794 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_p8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 8 229598743572043470 = some 240659887491083794 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 6 2 229598743572043470 240659887491083794 240659887491083794 endpoint_16_50_p6 endpoint_16_50_w6
private theorem endpoint_16_50_w8 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 8 2 240659887491083794 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_p10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 10 229598743572043470 = some 240659887491083794 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 8 2 229598743572043470 240659887491083794 240659887491083794 endpoint_16_50_p8 endpoint_16_50_w8
private theorem endpoint_16_50_w10 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 10 2 240659887491083794 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_p12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 12 229598743572043470 = some 240659887491083794 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 10 2 229598743572043470 240659887491083794 240659887491083794 endpoint_16_50_p10 endpoint_16_50_w10
private theorem endpoint_16_50_w12 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 12 2 240659887491083794 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_p14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 14 229598743572043470 = some 240659887491083794 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 12 2 229598743572043470 240659887491083794 240659887491083794 endpoint_16_50_p12 endpoint_16_50_w12
private theorem endpoint_16_50_w14 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 14 1 240659887491083794 = some 240659887491083794 := by decide +kernel
private theorem endpoint_16_50_p15 : receiptWindow endpoint_16_50_flag endpoint_16_50_sources 0 15 229598743572043470 = some 240659887491083794 :=
  join_receipt_window endpoint_16_50_flag endpoint_16_50_sources 0 14 1 229598743572043470 240659887491083794 240659887491083794 endpoint_16_50_p14 endpoint_16_50_w14
def endpoint_16_50 : CertifiedEndpoint :=
  ⟨⟨16, 50, 2561⟩, 240659887491083794, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_50_flag endpoint_16_50_sources 15 229598743572043470 240659887491083794 rfl endpoint_16_50_base endpoint_16_50_p15) (by decide)⟩
private def endpoint_16_51_flag : Flag := ⟨16, 51, 2517⟩
private def endpoint_16_51_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_51_base : receiptBase endpoint_16_51_flag endpoint_16_51_sources = some 229653420901186522 := by decide +kernel
private theorem endpoint_16_51_w0 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 2 229653420901186522 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_w2 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 2 2 244193108973135050 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_p4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 4 229653420901186522 = some 244193108973135050 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 2 2 229653420901186522 244193108973135050 244193108973135050 endpoint_16_51_w0 endpoint_16_51_w2
private theorem endpoint_16_51_w4 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 4 2 244193108973135050 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_p6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 6 229653420901186522 = some 244193108973135050 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 4 2 229653420901186522 244193108973135050 244193108973135050 endpoint_16_51_p4 endpoint_16_51_w4
private theorem endpoint_16_51_w6 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 6 2 244193108973135050 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_p8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 8 229653420901186522 = some 244193108973135050 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 6 2 229653420901186522 244193108973135050 244193108973135050 endpoint_16_51_p6 endpoint_16_51_w6
private theorem endpoint_16_51_w8 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 8 2 244193108973135050 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_p10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 10 229653420901186522 = some 244193108973135050 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 8 2 229653420901186522 244193108973135050 244193108973135050 endpoint_16_51_p8 endpoint_16_51_w8
private theorem endpoint_16_51_w10 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 10 2 244193108973135050 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_p12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 12 229653420901186522 = some 244193108973135050 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 10 2 229653420901186522 244193108973135050 244193108973135050 endpoint_16_51_p10 endpoint_16_51_w10
private theorem endpoint_16_51_w12 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 12 2 244193108973135050 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_p14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 14 229653420901186522 = some 244193108973135050 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 12 2 229653420901186522 244193108973135050 244193108973135050 endpoint_16_51_p12 endpoint_16_51_w12
private theorem endpoint_16_51_w14 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 14 1 244193108973135050 = some 244193108973135050 := by decide +kernel
private theorem endpoint_16_51_p15 : receiptWindow endpoint_16_51_flag endpoint_16_51_sources 0 15 229653420901186522 = some 244193108973135050 :=
  join_receipt_window endpoint_16_51_flag endpoint_16_51_sources 0 14 1 229653420901186522 244193108973135050 244193108973135050 endpoint_16_51_p14 endpoint_16_51_w14
def endpoint_16_51 : CertifiedEndpoint :=
  ⟨⟨16, 51, 2517⟩, 244193108973135050, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_51_flag endpoint_16_51_sources 15 229653420901186522 244193108973135050 rfl endpoint_16_51_base endpoint_16_51_p15) (by decide)⟩
private def endpoint_16_52_flag : Flag := ⟨16, 52, 2472⟩
private def endpoint_16_52_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_52_base : receiptBase endpoint_16_52_flag endpoint_16_52_sources = some 229479102620908154 := by decide +kernel
private theorem endpoint_16_52_w0 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 2 229479102620908154 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_w2 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 2 2 247561949316676400 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_p4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 4 229479102620908154 = some 247561949316676400 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 2 2 229479102620908154 247561949316676400 247561949316676400 endpoint_16_52_w0 endpoint_16_52_w2
private theorem endpoint_16_52_w4 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 4 2 247561949316676400 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_p6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 6 229479102620908154 = some 247561949316676400 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 4 2 229479102620908154 247561949316676400 247561949316676400 endpoint_16_52_p4 endpoint_16_52_w4
private theorem endpoint_16_52_w6 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 6 2 247561949316676400 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_p8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 8 229479102620908154 = some 247561949316676400 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 6 2 229479102620908154 247561949316676400 247561949316676400 endpoint_16_52_p6 endpoint_16_52_w6
private theorem endpoint_16_52_w8 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 8 2 247561949316676400 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_p10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 10 229479102620908154 = some 247561949316676400 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 8 2 229479102620908154 247561949316676400 247561949316676400 endpoint_16_52_p8 endpoint_16_52_w8
private theorem endpoint_16_52_w10 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 10 2 247561949316676400 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_p12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 12 229479102620908154 = some 247561949316676400 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 10 2 229479102620908154 247561949316676400 247561949316676400 endpoint_16_52_p10 endpoint_16_52_w10
private theorem endpoint_16_52_w12 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 12 2 247561949316676400 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_p14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 14 229479102620908154 = some 247561949316676400 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 12 2 229479102620908154 247561949316676400 247561949316676400 endpoint_16_52_p12 endpoint_16_52_w12
private theorem endpoint_16_52_w14 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 14 1 247561949316676400 = some 247561949316676400 := by decide +kernel
private theorem endpoint_16_52_p15 : receiptWindow endpoint_16_52_flag endpoint_16_52_sources 0 15 229479102620908154 = some 247561949316676400 :=
  join_receipt_window endpoint_16_52_flag endpoint_16_52_sources 0 14 1 229479102620908154 247561949316676400 247561949316676400 endpoint_16_52_p14 endpoint_16_52_w14
def endpoint_16_52 : CertifiedEndpoint :=
  ⟨⟨16, 52, 2472⟩, 247561949316676400, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_52_flag endpoint_16_52_sources 15 229479102620908154 247561949316676400 rfl endpoint_16_52_base endpoint_16_52_p15) (by decide)⟩
private def endpoint_16_53_flag : Flag := ⟨16, 53, 2426⟩
private def endpoint_16_53_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_53_base : receiptBase endpoint_16_53_flag endpoint_16_53_sources = some 229071152101502004 := by decide +kernel
private theorem endpoint_16_53_w0 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 2 229071152101502004 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_w2 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 2 2 250762723347164959 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_p4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 4 229071152101502004 = some 250762723347164959 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 2 2 229071152101502004 250762723347164959 250762723347164959 endpoint_16_53_w0 endpoint_16_53_w2
private theorem endpoint_16_53_w4 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 4 2 250762723347164959 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_p6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 6 229071152101502004 = some 250762723347164959 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 4 2 229071152101502004 250762723347164959 250762723347164959 endpoint_16_53_p4 endpoint_16_53_w4
private theorem endpoint_16_53_w6 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 6 2 250762723347164959 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_p8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 8 229071152101502004 = some 250762723347164959 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 6 2 229071152101502004 250762723347164959 250762723347164959 endpoint_16_53_p6 endpoint_16_53_w6
private theorem endpoint_16_53_w8 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 8 2 250762723347164959 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_p10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 10 229071152101502004 = some 250762723347164959 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 8 2 229071152101502004 250762723347164959 250762723347164959 endpoint_16_53_p8 endpoint_16_53_w8
private theorem endpoint_16_53_w10 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 10 2 250762723347164959 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_p12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 12 229071152101502004 = some 250762723347164959 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 10 2 229071152101502004 250762723347164959 250762723347164959 endpoint_16_53_p10 endpoint_16_53_w10
private theorem endpoint_16_53_w12 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 12 2 250762723347164959 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_p14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 14 229071152101502004 = some 250762723347164959 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 12 2 229071152101502004 250762723347164959 250762723347164959 endpoint_16_53_p12 endpoint_16_53_w12
private theorem endpoint_16_53_w14 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 14 1 250762723347164959 = some 250762723347164959 := by decide +kernel
private theorem endpoint_16_53_p15 : receiptWindow endpoint_16_53_flag endpoint_16_53_sources 0 15 229071152101502004 = some 250762723347164959 :=
  join_receipt_window endpoint_16_53_flag endpoint_16_53_sources 0 14 1 229071152101502004 250762723347164959 250762723347164959 endpoint_16_53_p14 endpoint_16_53_w14
def endpoint_16_53 : CertifiedEndpoint :=
  ⟨⟨16, 53, 2426⟩, 250762723347164959, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_53_flag endpoint_16_53_sources 15 229071152101502004 250762723347164959 rfl endpoint_16_53_base endpoint_16_53_p15) (by decide)⟩
private def endpoint_16_54_flag : Flag := ⟨16, 54, 2379⟩
private def endpoint_16_54_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_16_54_base : receiptBase endpoint_16_54_flag endpoint_16_54_sources = some 228424932713261713 := by decide +kernel
private theorem endpoint_16_54_w0 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 2 228424932713261713 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_w2 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 2 2 253791745890057842 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_p4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 4 228424932713261713 = some 253791745890057842 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 2 2 228424932713261713 253791745890057842 253791745890057842 endpoint_16_54_w0 endpoint_16_54_w2
private theorem endpoint_16_54_w4 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 4 2 253791745890057842 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_p6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 6 228424932713261713 = some 253791745890057842 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 4 2 228424932713261713 253791745890057842 253791745890057842 endpoint_16_54_p4 endpoint_16_54_w4
private theorem endpoint_16_54_w6 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 6 2 253791745890057842 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_p8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 8 228424932713261713 = some 253791745890057842 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 6 2 228424932713261713 253791745890057842 253791745890057842 endpoint_16_54_p6 endpoint_16_54_w6
private theorem endpoint_16_54_w8 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 8 2 253791745890057842 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_p10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 10 228424932713261713 = some 253791745890057842 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 8 2 228424932713261713 253791745890057842 253791745890057842 endpoint_16_54_p8 endpoint_16_54_w8
private theorem endpoint_16_54_w10 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 10 2 253791745890057842 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_p12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 12 228424932713261713 = some 253791745890057842 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 10 2 228424932713261713 253791745890057842 253791745890057842 endpoint_16_54_p10 endpoint_16_54_w10
private theorem endpoint_16_54_w12 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 12 2 253791745890057842 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_p14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 14 228424932713261713 = some 253791745890057842 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 12 2 228424932713261713 253791745890057842 253791745890057842 endpoint_16_54_p12 endpoint_16_54_w12
private theorem endpoint_16_54_w14 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 14 1 253791745890057842 = some 253791745890057842 := by decide +kernel
private theorem endpoint_16_54_p15 : receiptWindow endpoint_16_54_flag endpoint_16_54_sources 0 15 228424932713261713 = some 253791745890057842 :=
  join_receipt_window endpoint_16_54_flag endpoint_16_54_sources 0 14 1 228424932713261713 253791745890057842 253791745890057842 endpoint_16_54_p14 endpoint_16_54_w14
def endpoint_16_54 : CertifiedEndpoint :=
  ⟨⟨16, 54, 2379⟩, 253791745890057842, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_16_54_flag endpoint_16_54_sources 15 228424932713261713 253791745890057842 rfl endpoint_16_54_base endpoint_16_54_p15) (by decide)⟩
private def endpoint_16_55_flag : Flag := ⟨16, 55, 2330⟩
private def endpoint_16_55_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_55_base : receiptBase endpoint_16_55_flag endpoint_16_55_sources = some 233194595909915709 := by decide +kernel
private theorem endpoint_16_55_w0 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 2 233194595909915709 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_w2 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 2 2 248440751561694713 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_p4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 4 233194595909915709 = some 248440751561694713 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 2 2 233194595909915709 248440751561694713 248440751561694713 endpoint_16_55_w0 endpoint_16_55_w2
private theorem endpoint_16_55_w4 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 4 2 248440751561694713 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_p6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 6 233194595909915709 = some 248440751561694713 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 4 2 233194595909915709 248440751561694713 248440751561694713 endpoint_16_55_p4 endpoint_16_55_w4
private theorem endpoint_16_55_w6 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 6 2 248440751561694713 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_p8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 8 233194595909915709 = some 248440751561694713 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 6 2 233194595909915709 248440751561694713 248440751561694713 endpoint_16_55_p6 endpoint_16_55_w6
private theorem endpoint_16_55_w8 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 8 2 248440751561694713 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_p10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 10 233194595909915709 = some 248440751561694713 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 8 2 233194595909915709 248440751561694713 248440751561694713 endpoint_16_55_p8 endpoint_16_55_w8
private theorem endpoint_16_55_w10 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 10 2 248440751561694713 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_p12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 12 233194595909915709 = some 248440751561694713 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 10 2 233194595909915709 248440751561694713 248440751561694713 endpoint_16_55_p10 endpoint_16_55_w10
private theorem endpoint_16_55_w12 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 12 2 248440751561694713 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_p14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 14 233194595909915709 = some 248440751561694713 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 12 2 233194595909915709 248440751561694713 248440751561694713 endpoint_16_55_p12 endpoint_16_55_w12
private theorem endpoint_16_55_w14 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 14 1 248440751561694713 = some 248440751561694713 := by decide +kernel
private theorem endpoint_16_55_p15 : receiptWindow endpoint_16_55_flag endpoint_16_55_sources 0 15 233194595909915709 = some 248440751561694713 :=
  join_receipt_window endpoint_16_55_flag endpoint_16_55_sources 0 14 1 233194595909915709 248440751561694713 248440751561694713 endpoint_16_55_p14 endpoint_16_55_w14
def endpoint_16_55 : CertifiedEndpoint :=
  ⟨⟨16, 55, 2330⟩, 248440751561694713, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_55_flag endpoint_16_55_sources 15 233194595909915709 248440751561694713 rfl endpoint_16_55_base endpoint_16_55_p15) (by decide)⟩
private def endpoint_16_56_flag : Flag := ⟨16, 56, 2281⟩
private def endpoint_16_56_sources : Sources := ⟨contact28, contact11, contact29⟩
private theorem endpoint_16_56_base : receiptBase endpoint_16_56_flag endpoint_16_56_sources = some 232093838986502638 := by decide +kernel
private theorem endpoint_16_56_w0 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 2 232093838986502638 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_w2 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 2 2 250937803293014444 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_p4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 4 232093838986502638 = some 250937803293014444 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 2 2 232093838986502638 250937803293014444 250937803293014444 endpoint_16_56_w0 endpoint_16_56_w2
private theorem endpoint_16_56_w4 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 4 2 250937803293014444 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_p6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 6 232093838986502638 = some 250937803293014444 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 4 2 232093838986502638 250937803293014444 250937803293014444 endpoint_16_56_p4 endpoint_16_56_w4
private theorem endpoint_16_56_w6 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 6 2 250937803293014444 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_p8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 8 232093838986502638 = some 250937803293014444 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 6 2 232093838986502638 250937803293014444 250937803293014444 endpoint_16_56_p6 endpoint_16_56_w6
private theorem endpoint_16_56_w8 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 8 2 250937803293014444 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_p10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 10 232093838986502638 = some 250937803293014444 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 8 2 232093838986502638 250937803293014444 250937803293014444 endpoint_16_56_p8 endpoint_16_56_w8
private theorem endpoint_16_56_w10 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 10 2 250937803293014444 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_p12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 12 232093838986502638 = some 250937803293014444 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 10 2 232093838986502638 250937803293014444 250937803293014444 endpoint_16_56_p10 endpoint_16_56_w10
private theorem endpoint_16_56_w12 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 12 2 250937803293014444 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_p14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 14 232093838986502638 = some 250937803293014444 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 12 2 232093838986502638 250937803293014444 250937803293014444 endpoint_16_56_p12 endpoint_16_56_w12
private theorem endpoint_16_56_w14 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 14 1 250937803293014444 = some 250937803293014444 := by decide +kernel
private theorem endpoint_16_56_p15 : receiptWindow endpoint_16_56_flag endpoint_16_56_sources 0 15 232093838986502638 = some 250937803293014444 :=
  join_receipt_window endpoint_16_56_flag endpoint_16_56_sources 0 14 1 232093838986502638 250937803293014444 250937803293014444 endpoint_16_56_p14 endpoint_16_56_w14
def endpoint_16_56 : CertifiedEndpoint :=
  ⟨⟨16, 56, 2281⟩, 250937803293014444, .terminal ⟨contact28, contact11, contact29⟩ (finish_receipt_window endpoint_16_56_flag endpoint_16_56_sources 15 232093838986502638 250937803293014444 rfl endpoint_16_56_base endpoint_16_56_p15) (by decide)⟩
private def endpoint_16_57_flag : Flag := ⟨16, 57, 2230⟩
private def endpoint_16_57_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_57_base : receiptBase endpoint_16_57_flag endpoint_16_57_sources = some 231674332941631438 := by decide +kernel
private theorem endpoint_16_57_w0 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 2 231674332941631438 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_w2 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 2 2 235706161939355209 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_p4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 4 231674332941631438 = some 235706161939355209 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 2 2 231674332941631438 235706161939355209 235706161939355209 endpoint_16_57_w0 endpoint_16_57_w2
private theorem endpoint_16_57_w4 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 4 2 235706161939355209 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_p6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 6 231674332941631438 = some 235706161939355209 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 4 2 231674332941631438 235706161939355209 235706161939355209 endpoint_16_57_p4 endpoint_16_57_w4
private theorem endpoint_16_57_w6 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 6 2 235706161939355209 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_p8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 8 231674332941631438 = some 235706161939355209 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 6 2 231674332941631438 235706161939355209 235706161939355209 endpoint_16_57_p6 endpoint_16_57_w6
private theorem endpoint_16_57_w8 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 8 2 235706161939355209 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_p10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 10 231674332941631438 = some 235706161939355209 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 8 2 231674332941631438 235706161939355209 235706161939355209 endpoint_16_57_p8 endpoint_16_57_w8
private theorem endpoint_16_57_w10 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 10 2 235706161939355209 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_p12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 12 231674332941631438 = some 235706161939355209 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 10 2 231674332941631438 235706161939355209 235706161939355209 endpoint_16_57_p10 endpoint_16_57_w10
private theorem endpoint_16_57_w12 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 12 2 235706161939355209 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_p14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 14 231674332941631438 = some 235706161939355209 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 12 2 231674332941631438 235706161939355209 235706161939355209 endpoint_16_57_p12 endpoint_16_57_w12
private theorem endpoint_16_57_w14 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 14 1 235706161939355209 = some 235706161939355209 := by decide +kernel
private theorem endpoint_16_57_p15 : receiptWindow endpoint_16_57_flag endpoint_16_57_sources 0 15 231674332941631438 = some 235706161939355209 :=
  join_receipt_window endpoint_16_57_flag endpoint_16_57_sources 0 14 1 231674332941631438 235706161939355209 235706161939355209 endpoint_16_57_p14 endpoint_16_57_w14
def endpoint_16_57 : CertifiedEndpoint :=
  ⟨⟨16, 57, 2230⟩, 235706161939355209, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_57_flag endpoint_16_57_sources 15 231674332941631438 235706161939355209 rfl endpoint_16_57_base endpoint_16_57_p15) (by decide)⟩
private def endpoint_16_58_flag : Flag := ⟨16, 58, 2177⟩
private def endpoint_16_58_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_58_base : receiptBase endpoint_16_58_flag endpoint_16_58_sources = some 229789138884001131 := by decide +kernel
private theorem endpoint_16_58_w0 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 2 229789138884001131 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_w2 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 2 2 237350435127723446 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_p4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 4 229789138884001131 = some 237350435127723446 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 2 2 229789138884001131 237350435127723446 237350435127723446 endpoint_16_58_w0 endpoint_16_58_w2
private theorem endpoint_16_58_w4 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 4 2 237350435127723446 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_p6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 6 229789138884001131 = some 237350435127723446 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 4 2 229789138884001131 237350435127723446 237350435127723446 endpoint_16_58_p4 endpoint_16_58_w4
private theorem endpoint_16_58_w6 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 6 2 237350435127723446 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_p8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 8 229789138884001131 = some 237350435127723446 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 6 2 229789138884001131 237350435127723446 237350435127723446 endpoint_16_58_p6 endpoint_16_58_w6
private theorem endpoint_16_58_w8 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 8 2 237350435127723446 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_p10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 10 229789138884001131 = some 237350435127723446 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 8 2 229789138884001131 237350435127723446 237350435127723446 endpoint_16_58_p8 endpoint_16_58_w8
private theorem endpoint_16_58_w10 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 10 2 237350435127723446 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_p12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 12 229789138884001131 = some 237350435127723446 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 10 2 229789138884001131 237350435127723446 237350435127723446 endpoint_16_58_p10 endpoint_16_58_w10
private theorem endpoint_16_58_w12 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 12 2 237350435127723446 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_p14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 14 229789138884001131 = some 237350435127723446 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 12 2 229789138884001131 237350435127723446 237350435127723446 endpoint_16_58_p12 endpoint_16_58_w12
private theorem endpoint_16_58_w14 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 14 1 237350435127723446 = some 237350435127723446 := by decide +kernel
private theorem endpoint_16_58_p15 : receiptWindow endpoint_16_58_flag endpoint_16_58_sources 0 15 229789138884001131 = some 237350435127723446 :=
  join_receipt_window endpoint_16_58_flag endpoint_16_58_sources 0 14 1 229789138884001131 237350435127723446 237350435127723446 endpoint_16_58_p14 endpoint_16_58_w14
def endpoint_16_58 : CertifiedEndpoint :=
  ⟨⟨16, 58, 2177⟩, 237350435127723446, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_58_flag endpoint_16_58_sources 15 229789138884001131 237350435127723446 rfl endpoint_16_58_base endpoint_16_58_p15) (by decide)⟩
private def endpoint_16_59_flag : Flag := ⟨16, 59, 2124⟩
private def endpoint_16_59_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_59_base : receiptBase endpoint_16_59_flag endpoint_16_59_sources = some 227736652207961044 := by decide +kernel
private theorem endpoint_16_59_w0 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 2 227736652207961044 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_w2 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 2 2 238860753510901563 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_p4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 4 227736652207961044 = some 238860753510901563 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 2 2 227736652207961044 238860753510901563 238860753510901563 endpoint_16_59_w0 endpoint_16_59_w2
private theorem endpoint_16_59_w4 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 4 2 238860753510901563 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_p6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 6 227736652207961044 = some 238860753510901563 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 4 2 227736652207961044 238860753510901563 238860753510901563 endpoint_16_59_p4 endpoint_16_59_w4
private theorem endpoint_16_59_w6 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 6 2 238860753510901563 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_p8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 8 227736652207961044 = some 238860753510901563 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 6 2 227736652207961044 238860753510901563 238860753510901563 endpoint_16_59_p6 endpoint_16_59_w6
private theorem endpoint_16_59_w8 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 8 2 238860753510901563 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_p10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 10 227736652207961044 = some 238860753510901563 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 8 2 227736652207961044 238860753510901563 238860753510901563 endpoint_16_59_p8 endpoint_16_59_w8
private theorem endpoint_16_59_w10 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 10 2 238860753510901563 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_p12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 12 227736652207961044 = some 238860753510901563 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 10 2 227736652207961044 238860753510901563 238860753510901563 endpoint_16_59_p10 endpoint_16_59_w10
private theorem endpoint_16_59_w12 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 12 2 238860753510901563 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_p14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 14 227736652207961044 = some 238860753510901563 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 12 2 227736652207961044 238860753510901563 238860753510901563 endpoint_16_59_p12 endpoint_16_59_w12
private theorem endpoint_16_59_w14 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 14 1 238860753510901563 = some 238860753510901563 := by decide +kernel
private theorem endpoint_16_59_p15 : receiptWindow endpoint_16_59_flag endpoint_16_59_sources 0 15 227736652207961044 = some 238860753510901563 :=
  join_receipt_window endpoint_16_59_flag endpoint_16_59_sources 0 14 1 227736652207961044 238860753510901563 238860753510901563 endpoint_16_59_p14 endpoint_16_59_w14
def endpoint_16_59 : CertifiedEndpoint :=
  ⟨⟨16, 59, 2124⟩, 238860753510901563, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_59_flag endpoint_16_59_sources 15 227736652207961044 238860753510901563 rfl endpoint_16_59_base endpoint_16_59_p15) (by decide)⟩
private def endpoint_16_60_flag : Flag := ⟨16, 60, 2068⟩
private def endpoint_16_60_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_60_base : receiptBase endpoint_16_60_flag endpoint_16_60_sources = some 225198653923128885 := by decide +kernel
private theorem endpoint_16_60_w0 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 2 225198653923128885 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_w2 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 2 2 240050023550815192 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_p4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 4 225198653923128885 = some 240050023550815192 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 2 2 225198653923128885 240050023550815192 240050023550815192 endpoint_16_60_w0 endpoint_16_60_w2
private theorem endpoint_16_60_w4 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 4 2 240050023550815192 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_p6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 6 225198653923128885 = some 240050023550815192 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 4 2 225198653923128885 240050023550815192 240050023550815192 endpoint_16_60_p4 endpoint_16_60_w4
private theorem endpoint_16_60_w6 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 6 2 240050023550815192 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_p8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 8 225198653923128885 = some 240050023550815192 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 6 2 225198653923128885 240050023550815192 240050023550815192 endpoint_16_60_p6 endpoint_16_60_w6
private theorem endpoint_16_60_w8 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 8 2 240050023550815192 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_p10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 10 225198653923128885 = some 240050023550815192 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 8 2 225198653923128885 240050023550815192 240050023550815192 endpoint_16_60_p8 endpoint_16_60_w8
private theorem endpoint_16_60_w10 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 10 2 240050023550815192 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_p12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 12 225198653923128885 = some 240050023550815192 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 10 2 225198653923128885 240050023550815192 240050023550815192 endpoint_16_60_p10 endpoint_16_60_w10
private theorem endpoint_16_60_w12 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 12 2 240050023550815192 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_p14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 14 225198653923128885 = some 240050023550815192 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 12 2 225198653923128885 240050023550815192 240050023550815192 endpoint_16_60_p12 endpoint_16_60_w12
private theorem endpoint_16_60_w14 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 14 1 240050023550815192 = some 240050023550815192 := by decide +kernel
private theorem endpoint_16_60_p15 : receiptWindow endpoint_16_60_flag endpoint_16_60_sources 0 15 225198653923128885 = some 240050023550815192 :=
  join_receipt_window endpoint_16_60_flag endpoint_16_60_sources 0 14 1 225198653923128885 240050023550815192 240050023550815192 endpoint_16_60_p14 endpoint_16_60_w14
def endpoint_16_60 : CertifiedEndpoint :=
  ⟨⟨16, 60, 2068⟩, 240050023550815192, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_60_flag endpoint_16_60_sources 15 225198653923128885 240050023550815192 rfl endpoint_16_60_base endpoint_16_60_p15) (by decide)⟩
private def endpoint_16_61_flag : Flag := ⟨16, 61, 2012⟩
private def endpoint_16_61_sources : Sources := ⟨contact14, contact14, contact12⟩
private theorem endpoint_16_61_base : receiptBase endpoint_16_61_flag endpoint_16_61_sources = some 222483982125396679 := by decide +kernel
private theorem endpoint_16_61_w0 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 2 222483982125396679 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_w2 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 2 2 241097968436452931 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_p4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 4 222483982125396679 = some 241097968436452931 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 2 2 222483982125396679 241097968436452931 241097968436452931 endpoint_16_61_w0 endpoint_16_61_w2
private theorem endpoint_16_61_w4 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 4 2 241097968436452931 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_p6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 6 222483982125396679 = some 241097968436452931 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 4 2 222483982125396679 241097968436452931 241097968436452931 endpoint_16_61_p4 endpoint_16_61_w4
private theorem endpoint_16_61_w6 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 6 2 241097968436452931 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_p8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 8 222483982125396679 = some 241097968436452931 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 6 2 222483982125396679 241097968436452931 241097968436452931 endpoint_16_61_p6 endpoint_16_61_w6
private theorem endpoint_16_61_w8 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 8 2 241097968436452931 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_p10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 10 222483982125396679 = some 241097968436452931 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 8 2 222483982125396679 241097968436452931 241097968436452931 endpoint_16_61_p8 endpoint_16_61_w8
private theorem endpoint_16_61_w10 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 10 2 241097968436452931 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_p12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 12 222483982125396679 = some 241097968436452931 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 10 2 222483982125396679 241097968436452931 241097968436452931 endpoint_16_61_p10 endpoint_16_61_w10
private theorem endpoint_16_61_w12 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 12 2 241097968436452931 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_p14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 14 222483982125396679 = some 241097968436452931 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 12 2 222483982125396679 241097968436452931 241097968436452931 endpoint_16_61_p12 endpoint_16_61_w12
private theorem endpoint_16_61_w14 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 14 1 241097968436452931 = some 241097968436452931 := by decide +kernel
private theorem endpoint_16_61_p15 : receiptWindow endpoint_16_61_flag endpoint_16_61_sources 0 15 222483982125396679 = some 241097968436452931 :=
  join_receipt_window endpoint_16_61_flag endpoint_16_61_sources 0 14 1 222483982125396679 241097968436452931 241097968436452931 endpoint_16_61_p14 endpoint_16_61_w14
def endpoint_16_61 : CertifiedEndpoint :=
  ⟨⟨16, 61, 2012⟩, 241097968436452931, .terminal ⟨contact14, contact14, contact12⟩ (finish_receipt_window endpoint_16_61_flag endpoint_16_61_sources 15 222483982125396679 241097968436452931 rfl endpoint_16_61_base endpoint_16_61_p15) (by decide)⟩
private def endpoint_16_62_flag : Flag := ⟨16, 62, 1953⟩
private def endpoint_16_62_sources : Sources := ⟨contact15, contact15, contact12⟩
private theorem endpoint_16_62_base : receiptBase endpoint_16_62_flag endpoint_16_62_sources = some 220355392960076461 := by decide +kernel
private theorem endpoint_16_62_w0 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 2 220355392960076461 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_w2 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 2 2 235108949207319342 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_p4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 4 220355392960076461 = some 235108949207319342 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 2 2 220355392960076461 235108949207319342 235108949207319342 endpoint_16_62_w0 endpoint_16_62_w2
private theorem endpoint_16_62_w4 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 4 2 235108949207319342 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_p6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 6 220355392960076461 = some 235108949207319342 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 4 2 220355392960076461 235108949207319342 235108949207319342 endpoint_16_62_p4 endpoint_16_62_w4
private theorem endpoint_16_62_w6 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 6 2 235108949207319342 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_p8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 8 220355392960076461 = some 235108949207319342 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 6 2 220355392960076461 235108949207319342 235108949207319342 endpoint_16_62_p6 endpoint_16_62_w6
private theorem endpoint_16_62_w8 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 8 2 235108949207319342 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_p10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 10 220355392960076461 = some 235108949207319342 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 8 2 220355392960076461 235108949207319342 235108949207319342 endpoint_16_62_p8 endpoint_16_62_w8
private theorem endpoint_16_62_w10 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 10 2 235108949207319342 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_p12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 12 220355392960076461 = some 235108949207319342 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 10 2 220355392960076461 235108949207319342 235108949207319342 endpoint_16_62_p10 endpoint_16_62_w10
private theorem endpoint_16_62_w12 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 12 2 235108949207319342 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_p14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 14 220355392960076461 = some 235108949207319342 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 12 2 220355392960076461 235108949207319342 235108949207319342 endpoint_16_62_p12 endpoint_16_62_w12
private theorem endpoint_16_62_w14 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 14 1 235108949207319342 = some 235108949207319342 := by decide +kernel
private theorem endpoint_16_62_p15 : receiptWindow endpoint_16_62_flag endpoint_16_62_sources 0 15 220355392960076461 = some 235108949207319342 :=
  join_receipt_window endpoint_16_62_flag endpoint_16_62_sources 0 14 1 220355392960076461 235108949207319342 235108949207319342 endpoint_16_62_p14 endpoint_16_62_w14
def endpoint_16_62 : CertifiedEndpoint :=
  ⟨⟨16, 62, 1953⟩, 235108949207319342, .terminal ⟨contact15, contact15, contact12⟩ (finish_receipt_window endpoint_16_62_flag endpoint_16_62_sources 15 220355392960076461 235108949207319342 rfl endpoint_16_62_base endpoint_16_62_p15) (by decide)⟩

def endpointBlock10 : List CertifiedEndpoint := [
  endpoint_14_81, endpoint_14_82, endpoint_14_83, endpoint_14_84, endpoint_14_85, endpoint_14_86, endpoint_14_87,
  endpoint_14_88, endpoint_15_15, endpoint_15_16, endpoint_15_17, endpoint_15_18, endpoint_15_19, endpoint_15_20,
  endpoint_15_21, endpoint_15_22, endpoint_15_23, endpoint_15_24, endpoint_15_25, endpoint_15_26, endpoint_15_27,
  endpoint_15_28, endpoint_15_29, endpoint_15_30, endpoint_15_31, endpoint_15_32, endpoint_15_33, endpoint_15_34,
  endpoint_15_35, endpoint_15_36, endpoint_15_37, endpoint_15_38, endpoint_15_39, endpoint_15_40, endpoint_15_41,
  endpoint_15_42, endpoint_15_43, endpoint_15_44, endpoint_15_45, endpoint_15_46, endpoint_15_47, endpoint_15_48,
  endpoint_15_49, endpoint_15_50, endpoint_15_51, endpoint_15_52, endpoint_15_53, endpoint_15_54, endpoint_15_55,
  endpoint_15_56, endpoint_15_57, endpoint_15_58, endpoint_15_59, endpoint_15_60, endpoint_15_61, endpoint_15_62,
  endpoint_15_63, endpoint_15_64, endpoint_15_65, endpoint_15_66, endpoint_15_67, endpoint_15_68, endpoint_15_69,
  endpoint_15_70, endpoint_15_71, endpoint_15_72, endpoint_15_73, endpoint_15_74, endpoint_15_75, endpoint_15_76,
  endpoint_15_77, endpoint_15_78, endpoint_15_79, endpoint_15_80, endpoint_15_81, endpoint_15_82, endpoint_15_83,
  endpoint_15_84, endpoint_15_85, endpoint_15_86, endpoint_16_16, endpoint_16_17, endpoint_16_18, endpoint_16_19,
  endpoint_16_20, endpoint_16_21, endpoint_16_22, endpoint_16_23, endpoint_16_24, endpoint_16_25, endpoint_16_26,
  endpoint_16_27, endpoint_16_28, endpoint_16_29, endpoint_16_30, endpoint_16_31, endpoint_16_32, endpoint_16_33,
  endpoint_16_34, endpoint_16_35, endpoint_16_36, endpoint_16_37, endpoint_16_38, endpoint_16_39, endpoint_16_40,
  endpoint_16_41, endpoint_16_42, endpoint_16_43, endpoint_16_44, endpoint_16_45, endpoint_16_46, endpoint_16_47,
  endpoint_16_48, endpoint_16_49, endpoint_16_50, endpoint_16_51, endpoint_16_52, endpoint_16_53, endpoint_16_54,
  endpoint_16_55, endpoint_16_56, endpoint_16_57, endpoint_16_58, endpoint_16_59, endpoint_16_60, endpoint_16_61,
  endpoint_16_62
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
