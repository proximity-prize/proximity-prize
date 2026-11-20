import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice
import ProximityPrize.SubmissionLower.Koala6844ReceiptsProfiles
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPriceWindows

namespace ProximityPrize.SubmissionLower.Koala6844Receipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def endpoint_8_58_flag : Flag := ⟨8, 58, 3701⟩
private def endpoint_8_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_58_base : receiptBase endpoint_8_58_flag endpoint_8_58_sources = some 232468886927880191 := by decide +kernel
private theorem endpoint_8_58_w0 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 2 232468886927880191 = some 232468886927880191 := by decide +kernel
private theorem endpoint_8_58_w2 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 2 2 232468886927880191 = some 232468886927880191 := by decide +kernel
private theorem endpoint_8_58_p4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 4 232468886927880191 = some 232468886927880191 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 2 2 232468886927880191 232468886927880191 232468886927880191 endpoint_8_58_w0 endpoint_8_58_w2
private theorem endpoint_8_58_w4 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 4 2 232468886927880191 = some 232468886927880191 := by decide +kernel
private theorem endpoint_8_58_p6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 6 232468886927880191 = some 232468886927880191 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 4 2 232468886927880191 232468886927880191 232468886927880191 endpoint_8_58_p4 endpoint_8_58_w4
private theorem endpoint_8_58_w6 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 6 1 232468886927880191 = some 232468886927880191 := by decide +kernel
private theorem endpoint_8_58_p7 : receiptWindow endpoint_8_58_flag endpoint_8_58_sources 0 7 232468886927880191 = some 232468886927880191 :=
  join_receipt_window endpoint_8_58_flag endpoint_8_58_sources 0 6 1 232468886927880191 232468886927880191 232468886927880191 endpoint_8_58_p6 endpoint_8_58_w6
def endpoint_8_58 : CertifiedEndpoint :=
  ⟨⟨8, 58, 3701⟩, 232468886927880191, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_58_flag endpoint_8_58_sources 7 232468886927880191 232468886927880191 rfl endpoint_8_58_base endpoint_8_58_p7) (by decide)⟩
private def endpoint_8_59_flag : Flag := ⟨8, 59, 3657⟩
private def endpoint_8_59_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_59_base : receiptBase endpoint_8_59_flag endpoint_8_59_sources = some 233212507699068530 := by decide +kernel
private theorem endpoint_8_59_w0 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 2 233212507699068530 = some 233212507699068530 := by decide +kernel
private theorem endpoint_8_59_w2 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 2 2 233212507699068530 = some 233212507699068530 := by decide +kernel
private theorem endpoint_8_59_p4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 4 233212507699068530 = some 233212507699068530 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 2 2 233212507699068530 233212507699068530 233212507699068530 endpoint_8_59_w0 endpoint_8_59_w2
private theorem endpoint_8_59_w4 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 4 2 233212507699068530 = some 233212507699068530 := by decide +kernel
private theorem endpoint_8_59_p6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 6 233212507699068530 = some 233212507699068530 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 4 2 233212507699068530 233212507699068530 233212507699068530 endpoint_8_59_p4 endpoint_8_59_w4
private theorem endpoint_8_59_w6 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 6 1 233212507699068530 = some 233212507699068530 := by decide +kernel
private theorem endpoint_8_59_p7 : receiptWindow endpoint_8_59_flag endpoint_8_59_sources 0 7 233212507699068530 = some 233212507699068530 :=
  join_receipt_window endpoint_8_59_flag endpoint_8_59_sources 0 6 1 233212507699068530 233212507699068530 233212507699068530 endpoint_8_59_p6 endpoint_8_59_w6
def endpoint_8_59 : CertifiedEndpoint :=
  ⟨⟨8, 59, 3657⟩, 233212507699068530, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_59_flag endpoint_8_59_sources 7 233212507699068530 233212507699068530 rfl endpoint_8_59_base endpoint_8_59_p7) (by decide)⟩
private def endpoint_8_60_flag : Flag := ⟨8, 60, 3611⟩
private def endpoint_8_60_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_8_60_base : receiptBase endpoint_8_60_flag endpoint_8_60_sources = some 233744460201273859 := by decide +kernel
private theorem endpoint_8_60_w0 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 2 233744460201273859 = some 233744460201273859 := by decide +kernel
private theorem endpoint_8_60_w2 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 2 2 233744460201273859 = some 233744460201273859 := by decide +kernel
private theorem endpoint_8_60_p4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 4 233744460201273859 = some 233744460201273859 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 2 2 233744460201273859 233744460201273859 233744460201273859 endpoint_8_60_w0 endpoint_8_60_w2
private theorem endpoint_8_60_w4 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 4 2 233744460201273859 = some 233744460201273859 := by decide +kernel
private theorem endpoint_8_60_p6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 6 233744460201273859 = some 233744460201273859 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 4 2 233744460201273859 233744460201273859 233744460201273859 endpoint_8_60_p4 endpoint_8_60_w4
private theorem endpoint_8_60_w6 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 6 1 233744460201273859 = some 233744460201273859 := by decide +kernel
private theorem endpoint_8_60_p7 : receiptWindow endpoint_8_60_flag endpoint_8_60_sources 0 7 233744460201273859 = some 233744460201273859 :=
  join_receipt_window endpoint_8_60_flag endpoint_8_60_sources 0 6 1 233744460201273859 233744460201273859 233744460201273859 endpoint_8_60_p6 endpoint_8_60_w6
def endpoint_8_60 : CertifiedEndpoint :=
  ⟨⟨8, 60, 3611⟩, 233744460201273859, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_8_60_flag endpoint_8_60_sources 7 233744460201273859 233744460201273859 rfl endpoint_8_60_base endpoint_8_60_p7) (by decide)⟩
private def endpoint_8_61_flag : Flag := ⟨8, 61, 3563⟩
private def endpoint_8_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_61_base : receiptBase endpoint_8_61_flag endpoint_8_61_sources = some 236442719214255233 := by decide +kernel
private theorem endpoint_8_61_w0 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 2 236442719214255233 = some 236442719214255233 := by decide +kernel
private theorem endpoint_8_61_w2 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 2 2 236442719214255233 = some 236442719214255233 := by decide +kernel
private theorem endpoint_8_61_p4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 4 236442719214255233 = some 236442719214255233 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 2 2 236442719214255233 236442719214255233 236442719214255233 endpoint_8_61_w0 endpoint_8_61_w2
private theorem endpoint_8_61_w4 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 4 2 236442719214255233 = some 236442719214255233 := by decide +kernel
private theorem endpoint_8_61_p6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 6 236442719214255233 = some 236442719214255233 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 4 2 236442719214255233 236442719214255233 236442719214255233 endpoint_8_61_p4 endpoint_8_61_w4
private theorem endpoint_8_61_w6 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 6 1 236442719214255233 = some 236442719214255233 := by decide +kernel
private theorem endpoint_8_61_p7 : receiptWindow endpoint_8_61_flag endpoint_8_61_sources 0 7 236442719214255233 = some 236442719214255233 :=
  join_receipt_window endpoint_8_61_flag endpoint_8_61_sources 0 6 1 236442719214255233 236442719214255233 236442719214255233 endpoint_8_61_p6 endpoint_8_61_w6
def endpoint_8_61 : CertifiedEndpoint :=
  ⟨⟨8, 61, 3563⟩, 236442719214255233, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_61_flag endpoint_8_61_sources 7 236442719214255233 236442719214255233 rfl endpoint_8_61_base endpoint_8_61_p7) (by decide)⟩
private def endpoint_8_62_flag : Flag := ⟨8, 62, 3512⟩
private def endpoint_8_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_62_base : receiptBase endpoint_8_62_flag endpoint_8_62_sources = some 236446271621450583 := by decide +kernel
private theorem endpoint_8_62_w0 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 2 236446271621450583 = some 236446271621450583 := by decide +kernel
private theorem endpoint_8_62_w2 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 2 2 236446271621450583 = some 236446271621450583 := by decide +kernel
private theorem endpoint_8_62_p4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 4 236446271621450583 = some 236446271621450583 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 2 2 236446271621450583 236446271621450583 236446271621450583 endpoint_8_62_w0 endpoint_8_62_w2
private theorem endpoint_8_62_w4 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 4 2 236446271621450583 = some 236446271621450583 := by decide +kernel
private theorem endpoint_8_62_p6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 6 236446271621450583 = some 236446271621450583 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 4 2 236446271621450583 236446271621450583 236446271621450583 endpoint_8_62_p4 endpoint_8_62_w4
private theorem endpoint_8_62_w6 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 6 1 236446271621450583 = some 236446271621450583 := by decide +kernel
private theorem endpoint_8_62_p7 : receiptWindow endpoint_8_62_flag endpoint_8_62_sources 0 7 236446271621450583 = some 236446271621450583 :=
  join_receipt_window endpoint_8_62_flag endpoint_8_62_sources 0 6 1 236446271621450583 236446271621450583 236446271621450583 endpoint_8_62_p6 endpoint_8_62_w6
def endpoint_8_62 : CertifiedEndpoint :=
  ⟨⟨8, 62, 3512⟩, 236446271621450583, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_62_flag endpoint_8_62_sources 7 236446271621450583 236446271621450583 rfl endpoint_8_62_base endpoint_8_62_p7) (by decide)⟩
private def endpoint_8_63_flag : Flag := ⟨8, 63, 3460⟩
private def endpoint_8_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_63_base : receiptBase endpoint_8_63_flag endpoint_8_63_sources = some 236284284171583673 := by decide +kernel
private theorem endpoint_8_63_w0 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 2 236284284171583673 = some 236284284171583673 := by decide +kernel
private theorem endpoint_8_63_w2 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 2 2 236284284171583673 = some 236284284171583673 := by decide +kernel
private theorem endpoint_8_63_p4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 4 236284284171583673 = some 236284284171583673 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 2 2 236284284171583673 236284284171583673 236284284171583673 endpoint_8_63_w0 endpoint_8_63_w2
private theorem endpoint_8_63_w4 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 4 2 236284284171583673 = some 236284284171583673 := by decide +kernel
private theorem endpoint_8_63_p6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 6 236284284171583673 = some 236284284171583673 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 4 2 236284284171583673 236284284171583673 236284284171583673 endpoint_8_63_p4 endpoint_8_63_w4
private theorem endpoint_8_63_w6 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 6 1 236284284171583673 = some 236284284171583673 := by decide +kernel
private theorem endpoint_8_63_p7 : receiptWindow endpoint_8_63_flag endpoint_8_63_sources 0 7 236284284171583673 = some 236284284171583673 :=
  join_receipt_window endpoint_8_63_flag endpoint_8_63_sources 0 6 1 236284284171583673 236284284171583673 236284284171583673 endpoint_8_63_p6 endpoint_8_63_w6
def endpoint_8_63 : CertifiedEndpoint :=
  ⟨⟨8, 63, 3460⟩, 236284284171583673, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_63_flag endpoint_8_63_sources 7 236284284171583673 236284284171583673 rfl endpoint_8_63_base endpoint_8_63_p7) (by decide)⟩
private def endpoint_8_64_flag : Flag := ⟨8, 64, 3404⟩
private def endpoint_8_64_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_8_64_base : receiptBase endpoint_8_64_flag endpoint_8_64_sources = some 235748223156959615 := by decide +kernel
private theorem endpoint_8_64_w0 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 2 235748223156959615 = some 235748223156959615 := by decide +kernel
private theorem endpoint_8_64_w2 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 2 2 235748223156959615 = some 235748223156959615 := by decide +kernel
private theorem endpoint_8_64_p4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 4 235748223156959615 = some 235748223156959615 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 2 2 235748223156959615 235748223156959615 235748223156959615 endpoint_8_64_w0 endpoint_8_64_w2
private theorem endpoint_8_64_w4 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 4 2 235748223156959615 = some 235748223156959615 := by decide +kernel
private theorem endpoint_8_64_p6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 6 235748223156959615 = some 235748223156959615 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 4 2 235748223156959615 235748223156959615 235748223156959615 endpoint_8_64_p4 endpoint_8_64_w4
private theorem endpoint_8_64_w6 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 6 1 235748223156959615 = some 235748223156959615 := by decide +kernel
private theorem endpoint_8_64_p7 : receiptWindow endpoint_8_64_flag endpoint_8_64_sources 0 7 235748223156959615 = some 235748223156959615 :=
  join_receipt_window endpoint_8_64_flag endpoint_8_64_sources 0 6 1 235748223156959615 235748223156959615 235748223156959615 endpoint_8_64_p6 endpoint_8_64_w6
def endpoint_8_64 : CertifiedEndpoint :=
  ⟨⟨8, 64, 3404⟩, 235748223156959615, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_8_64_flag endpoint_8_64_sources 7 235748223156959615 235748223156959615 rfl endpoint_8_64_base endpoint_8_64_p7) (by decide)⟩
private def endpoint_8_65_flag : Flag := ⟨8, 65, 3346⟩
private def endpoint_8_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_65_base : receiptBase endpoint_8_65_flag endpoint_8_65_sources = some 236482477652285161 := by decide +kernel
private theorem endpoint_8_65_w0 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 2 236482477652285161 = some 236482477652285161 := by decide +kernel
private theorem endpoint_8_65_w2 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 2 2 236482477652285161 = some 236482477652285161 := by decide +kernel
private theorem endpoint_8_65_p4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 4 236482477652285161 = some 236482477652285161 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 2 2 236482477652285161 236482477652285161 236482477652285161 endpoint_8_65_w0 endpoint_8_65_w2
private theorem endpoint_8_65_w4 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 4 2 236482477652285161 = some 236482477652285161 := by decide +kernel
private theorem endpoint_8_65_p6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 6 236482477652285161 = some 236482477652285161 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 4 2 236482477652285161 236482477652285161 236482477652285161 endpoint_8_65_p4 endpoint_8_65_w4
private theorem endpoint_8_65_w6 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 6 1 236482477652285161 = some 236482477652285161 := by decide +kernel
private theorem endpoint_8_65_p7 : receiptWindow endpoint_8_65_flag endpoint_8_65_sources 0 7 236482477652285161 = some 236482477652285161 :=
  join_receipt_window endpoint_8_65_flag endpoint_8_65_sources 0 6 1 236482477652285161 236482477652285161 236482477652285161 endpoint_8_65_p6 endpoint_8_65_w6
def endpoint_8_65 : CertifiedEndpoint :=
  ⟨⟨8, 65, 3346⟩, 236482477652285161, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_65_flag endpoint_8_65_sources 7 236482477652285161 236482477652285161 rfl endpoint_8_65_base endpoint_8_65_p7) (by decide)⟩
private def endpoint_8_66_flag : Flag := ⟨8, 66, 3285⟩
private def endpoint_8_66_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_66_base : receiptBase endpoint_8_66_flag endpoint_8_66_sources = some 235372186319203105 := by decide +kernel
private theorem endpoint_8_66_w0 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 2 235372186319203105 = some 235372186319203105 := by decide +kernel
private theorem endpoint_8_66_w2 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 2 2 235372186319203105 = some 235372186319203105 := by decide +kernel
private theorem endpoint_8_66_p4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 4 235372186319203105 = some 235372186319203105 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 2 2 235372186319203105 235372186319203105 235372186319203105 endpoint_8_66_w0 endpoint_8_66_w2
private theorem endpoint_8_66_w4 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 4 2 235372186319203105 = some 235372186319203105 := by decide +kernel
private theorem endpoint_8_66_p6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 6 235372186319203105 = some 235372186319203105 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 4 2 235372186319203105 235372186319203105 235372186319203105 endpoint_8_66_p4 endpoint_8_66_w4
private theorem endpoint_8_66_w6 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 6 1 235372186319203105 = some 235372186319203105 := by decide +kernel
private theorem endpoint_8_66_p7 : receiptWindow endpoint_8_66_flag endpoint_8_66_sources 0 7 235372186319203105 = some 235372186319203105 :=
  join_receipt_window endpoint_8_66_flag endpoint_8_66_sources 0 6 1 235372186319203105 235372186319203105 235372186319203105 endpoint_8_66_p6 endpoint_8_66_w6
def endpoint_8_66 : CertifiedEndpoint :=
  ⟨⟨8, 66, 3285⟩, 235372186319203105, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_66_flag endpoint_8_66_sources 7 235372186319203105 235372186319203105 rfl endpoint_8_66_base endpoint_8_66_p7) (by decide)⟩
private def endpoint_8_67_flag : Flag := ⟨8, 67, 3221⟩
private def endpoint_8_67_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_8_67_base : receiptBase endpoint_8_67_flag endpoint_8_67_sources = some 233928020459652945 := by decide +kernel
private theorem endpoint_8_67_w0 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 2 233928020459652945 = some 233928020459652945 := by decide +kernel
private theorem endpoint_8_67_w2 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 2 2 233928020459652945 = some 233928020459652945 := by decide +kernel
private theorem endpoint_8_67_p4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 4 233928020459652945 = some 233928020459652945 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 2 2 233928020459652945 233928020459652945 233928020459652945 endpoint_8_67_w0 endpoint_8_67_w2
private theorem endpoint_8_67_w4 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 4 2 233928020459652945 = some 233928020459652945 := by decide +kernel
private theorem endpoint_8_67_p6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 6 233928020459652945 = some 233928020459652945 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 4 2 233928020459652945 233928020459652945 233928020459652945 endpoint_8_67_p4 endpoint_8_67_w4
private theorem endpoint_8_67_w6 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 6 1 233928020459652945 = some 233928020459652945 := by decide +kernel
private theorem endpoint_8_67_p7 : receiptWindow endpoint_8_67_flag endpoint_8_67_sources 0 7 233928020459652945 = some 233928020459652945 :=
  join_receipt_window endpoint_8_67_flag endpoint_8_67_sources 0 6 1 233928020459652945 233928020459652945 233928020459652945 endpoint_8_67_p6 endpoint_8_67_w6
def endpoint_8_67 : CertifiedEndpoint :=
  ⟨⟨8, 67, 3221⟩, 233928020459652945, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_8_67_flag endpoint_8_67_sources 7 233928020459652945 233928020459652945 rfl endpoint_8_67_base endpoint_8_67_p7) (by decide)⟩
private def endpoint_8_68_flag : Flag := ⟨8, 68, 3153⟩
private def endpoint_8_68_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_68_base : receiptBase endpoint_8_68_flag endpoint_8_68_sources = some 233614459324737657 := by decide +kernel
private theorem endpoint_8_68_w0 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 2 233614459324737657 = some 233614459324737657 := by decide +kernel
private theorem endpoint_8_68_w2 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 2 2 233614459324737657 = some 233614459324737657 := by decide +kernel
private theorem endpoint_8_68_p4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 4 233614459324737657 = some 233614459324737657 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 2 2 233614459324737657 233614459324737657 233614459324737657 endpoint_8_68_w0 endpoint_8_68_w2
private theorem endpoint_8_68_w4 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 4 2 233614459324737657 = some 233614459324737657 := by decide +kernel
private theorem endpoint_8_68_p6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 6 233614459324737657 = some 233614459324737657 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 4 2 233614459324737657 233614459324737657 233614459324737657 endpoint_8_68_p4 endpoint_8_68_w4
private theorem endpoint_8_68_w6 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 6 1 233614459324737657 = some 233614459324737657 := by decide +kernel
private theorem endpoint_8_68_p7 : receiptWindow endpoint_8_68_flag endpoint_8_68_sources 0 7 233614459324737657 = some 233614459324737657 :=
  join_receipt_window endpoint_8_68_flag endpoint_8_68_sources 0 6 1 233614459324737657 233614459324737657 233614459324737657 endpoint_8_68_p6 endpoint_8_68_w6
def endpoint_8_68 : CertifiedEndpoint :=
  ⟨⟨8, 68, 3153⟩, 233614459324737657, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_68_flag endpoint_8_68_sources 7 233614459324737657 233614459324737657 rfl endpoint_8_68_base endpoint_8_68_p7) (by decide)⟩
private def endpoint_8_69_flag : Flag := ⟨8, 69, 3082⟩
private def endpoint_8_69_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_8_69_base : receiptBase endpoint_8_69_flag endpoint_8_69_sources = some 231388698917117996 := by decide +kernel
private theorem endpoint_8_69_w0 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 2 231388698917117996 = some 231388698917117996 := by decide +kernel
private theorem endpoint_8_69_w2 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 2 2 231388698917117996 = some 231388698917117996 := by decide +kernel
private theorem endpoint_8_69_p4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 4 231388698917117996 = some 231388698917117996 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 2 2 231388698917117996 231388698917117996 231388698917117996 endpoint_8_69_w0 endpoint_8_69_w2
private theorem endpoint_8_69_w4 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 4 2 231388698917117996 = some 231388698917117996 := by decide +kernel
private theorem endpoint_8_69_p6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 6 231388698917117996 = some 231388698917117996 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 4 2 231388698917117996 231388698917117996 231388698917117996 endpoint_8_69_p4 endpoint_8_69_w4
private theorem endpoint_8_69_w6 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 6 1 231388698917117996 = some 231388698917117996 := by decide +kernel
private theorem endpoint_8_69_p7 : receiptWindow endpoint_8_69_flag endpoint_8_69_sources 0 7 231388698917117996 = some 231388698917117996 :=
  join_receipt_window endpoint_8_69_flag endpoint_8_69_sources 0 6 1 231388698917117996 231388698917117996 231388698917117996 endpoint_8_69_p6 endpoint_8_69_w6
def endpoint_8_69 : CertifiedEndpoint :=
  ⟨⟨8, 69, 3082⟩, 231388698917117996, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_8_69_flag endpoint_8_69_sources 7 231388698917117996 231388698917117996 rfl endpoint_8_69_base endpoint_8_69_p7) (by decide)⟩
private def endpoint_8_70_flag : Flag := ⟨8, 70, 3009⟩
private def endpoint_8_70_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_8_70_base : receiptBase endpoint_8_70_flag endpoint_8_70_sources = some 230432972588573789 := by decide +kernel
private theorem endpoint_8_70_w0 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 2 230432972588573789 = some 230432972588573789 := by decide +kernel
private theorem endpoint_8_70_w2 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 2 2 230432972588573789 = some 230432972588573789 := by decide +kernel
private theorem endpoint_8_70_p4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 4 230432972588573789 = some 230432972588573789 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 2 2 230432972588573789 230432972588573789 230432972588573789 endpoint_8_70_w0 endpoint_8_70_w2
private theorem endpoint_8_70_w4 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 4 2 230432972588573789 = some 230432972588573789 := by decide +kernel
private theorem endpoint_8_70_p6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 6 230432972588573789 = some 230432972588573789 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 4 2 230432972588573789 230432972588573789 230432972588573789 endpoint_8_70_p4 endpoint_8_70_w4
private theorem endpoint_8_70_w6 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 6 1 230432972588573789 = some 230432972588573789 := by decide +kernel
private theorem endpoint_8_70_p7 : receiptWindow endpoint_8_70_flag endpoint_8_70_sources 0 7 230432972588573789 = some 230432972588573789 :=
  join_receipt_window endpoint_8_70_flag endpoint_8_70_sources 0 6 1 230432972588573789 230432972588573789 230432972588573789 endpoint_8_70_p6 endpoint_8_70_w6
def endpoint_8_70 : CertifiedEndpoint :=
  ⟨⟨8, 70, 3009⟩, 230432972588573789, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_8_70_flag endpoint_8_70_sources 7 230432972588573789 230432972588573789 rfl endpoint_8_70_base endpoint_8_70_p7) (by decide)⟩
private def endpoint_8_71_flag : Flag := ⟨8, 71, 2932⟩
private def endpoint_8_71_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_8_71_base : receiptBase endpoint_8_71_flag endpoint_8_71_sources = some 229026293033528888 := by decide +kernel
private theorem endpoint_8_71_w0 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 2 229026293033528888 = some 229026293033528888 := by decide +kernel
private theorem endpoint_8_71_w2 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 2 2 229026293033528888 = some 229026293033528888 := by decide +kernel
private theorem endpoint_8_71_p4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 4 229026293033528888 = some 229026293033528888 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 2 2 229026293033528888 229026293033528888 229026293033528888 endpoint_8_71_w0 endpoint_8_71_w2
private theorem endpoint_8_71_w4 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 4 2 229026293033528888 = some 229026293033528888 := by decide +kernel
private theorem endpoint_8_71_p6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 6 229026293033528888 = some 229026293033528888 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 4 2 229026293033528888 229026293033528888 229026293033528888 endpoint_8_71_p4 endpoint_8_71_w4
private theorem endpoint_8_71_w6 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 6 1 229026293033528888 = some 229026293033528888 := by decide +kernel
private theorem endpoint_8_71_p7 : receiptWindow endpoint_8_71_flag endpoint_8_71_sources 0 7 229026293033528888 = some 229026293033528888 :=
  join_receipt_window endpoint_8_71_flag endpoint_8_71_sources 0 6 1 229026293033528888 229026293033528888 229026293033528888 endpoint_8_71_p6 endpoint_8_71_w6
def endpoint_8_71 : CertifiedEndpoint :=
  ⟨⟨8, 71, 2932⟩, 229026293033528888, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_8_71_flag endpoint_8_71_sources 7 229026293033528888 229026293033528888 rfl endpoint_8_71_base endpoint_8_71_p7) (by decide)⟩
private def endpoint_8_72_flag : Flag := ⟨8, 72, 2852⟩
private def endpoint_8_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_72_base : receiptBase endpoint_8_72_flag endpoint_8_72_sources = some 227089344546175076 := by decide +kernel
private theorem endpoint_8_72_w0 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 2 227089344546175076 = some 227089344546175076 := by decide +kernel
private theorem endpoint_8_72_w2 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 2 2 227089344546175076 = some 227089344546175076 := by decide +kernel
private theorem endpoint_8_72_p4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 4 227089344546175076 = some 227089344546175076 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 2 2 227089344546175076 227089344546175076 227089344546175076 endpoint_8_72_w0 endpoint_8_72_w2
private theorem endpoint_8_72_w4 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 4 2 227089344546175076 = some 227089344546175076 := by decide +kernel
private theorem endpoint_8_72_p6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 6 227089344546175076 = some 227089344546175076 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 4 2 227089344546175076 227089344546175076 227089344546175076 endpoint_8_72_p4 endpoint_8_72_w4
private theorem endpoint_8_72_w6 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 6 1 227089344546175076 = some 227089344546175076 := by decide +kernel
private theorem endpoint_8_72_p7 : receiptWindow endpoint_8_72_flag endpoint_8_72_sources 0 7 227089344546175076 = some 227089344546175076 :=
  join_receipt_window endpoint_8_72_flag endpoint_8_72_sources 0 6 1 227089344546175076 227089344546175076 227089344546175076 endpoint_8_72_p6 endpoint_8_72_w6
def endpoint_8_72 : CertifiedEndpoint :=
  ⟨⟨8, 72, 2852⟩, 227089344546175076, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_72_flag endpoint_8_72_sources 7 227089344546175076 227089344546175076 rfl endpoint_8_72_base endpoint_8_72_p7) (by decide)⟩
private def endpoint_8_73_flag : Flag := ⟨8, 73, 2769⟩
private def endpoint_8_73_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_73_base : receiptBase endpoint_8_73_flag endpoint_8_73_sources = some 223278939001974755 := by decide +kernel
private theorem endpoint_8_73_w0 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 2 223278939001974755 = some 223278939001974755 := by decide +kernel
private theorem endpoint_8_73_w2 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 2 2 223278939001974755 = some 223278939001974755 := by decide +kernel
private theorem endpoint_8_73_p4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 4 223278939001974755 = some 223278939001974755 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 2 2 223278939001974755 223278939001974755 223278939001974755 endpoint_8_73_w0 endpoint_8_73_w2
private theorem endpoint_8_73_w4 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 4 2 223278939001974755 = some 223278939001974755 := by decide +kernel
private theorem endpoint_8_73_p6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 6 223278939001974755 = some 223278939001974755 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 4 2 223278939001974755 223278939001974755 223278939001974755 endpoint_8_73_p4 endpoint_8_73_w4
private theorem endpoint_8_73_w6 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 6 1 223278939001974755 = some 223278939001974755 := by decide +kernel
private theorem endpoint_8_73_p7 : receiptWindow endpoint_8_73_flag endpoint_8_73_sources 0 7 223278939001974755 = some 223278939001974755 :=
  join_receipt_window endpoint_8_73_flag endpoint_8_73_sources 0 6 1 223278939001974755 223278939001974755 223278939001974755 endpoint_8_73_p6 endpoint_8_73_w6
def endpoint_8_73 : CertifiedEndpoint :=
  ⟨⟨8, 73, 2769⟩, 223278939001974755, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_73_flag endpoint_8_73_sources 7 223278939001974755 223278939001974755 rfl endpoint_8_73_base endpoint_8_73_p7) (by decide)⟩
private def endpoint_8_74_flag : Flag := ⟨8, 74, 2682⟩
private def endpoint_8_74_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_8_74_base : receiptBase endpoint_8_74_flag endpoint_8_74_sources = some 218978150724422902 := by decide +kernel
private theorem endpoint_8_74_w0 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 2 218978150724422902 = some 218978150724422902 := by decide +kernel
private theorem endpoint_8_74_w2 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 2 2 218978150724422902 = some 218978150724422902 := by decide +kernel
private theorem endpoint_8_74_p4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 4 218978150724422902 = some 218978150724422902 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 2 2 218978150724422902 218978150724422902 218978150724422902 endpoint_8_74_w0 endpoint_8_74_w2
private theorem endpoint_8_74_w4 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 4 2 218978150724422902 = some 218978150724422902 := by decide +kernel
private theorem endpoint_8_74_p6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 6 218978150724422902 = some 218978150724422902 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 4 2 218978150724422902 218978150724422902 218978150724422902 endpoint_8_74_p4 endpoint_8_74_w4
private theorem endpoint_8_74_w6 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 6 1 218978150724422902 = some 218978150724422902 := by decide +kernel
private theorem endpoint_8_74_p7 : receiptWindow endpoint_8_74_flag endpoint_8_74_sources 0 7 218978150724422902 = some 218978150724422902 :=
  join_receipt_window endpoint_8_74_flag endpoint_8_74_sources 0 6 1 218978150724422902 218978150724422902 218978150724422902 endpoint_8_74_p6 endpoint_8_74_w6
def endpoint_8_74 : CertifiedEndpoint :=
  ⟨⟨8, 74, 2682⟩, 218978150724422902, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_8_74_flag endpoint_8_74_sources 7 218978150724422902 218978150724422902 rfl endpoint_8_74_base endpoint_8_74_p7) (by decide)⟩
private def endpoint_8_75_flag : Flag := ⟨8, 75, 2593⟩
private def endpoint_8_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_75_base : receiptBase endpoint_8_75_flag endpoint_8_75_sources = some 218529487738072626 := by decide +kernel
private theorem endpoint_8_75_w0 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 2 218529487738072626 = some 218529487738072626 := by decide +kernel
private theorem endpoint_8_75_w2 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 2 2 218529487738072626 = some 218529487738072626 := by decide +kernel
private theorem endpoint_8_75_p4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 4 218529487738072626 = some 218529487738072626 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 2 2 218529487738072626 218529487738072626 218529487738072626 endpoint_8_75_w0 endpoint_8_75_w2
private theorem endpoint_8_75_w4 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 4 2 218529487738072626 = some 218529487738072626 := by decide +kernel
private theorem endpoint_8_75_p6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 6 218529487738072626 = some 218529487738072626 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 4 2 218529487738072626 218529487738072626 218529487738072626 endpoint_8_75_p4 endpoint_8_75_w4
private theorem endpoint_8_75_w6 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 6 1 218529487738072626 = some 218529487738072626 := by decide +kernel
private theorem endpoint_8_75_p7 : receiptWindow endpoint_8_75_flag endpoint_8_75_sources 0 7 218529487738072626 = some 218529487738072626 :=
  join_receipt_window endpoint_8_75_flag endpoint_8_75_sources 0 6 1 218529487738072626 218529487738072626 218529487738072626 endpoint_8_75_p6 endpoint_8_75_w6
def endpoint_8_75 : CertifiedEndpoint :=
  ⟨⟨8, 75, 2593⟩, 218529487738072626, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_75_flag endpoint_8_75_sources 7 218529487738072626 218529487738072626 rfl endpoint_8_75_base endpoint_8_75_p7) (by decide)⟩
private def endpoint_8_76_flag : Flag := ⟨8, 76, 2500⟩
private def endpoint_8_76_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_8_76_base : receiptBase endpoint_8_76_flag endpoint_8_76_sources = some 213333652645886563 := by decide +kernel
private theorem endpoint_8_76_w0 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 2 213333652645886563 = some 213333652645886563 := by decide +kernel
private theorem endpoint_8_76_w2 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 2 2 213333652645886563 = some 213333652645886563 := by decide +kernel
private theorem endpoint_8_76_p4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 4 213333652645886563 = some 213333652645886563 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 2 2 213333652645886563 213333652645886563 213333652645886563 endpoint_8_76_w0 endpoint_8_76_w2
private theorem endpoint_8_76_w4 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 4 2 213333652645886563 = some 213333652645886563 := by decide +kernel
private theorem endpoint_8_76_p6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 6 213333652645886563 = some 213333652645886563 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 4 2 213333652645886563 213333652645886563 213333652645886563 endpoint_8_76_p4 endpoint_8_76_w4
private theorem endpoint_8_76_w6 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 6 1 213333652645886563 = some 213333652645886563 := by decide +kernel
private theorem endpoint_8_76_p7 : receiptWindow endpoint_8_76_flag endpoint_8_76_sources 0 7 213333652645886563 = some 213333652645886563 :=
  join_receipt_window endpoint_8_76_flag endpoint_8_76_sources 0 6 1 213333652645886563 213333652645886563 213333652645886563 endpoint_8_76_p6 endpoint_8_76_w6
def endpoint_8_76 : CertifiedEndpoint :=
  ⟨⟨8, 76, 2500⟩, 213333652645886563, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_8_76_flag endpoint_8_76_sources 7 213333652645886563 213333652645886563 rfl endpoint_8_76_base endpoint_8_76_p7) (by decide)⟩
private def endpoint_8_77_flag : Flag := ⟨8, 77, 2405⟩
private def endpoint_8_77_sources : Sources := ⟨contact11, contact11, contact13⟩
private theorem endpoint_8_77_base : receiptBase endpoint_8_77_flag endpoint_8_77_sources = some 207834455229033955 := by decide +kernel
private theorem endpoint_8_77_w0 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 2 207834455229033955 = some 207834455229033955 := by decide +kernel
private theorem endpoint_8_77_w2 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 2 2 207834455229033955 = some 207834455229033955 := by decide +kernel
private theorem endpoint_8_77_p4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 4 207834455229033955 = some 207834455229033955 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 2 2 207834455229033955 207834455229033955 207834455229033955 endpoint_8_77_w0 endpoint_8_77_w2
private theorem endpoint_8_77_w4 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 4 2 207834455229033955 = some 207834455229033955 := by decide +kernel
private theorem endpoint_8_77_p6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 6 207834455229033955 = some 207834455229033955 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 4 2 207834455229033955 207834455229033955 207834455229033955 endpoint_8_77_p4 endpoint_8_77_w4
private theorem endpoint_8_77_w6 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 6 1 207834455229033955 = some 207834455229033955 := by decide +kernel
private theorem endpoint_8_77_p7 : receiptWindow endpoint_8_77_flag endpoint_8_77_sources 0 7 207834455229033955 = some 207834455229033955 :=
  join_receipt_window endpoint_8_77_flag endpoint_8_77_sources 0 6 1 207834455229033955 207834455229033955 207834455229033955 endpoint_8_77_p6 endpoint_8_77_w6
def endpoint_8_77 : CertifiedEndpoint :=
  ⟨⟨8, 77, 2405⟩, 207834455229033955, .terminal ⟨contact11, contact11, contact13⟩ (finish_receipt_window endpoint_8_77_flag endpoint_8_77_sources 7 207834455229033955 207834455229033955 rfl endpoint_8_77_base endpoint_8_77_p7) (by decide)⟩
private def endpoint_8_78_flag : Flag := ⟨8, 78, 2306⟩
private def endpoint_8_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_78_base : receiptBase endpoint_8_78_flag endpoint_8_78_sources = some 203715444723032284 := by decide +kernel
private theorem endpoint_8_78_w0 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 2 203715444723032284 = some 203715444723032284 := by decide +kernel
private theorem endpoint_8_78_w2 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 2 2 203715444723032284 = some 203715444723032284 := by decide +kernel
private theorem endpoint_8_78_p4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 4 203715444723032284 = some 203715444723032284 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 2 2 203715444723032284 203715444723032284 203715444723032284 endpoint_8_78_w0 endpoint_8_78_w2
private theorem endpoint_8_78_w4 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 4 2 203715444723032284 = some 203715444723032284 := by decide +kernel
private theorem endpoint_8_78_p6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 6 203715444723032284 = some 203715444723032284 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 4 2 203715444723032284 203715444723032284 203715444723032284 endpoint_8_78_p4 endpoint_8_78_w4
private theorem endpoint_8_78_w6 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 6 1 203715444723032284 = some 203715444723032284 := by decide +kernel
private theorem endpoint_8_78_p7 : receiptWindow endpoint_8_78_flag endpoint_8_78_sources 0 7 203715444723032284 = some 203715444723032284 :=
  join_receipt_window endpoint_8_78_flag endpoint_8_78_sources 0 6 1 203715444723032284 203715444723032284 203715444723032284 endpoint_8_78_p6 endpoint_8_78_w6
def endpoint_8_78 : CertifiedEndpoint :=
  ⟨⟨8, 78, 2306⟩, 203715444723032284, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_78_flag endpoint_8_78_sources 7 203715444723032284 203715444723032284 rfl endpoint_8_78_base endpoint_8_78_p7) (by decide)⟩
private def endpoint_8_79_flag : Flag := ⟨8, 79, 2204⟩
private def endpoint_8_79_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_79_base : receiptBase endpoint_8_79_flag endpoint_8_79_sources = some 197022953598016838 := by decide +kernel
private theorem endpoint_8_79_w0 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 2 197022953598016838 = some 197022953598016838 := by decide +kernel
private theorem endpoint_8_79_w2 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 2 2 197022953598016838 = some 197022953598016838 := by decide +kernel
private theorem endpoint_8_79_p4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 4 197022953598016838 = some 197022953598016838 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 2 2 197022953598016838 197022953598016838 197022953598016838 endpoint_8_79_w0 endpoint_8_79_w2
private theorem endpoint_8_79_w4 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 4 2 197022953598016838 = some 197022953598016838 := by decide +kernel
private theorem endpoint_8_79_p6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 6 197022953598016838 = some 197022953598016838 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 4 2 197022953598016838 197022953598016838 197022953598016838 endpoint_8_79_p4 endpoint_8_79_w4
private theorem endpoint_8_79_w6 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 6 1 197022953598016838 = some 197022953598016838 := by decide +kernel
private theorem endpoint_8_79_p7 : receiptWindow endpoint_8_79_flag endpoint_8_79_sources 0 7 197022953598016838 = some 197022953598016838 :=
  join_receipt_window endpoint_8_79_flag endpoint_8_79_sources 0 6 1 197022953598016838 197022953598016838 197022953598016838 endpoint_8_79_p6 endpoint_8_79_w6
def endpoint_8_79 : CertifiedEndpoint :=
  ⟨⟨8, 79, 2204⟩, 197022953598016838, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_79_flag endpoint_8_79_sources 7 197022953598016838 197022953598016838 rfl endpoint_8_79_base endpoint_8_79_p7) (by decide)⟩
private def endpoint_8_80_flag : Flag := ⟨8, 80, 2098⟩
private def endpoint_8_80_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_8_80_base : receiptBase endpoint_8_80_flag endpoint_8_80_sources = some 189764758356613519 := by decide +kernel
private theorem endpoint_8_80_w0 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 2 189764758356613519 = some 189764758356613519 := by decide +kernel
private theorem endpoint_8_80_w2 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 2 2 189764758356613519 = some 189764758356613519 := by decide +kernel
private theorem endpoint_8_80_p4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 4 189764758356613519 = some 189764758356613519 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 2 2 189764758356613519 189764758356613519 189764758356613519 endpoint_8_80_w0 endpoint_8_80_w2
private theorem endpoint_8_80_w4 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 4 2 189764758356613519 = some 189764758356613519 := by decide +kernel
private theorem endpoint_8_80_p6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 6 189764758356613519 = some 189764758356613519 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 4 2 189764758356613519 189764758356613519 189764758356613519 endpoint_8_80_p4 endpoint_8_80_w4
private theorem endpoint_8_80_w6 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 6 1 189764758356613519 = some 189764758356613519 := by decide +kernel
private theorem endpoint_8_80_p7 : receiptWindow endpoint_8_80_flag endpoint_8_80_sources 0 7 189764758356613519 = some 189764758356613519 :=
  join_receipt_window endpoint_8_80_flag endpoint_8_80_sources 0 6 1 189764758356613519 189764758356613519 189764758356613519 endpoint_8_80_p6 endpoint_8_80_w6
def endpoint_8_80 : CertifiedEndpoint :=
  ⟨⟨8, 80, 2098⟩, 189764758356613519, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_8_80_flag endpoint_8_80_sources 7 189764758356613519 189764758356613519 rfl endpoint_8_80_base endpoint_8_80_p7) (by decide)⟩
private def endpoint_8_81_flag : Flag := ⟨8, 81, 1990⟩
private def endpoint_8_81_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_8_81_base : receiptBase endpoint_8_81_flag endpoint_8_81_sources = some 184102937892520742 := by decide +kernel
private theorem endpoint_8_81_w0 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 2 184102937892520742 = some 184102937892520742 := by decide +kernel
private theorem endpoint_8_81_w2 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 2 2 184102937892520742 = some 184102937892520742 := by decide +kernel
private theorem endpoint_8_81_p4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 4 184102937892520742 = some 184102937892520742 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 2 2 184102937892520742 184102937892520742 184102937892520742 endpoint_8_81_w0 endpoint_8_81_w2
private theorem endpoint_8_81_w4 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 4 2 184102937892520742 = some 184102937892520742 := by decide +kernel
private theorem endpoint_8_81_p6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 6 184102937892520742 = some 184102937892520742 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 4 2 184102937892520742 184102937892520742 184102937892520742 endpoint_8_81_p4 endpoint_8_81_w4
private theorem endpoint_8_81_w6 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 6 1 184102937892520742 = some 184102937892520742 := by decide +kernel
private theorem endpoint_8_81_p7 : receiptWindow endpoint_8_81_flag endpoint_8_81_sources 0 7 184102937892520742 = some 184102937892520742 :=
  join_receipt_window endpoint_8_81_flag endpoint_8_81_sources 0 6 1 184102937892520742 184102937892520742 184102937892520742 endpoint_8_81_p6 endpoint_8_81_w6
def endpoint_8_81 : CertifiedEndpoint :=
  ⟨⟨8, 81, 1990⟩, 184102937892520742, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_8_81_flag endpoint_8_81_sources 7 184102937892520742 184102937892520742 rfl endpoint_8_81_base endpoint_8_81_p7) (by decide)⟩
private def endpoint_8_82_flag : Flag := ⟨8, 82, 1878⟩
private def endpoint_8_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_8_82_base : receiptBase endpoint_8_82_flag endpoint_8_82_sources = some 177688431380576348 := by decide +kernel
private theorem endpoint_8_82_w0 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 2 177688431380576348 = some 177688431380576348 := by decide +kernel
private theorem endpoint_8_82_w2 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 2 2 177688431380576348 = some 177688431380576348 := by decide +kernel
private theorem endpoint_8_82_p4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 4 177688431380576348 = some 177688431380576348 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 2 2 177688431380576348 177688431380576348 177688431380576348 endpoint_8_82_w0 endpoint_8_82_w2
private theorem endpoint_8_82_w4 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 4 2 177688431380576348 = some 177688431380576348 := by decide +kernel
private theorem endpoint_8_82_p6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 6 177688431380576348 = some 177688431380576348 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 4 2 177688431380576348 177688431380576348 177688431380576348 endpoint_8_82_p4 endpoint_8_82_w4
private theorem endpoint_8_82_w6 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 6 1 177688431380576348 = some 177688431380576348 := by decide +kernel
private theorem endpoint_8_82_p7 : receiptWindow endpoint_8_82_flag endpoint_8_82_sources 0 7 177688431380576348 = some 177688431380576348 :=
  join_receipt_window endpoint_8_82_flag endpoint_8_82_sources 0 6 1 177688431380576348 177688431380576348 177688431380576348 endpoint_8_82_p6 endpoint_8_82_w6
def endpoint_8_82 : CertifiedEndpoint :=
  ⟨⟨8, 82, 1878⟩, 177688431380576348, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_8_82_flag endpoint_8_82_sources 7 177688431380576348 177688431380576348 rfl endpoint_8_82_base endpoint_8_82_p7) (by decide)⟩
def endpoint_8_83 : CertifiedEndpoint :=
  ⟨⟨8, 83, 1764⟩, 262182192239616201, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_84 : CertifiedEndpoint :=
  ⟨⟨8, 84, 1646⟩, 247231622661159418, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_85 : CertifiedEndpoint :=
  ⟨⟨8, 85, 1524⟩, 231195790360956441, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_86 : CertifiedEndpoint :=
  ⟨⟨8, 86, 1400⟩, 214367860093324316, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_87 : CertifiedEndpoint :=
  ⟨⟨8, 87, 1272⟩, 196415839616544277, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_88 : CertifiedEndpoint :=
  ⟨⟨8, 88, 1142⟩, 177640659182413714, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_89 : CertifiedEndpoint :=
  ⟨⟨8, 89, 1008⟩, 157702561051733517, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_90 : CertifiedEndpoint :=
  ⟨⟨8, 90, 871⟩, 136744244852922037, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_91 : CertifiedEndpoint :=
  ⟨⟨8, 91, 730⟩, 114580300721419031, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_92 : CertifiedEndpoint :=
  ⟨⟨8, 92, 587⟩, 91527189903982577, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_93 : CertifiedEndpoint :=
  ⟨⟨8, 93, 440⟩, 67229623666452877, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_94 : CertifiedEndpoint :=
  ⟨⟨8, 94, 290⟩, 41838067134728626, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_8_95 : CertifiedEndpoint :=
  ⟨⟨8, 95, 137⟩, 15335047939479050, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_9 : CertifiedEndpoint :=
  ⟨⟨9, 9, 4989⟩, 58672794825562698, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_10 : CertifiedEndpoint :=
  ⟨⟨9, 10, 4968⟩, 61959731289808156, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_11 : CertifiedEndpoint :=
  ⟨⟨9, 11, 4947⟩, 65216722474110392, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_12 : CertifiedEndpoint :=
  ⟨⟨9, 12, 4926⟩, 75746829910153242, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_13 : CertifiedEndpoint :=
  ⟨⟨9, 13, 4905⟩, 86182376962124558, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_14 : CertifiedEndpoint :=
  ⟨⟨9, 14, 4883⟩, 96503563306695195, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_15 : CertifiedEndpoint :=
  ⟨⟨9, 15, 4861⟩, 106725791109795622, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_16 : CertifiedEndpoint :=
  ⟨⟨9, 16, 4839⟩, 116849060371425839, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_17 : CertifiedEndpoint :=
  ⟨⟨9, 17, 4817⟩, 126873371091585846, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_18 : CertifiedEndpoint :=
  ⟨⟨9, 18, 4794⟩, 136770126632149146, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_19 : CertifiedEndpoint :=
  ⟨⟨9, 19, 4772⟩, 146594321190669395, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_20 : CertifiedEndpoint :=
  ⟨⟨9, 20, 4749⟩, 156286562412194261, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_21 : CertifiedEndpoint :=
  ⟨⟨9, 21, 4726⟩, 165875446934850241, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_22 : CertifiedEndpoint :=
  ⟨⟨9, 22, 4702⟩, 175323581805713486, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_23 : CertifiedEndpoint :=
  ⟨⟨9, 23, 4679⟩, 184703553851932356, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_24 : CertifiedEndpoint :=
  ⟨⟨9, 24, 4655⟩, 193938378088959815, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_25 : CertifiedEndpoint :=
  ⟨⟨9, 25, 4631⟩, 203065447469719712, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_26 : CertifiedEndpoint :=
  ⟨⟨9, 26, 4606⟩, 212038572726490846, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_27 : CertifiedEndpoint :=
  ⟨⟨9, 27, 4582⟩, 220947933316016281, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_28 : CertifiedEndpoint :=
  ⟨⟨9, 28, 4557⟩, 229698951624154277, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_29 : CertifiedEndpoint :=
  ⟨⟨9, 29, 4531⟩, 238285030414806820, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_30 : CertifiedEndpoint :=
  ⟨⟨9, 30, 4506⟩, 246809543616913002, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_31 : CertifiedEndpoint :=
  ⟨⟨9, 31, 4480⟩, 255164719144135055, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_32 : CertifiedEndpoint :=
  ⟨⟨9, 32, 4454⟩, 263403343500292194, .intrinsic (by decide +kernel) (by decide)⟩
private def endpoint_9_33_flag : Flag := ⟨9, 33, 4427⟩
private def endpoint_9_33_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_33_base : receiptBase endpoint_9_33_flag endpoint_9_33_sources = some 183793736370388836 := by decide +kernel
private theorem endpoint_9_33_w0 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 2 183793736370388836 = some 183793736370388836 := by decide +kernel
private theorem endpoint_9_33_w2 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 2 2 183793736370388836 = some 183793736370388836 := by decide +kernel
private theorem endpoint_9_33_p4 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 4 183793736370388836 = some 183793736370388836 :=
  join_receipt_window endpoint_9_33_flag endpoint_9_33_sources 0 2 2 183793736370388836 183793736370388836 183793736370388836 endpoint_9_33_w0 endpoint_9_33_w2
private theorem endpoint_9_33_w4 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 4 2 183793736370388836 = some 183793736370388836 := by decide +kernel
private theorem endpoint_9_33_p6 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 6 183793736370388836 = some 183793736370388836 :=
  join_receipt_window endpoint_9_33_flag endpoint_9_33_sources 0 4 2 183793736370388836 183793736370388836 183793736370388836 endpoint_9_33_p4 endpoint_9_33_w4
private theorem endpoint_9_33_w6 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 6 2 183793736370388836 = some 183793736370388836 := by decide +kernel
private theorem endpoint_9_33_p8 : receiptWindow endpoint_9_33_flag endpoint_9_33_sources 0 8 183793736370388836 = some 183793736370388836 :=
  join_receipt_window endpoint_9_33_flag endpoint_9_33_sources 0 6 2 183793736370388836 183793736370388836 183793736370388836 endpoint_9_33_p6 endpoint_9_33_w6
def endpoint_9_33 : CertifiedEndpoint :=
  ⟨⟨9, 33, 4427⟩, 183793736370388836, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_33_flag endpoint_9_33_sources 8 183793736370388836 183793736370388836 rfl endpoint_9_33_base endpoint_9_33_p8) (by decide)⟩
private def endpoint_9_34_flag : Flag := ⟨9, 34, 4400⟩
private def endpoint_9_34_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_34_base : receiptBase endpoint_9_34_flag endpoint_9_34_sources = some 187220821518930705 := by decide +kernel
private theorem endpoint_9_34_w0 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 2 187220821518930705 = some 187220821518930705 := by decide +kernel
private theorem endpoint_9_34_w2 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 2 2 187220821518930705 = some 187220821518930705 := by decide +kernel
private theorem endpoint_9_34_p4 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 4 187220821518930705 = some 187220821518930705 :=
  join_receipt_window endpoint_9_34_flag endpoint_9_34_sources 0 2 2 187220821518930705 187220821518930705 187220821518930705 endpoint_9_34_w0 endpoint_9_34_w2
private theorem endpoint_9_34_w4 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 4 2 187220821518930705 = some 187220821518930705 := by decide +kernel
private theorem endpoint_9_34_p6 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 6 187220821518930705 = some 187220821518930705 :=
  join_receipt_window endpoint_9_34_flag endpoint_9_34_sources 0 4 2 187220821518930705 187220821518930705 187220821518930705 endpoint_9_34_p4 endpoint_9_34_w4
private theorem endpoint_9_34_w6 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 6 2 187220821518930705 = some 187220821518930705 := by decide +kernel
private theorem endpoint_9_34_p8 : receiptWindow endpoint_9_34_flag endpoint_9_34_sources 0 8 187220821518930705 = some 187220821518930705 :=
  join_receipt_window endpoint_9_34_flag endpoint_9_34_sources 0 6 2 187220821518930705 187220821518930705 187220821518930705 endpoint_9_34_p6 endpoint_9_34_w6
def endpoint_9_34 : CertifiedEndpoint :=
  ⟨⟨9, 34, 4400⟩, 187220821518930705, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_34_flag endpoint_9_34_sources 8 187220821518930705 187220821518930705 rfl endpoint_9_34_base endpoint_9_34_p8) (by decide)⟩
private def endpoint_9_35_flag : Flag := ⟨9, 35, 4373⟩
private def endpoint_9_35_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_35_base : receiptBase endpoint_9_35_flag endpoint_9_35_sources = some 190592077036655823 := by decide +kernel
private theorem endpoint_9_35_w0 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 2 190592077036655823 = some 190592077036655823 := by decide +kernel
private theorem endpoint_9_35_w2 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 2 2 190592077036655823 = some 190592077036655823 := by decide +kernel
private theorem endpoint_9_35_p4 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 4 190592077036655823 = some 190592077036655823 :=
  join_receipt_window endpoint_9_35_flag endpoint_9_35_sources 0 2 2 190592077036655823 190592077036655823 190592077036655823 endpoint_9_35_w0 endpoint_9_35_w2
private theorem endpoint_9_35_w4 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 4 2 190592077036655823 = some 190592077036655823 := by decide +kernel
private theorem endpoint_9_35_p6 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 6 190592077036655823 = some 190592077036655823 :=
  join_receipt_window endpoint_9_35_flag endpoint_9_35_sources 0 4 2 190592077036655823 190592077036655823 190592077036655823 endpoint_9_35_p4 endpoint_9_35_w4
private theorem endpoint_9_35_w6 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 6 2 190592077036655823 = some 190592077036655823 := by decide +kernel
private theorem endpoint_9_35_p8 : receiptWindow endpoint_9_35_flag endpoint_9_35_sources 0 8 190592077036655823 = some 190592077036655823 :=
  join_receipt_window endpoint_9_35_flag endpoint_9_35_sources 0 6 2 190592077036655823 190592077036655823 190592077036655823 endpoint_9_35_p6 endpoint_9_35_w6
def endpoint_9_35 : CertifiedEndpoint :=
  ⟨⟨9, 35, 4373⟩, 190592077036655823, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_35_flag endpoint_9_35_sources 8 190592077036655823 190592077036655823 rfl endpoint_9_35_base endpoint_9_35_p8) (by decide)⟩
private def endpoint_9_36_flag : Flag := ⟨9, 36, 4345⟩
private def endpoint_9_36_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_36_base : receiptBase endpoint_9_36_flag endpoint_9_36_sources = some 193863449980324894 := by decide +kernel
private theorem endpoint_9_36_w0 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 2 193863449980324894 = some 193863449980324894 := by decide +kernel
private theorem endpoint_9_36_w2 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 2 2 193863449980324894 = some 193863449980324894 := by decide +kernel
private theorem endpoint_9_36_p4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 4 193863449980324894 = some 193863449980324894 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 2 2 193863449980324894 193863449980324894 193863449980324894 endpoint_9_36_w0 endpoint_9_36_w2
private theorem endpoint_9_36_w4 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 4 2 193863449980324894 = some 193863449980324894 := by decide +kernel
private theorem endpoint_9_36_p6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 6 193863449980324894 = some 193863449980324894 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 4 2 193863449980324894 193863449980324894 193863449980324894 endpoint_9_36_p4 endpoint_9_36_w4
private theorem endpoint_9_36_w6 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 6 2 193863449980324894 = some 193863449980324894 := by decide +kernel
private theorem endpoint_9_36_p8 : receiptWindow endpoint_9_36_flag endpoint_9_36_sources 0 8 193863449980324894 = some 193863449980324894 :=
  join_receipt_window endpoint_9_36_flag endpoint_9_36_sources 0 6 2 193863449980324894 193863449980324894 193863449980324894 endpoint_9_36_p6 endpoint_9_36_w6
def endpoint_9_36 : CertifiedEndpoint :=
  ⟨⟨9, 36, 4345⟩, 193863449980324894, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_36_flag endpoint_9_36_sources 8 193863449980324894 193863449980324894 rfl endpoint_9_36_base endpoint_9_36_p8) (by decide)⟩
private def endpoint_9_37_flag : Flag := ⟨9, 37, 4317⟩
private def endpoint_9_37_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_37_base : receiptBase endpoint_9_37_flag endpoint_9_37_sources = some 197076963288405878 := by decide +kernel
private theorem endpoint_9_37_w0 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 2 197076963288405878 = some 197076963288405878 := by decide +kernel
private theorem endpoint_9_37_w2 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 2 2 197076963288405878 = some 197076963288405878 := by decide +kernel
private theorem endpoint_9_37_p4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 4 197076963288405878 = some 197076963288405878 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 2 2 197076963288405878 197076963288405878 197076963288405878 endpoint_9_37_w0 endpoint_9_37_w2
private theorem endpoint_9_37_w4 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 4 2 197076963288405878 = some 197076963288405878 := by decide +kernel
private theorem endpoint_9_37_p6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 6 197076963288405878 = some 197076963288405878 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 4 2 197076963288405878 197076963288405878 197076963288405878 endpoint_9_37_p4 endpoint_9_37_w4
private theorem endpoint_9_37_w6 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 6 2 197076963288405878 = some 197076963288405878 := by decide +kernel
private theorem endpoint_9_37_p8 : receiptWindow endpoint_9_37_flag endpoint_9_37_sources 0 8 197076963288405878 = some 197076963288405878 :=
  join_receipt_window endpoint_9_37_flag endpoint_9_37_sources 0 6 2 197076963288405878 197076963288405878 197076963288405878 endpoint_9_37_p6 endpoint_9_37_w6
def endpoint_9_37 : CertifiedEndpoint :=
  ⟨⟨9, 37, 4317⟩, 197076963288405878, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_37_flag endpoint_9_37_sources 8 197076963288405878 197076963288405878 rfl endpoint_9_37_base endpoint_9_37_p8) (by decide)⟩
private def endpoint_9_38_flag : Flag := ⟨9, 38, 4289⟩
private def endpoint_9_38_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_38_base : receiptBase endpoint_9_38_flag endpoint_9_38_sources = some 200232616960898775 := by decide +kernel
private theorem endpoint_9_38_w0 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 2 200232616960898775 = some 200232616960898775 := by decide +kernel
private theorem endpoint_9_38_w2 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 2 2 200232616960898775 = some 200232616960898775 := by decide +kernel
private theorem endpoint_9_38_p4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 4 200232616960898775 = some 200232616960898775 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 2 2 200232616960898775 200232616960898775 200232616960898775 endpoint_9_38_w0 endpoint_9_38_w2
private theorem endpoint_9_38_w4 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 4 2 200232616960898775 = some 200232616960898775 := by decide +kernel
private theorem endpoint_9_38_p6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 6 200232616960898775 = some 200232616960898775 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 4 2 200232616960898775 200232616960898775 200232616960898775 endpoint_9_38_p4 endpoint_9_38_w4
private theorem endpoint_9_38_w6 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 6 2 200232616960898775 = some 200232616960898775 := by decide +kernel
private theorem endpoint_9_38_p8 : receiptWindow endpoint_9_38_flag endpoint_9_38_sources 0 8 200232616960898775 = some 200232616960898775 :=
  join_receipt_window endpoint_9_38_flag endpoint_9_38_sources 0 6 2 200232616960898775 200232616960898775 200232616960898775 endpoint_9_38_p6 endpoint_9_38_w6
def endpoint_9_38 : CertifiedEndpoint :=
  ⟨⟨9, 38, 4289⟩, 200232616960898775, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_38_flag endpoint_9_38_sources 8 200232616960898775 200232616960898775 rfl endpoint_9_38_base endpoint_9_38_p8) (by decide)⟩
private def endpoint_9_39_flag : Flag := ⟨9, 39, 4260⟩
private def endpoint_9_39_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_39_base : receiptBase endpoint_9_39_flag endpoint_9_39_sources = some 203283313047407285 := by decide +kernel
private theorem endpoint_9_39_w0 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 2 203283313047407285 = some 203283313047407285 := by decide +kernel
private theorem endpoint_9_39_w2 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 2 2 203283313047407285 = some 203283313047407285 := by decide +kernel
private theorem endpoint_9_39_p4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 4 203283313047407285 = some 203283313047407285 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 2 2 203283313047407285 203283313047407285 203283313047407285 endpoint_9_39_w0 endpoint_9_39_w2
private theorem endpoint_9_39_w4 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 4 2 203283313047407285 = some 203283313047407285 := by decide +kernel
private theorem endpoint_9_39_p6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 6 203283313047407285 = some 203283313047407285 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 4 2 203283313047407285 203283313047407285 203283313047407285 endpoint_9_39_p4 endpoint_9_39_w4
private theorem endpoint_9_39_w6 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 6 2 203283313047407285 = some 203283313047407285 := by decide +kernel
private theorem endpoint_9_39_p8 : receiptWindow endpoint_9_39_flag endpoint_9_39_sources 0 8 203283313047407285 = some 203283313047407285 :=
  join_receipt_window endpoint_9_39_flag endpoint_9_39_sources 0 6 2 203283313047407285 203283313047407285 203283313047407285 endpoint_9_39_p6 endpoint_9_39_w6
def endpoint_9_39 : CertifiedEndpoint :=
  ⟨⟨9, 39, 4260⟩, 203283313047407285, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_39_flag endpoint_9_39_sources 8 203283313047407285 203283313047407285 rfl endpoint_9_39_base endpoint_9_39_p8) (by decide)⟩
private def endpoint_9_40_flag : Flag := ⟨9, 40, 4230⟩
private def endpoint_9_40_sources : Sources := ⟨contact17, contact01, contact10⟩
private theorem endpoint_9_40_base : receiptBase endpoint_9_40_flag endpoint_9_40_sources = some 206226006540774406 := by decide +kernel
private theorem endpoint_9_40_w0 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 2 206226006540774406 = some 206226006540774406 := by decide +kernel
private theorem endpoint_9_40_w2 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 2 2 206226006540774406 = some 206226006540774406 := by decide +kernel
private theorem endpoint_9_40_p4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 4 206226006540774406 = some 206226006540774406 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 2 2 206226006540774406 206226006540774406 206226006540774406 endpoint_9_40_w0 endpoint_9_40_w2
private theorem endpoint_9_40_w4 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 4 2 206226006540774406 = some 206226006540774406 := by decide +kernel
private theorem endpoint_9_40_p6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 6 206226006540774406 = some 206226006540774406 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 4 2 206226006540774406 206226006540774406 206226006540774406 endpoint_9_40_p4 endpoint_9_40_w4
private theorem endpoint_9_40_w6 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 6 2 206226006540774406 = some 206226006540774406 := by decide +kernel
private theorem endpoint_9_40_p8 : receiptWindow endpoint_9_40_flag endpoint_9_40_sources 0 8 206226006540774406 = some 206226006540774406 :=
  join_receipt_window endpoint_9_40_flag endpoint_9_40_sources 0 6 2 206226006540774406 206226006540774406 206226006540774406 endpoint_9_40_p6 endpoint_9_40_w6
def endpoint_9_40 : CertifiedEndpoint :=
  ⟨⟨9, 40, 4230⟩, 206226006540774406, .terminal ⟨contact17, contact01, contact10⟩ (finish_receipt_window endpoint_9_40_flag endpoint_9_40_sources 8 206226006540774406 206226006540774406 rfl endpoint_9_40_base endpoint_9_40_p8) (by decide)⟩
private def endpoint_9_41_flag : Flag := ⟨9, 41, 4200⟩
private def endpoint_9_41_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_41_base : receiptBase endpoint_9_41_flag endpoint_9_41_sources = some 209630431906113278 := by decide +kernel
private theorem endpoint_9_41_w0 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 2 209630431906113278 = some 209630431906113278 := by decide +kernel
private theorem endpoint_9_41_w2 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 2 2 209630431906113278 = some 209630431906113278 := by decide +kernel
private theorem endpoint_9_41_p4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 4 209630431906113278 = some 209630431906113278 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 2 2 209630431906113278 209630431906113278 209630431906113278 endpoint_9_41_w0 endpoint_9_41_w2
private theorem endpoint_9_41_w4 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 4 2 209630431906113278 = some 209630431906113278 := by decide +kernel
private theorem endpoint_9_41_p6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 6 209630431906113278 = some 209630431906113278 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 4 2 209630431906113278 209630431906113278 209630431906113278 endpoint_9_41_p4 endpoint_9_41_w4
private theorem endpoint_9_41_w6 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 6 2 209630431906113278 = some 209630431906113278 := by decide +kernel
private theorem endpoint_9_41_p8 : receiptWindow endpoint_9_41_flag endpoint_9_41_sources 0 8 209630431906113278 = some 209630431906113278 :=
  join_receipt_window endpoint_9_41_flag endpoint_9_41_sources 0 6 2 209630431906113278 209630431906113278 209630431906113278 endpoint_9_41_p6 endpoint_9_41_w6
def endpoint_9_41 : CertifiedEndpoint :=
  ⟨⟨9, 41, 4200⟩, 209630431906113278, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_41_flag endpoint_9_41_sources 8 209630431906113278 209630431906113278 rfl endpoint_9_41_base endpoint_9_41_p8) (by decide)⟩
private def endpoint_9_42_flag : Flag := ⟨9, 42, 4170⟩
private def endpoint_9_42_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_42_base : receiptBase endpoint_9_42_flag endpoint_9_42_sources = some 212418473997056902 := by decide +kernel
private theorem endpoint_9_42_w0 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 2 212418473997056902 = some 212418473997056902 := by decide +kernel
private theorem endpoint_9_42_w2 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 2 2 212418473997056902 = some 212418473997056902 := by decide +kernel
private theorem endpoint_9_42_p4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 4 212418473997056902 = some 212418473997056902 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 2 2 212418473997056902 212418473997056902 212418473997056902 endpoint_9_42_w0 endpoint_9_42_w2
private theorem endpoint_9_42_w4 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 4 2 212418473997056902 = some 212418473997056902 := by decide +kernel
private theorem endpoint_9_42_p6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 6 212418473997056902 = some 212418473997056902 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 4 2 212418473997056902 212418473997056902 212418473997056902 endpoint_9_42_p4 endpoint_9_42_w4
private theorem endpoint_9_42_w6 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 6 2 212418473997056902 = some 212418473997056902 := by decide +kernel
private theorem endpoint_9_42_p8 : receiptWindow endpoint_9_42_flag endpoint_9_42_sources 0 8 212418473997056902 = some 212418473997056902 :=
  join_receipt_window endpoint_9_42_flag endpoint_9_42_sources 0 6 2 212418473997056902 212418473997056902 212418473997056902 endpoint_9_42_p6 endpoint_9_42_w6
def endpoint_9_42 : CertifiedEndpoint :=
  ⟨⟨9, 42, 4170⟩, 212418473997056902, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_42_flag endpoint_9_42_sources 8 212418473997056902 212418473997056902 rfl endpoint_9_42_base endpoint_9_42_p8) (by decide)⟩
private def endpoint_9_43_flag : Flag := ⟨9, 43, 4139⟩
private def endpoint_9_43_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_43_base : receiptBase endpoint_9_43_flag endpoint_9_43_sources = some 215093537548427739 := by decide +kernel
private theorem endpoint_9_43_w0 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 2 215093537548427739 = some 215093537548427739 := by decide +kernel
private theorem endpoint_9_43_w2 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 2 2 215093537548427739 = some 215093537548427739 := by decide +kernel
private theorem endpoint_9_43_p4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 4 215093537548427739 = some 215093537548427739 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 2 2 215093537548427739 215093537548427739 215093537548427739 endpoint_9_43_w0 endpoint_9_43_w2
private theorem endpoint_9_43_w4 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 4 2 215093537548427739 = some 215093537548427739 := by decide +kernel
private theorem endpoint_9_43_p6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 6 215093537548427739 = some 215093537548427739 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 4 2 215093537548427739 215093537548427739 215093537548427739 endpoint_9_43_p4 endpoint_9_43_w4
private theorem endpoint_9_43_w6 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 6 2 215093537548427739 = some 215093537548427739 := by decide +kernel
private theorem endpoint_9_43_p8 : receiptWindow endpoint_9_43_flag endpoint_9_43_sources 0 8 215093537548427739 = some 215093537548427739 :=
  join_receipt_window endpoint_9_43_flag endpoint_9_43_sources 0 6 2 215093537548427739 215093537548427739 215093537548427739 endpoint_9_43_p6 endpoint_9_43_w6
def endpoint_9_43 : CertifiedEndpoint :=
  ⟨⟨9, 43, 4139⟩, 215093537548427739, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_43_flag endpoint_9_43_sources 8 215093537548427739 215093537548427739 rfl endpoint_9_43_base endpoint_9_43_p8) (by decide)⟩
private def endpoint_9_44_flag : Flag := ⟨9, 44, 4108⟩
private def endpoint_9_44_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_44_base : receiptBase endpoint_9_44_flag endpoint_9_44_sources = some 217704939376768950 := by decide +kernel
private theorem endpoint_9_44_w0 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 2 217704939376768950 = some 217704939376768950 := by decide +kernel
private theorem endpoint_9_44_w2 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 2 2 217704939376768950 = some 217704939376768950 := by decide +kernel
private theorem endpoint_9_44_p4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 4 217704939376768950 = some 217704939376768950 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 2 2 217704939376768950 217704939376768950 217704939376768950 endpoint_9_44_w0 endpoint_9_44_w2
private theorem endpoint_9_44_w4 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 4 2 217704939376768950 = some 217704939376768950 := by decide +kernel
private theorem endpoint_9_44_p6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 6 217704939376768950 = some 217704939376768950 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 4 2 217704939376768950 217704939376768950 217704939376768950 endpoint_9_44_p4 endpoint_9_44_w4
private theorem endpoint_9_44_w6 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 6 2 217704939376768950 = some 217704939376768950 := by decide +kernel
private theorem endpoint_9_44_p8 : receiptWindow endpoint_9_44_flag endpoint_9_44_sources 0 8 217704939376768950 = some 217704939376768950 :=
  join_receipt_window endpoint_9_44_flag endpoint_9_44_sources 0 6 2 217704939376768950 217704939376768950 217704939376768950 endpoint_9_44_p6 endpoint_9_44_w6
def endpoint_9_44 : CertifiedEndpoint :=
  ⟨⟨9, 44, 4108⟩, 217704939376768950, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_44_flag endpoint_9_44_sources 8 217704939376768950 217704939376768950 rfl endpoint_9_44_base endpoint_9_44_p8) (by decide)⟩
private def endpoint_9_45_flag : Flag := ⟨9, 45, 4075⟩
private def endpoint_9_45_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_45_base : receiptBase endpoint_9_45_flag endpoint_9_45_sources = some 220145961820672990 := by decide +kernel
private theorem endpoint_9_45_w0 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 2 220145961820672990 = some 220145961820672990 := by decide +kernel
private theorem endpoint_9_45_w2 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 2 2 220145961820672990 = some 220145961820672990 := by decide +kernel
private theorem endpoint_9_45_p4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 4 220145961820672990 = some 220145961820672990 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 2 2 220145961820672990 220145961820672990 220145961820672990 endpoint_9_45_w0 endpoint_9_45_w2
private theorem endpoint_9_45_w4 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 4 2 220145961820672990 = some 220145961820672990 := by decide +kernel
private theorem endpoint_9_45_p6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 6 220145961820672990 = some 220145961820672990 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 4 2 220145961820672990 220145961820672990 220145961820672990 endpoint_9_45_p4 endpoint_9_45_w4
private theorem endpoint_9_45_w6 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 6 2 220145961820672990 = some 220145961820672990 := by decide +kernel
private theorem endpoint_9_45_p8 : receiptWindow endpoint_9_45_flag endpoint_9_45_sources 0 8 220145961820672990 = some 220145961820672990 :=
  join_receipt_window endpoint_9_45_flag endpoint_9_45_sources 0 6 2 220145961820672990 220145961820672990 220145961820672990 endpoint_9_45_p6 endpoint_9_45_w6
def endpoint_9_45 : CertifiedEndpoint :=
  ⟨⟨9, 45, 4075⟩, 220145961820672990, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_45_flag endpoint_9_45_sources 8 220145961820672990 220145961820672990 rfl endpoint_9_45_base endpoint_9_45_p8) (by decide)⟩
private def endpoint_9_46_flag : Flag := ⟨9, 46, 4043⟩
private def endpoint_9_46_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_46_base : receiptBase endpoint_9_46_flag endpoint_9_46_sources = some 222573649861630720 := by decide +kernel
private theorem endpoint_9_46_w0 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 2 222573649861630720 = some 222573649861630720 := by decide +kernel
private theorem endpoint_9_46_w2 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 2 2 222573649861630720 = some 222573649861630720 := by decide +kernel
private theorem endpoint_9_46_p4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 4 222573649861630720 = some 222573649861630720 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 2 2 222573649861630720 222573649861630720 222573649861630720 endpoint_9_46_w0 endpoint_9_46_w2
private theorem endpoint_9_46_w4 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 4 2 222573649861630720 = some 222573649861630720 := by decide +kernel
private theorem endpoint_9_46_p6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 6 222573649861630720 = some 222573649861630720 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 4 2 222573649861630720 222573649861630720 222573649861630720 endpoint_9_46_p4 endpoint_9_46_w4
private theorem endpoint_9_46_w6 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 6 2 222573649861630720 = some 222573649861630720 := by decide +kernel
private theorem endpoint_9_46_p8 : receiptWindow endpoint_9_46_flag endpoint_9_46_sources 0 8 222573649861630720 = some 222573649861630720 :=
  join_receipt_window endpoint_9_46_flag endpoint_9_46_sources 0 6 2 222573649861630720 222573649861630720 222573649861630720 endpoint_9_46_p6 endpoint_9_46_w6
def endpoint_9_46 : CertifiedEndpoint :=
  ⟨⟨9, 46, 4043⟩, 222573649861630720, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_46_flag endpoint_9_46_sources 8 222573649861630720 222573649861630720 rfl endpoint_9_46_base endpoint_9_46_p8) (by decide)⟩
private def endpoint_9_47_flag : Flag := ⟨9, 47, 4009⟩
private def endpoint_9_47_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_47_base : receiptBase endpoint_9_47_flag endpoint_9_47_sources = some 224824895496910362 := by decide +kernel
private theorem endpoint_9_47_w0 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 2 224824895496910362 = some 224824895496910362 := by decide +kernel
private theorem endpoint_9_47_w2 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 2 2 224824895496910362 = some 224824895496910362 := by decide +kernel
private theorem endpoint_9_47_p4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 4 224824895496910362 = some 224824895496910362 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 2 2 224824895496910362 224824895496910362 224824895496910362 endpoint_9_47_w0 endpoint_9_47_w2
private theorem endpoint_9_47_w4 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 4 2 224824895496910362 = some 224824895496910362 := by decide +kernel
private theorem endpoint_9_47_p6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 6 224824895496910362 = some 224824895496910362 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 4 2 224824895496910362 224824895496910362 224824895496910362 endpoint_9_47_p4 endpoint_9_47_w4
private theorem endpoint_9_47_w6 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 6 2 224824895496910362 = some 224824895496910362 := by decide +kernel
private theorem endpoint_9_47_p8 : receiptWindow endpoint_9_47_flag endpoint_9_47_sources 0 8 224824895496910362 = some 224824895496910362 :=
  join_receipt_window endpoint_9_47_flag endpoint_9_47_sources 0 6 2 224824895496910362 224824895496910362 224824895496910362 endpoint_9_47_p6 endpoint_9_47_w6
def endpoint_9_47 : CertifiedEndpoint :=
  ⟨⟨9, 47, 4009⟩, 224824895496910362, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_47_flag endpoint_9_47_sources 8 224824895496910362 224824895496910362 rfl endpoint_9_47_base endpoint_9_47_p8) (by decide)⟩
private def endpoint_9_48_flag : Flag := ⟨9, 48, 3975⟩
private def endpoint_9_48_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_48_base : receiptBase endpoint_9_48_flag endpoint_9_48_sources = some 227006416387919462 := by decide +kernel
private theorem endpoint_9_48_w0 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 2 227006416387919462 = some 227006416387919462 := by decide +kernel
private theorem endpoint_9_48_w2 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 2 2 227006416387919462 = some 227006416387919462 := by decide +kernel
private theorem endpoint_9_48_p4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 4 227006416387919462 = some 227006416387919462 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 2 2 227006416387919462 227006416387919462 227006416387919462 endpoint_9_48_w0 endpoint_9_48_w2
private theorem endpoint_9_48_w4 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 4 2 227006416387919462 = some 227006416387919462 := by decide +kernel
private theorem endpoint_9_48_p6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 6 227006416387919462 = some 227006416387919462 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 4 2 227006416387919462 227006416387919462 227006416387919462 endpoint_9_48_p4 endpoint_9_48_w4
private theorem endpoint_9_48_w6 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 6 2 227006416387919462 = some 227006416387919462 := by decide +kernel
private theorem endpoint_9_48_p8 : receiptWindow endpoint_9_48_flag endpoint_9_48_sources 0 8 227006416387919462 = some 227006416387919462 :=
  join_receipt_window endpoint_9_48_flag endpoint_9_48_sources 0 6 2 227006416387919462 227006416387919462 227006416387919462 endpoint_9_48_p6 endpoint_9_48_w6
def endpoint_9_48 : CertifiedEndpoint :=
  ⟨⟨9, 48, 3975⟩, 227006416387919462, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_48_flag endpoint_9_48_sources 8 227006416387919462 227006416387919462 rfl endpoint_9_48_base endpoint_9_48_p8) (by decide)⟩
private def endpoint_9_49_flag : Flag := ⟨9, 49, 3941⟩
private def endpoint_9_49_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_49_base : receiptBase endpoint_9_49_flag endpoint_9_49_sources = some 229118212534658021 := by decide +kernel
private theorem endpoint_9_49_w0 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 2 229118212534658021 = some 229118212534658021 := by decide +kernel
private theorem endpoint_9_49_w2 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 2 2 229118212534658021 = some 229118212534658021 := by decide +kernel
private theorem endpoint_9_49_p4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 4 229118212534658021 = some 229118212534658021 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 2 2 229118212534658021 229118212534658021 229118212534658021 endpoint_9_49_w0 endpoint_9_49_w2
private theorem endpoint_9_49_w4 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 4 2 229118212534658021 = some 229118212534658021 := by decide +kernel
private theorem endpoint_9_49_p6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 6 229118212534658021 = some 229118212534658021 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 4 2 229118212534658021 229118212534658021 229118212534658021 endpoint_9_49_p4 endpoint_9_49_w4
private theorem endpoint_9_49_w6 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 6 2 229118212534658021 = some 229118212534658021 := by decide +kernel
private theorem endpoint_9_49_p8 : receiptWindow endpoint_9_49_flag endpoint_9_49_sources 0 8 229118212534658021 = some 229118212534658021 :=
  join_receipt_window endpoint_9_49_flag endpoint_9_49_sources 0 6 2 229118212534658021 229118212534658021 229118212534658021 endpoint_9_49_p6 endpoint_9_49_w6
def endpoint_9_49 : CertifiedEndpoint :=
  ⟨⟨9, 49, 3941⟩, 229118212534658021, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_49_flag endpoint_9_49_sources 8 229118212534658021 229118212534658021 rfl endpoint_9_49_base endpoint_9_49_p8) (by decide)⟩
private def endpoint_9_50_flag : Flag := ⟨9, 50, 3905⟩
private def endpoint_9_50_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_50_base : receiptBase endpoint_9_50_flag endpoint_9_50_sources = some 231043461240316963 := by decide +kernel
private theorem endpoint_9_50_w0 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 2 231043461240316963 = some 231043461240316963 := by decide +kernel
private theorem endpoint_9_50_w2 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 2 2 231043461240316963 = some 231043461240316963 := by decide +kernel
private theorem endpoint_9_50_p4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 4 231043461240316963 = some 231043461240316963 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 2 2 231043461240316963 231043461240316963 231043461240316963 endpoint_9_50_w0 endpoint_9_50_w2
private theorem endpoint_9_50_w4 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 4 2 231043461240316963 = some 231043461240316963 := by decide +kernel
private theorem endpoint_9_50_p6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 6 231043461240316963 = some 231043461240316963 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 4 2 231043461240316963 231043461240316963 231043461240316963 endpoint_9_50_p4 endpoint_9_50_w4
private theorem endpoint_9_50_w6 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 6 2 231043461240316963 = some 231043461240316963 := by decide +kernel
private theorem endpoint_9_50_p8 : receiptWindow endpoint_9_50_flag endpoint_9_50_sources 0 8 231043461240316963 = some 231043461240316963 :=
  join_receipt_window endpoint_9_50_flag endpoint_9_50_sources 0 6 2 231043461240316963 231043461240316963 231043461240316963 endpoint_9_50_p6 endpoint_9_50_w6
def endpoint_9_50 : CertifiedEndpoint :=
  ⟨⟨9, 50, 3905⟩, 231043461240316963, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_50_flag endpoint_9_50_sources 8 231043461240316963 231043461240316963 rfl endpoint_9_50_base endpoint_9_50_p8) (by decide)⟩
private def endpoint_9_51_flag : Flag := ⟨9, 51, 3869⟩
private def endpoint_9_51_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_51_base : receiptBase endpoint_9_51_flag endpoint_9_51_sources = some 232894943187544753 := by decide +kernel
private theorem endpoint_9_51_w0 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 2 232894943187544753 = some 232894943187544753 := by decide +kernel
private theorem endpoint_9_51_w2 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 2 2 232894943187544753 = some 232894943187544753 := by decide +kernel
private theorem endpoint_9_51_p4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 4 232894943187544753 = some 232894943187544753 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 2 2 232894943187544753 232894943187544753 232894943187544753 endpoint_9_51_w0 endpoint_9_51_w2
private theorem endpoint_9_51_w4 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 4 2 232894943187544753 = some 232894943187544753 := by decide +kernel
private theorem endpoint_9_51_p6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 6 232894943187544753 = some 232894943187544753 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 4 2 232894943187544753 232894943187544753 232894943187544753 endpoint_9_51_p4 endpoint_9_51_w4
private theorem endpoint_9_51_w6 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 6 2 232894943187544753 = some 232894943187544753 := by decide +kernel
private theorem endpoint_9_51_p8 : receiptWindow endpoint_9_51_flag endpoint_9_51_sources 0 8 232894943187544753 = some 232894943187544753 :=
  join_receipt_window endpoint_9_51_flag endpoint_9_51_sources 0 6 2 232894943187544753 232894943187544753 232894943187544753 endpoint_9_51_p6 endpoint_9_51_w6
def endpoint_9_51 : CertifiedEndpoint :=
  ⟨⟨9, 51, 3869⟩, 232894943187544753, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_51_flag endpoint_9_51_sources 8 232894943187544753 232894943187544753 rfl endpoint_9_51_base endpoint_9_51_p8) (by decide)⟩
private def endpoint_9_52_flag : Flag := ⟨9, 52, 3831⟩
private def endpoint_9_52_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_52_base : receiptBase endpoint_9_52_flag endpoint_9_52_sources = some 234551793665371705 := by decide +kernel
private theorem endpoint_9_52_w0 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 2 234551793665371705 = some 234551793665371705 := by decide +kernel
private theorem endpoint_9_52_w2 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 2 2 234551793665371705 = some 234551793665371705 := by decide +kernel
private theorem endpoint_9_52_p4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 4 234551793665371705 = some 234551793665371705 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 2 2 234551793665371705 234551793665371705 234551793665371705 endpoint_9_52_w0 endpoint_9_52_w2
private theorem endpoint_9_52_w4 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 4 2 234551793665371705 = some 234551793665371705 := by decide +kernel
private theorem endpoint_9_52_p6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 6 234551793665371705 = some 234551793665371705 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 4 2 234551793665371705 234551793665371705 234551793665371705 endpoint_9_52_p4 endpoint_9_52_w4
private theorem endpoint_9_52_w6 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 6 2 234551793665371705 = some 234551793665371705 := by decide +kernel
private theorem endpoint_9_52_p8 : receiptWindow endpoint_9_52_flag endpoint_9_52_sources 0 8 234551793665371705 = some 234551793665371705 :=
  join_receipt_window endpoint_9_52_flag endpoint_9_52_sources 0 6 2 234551793665371705 234551793665371705 234551793665371705 endpoint_9_52_p6 endpoint_9_52_w6
def endpoint_9_52 : CertifiedEndpoint :=
  ⟨⟨9, 52, 3831⟩, 234551793665371705, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_52_flag endpoint_9_52_sources 8 234551793665371705 234551793665371705 rfl endpoint_9_52_base endpoint_9_52_p8) (by decide)⟩
private def endpoint_9_53_flag : Flag := ⟨9, 53, 3793⟩
private def endpoint_9_53_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_53_base : receiptBase endpoint_9_53_flag endpoint_9_53_sources = some 236130835370606893 := by decide +kernel
private theorem endpoint_9_53_w0 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 2 236130835370606893 = some 236130835370606893 := by decide +kernel
private theorem endpoint_9_53_w2 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 2 2 236130835370606893 = some 236130835370606893 := by decide +kernel
private theorem endpoint_9_53_p4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 4 236130835370606893 = some 236130835370606893 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 2 2 236130835370606893 236130835370606893 236130835370606893 endpoint_9_53_w0 endpoint_9_53_w2
private theorem endpoint_9_53_w4 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 4 2 236130835370606893 = some 236130835370606893 := by decide +kernel
private theorem endpoint_9_53_p6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 6 236130835370606893 = some 236130835370606893 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 4 2 236130835370606893 236130835370606893 236130835370606893 endpoint_9_53_p4 endpoint_9_53_w4
private theorem endpoint_9_53_w6 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 6 2 236130835370606893 = some 236130835370606893 := by decide +kernel
private theorem endpoint_9_53_p8 : receiptWindow endpoint_9_53_flag endpoint_9_53_sources 0 8 236130835370606893 = some 236130835370606893 :=
  join_receipt_window endpoint_9_53_flag endpoint_9_53_sources 0 6 2 236130835370606893 236130835370606893 236130835370606893 endpoint_9_53_p6 endpoint_9_53_w6
def endpoint_9_53 : CertifiedEndpoint :=
  ⟨⟨9, 53, 3793⟩, 236130835370606893, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_53_flag endpoint_9_53_sources 8 236130835370606893 236130835370606893 rfl endpoint_9_53_base endpoint_9_53_p8) (by decide)⟩
private def endpoint_9_54_flag : Flag := ⟨9, 54, 3754⟩
private def endpoint_9_54_sources : Sources := ⟨contact00, contact01, contact02⟩
private theorem endpoint_9_54_base : receiptBase endpoint_9_54_flag endpoint_9_54_sources = some 237569614940685168 := by decide +kernel
private theorem endpoint_9_54_w0 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 2 237569614940685168 = some 237569614940685168 := by decide +kernel
private theorem endpoint_9_54_w2 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 2 2 237569614940685168 = some 237569614940685168 := by decide +kernel
private theorem endpoint_9_54_p4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 4 237569614940685168 = some 237569614940685168 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 2 2 237569614940685168 237569614940685168 237569614940685168 endpoint_9_54_w0 endpoint_9_54_w2
private theorem endpoint_9_54_w4 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 4 2 237569614940685168 = some 237569614940685168 := by decide +kernel
private theorem endpoint_9_54_p6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 6 237569614940685168 = some 237569614940685168 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 4 2 237569614940685168 237569614940685168 237569614940685168 endpoint_9_54_p4 endpoint_9_54_w4
private theorem endpoint_9_54_w6 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 6 2 237569614940685168 = some 237569614940685168 := by decide +kernel
private theorem endpoint_9_54_p8 : receiptWindow endpoint_9_54_flag endpoint_9_54_sources 0 8 237569614940685168 = some 237569614940685168 :=
  join_receipt_window endpoint_9_54_flag endpoint_9_54_sources 0 6 2 237569614940685168 237569614940685168 237569614940685168 endpoint_9_54_p6 endpoint_9_54_w6
def endpoint_9_54 : CertifiedEndpoint :=
  ⟨⟨9, 54, 3754⟩, 237569614940685168, .terminal ⟨contact00, contact01, contact02⟩ (finish_receipt_window endpoint_9_54_flag endpoint_9_54_sources 8 237569614940685168 237569614940685168 rfl endpoint_9_54_base endpoint_9_54_p8) (by decide)⟩
private def endpoint_9_55_flag : Flag := ⟨9, 55, 3713⟩
private def endpoint_9_55_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_55_base : receiptBase endpoint_9_55_flag endpoint_9_55_sources = some 239558870117792972 := by decide +kernel
private theorem endpoint_9_55_w0 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 2 239558870117792972 = some 239558870117792972 := by decide +kernel
private theorem endpoint_9_55_w2 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 2 2 239558870117792972 = some 239558870117792972 := by decide +kernel
private theorem endpoint_9_55_p4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 4 239558870117792972 = some 239558870117792972 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 2 2 239558870117792972 239558870117792972 239558870117792972 endpoint_9_55_w0 endpoint_9_55_w2
private theorem endpoint_9_55_w4 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 4 2 239558870117792972 = some 239558870117792972 := by decide +kernel
private theorem endpoint_9_55_p6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 6 239558870117792972 = some 239558870117792972 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 4 2 239558870117792972 239558870117792972 239558870117792972 endpoint_9_55_p4 endpoint_9_55_w4
private theorem endpoint_9_55_w6 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 6 2 239558870117792972 = some 239558870117792972 := by decide +kernel
private theorem endpoint_9_55_p8 : receiptWindow endpoint_9_55_flag endpoint_9_55_sources 0 8 239558870117792972 = some 239558870117792972 :=
  join_receipt_window endpoint_9_55_flag endpoint_9_55_sources 0 6 2 239558870117792972 239558870117792972 239558870117792972 endpoint_9_55_p6 endpoint_9_55_w6
def endpoint_9_55 : CertifiedEndpoint :=
  ⟨⟨9, 55, 3713⟩, 239558870117792972, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_55_flag endpoint_9_55_sources 8 239558870117792972 239558870117792972 rfl endpoint_9_55_base endpoint_9_55_p8) (by decide)⟩
private def endpoint_9_56_flag : Flag := ⟨9, 56, 3671⟩
private def endpoint_9_56_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_56_base : receiptBase endpoint_9_56_flag endpoint_9_56_sources = some 240649912447402571 := by decide +kernel
private theorem endpoint_9_56_w0 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 2 240649912447402571 = some 240649912447402571 := by decide +kernel
private theorem endpoint_9_56_w2 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 2 2 240649912447402571 = some 240649912447402571 := by decide +kernel
private theorem endpoint_9_56_p4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 4 240649912447402571 = some 240649912447402571 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 2 2 240649912447402571 240649912447402571 240649912447402571 endpoint_9_56_w0 endpoint_9_56_w2
private theorem endpoint_9_56_w4 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 4 2 240649912447402571 = some 240649912447402571 := by decide +kernel
private theorem endpoint_9_56_p6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 6 240649912447402571 = some 240649912447402571 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 4 2 240649912447402571 240649912447402571 240649912447402571 endpoint_9_56_p4 endpoint_9_56_w4
private theorem endpoint_9_56_w6 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 6 2 240649912447402571 = some 240649912447402571 := by decide +kernel
private theorem endpoint_9_56_p8 : receiptWindow endpoint_9_56_flag endpoint_9_56_sources 0 8 240649912447402571 = some 240649912447402571 :=
  join_receipt_window endpoint_9_56_flag endpoint_9_56_sources 0 6 2 240649912447402571 240649912447402571 240649912447402571 endpoint_9_56_p6 endpoint_9_56_w6
def endpoint_9_56 : CertifiedEndpoint :=
  ⟨⟨9, 56, 3671⟩, 240649912447402571, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_56_flag endpoint_9_56_sources 8 240649912447402571 240649912447402571 rfl endpoint_9_56_base endpoint_9_56_p8) (by decide)⟩
private def endpoint_9_57_flag : Flag := ⟨9, 57, 3628⟩
private def endpoint_9_57_sources : Sources := ⟨contact18, contact01, contact02⟩
private theorem endpoint_9_57_base : receiptBase endpoint_9_57_flag endpoint_9_57_sources = some 241588974054827598 := by decide +kernel
private theorem endpoint_9_57_w0 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 2 241588974054827598 = some 241588974054827598 := by decide +kernel
private theorem endpoint_9_57_w2 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 2 2 241588974054827598 = some 241588974054827598 := by decide +kernel
private theorem endpoint_9_57_p4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 4 241588974054827598 = some 241588974054827598 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 2 2 241588974054827598 241588974054827598 241588974054827598 endpoint_9_57_w0 endpoint_9_57_w2
private theorem endpoint_9_57_w4 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 4 2 241588974054827598 = some 241588974054827598 := by decide +kernel
private theorem endpoint_9_57_p6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 6 241588974054827598 = some 241588974054827598 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 4 2 241588974054827598 241588974054827598 241588974054827598 endpoint_9_57_p4 endpoint_9_57_w4
private theorem endpoint_9_57_w6 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 6 2 241588974054827598 = some 241588974054827598 := by decide +kernel
private theorem endpoint_9_57_p8 : receiptWindow endpoint_9_57_flag endpoint_9_57_sources 0 8 241588974054827598 = some 241588974054827598 :=
  join_receipt_window endpoint_9_57_flag endpoint_9_57_sources 0 6 2 241588974054827598 241588974054827598 241588974054827598 endpoint_9_57_p6 endpoint_9_57_w6
def endpoint_9_57 : CertifiedEndpoint :=
  ⟨⟨9, 57, 3628⟩, 241588974054827598, .terminal ⟨contact18, contact01, contact02⟩ (finish_receipt_window endpoint_9_57_flag endpoint_9_57_sources 8 241588974054827598 241588974054827598 rfl endpoint_9_57_base endpoint_9_57_p8) (by decide)⟩
private def endpoint_9_58_flag : Flag := ⟨9, 58, 3584⟩
private def endpoint_9_58_sources : Sources := ⟨contact01, contact01, contact02⟩
private theorem endpoint_9_58_base : receiptBase endpoint_9_58_flag endpoint_9_58_sources = some 242452337254303008 := by decide +kernel
private theorem endpoint_9_58_w0 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 2 242452337254303008 = some 242452337254303008 := by decide +kernel
private theorem endpoint_9_58_w2 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 2 2 242452337254303008 = some 242452337254303008 := by decide +kernel
private theorem endpoint_9_58_p4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 4 242452337254303008 = some 242452337254303008 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 2 2 242452337254303008 242452337254303008 242452337254303008 endpoint_9_58_w0 endpoint_9_58_w2
private theorem endpoint_9_58_w4 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 4 2 242452337254303008 = some 242452337254303008 := by decide +kernel
private theorem endpoint_9_58_p6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 6 242452337254303008 = some 242452337254303008 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 4 2 242452337254303008 242452337254303008 242452337254303008 endpoint_9_58_p4 endpoint_9_58_w4
private theorem endpoint_9_58_w6 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 6 2 242452337254303008 = some 242452337254303008 := by decide +kernel
private theorem endpoint_9_58_p8 : receiptWindow endpoint_9_58_flag endpoint_9_58_sources 0 8 242452337254303008 = some 242452337254303008 :=
  join_receipt_window endpoint_9_58_flag endpoint_9_58_sources 0 6 2 242452337254303008 242452337254303008 242452337254303008 endpoint_9_58_p6 endpoint_9_58_w6
def endpoint_9_58 : CertifiedEndpoint :=
  ⟨⟨9, 58, 3584⟩, 242452337254303008, .terminal ⟨contact01, contact01, contact02⟩ (finish_receipt_window endpoint_9_58_flag endpoint_9_58_sources 8 242452337254303008 242452337254303008 rfl endpoint_9_58_base endpoint_9_58_p8) (by decide)⟩
private def endpoint_9_59_flag : Flag := ⟨9, 59, 3538⟩
private def endpoint_9_59_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_59_base : receiptBase endpoint_9_59_flag endpoint_9_59_sources = some 245390127690639235 := by decide +kernel
private theorem endpoint_9_59_w0 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 2 245390127690639235 = some 245390127690639235 := by decide +kernel
private theorem endpoint_9_59_w2 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 2 2 245390127690639235 = some 245390127690639235 := by decide +kernel
private theorem endpoint_9_59_p4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 4 245390127690639235 = some 245390127690639235 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 2 2 245390127690639235 245390127690639235 245390127690639235 endpoint_9_59_w0 endpoint_9_59_w2
private theorem endpoint_9_59_w4 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 4 2 245390127690639235 = some 245390127690639235 := by decide +kernel
private theorem endpoint_9_59_p6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 6 245390127690639235 = some 245390127690639235 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 4 2 245390127690639235 245390127690639235 245390127690639235 endpoint_9_59_p4 endpoint_9_59_w4
private theorem endpoint_9_59_w6 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 6 2 245390127690639235 = some 245390127690639235 := by decide +kernel
private theorem endpoint_9_59_p8 : receiptWindow endpoint_9_59_flag endpoint_9_59_sources 0 8 245390127690639235 = some 245390127690639235 :=
  join_receipt_window endpoint_9_59_flag endpoint_9_59_sources 0 6 2 245390127690639235 245390127690639235 245390127690639235 endpoint_9_59_p6 endpoint_9_59_w6
def endpoint_9_59 : CertifiedEndpoint :=
  ⟨⟨9, 59, 3538⟩, 245390127690639235, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_59_flag endpoint_9_59_sources 8 245390127690639235 245390127690639235 rfl endpoint_9_59_base endpoint_9_59_p8) (by decide)⟩
private def endpoint_9_60_flag : Flag := ⟨9, 60, 3490⟩
private def endpoint_9_60_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_60_base : receiptBase endpoint_9_60_flag endpoint_9_60_sources = some 245677680065310893 := by decide +kernel
private theorem endpoint_9_60_w0 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 2 245677680065310893 = some 245677680065310893 := by decide +kernel
private theorem endpoint_9_60_w2 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 2 2 245677680065310893 = some 245677680065310893 := by decide +kernel
private theorem endpoint_9_60_p4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 4 245677680065310893 = some 245677680065310893 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 2 2 245677680065310893 245677680065310893 245677680065310893 endpoint_9_60_w0 endpoint_9_60_w2
private theorem endpoint_9_60_w4 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 4 2 245677680065310893 = some 245677680065310893 := by decide +kernel
private theorem endpoint_9_60_p6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 6 245677680065310893 = some 245677680065310893 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 4 2 245677680065310893 245677680065310893 245677680065310893 endpoint_9_60_p4 endpoint_9_60_w4
private theorem endpoint_9_60_w6 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 6 2 245677680065310893 = some 245677680065310893 := by decide +kernel
private theorem endpoint_9_60_p8 : receiptWindow endpoint_9_60_flag endpoint_9_60_sources 0 8 245677680065310893 = some 245677680065310893 :=
  join_receipt_window endpoint_9_60_flag endpoint_9_60_sources 0 6 2 245677680065310893 245677680065310893 245677680065310893 endpoint_9_60_p6 endpoint_9_60_w6
def endpoint_9_60 : CertifiedEndpoint :=
  ⟨⟨9, 60, 3490⟩, 245677680065310893, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_60_flag endpoint_9_60_sources 8 245677680065310893 245677680065310893 rfl endpoint_9_60_base endpoint_9_60_p8) (by decide)⟩
private def endpoint_9_61_flag : Flag := ⟨9, 61, 3440⟩
private def endpoint_9_61_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_61_base : receiptBase endpoint_9_61_flag endpoint_9_61_sources = some 245725034906880783 := by decide +kernel
private theorem endpoint_9_61_w0 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 2 245725034906880783 = some 245725034906880783 := by decide +kernel
private theorem endpoint_9_61_w2 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 2 2 245725034906880783 = some 245725034906880783 := by decide +kernel
private theorem endpoint_9_61_p4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 4 245725034906880783 = some 245725034906880783 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 2 2 245725034906880783 245725034906880783 245725034906880783 endpoint_9_61_w0 endpoint_9_61_w2
private theorem endpoint_9_61_w4 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 4 2 245725034906880783 = some 245725034906880783 := by decide +kernel
private theorem endpoint_9_61_p6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 6 245725034906880783 = some 245725034906880783 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 4 2 245725034906880783 245725034906880783 245725034906880783 endpoint_9_61_p4 endpoint_9_61_w4
private theorem endpoint_9_61_w6 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 6 2 245725034906880783 = some 245725034906880783 := by decide +kernel
private theorem endpoint_9_61_p8 : receiptWindow endpoint_9_61_flag endpoint_9_61_sources 0 8 245725034906880783 = some 245725034906880783 :=
  join_receipt_window endpoint_9_61_flag endpoint_9_61_sources 0 6 2 245725034906880783 245725034906880783 245725034906880783 endpoint_9_61_p6 endpoint_9_61_w6
def endpoint_9_61 : CertifiedEndpoint :=
  ⟨⟨9, 61, 3440⟩, 245725034906880783, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_61_flag endpoint_9_61_sources 8 245725034906880783 245725034906880783 rfl endpoint_9_61_base endpoint_9_61_p8) (by decide)⟩
private def endpoint_9_62_flag : Flag := ⟨9, 62, 3387⟩
private def endpoint_9_62_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_62_base : receiptBase endpoint_9_62_flag endpoint_9_62_sources = some 245454402655334159 := by decide +kernel
private theorem endpoint_9_62_w0 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 2 245454402655334159 = some 245454402655334159 := by decide +kernel
private theorem endpoint_9_62_w2 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 2 2 245454402655334159 = some 245454402655334159 := by decide +kernel
private theorem endpoint_9_62_p4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 4 245454402655334159 = some 245454402655334159 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 2 2 245454402655334159 245454402655334159 245454402655334159 endpoint_9_62_w0 endpoint_9_62_w2
private theorem endpoint_9_62_w4 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 4 2 245454402655334159 = some 245454402655334159 := by decide +kernel
private theorem endpoint_9_62_p6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 6 245454402655334159 = some 245454402655334159 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 4 2 245454402655334159 245454402655334159 245454402655334159 endpoint_9_62_p4 endpoint_9_62_w4
private theorem endpoint_9_62_w6 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 6 2 245454402655334159 = some 245454402655334159 := by decide +kernel
private theorem endpoint_9_62_p8 : receiptWindow endpoint_9_62_flag endpoint_9_62_sources 0 8 245454402655334159 = some 245454402655334159 :=
  join_receipt_window endpoint_9_62_flag endpoint_9_62_sources 0 6 2 245454402655334159 245454402655334159 245454402655334159 endpoint_9_62_p6 endpoint_9_62_w6
def endpoint_9_62 : CertifiedEndpoint :=
  ⟨⟨9, 62, 3387⟩, 245454402655334159, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_62_flag endpoint_9_62_sources 8 245454402655334159 245454402655334159 rfl endpoint_9_62_base endpoint_9_62_p8) (by decide)⟩
private def endpoint_9_63_flag : Flag := ⟨9, 63, 3332⟩
private def endpoint_9_63_sources : Sources := ⟨contact03, contact03, contact04⟩
private theorem endpoint_9_63_base : receiptBase endpoint_9_63_flag endpoint_9_63_sources = some 244929299885348277 := by decide +kernel
private theorem endpoint_9_63_w0 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 2 244929299885348277 = some 244929299885348277 := by decide +kernel
private theorem endpoint_9_63_w2 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 2 2 244929299885348277 = some 244929299885348277 := by decide +kernel
private theorem endpoint_9_63_p4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 4 244929299885348277 = some 244929299885348277 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 2 2 244929299885348277 244929299885348277 244929299885348277 endpoint_9_63_w0 endpoint_9_63_w2
private theorem endpoint_9_63_w4 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 4 2 244929299885348277 = some 244929299885348277 := by decide +kernel
private theorem endpoint_9_63_p6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 6 244929299885348277 = some 244929299885348277 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 4 2 244929299885348277 244929299885348277 244929299885348277 endpoint_9_63_p4 endpoint_9_63_w4
private theorem endpoint_9_63_w6 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 6 2 244929299885348277 = some 244929299885348277 := by decide +kernel
private theorem endpoint_9_63_p8 : receiptWindow endpoint_9_63_flag endpoint_9_63_sources 0 8 244929299885348277 = some 244929299885348277 :=
  join_receipt_window endpoint_9_63_flag endpoint_9_63_sources 0 6 2 244929299885348277 244929299885348277 244929299885348277 endpoint_9_63_p6 endpoint_9_63_w6
def endpoint_9_63 : CertifiedEndpoint :=
  ⟨⟨9, 63, 3332⟩, 244929299885348277, .terminal ⟨contact03, contact03, contact04⟩ (finish_receipt_window endpoint_9_63_flag endpoint_9_63_sources 8 244929299885348277 244929299885348277 rfl endpoint_9_63_base endpoint_9_63_p8) (by decide)⟩
private def endpoint_9_64_flag : Flag := ⟨9, 64, 3274⟩
private def endpoint_9_64_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_64_base : receiptBase endpoint_9_64_flag endpoint_9_64_sources = some 245477222199474716 := by decide +kernel
private theorem endpoint_9_64_w0 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 2 245477222199474716 = some 245477222199474716 := by decide +kernel
private theorem endpoint_9_64_w2 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 2 2 245477222199474716 = some 245477222199474716 := by decide +kernel
private theorem endpoint_9_64_p4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 4 245477222199474716 = some 245477222199474716 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 2 2 245477222199474716 245477222199474716 245477222199474716 endpoint_9_64_w0 endpoint_9_64_w2
private theorem endpoint_9_64_w4 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 4 2 245477222199474716 = some 245477222199474716 := by decide +kernel
private theorem endpoint_9_64_p6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 6 245477222199474716 = some 245477222199474716 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 4 2 245477222199474716 245477222199474716 245477222199474716 endpoint_9_64_p4 endpoint_9_64_w4
private theorem endpoint_9_64_w6 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 6 2 245477222199474716 = some 245477222199474716 := by decide +kernel
private theorem endpoint_9_64_p8 : receiptWindow endpoint_9_64_flag endpoint_9_64_sources 0 8 245477222199474716 = some 245477222199474716 :=
  join_receipt_window endpoint_9_64_flag endpoint_9_64_sources 0 6 2 245477222199474716 245477222199474716 245477222199474716 endpoint_9_64_p6 endpoint_9_64_w6
def endpoint_9_64 : CertifiedEndpoint :=
  ⟨⟨9, 64, 3274⟩, 245477222199474716, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_64_flag endpoint_9_64_sources 8 245477222199474716 245477222199474716 rfl endpoint_9_64_base endpoint_9_64_p8) (by decide)⟩
private def endpoint_9_65_flag : Flag := ⟨9, 65, 3213⟩
private def endpoint_9_65_sources : Sources := ⟨contact05, contact05, contact04⟩
private theorem endpoint_9_65_base : receiptBase endpoint_9_65_flag endpoint_9_65_sources = some 244269283963568957 := by decide +kernel
private theorem endpoint_9_65_w0 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 2 244269283963568957 = some 244269283963568957 := by decide +kernel
private theorem endpoint_9_65_w2 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 2 2 244269283963568957 = some 244269283963568957 := by decide +kernel
private theorem endpoint_9_65_p4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 4 244269283963568957 = some 244269283963568957 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 2 2 244269283963568957 244269283963568957 244269283963568957 endpoint_9_65_w0 endpoint_9_65_w2
private theorem endpoint_9_65_w4 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 4 2 244269283963568957 = some 244269283963568957 := by decide +kernel
private theorem endpoint_9_65_p6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 6 244269283963568957 = some 244269283963568957 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 4 2 244269283963568957 244269283963568957 244269283963568957 endpoint_9_65_p4 endpoint_9_65_w4
private theorem endpoint_9_65_w6 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 6 2 244269283963568957 = some 244269283963568957 := by decide +kernel
private theorem endpoint_9_65_p8 : receiptWindow endpoint_9_65_flag endpoint_9_65_sources 0 8 244269283963568957 = some 244269283963568957 :=
  join_receipt_window endpoint_9_65_flag endpoint_9_65_sources 0 6 2 244269283963568957 244269283963568957 244269283963568957 endpoint_9_65_p6 endpoint_9_65_w6
def endpoint_9_65 : CertifiedEndpoint :=
  ⟨⟨9, 65, 3213⟩, 244269283963568957, .terminal ⟨contact05, contact05, contact04⟩ (finish_receipt_window endpoint_9_65_flag endpoint_9_65_sources 8 244269283963568957 244269283963568957 rfl endpoint_9_65_base endpoint_9_65_p8) (by decide)⟩
private def endpoint_9_66_flag : Flag := ⟨9, 66, 3149⟩
private def endpoint_9_66_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_66_base : receiptBase endpoint_9_66_flag endpoint_9_66_sources = some 244157614311100735 := by decide +kernel
private theorem endpoint_9_66_w0 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 2 244157614311100735 = some 244157614311100735 := by decide +kernel
private theorem endpoint_9_66_w2 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 2 2 244157614311100735 = some 244157614311100735 := by decide +kernel
private theorem endpoint_9_66_p4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 4 244157614311100735 = some 244157614311100735 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 2 2 244157614311100735 244157614311100735 244157614311100735 endpoint_9_66_w0 endpoint_9_66_w2
private theorem endpoint_9_66_w4 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 4 2 244157614311100735 = some 244157614311100735 := by decide +kernel
private theorem endpoint_9_66_p6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 6 244157614311100735 = some 244157614311100735 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 4 2 244157614311100735 244157614311100735 244157614311100735 endpoint_9_66_p4 endpoint_9_66_w4
private theorem endpoint_9_66_w6 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 6 2 244157614311100735 = some 244157614311100735 := by decide +kernel
private theorem endpoint_9_66_p8 : receiptWindow endpoint_9_66_flag endpoint_9_66_sources 0 8 244157614311100735 = some 244157614311100735 :=
  join_receipt_window endpoint_9_66_flag endpoint_9_66_sources 0 6 2 244157614311100735 244157614311100735 244157614311100735 endpoint_9_66_p6 endpoint_9_66_w6
def endpoint_9_66 : CertifiedEndpoint :=
  ⟨⟨9, 66, 3149⟩, 244157614311100735, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_66_flag endpoint_9_66_sources 8 244157614311100735 244157614311100735 rfl endpoint_9_66_base endpoint_9_66_p8) (by decide)⟩
private def endpoint_9_67_flag : Flag := ⟨9, 67, 3082⟩
private def endpoint_9_67_sources : Sources := ⟨contact06, contact06, contact04⟩
private theorem endpoint_9_67_base : receiptBase endpoint_9_67_flag endpoint_9_67_sources = some 242220443778697894 := by decide +kernel
private theorem endpoint_9_67_w0 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 2 242220443778697894 = some 242220443778697894 := by decide +kernel
private theorem endpoint_9_67_w2 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 2 2 242220443778697894 = some 242220443778697894 := by decide +kernel
private theorem endpoint_9_67_p4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 4 242220443778697894 = some 242220443778697894 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 2 2 242220443778697894 242220443778697894 242220443778697894 endpoint_9_67_w0 endpoint_9_67_w2
private theorem endpoint_9_67_w4 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 4 2 242220443778697894 = some 242220443778697894 := by decide +kernel
private theorem endpoint_9_67_p6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 6 242220443778697894 = some 242220443778697894 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 4 2 242220443778697894 242220443778697894 242220443778697894 endpoint_9_67_p4 endpoint_9_67_w4
private theorem endpoint_9_67_w6 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 6 2 242220443778697894 = some 242220443778697894 := by decide +kernel
private theorem endpoint_9_67_p8 : receiptWindow endpoint_9_67_flag endpoint_9_67_sources 0 8 242220443778697894 = some 242220443778697894 :=
  join_receipt_window endpoint_9_67_flag endpoint_9_67_sources 0 6 2 242220443778697894 242220443778697894 242220443778697894 endpoint_9_67_p6 endpoint_9_67_w6
def endpoint_9_67 : CertifiedEndpoint :=
  ⟨⟨9, 67, 3082⟩, 242220443778697894, .terminal ⟨contact06, contact06, contact04⟩ (finish_receipt_window endpoint_9_67_flag endpoint_9_67_sources 8 242220443778697894 242220443778697894 rfl endpoint_9_67_base endpoint_9_67_p8) (by decide)⟩
private def endpoint_9_68_flag : Flag := ⟨9, 68, 3012⟩
private def endpoint_9_68_sources : Sources := ⟨contact07, contact07, contact04⟩
private theorem endpoint_9_68_base : receiptBase endpoint_9_68_flag endpoint_9_68_sources = some 241381478690016219 := by decide +kernel
private theorem endpoint_9_68_w0 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 2 241381478690016219 = some 241381478690016219 := by decide +kernel
private theorem endpoint_9_68_w2 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 2 2 241381478690016219 = some 241381478690016219 := by decide +kernel
private theorem endpoint_9_68_p4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 4 241381478690016219 = some 241381478690016219 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 2 2 241381478690016219 241381478690016219 241381478690016219 endpoint_9_68_w0 endpoint_9_68_w2
private theorem endpoint_9_68_w4 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 4 2 241381478690016219 = some 241381478690016219 := by decide +kernel
private theorem endpoint_9_68_p6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 6 241381478690016219 = some 241381478690016219 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 4 2 241381478690016219 241381478690016219 241381478690016219 endpoint_9_68_p4 endpoint_9_68_w4
private theorem endpoint_9_68_w6 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 6 2 241381478690016219 = some 241381478690016219 := by decide +kernel
private theorem endpoint_9_68_p8 : receiptWindow endpoint_9_68_flag endpoint_9_68_sources 0 8 241381478690016219 = some 241381478690016219 :=
  join_receipt_window endpoint_9_68_flag endpoint_9_68_sources 0 6 2 241381478690016219 241381478690016219 241381478690016219 endpoint_9_68_p6 endpoint_9_68_w6
def endpoint_9_68 : CertifiedEndpoint :=
  ⟨⟨9, 68, 3012⟩, 241381478690016219, .terminal ⟨contact07, contact07, contact04⟩ (finish_receipt_window endpoint_9_68_flag endpoint_9_68_sources 8 241381478690016219 241381478690016219 rfl endpoint_9_68_base endpoint_9_68_p8) (by decide)⟩
private def endpoint_9_69_flag : Flag := ⟨9, 69, 2939⟩
private def endpoint_9_69_sources : Sources := ⟨contact08, contact08, contact04⟩
private theorem endpoint_9_69_base : receiptBase endpoint_9_69_flag endpoint_9_69_sources = some 240163973632656229 := by decide +kernel
private theorem endpoint_9_69_w0 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 2 240163973632656229 = some 240163973632656229 := by decide +kernel
private theorem endpoint_9_69_w2 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 2 2 240163973632656229 = some 240163973632656229 := by decide +kernel
private theorem endpoint_9_69_p4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 4 240163973632656229 = some 240163973632656229 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 2 2 240163973632656229 240163973632656229 240163973632656229 endpoint_9_69_w0 endpoint_9_69_w2
private theorem endpoint_9_69_w4 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 4 2 240163973632656229 = some 240163973632656229 := by decide +kernel
private theorem endpoint_9_69_p6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 6 240163973632656229 = some 240163973632656229 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 4 2 240163973632656229 240163973632656229 240163973632656229 endpoint_9_69_p4 endpoint_9_69_w4
private theorem endpoint_9_69_w6 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 6 2 240163973632656229 = some 240163973632656229 := by decide +kernel
private theorem endpoint_9_69_p8 : receiptWindow endpoint_9_69_flag endpoint_9_69_sources 0 8 240163973632656229 = some 240163973632656229 :=
  join_receipt_window endpoint_9_69_flag endpoint_9_69_sources 0 6 2 240163973632656229 240163973632656229 240163973632656229 endpoint_9_69_p6 endpoint_9_69_w6
def endpoint_9_69 : CertifiedEndpoint :=
  ⟨⟨9, 69, 2939⟩, 240163973632656229, .terminal ⟨contact08, contact08, contact04⟩ (finish_receipt_window endpoint_9_69_flag endpoint_9_69_sources 8 240163973632656229 240163973632656229 rfl endpoint_9_69_base endpoint_9_69_p8) (by decide)⟩
private def endpoint_9_70_flag : Flag := ⟨9, 70, 2863⟩
private def endpoint_9_70_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_70_base : receiptBase endpoint_9_70_flag endpoint_9_70_sources = some 238404472127172432 := by decide +kernel
private theorem endpoint_9_70_w0 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 2 238404472127172432 = some 238404472127172432 := by decide +kernel
private theorem endpoint_9_70_w2 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 2 2 238404472127172432 = some 238404472127172432 := by decide +kernel
private theorem endpoint_9_70_p4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 4 238404472127172432 = some 238404472127172432 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 2 2 238404472127172432 238404472127172432 238404472127172432 endpoint_9_70_w0 endpoint_9_70_w2
private theorem endpoint_9_70_w4 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 4 2 238404472127172432 = some 238404472127172432 := by decide +kernel
private theorem endpoint_9_70_p6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 6 238404472127172432 = some 238404472127172432 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 4 2 238404472127172432 238404472127172432 238404472127172432 endpoint_9_70_p4 endpoint_9_70_w4
private theorem endpoint_9_70_w6 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 6 2 238404472127172432 = some 238404472127172432 := by decide +kernel
private theorem endpoint_9_70_p8 : receiptWindow endpoint_9_70_flag endpoint_9_70_sources 0 8 238404472127172432 = some 238404472127172432 :=
  join_receipt_window endpoint_9_70_flag endpoint_9_70_sources 0 6 2 238404472127172432 238404472127172432 238404472127172432 endpoint_9_70_p6 endpoint_9_70_w6
def endpoint_9_70 : CertifiedEndpoint :=
  ⟨⟨9, 70, 2863⟩, 238404472127172432, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_70_flag endpoint_9_70_sources 8 238404472127172432 238404472127172432 rfl endpoint_9_70_base endpoint_9_70_p8) (by decide)⟩
private def endpoint_9_71_flag : Flag := ⟨9, 71, 2784⟩
private def endpoint_9_71_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_71_base : receiptBase endpoint_9_71_flag endpoint_9_71_sources = some 234843346231796642 := by decide +kernel
private theorem endpoint_9_71_w0 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 2 234843346231796642 = some 234843346231796642 := by decide +kernel
private theorem endpoint_9_71_w2 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 2 2 234843346231796642 = some 234843346231796642 := by decide +kernel
private theorem endpoint_9_71_p4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 4 234843346231796642 = some 234843346231796642 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 2 2 234843346231796642 234843346231796642 234843346231796642 endpoint_9_71_w0 endpoint_9_71_w2
private theorem endpoint_9_71_w4 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 4 2 234843346231796642 = some 234843346231796642 := by decide +kernel
private theorem endpoint_9_71_p6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 6 234843346231796642 = some 234843346231796642 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 4 2 234843346231796642 234843346231796642 234843346231796642 endpoint_9_71_p4 endpoint_9_71_w4
private theorem endpoint_9_71_w6 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 6 2 234843346231796642 = some 234843346231796642 := by decide +kernel
private theorem endpoint_9_71_p8 : receiptWindow endpoint_9_71_flag endpoint_9_71_sources 0 8 234843346231796642 = some 234843346231796642 :=
  join_receipt_window endpoint_9_71_flag endpoint_9_71_sources 0 6 2 234843346231796642 234843346231796642 234843346231796642 endpoint_9_71_p6 endpoint_9_71_w6
def endpoint_9_71 : CertifiedEndpoint :=
  ⟨⟨9, 71, 2784⟩, 234843346231796642, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_71_flag endpoint_9_71_sources 8 234843346231796642 234843346231796642 rfl endpoint_9_71_base endpoint_9_71_p8) (by decide)⟩
private def endpoint_9_72_flag : Flag := ⟨9, 72, 2701⟩
private def endpoint_9_72_sources : Sources := ⟨contact04, contact04, contact04⟩
private theorem endpoint_9_72_base : receiptBase endpoint_9_72_flag endpoint_9_72_sources = some 230774220028859740 := by decide +kernel
private theorem endpoint_9_72_w0 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 2 230774220028859740 = some 230774220028859740 := by decide +kernel
private theorem endpoint_9_72_w2 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 2 2 230774220028859740 = some 230774220028859740 := by decide +kernel
private theorem endpoint_9_72_p4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 4 230774220028859740 = some 230774220028859740 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 2 2 230774220028859740 230774220028859740 230774220028859740 endpoint_9_72_w0 endpoint_9_72_w2
private theorem endpoint_9_72_w4 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 4 2 230774220028859740 = some 230774220028859740 := by decide +kernel
private theorem endpoint_9_72_p6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 6 230774220028859740 = some 230774220028859740 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 4 2 230774220028859740 230774220028859740 230774220028859740 endpoint_9_72_p4 endpoint_9_72_w4
private theorem endpoint_9_72_w6 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 6 2 230774220028859740 = some 230774220028859740 := by decide +kernel
private theorem endpoint_9_72_p8 : receiptWindow endpoint_9_72_flag endpoint_9_72_sources 0 8 230774220028859740 = some 230774220028859740 :=
  join_receipt_window endpoint_9_72_flag endpoint_9_72_sources 0 6 2 230774220028859740 230774220028859740 230774220028859740 endpoint_9_72_p6 endpoint_9_72_w6
def endpoint_9_72 : CertifiedEndpoint :=
  ⟨⟨9, 72, 2701⟩, 230774220028859740, .terminal ⟨contact04, contact04, contact04⟩ (finish_receipt_window endpoint_9_72_flag endpoint_9_72_sources 8 230774220028859740 230774220028859740 rfl endpoint_9_72_base endpoint_9_72_p8) (by decide)⟩
private def endpoint_9_73_flag : Flag := ⟨9, 73, 2616⟩
private def endpoint_9_73_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_73_base : receiptBase endpoint_9_73_flag endpoint_9_73_sources = some 230956124751522784 := by decide +kernel
private theorem endpoint_9_73_w0 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 2 230956124751522784 = some 230956124751522784 := by decide +kernel
private theorem endpoint_9_73_w2 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 2 2 230956124751522784 = some 230956124751522784 := by decide +kernel
private theorem endpoint_9_73_p4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 4 230956124751522784 = some 230956124751522784 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 2 2 230956124751522784 230956124751522784 230956124751522784 endpoint_9_73_w0 endpoint_9_73_w2
private theorem endpoint_9_73_w4 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 4 2 230956124751522784 = some 230956124751522784 := by decide +kernel
private theorem endpoint_9_73_p6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 6 230956124751522784 = some 230956124751522784 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 4 2 230956124751522784 230956124751522784 230956124751522784 endpoint_9_73_p4 endpoint_9_73_w4
private theorem endpoint_9_73_w6 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 6 2 230956124751522784 = some 230956124751522784 := by decide +kernel
private theorem endpoint_9_73_p8 : receiptWindow endpoint_9_73_flag endpoint_9_73_sources 0 8 230956124751522784 = some 230956124751522784 :=
  join_receipt_window endpoint_9_73_flag endpoint_9_73_sources 0 6 2 230956124751522784 230956124751522784 230956124751522784 endpoint_9_73_p6 endpoint_9_73_w6
def endpoint_9_73 : CertifiedEndpoint :=
  ⟨⟨9, 73, 2616⟩, 230956124751522784, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_73_flag endpoint_9_73_sources 8 230956124751522784 230956124751522784 rfl endpoint_9_73_base endpoint_9_73_p8) (by decide)⟩
private def endpoint_9_74_flag : Flag := ⟨9, 74, 2527⟩
private def endpoint_9_74_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_74_base : receiptBase endpoint_9_74_flag endpoint_9_74_sources = some 225961265910616522 := by decide +kernel
private theorem endpoint_9_74_w0 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 2 225961265910616522 = some 225961265910616522 := by decide +kernel
private theorem endpoint_9_74_w2 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 2 2 225961265910616522 = some 225961265910616522 := by decide +kernel
private theorem endpoint_9_74_p4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 4 225961265910616522 = some 225961265910616522 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 2 2 225961265910616522 225961265910616522 225961265910616522 endpoint_9_74_w0 endpoint_9_74_w2
private theorem endpoint_9_74_w4 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 4 2 225961265910616522 = some 225961265910616522 := by decide +kernel
private theorem endpoint_9_74_p6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 6 225961265910616522 = some 225961265910616522 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 4 2 225961265910616522 225961265910616522 225961265910616522 endpoint_9_74_p4 endpoint_9_74_w4
private theorem endpoint_9_74_w6 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 6 2 225961265910616522 = some 225961265910616522 := by decide +kernel
private theorem endpoint_9_74_p8 : receiptWindow endpoint_9_74_flag endpoint_9_74_sources 0 8 225961265910616522 = some 225961265910616522 :=
  join_receipt_window endpoint_9_74_flag endpoint_9_74_sources 0 6 2 225961265910616522 225961265910616522 225961265910616522 endpoint_9_74_p6 endpoint_9_74_w6
def endpoint_9_74 : CertifiedEndpoint :=
  ⟨⟨9, 74, 2527⟩, 225961265910616522, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_74_flag endpoint_9_74_sources 8 225961265910616522 225961265910616522 rfl endpoint_9_74_base endpoint_9_74_p8) (by decide)⟩
private def endpoint_9_75_flag : Flag := ⟨9, 75, 2435⟩
private def endpoint_9_75_sources : Sources := ⟨contact11, contact11, contact12⟩
private theorem endpoint_9_75_base : receiptBase endpoint_9_75_flag endpoint_9_75_sources = some 220508952874076958 := by decide +kernel
private theorem endpoint_9_75_w0 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 2 220508952874076958 = some 220508952874076958 := by decide +kernel
private theorem endpoint_9_75_w2 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 2 2 220508952874076958 = some 220508952874076958 := by decide +kernel
private theorem endpoint_9_75_p4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 4 220508952874076958 = some 220508952874076958 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 2 2 220508952874076958 220508952874076958 220508952874076958 endpoint_9_75_w0 endpoint_9_75_w2
private theorem endpoint_9_75_w4 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 4 2 220508952874076958 = some 220508952874076958 := by decide +kernel
private theorem endpoint_9_75_p6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 6 220508952874076958 = some 220508952874076958 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 4 2 220508952874076958 220508952874076958 220508952874076958 endpoint_9_75_p4 endpoint_9_75_w4
private theorem endpoint_9_75_w6 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 6 2 220508952874076958 = some 220508952874076958 := by decide +kernel
private theorem endpoint_9_75_p8 : receiptWindow endpoint_9_75_flag endpoint_9_75_sources 0 8 220508952874076958 = some 220508952874076958 :=
  join_receipt_window endpoint_9_75_flag endpoint_9_75_sources 0 6 2 220508952874076958 220508952874076958 220508952874076958 endpoint_9_75_p6 endpoint_9_75_w6
def endpoint_9_75 : CertifiedEndpoint :=
  ⟨⟨9, 75, 2435⟩, 220508952874076958, .terminal ⟨contact11, contact11, contact12⟩ (finish_receipt_window endpoint_9_75_flag endpoint_9_75_sources 8 220508952874076958 220508952874076958 rfl endpoint_9_75_base endpoint_9_75_p8) (by decide)⟩
private def endpoint_9_76_flag : Flag := ⟨9, 76, 2340⟩
private def endpoint_9_76_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_76_base : receiptBase endpoint_9_76_flag endpoint_9_76_sources = some 216553312406952257 := by decide +kernel
private theorem endpoint_9_76_w0 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 2 216553312406952257 = some 216553312406952257 := by decide +kernel
private theorem endpoint_9_76_w2 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 2 2 216553312406952257 = some 216553312406952257 := by decide +kernel
private theorem endpoint_9_76_p4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 4 216553312406952257 = some 216553312406952257 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 2 2 216553312406952257 216553312406952257 216553312406952257 endpoint_9_76_w0 endpoint_9_76_w2
private theorem endpoint_9_76_w4 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 4 2 216553312406952257 = some 216553312406952257 := by decide +kernel
private theorem endpoint_9_76_p6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 6 216553312406952257 = some 216553312406952257 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 4 2 216553312406952257 216553312406952257 216553312406952257 endpoint_9_76_p4 endpoint_9_76_w4
private theorem endpoint_9_76_w6 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 6 2 216553312406952257 = some 216553312406952257 := by decide +kernel
private theorem endpoint_9_76_p8 : receiptWindow endpoint_9_76_flag endpoint_9_76_sources 0 8 216553312406952257 = some 216553312406952257 :=
  join_receipt_window endpoint_9_76_flag endpoint_9_76_sources 0 6 2 216553312406952257 216553312406952257 216553312406952257 endpoint_9_76_p6 endpoint_9_76_w6
def endpoint_9_76 : CertifiedEndpoint :=
  ⟨⟨9, 76, 2340⟩, 216553312406952257, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_76_flag endpoint_9_76_sources 8 216553312406952257 216553312406952257 rfl endpoint_9_76_base endpoint_9_76_p8) (by decide)⟩
private def endpoint_9_77_flag : Flag := ⟨9, 77, 2242⟩
private def endpoint_9_77_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_77_base : receiptBase endpoint_9_77_flag endpoint_9_77_sources = some 210012815828134107 := by decide +kernel
private theorem endpoint_9_77_w0 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 2 210012815828134107 = some 210012815828134107 := by decide +kernel
private theorem endpoint_9_77_w2 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 2 2 210012815828134107 = some 210012815828134107 := by decide +kernel
private theorem endpoint_9_77_p4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 4 210012815828134107 = some 210012815828134107 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 2 2 210012815828134107 210012815828134107 210012815828134107 endpoint_9_77_w0 endpoint_9_77_w2
private theorem endpoint_9_77_w4 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 4 2 210012815828134107 = some 210012815828134107 := by decide +kernel
private theorem endpoint_9_77_p6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 6 210012815828134107 = some 210012815828134107 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 4 2 210012815828134107 210012815828134107 210012815828134107 endpoint_9_77_p4 endpoint_9_77_w4
private theorem endpoint_9_77_w6 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 6 2 210012815828134107 = some 210012815828134107 := by decide +kernel
private theorem endpoint_9_77_p8 : receiptWindow endpoint_9_77_flag endpoint_9_77_sources 0 8 210012815828134107 = some 210012815828134107 :=
  join_receipt_window endpoint_9_77_flag endpoint_9_77_sources 0 6 2 210012815828134107 210012815828134107 210012815828134107 endpoint_9_77_p6 endpoint_9_77_w6
def endpoint_9_77 : CertifiedEndpoint :=
  ⟨⟨9, 77, 2242⟩, 210012815828134107, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_77_flag endpoint_9_77_sources 8 210012815828134107 210012815828134107 rfl endpoint_9_77_base endpoint_9_77_p8) (by decide)⟩
private def endpoint_9_78_flag : Flag := ⟨9, 78, 2141⟩
private def endpoint_9_78_sources : Sources := ⟨contact14, contact14, contact13⟩
private theorem endpoint_9_78_base : receiptBase endpoint_9_78_flag endpoint_9_78_sources = some 202978111001836059 := by decide +kernel
private theorem endpoint_9_78_w0 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 2 202978111001836059 = some 202978111001836059 := by decide +kernel
private theorem endpoint_9_78_w2 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 2 2 202978111001836059 = some 202978111001836059 := by decide +kernel
private theorem endpoint_9_78_p4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 4 202978111001836059 = some 202978111001836059 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 2 2 202978111001836059 202978111001836059 202978111001836059 endpoint_9_78_w0 endpoint_9_78_w2
private theorem endpoint_9_78_w4 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 4 2 202978111001836059 = some 202978111001836059 := by decide +kernel
private theorem endpoint_9_78_p6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 6 202978111001836059 = some 202978111001836059 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 4 2 202978111001836059 202978111001836059 202978111001836059 endpoint_9_78_p4 endpoint_9_78_w4
private theorem endpoint_9_78_w6 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 6 2 202978111001836059 = some 202978111001836059 := by decide +kernel
private theorem endpoint_9_78_p8 : receiptWindow endpoint_9_78_flag endpoint_9_78_sources 0 8 202978111001836059 = some 202978111001836059 :=
  join_receipt_window endpoint_9_78_flag endpoint_9_78_sources 0 6 2 202978111001836059 202978111001836059 202978111001836059 endpoint_9_78_p6 endpoint_9_78_w6
def endpoint_9_78 : CertifiedEndpoint :=
  ⟨⟨9, 78, 2141⟩, 202978111001836059, .terminal ⟨contact14, contact14, contact13⟩ (finish_receipt_window endpoint_9_78_flag endpoint_9_78_sources 8 202978111001836059 202978111001836059 rfl endpoint_9_78_base endpoint_9_78_p8) (by decide)⟩
private def endpoint_9_79_flag : Flag := ⟨9, 79, 2037⟩
private def endpoint_9_79_sources : Sources := ⟨contact15, contact15, contact13⟩
private theorem endpoint_9_79_base : receiptBase endpoint_9_79_flag endpoint_9_79_sources = some 197374721951164634 := by decide +kernel
private theorem endpoint_9_79_w0 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 2 197374721951164634 = some 197374721951164634 := by decide +kernel
private theorem endpoint_9_79_w2 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 2 2 197374721951164634 = some 197374721951164634 := by decide +kernel
private theorem endpoint_9_79_p4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 4 197374721951164634 = some 197374721951164634 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 2 2 197374721951164634 197374721951164634 197374721951164634 endpoint_9_79_w0 endpoint_9_79_w2
private theorem endpoint_9_79_w4 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 4 2 197374721951164634 = some 197374721951164634 := by decide +kernel
private theorem endpoint_9_79_p6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 6 197374721951164634 = some 197374721951164634 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 4 2 197374721951164634 197374721951164634 197374721951164634 endpoint_9_79_p4 endpoint_9_79_w4
private theorem endpoint_9_79_w6 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 6 2 197374721951164634 = some 197374721951164634 := by decide +kernel
private theorem endpoint_9_79_p8 : receiptWindow endpoint_9_79_flag endpoint_9_79_sources 0 8 197374721951164634 = some 197374721951164634 :=
  join_receipt_window endpoint_9_79_flag endpoint_9_79_sources 0 6 2 197374721951164634 197374721951164634 197374721951164634 endpoint_9_79_p6 endpoint_9_79_w6
def endpoint_9_79 : CertifiedEndpoint :=
  ⟨⟨9, 79, 2037⟩, 197374721951164634, .terminal ⟨contact15, contact15, contact13⟩ (finish_receipt_window endpoint_9_79_flag endpoint_9_79_sources 8 197374721951164634 197374721951164634 rfl endpoint_9_79_base endpoint_9_79_p8) (by decide)⟩
private def endpoint_9_80_flag : Flag := ⟨9, 80, 1929⟩
private def endpoint_9_80_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_80_base : receiptBase endpoint_9_80_flag endpoint_9_80_sources = some 191045353393949321 := by decide +kernel
private theorem endpoint_9_80_w0 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 2 191045353393949321 = some 191045353393949321 := by decide +kernel
private theorem endpoint_9_80_w2 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 2 2 191045353393949321 = some 191045353393949321 := by decide +kernel
private theorem endpoint_9_80_p4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 4 191045353393949321 = some 191045353393949321 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 2 2 191045353393949321 191045353393949321 191045353393949321 endpoint_9_80_w0 endpoint_9_80_w2
private theorem endpoint_9_80_w4 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 4 2 191045353393949321 = some 191045353393949321 := by decide +kernel
private theorem endpoint_9_80_p6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 6 191045353393949321 = some 191045353393949321 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 4 2 191045353393949321 191045353393949321 191045353393949321 endpoint_9_80_p4 endpoint_9_80_w4
private theorem endpoint_9_80_w6 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 6 2 191045353393949321 = some 191045353393949321 := by decide +kernel
private theorem endpoint_9_80_p8 : receiptWindow endpoint_9_80_flag endpoint_9_80_sources 0 8 191045353393949321 = some 191045353393949321 :=
  join_receipt_window endpoint_9_80_flag endpoint_9_80_sources 0 6 2 191045353393949321 191045353393949321 191045353393949321 endpoint_9_80_p6 endpoint_9_80_w6
def endpoint_9_80 : CertifiedEndpoint :=
  ⟨⟨9, 80, 1929⟩, 191045353393949321, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_80_flag endpoint_9_80_sources 8 191045353393949321 191045353393949321 rfl endpoint_9_80_base endpoint_9_80_p8) (by decide)⟩
private def endpoint_9_81_flag : Flag := ⟨9, 81, 1818⟩
private def endpoint_9_81_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_81_base : receiptBase endpoint_9_81_flag endpoint_9_81_sources = some 182143682413595799 := by decide +kernel
private theorem endpoint_9_81_w0 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 2 182143682413595799 = some 182143682413595799 := by decide +kernel
private theorem endpoint_9_81_w2 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 2 2 182143682413595799 = some 182143682413595799 := by decide +kernel
private theorem endpoint_9_81_p4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 4 182143682413595799 = some 182143682413595799 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 2 2 182143682413595799 182143682413595799 182143682413595799 endpoint_9_81_w0 endpoint_9_81_w2
private theorem endpoint_9_81_w4 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 4 2 182143682413595799 = some 182143682413595799 := by decide +kernel
private theorem endpoint_9_81_p6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 6 182143682413595799 = some 182143682413595799 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 4 2 182143682413595799 182143682413595799 182143682413595799 endpoint_9_81_p4 endpoint_9_81_w4
private theorem endpoint_9_81_w6 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 6 2 182143682413595799 = some 182143682413595799 := by decide +kernel
private theorem endpoint_9_81_p8 : receiptWindow endpoint_9_81_flag endpoint_9_81_sources 0 8 182143682413595799 = some 182143682413595799 :=
  join_receipt_window endpoint_9_81_flag endpoint_9_81_sources 0 6 2 182143682413595799 182143682413595799 182143682413595799 endpoint_9_81_p6 endpoint_9_81_w6
def endpoint_9_81 : CertifiedEndpoint :=
  ⟨⟨9, 81, 1818⟩, 182143682413595799, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_81_flag endpoint_9_81_sources 8 182143682413595799 182143682413595799 rfl endpoint_9_81_base endpoint_9_81_p8) (by decide)⟩
private def endpoint_9_82_flag : Flag := ⟨9, 82, 1705⟩
private def endpoint_9_82_sources : Sources := ⟨contact16, contact16, contact13⟩
private theorem endpoint_9_82_base : receiptBase endpoint_9_82_flag endpoint_9_82_sources = some 172792629163097426 := by decide +kernel
private theorem endpoint_9_82_w0 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 2 172792629163097426 = some 172792629163097426 := by decide +kernel
private theorem endpoint_9_82_w2 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 2 2 172792629163097426 = some 172792629163097426 := by decide +kernel
private theorem endpoint_9_82_p4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 4 172792629163097426 = some 172792629163097426 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 2 2 172792629163097426 172792629163097426 172792629163097426 endpoint_9_82_w0 endpoint_9_82_w2
private theorem endpoint_9_82_w4 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 4 2 172792629163097426 = some 172792629163097426 := by decide +kernel
private theorem endpoint_9_82_p6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 6 172792629163097426 = some 172792629163097426 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 4 2 172792629163097426 172792629163097426 172792629163097426 endpoint_9_82_p4 endpoint_9_82_w4
private theorem endpoint_9_82_w6 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 6 2 172792629163097426 = some 172792629163097426 := by decide +kernel
private theorem endpoint_9_82_p8 : receiptWindow endpoint_9_82_flag endpoint_9_82_sources 0 8 172792629163097426 = some 172792629163097426 :=
  join_receipt_window endpoint_9_82_flag endpoint_9_82_sources 0 6 2 172792629163097426 172792629163097426 172792629163097426 endpoint_9_82_p6 endpoint_9_82_w6
def endpoint_9_82 : CertifiedEndpoint :=
  ⟨⟨9, 82, 1705⟩, 172792629163097426, .terminal ⟨contact16, contact16, contact13⟩ (finish_receipt_window endpoint_9_82_flag endpoint_9_82_sources 8 172792629163097426 172792629163097426 rfl endpoint_9_82_base endpoint_9_82_p8) (by decide)⟩
def endpoint_9_83 : CertifiedEndpoint :=
  ⟨⟨9, 83, 1588⟩, 264859732313691139, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_84 : CertifiedEndpoint :=
  ⟨⟨9, 84, 1467⟩, 247146210510625755, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_85 : CertifiedEndpoint :=
  ⟨⟨9, 85, 1344⟩, 228546442761656951, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_86 : CertifiedEndpoint :=
  ⟨⟨9, 86, 1218⟩, 208869100604907218, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_87 : CertifiedEndpoint :=
  ⟨⟨9, 87, 1088⟩, 187914059263701695, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_88 : CertifiedEndpoint :=
  ⟨⟨9, 88, 955⟩, 165837461940728483, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_89 : CertifiedEndpoint :=
  ⟨⟨9, 89, 819⟩, 142619516927693540, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_90 : CertifiedEndpoint :=
  ⟨⟨9, 90, 680⟩, 118240432516302824, .intrinsic (by decide +kernel) (by decide)⟩
def endpoint_9_91 : CertifiedEndpoint :=
  ⟨⟨9, 91, 537⟩, 92491287615084122, .intrinsic (by decide +kernel) (by decide)⟩

def endpointBlock06 : List CertifiedEndpoint := [
  endpoint_8_58, endpoint_8_59, endpoint_8_60, endpoint_8_61, endpoint_8_62, endpoint_8_63, endpoint_8_64,
  endpoint_8_65, endpoint_8_66, endpoint_8_67, endpoint_8_68, endpoint_8_69, endpoint_8_70, endpoint_8_71,
  endpoint_8_72, endpoint_8_73, endpoint_8_74, endpoint_8_75, endpoint_8_76, endpoint_8_77, endpoint_8_78,
  endpoint_8_79, endpoint_8_80, endpoint_8_81, endpoint_8_82, endpoint_8_83, endpoint_8_84, endpoint_8_85,
  endpoint_8_86, endpoint_8_87, endpoint_8_88, endpoint_8_89, endpoint_8_90, endpoint_8_91, endpoint_8_92,
  endpoint_8_93, endpoint_8_94, endpoint_8_95, endpoint_9_9, endpoint_9_10, endpoint_9_11, endpoint_9_12,
  endpoint_9_13, endpoint_9_14, endpoint_9_15, endpoint_9_16, endpoint_9_17, endpoint_9_18, endpoint_9_19,
  endpoint_9_20, endpoint_9_21, endpoint_9_22, endpoint_9_23, endpoint_9_24, endpoint_9_25, endpoint_9_26,
  endpoint_9_27, endpoint_9_28, endpoint_9_29, endpoint_9_30, endpoint_9_31, endpoint_9_32, endpoint_9_33,
  endpoint_9_34, endpoint_9_35, endpoint_9_36, endpoint_9_37, endpoint_9_38, endpoint_9_39, endpoint_9_40,
  endpoint_9_41, endpoint_9_42, endpoint_9_43, endpoint_9_44, endpoint_9_45, endpoint_9_46, endpoint_9_47,
  endpoint_9_48, endpoint_9_49, endpoint_9_50, endpoint_9_51, endpoint_9_52, endpoint_9_53, endpoint_9_54,
  endpoint_9_55, endpoint_9_56, endpoint_9_57, endpoint_9_58, endpoint_9_59, endpoint_9_60, endpoint_9_61,
  endpoint_9_62, endpoint_9_63, endpoint_9_64, endpoint_9_65, endpoint_9_66, endpoint_9_67, endpoint_9_68,
  endpoint_9_69, endpoint_9_70, endpoint_9_71, endpoint_9_72, endpoint_9_73, endpoint_9_74, endpoint_9_75,
  endpoint_9_76, endpoint_9_77, endpoint_9_78, endpoint_9_79, endpoint_9_80, endpoint_9_81, endpoint_9_82,
  endpoint_9_83, endpoint_9_84, endpoint_9_85, endpoint_9_86, endpoint_9_87, endpoint_9_88, endpoint_9_89,
  endpoint_9_90, endpoint_9_91
]
end ProximityPrize.SubmissionLower.Koala6844Receipts
